(*i camlp4use: "q_MLast.cmo" i*)
open Term
open Environ
open Reduction
open Univ
open Declarations
open Names
open Inductive
open Util
open Nativelib
open Nativecode
open Nbeconv
open Unix

exception Find_at of int

(* Required to make camlp5 happy. *)
let loc = Ploc.dummy

let compile env c =
  if Sys.file_exists (env_name^".ml") then
    anomaly (env_name ^".ml already exists");
  if Sys.file_exists (terms_name^".ml") then
    anomaly (terms_name ^".ml already exists");
  let code,annots = translate env (RelKey (-1)) c in
  Pcaml.input_file := "/dev/null";
  let (dump,kns) = dump_env [c] env in
    Pcaml.input_file := "/dev/null";
    Pcaml.output_file := Some "envpr.ml";
    !Pcaml.print_implem (dump);
    Pcaml.output_file := Some "termspr.ml";
    !Pcaml.print_implem [(<:str_item< value c = $code$ >>, loc)];
  let kns = Stringmap.add "-1" (RelKey (-1),annots) kns in
    Nbeconv.print_implem (env_name^".ml") (compute_loc dump);
    Nbeconv.print_implem (terms_name^".ml")
	 [(<:str_item< open Nativelib >>, loc);
	  (<:str_item< open Nativevalues >>, loc);
	  (<:str_item< open $list: [env_name]$ >>, loc);
	  (<:str_item< value c = Obj.magic $code$ >>, loc);
	  (<:str_item< value _ = print_nf (lazy c) >>, loc)];
  kns

let decompose_prod env t =
  let (name,dom,codom as res) = destProd (whd_betadeltaiota env t) in
  if name = Anonymous then (Name (id_of_string "x"),dom,codom)
  else res

let find_rectype_a env c =
  let (t, l) =
    let t = whd_betadeltaiota env c in
    try destApp t with _ -> (t,[||]) in
  match kind_of_term t with
  | Ind ind -> (ind, l)
  | _ -> raise Not_found

let type_constructor mind mib typ params =
  let s = ind_subst mind mib in
  let ctyp = substl s typ in
  let nparams = Array.length params in
  if nparams = 0 then ctyp
  else
    let _,ctyp = decompose_prod_n nparams ctyp in
    substl (List.rev (Array.to_list params)) ctyp

let invert_tag cst tag reloc_tbl =
  try
    for j = 0 to Array.length reloc_tbl - 1 do
      let tagj,arity = reloc_tbl.(j) in
      if tag = tagj && (cst && arity = 0 || not(cst || arity = 0)) then
	raise (Find_at j)
      else ()
    done;raise Not_found
  with Find_at j -> (j+1)

let construct_of_constr const env tag typ =
  let (mind,_ as ind), allargs = find_rectype_a env typ in
    let mib,mip = lookup_mind_specif env ind in
    let nparams = mib.mind_nparams in
    let i = invert_tag const tag mip.mind_reloc_tbl in
    let params = Array.sub allargs 0 nparams in
    let ctyp = type_constructor mind mib (mip.mind_nf_lc.(i-1)) params in
      (Term.mkApp(mkConstruct(ind,i), params), ctyp)

let rec app_construct_args n kns env t ty args =
  let (_,xs) =
    Array.fold_right
        (fun arg (ty,args) ->
           let _,dom,codom = try decompose_prod env ty with _ -> exit 124 in
           let t = rebuild_constr (n+1) kns env dom arg in
           (subst1 t codom, t::args))
        args (ty,[])
  in
    Term.mkApp (t,Array.of_list xs)

and rebuild_constr n kns env ty t =
  match t with
  |  Lam st ->
      let name,dom,codom  = decompose_prod env ty in
      mkLambda (name,dom,rebuild_constr (n+1) kns env codom st)
  | Rel i ->
      mkRel (i+1)
  (*| App of lam * lam array*)
  | Const_int tag ->
    fst (construct_of_constr true env tag ty)
  | Const_block (tag,args) ->
      let capp,ctyp = construct_of_constr false env tag ty in
      app_construct_args n kns env capp ctyp args
  | Id s ->
       let (ik,_) = Stringmap.find s kns in
      (match ik with
        | ConstKey c -> mkConst c
        (*| VarKey id -> mkVar id*)
        | _ -> assert false)
  | Var id ->
      mkVar id

  (*| Case of lam * (tag * int array * lam) array
  | Fix of int * lam

    | Set -> mkSet
    | Prop -> mkProp
    | Type u -> mkType (type1_univ)
    | Lambda st ->
        let name,dom,codom  = decompose_prod env ty in
        mkLambda (name,dom,rebuild_constr (n+1) kns env codom st)
    | Rel i -> mkRel (i+1)
    | Var id -> mkVar id
    | Con s ->
        let (ik,_) = Stringmap.find s kns in
        (match ik with
          | ConstKey c -> mkConst c
          | _ -> assert false)
    | App (f::l) ->
        let ft = rebuild_constr n kns env mkSet f in
        let lt = List.map (rebuild_constr n kns env mkSet) l in
          mkApp (ft,Array.of_list lt)
    | Const (i,args) ->
      let (mind,_ as ind), allargs = find_rectype_args env ty in
      let mib,mip = lookup_mind_specif env ind in
      let nparams = mib.mind_nparams in
      let params = Array.sub allargs 0 nparams in
      let ctyp = type_constructor mind mib (mip.mind_nf_lc.(i-1)) params in
      let t = mkApp(mkConstruct(ind,i), params) in
        app_construct_args n kns env t ctyp args
    | Match (s,i,pi,c,ac) ->
      let (_,annots) = Stringmap.find s kns in
      let ci = match NbeAnnotTbl.find i annots with
        | CaseAnnot ci -> ci
        | _ -> assert false
      in
      let pi_constr = rebuild_constr n kns env ty pi in
      let c_constr = rebuild_constr n kns env mkSet c in
      let ac_constr = Array.map (rebuild_constr n (**) kns env ty) ac in
        mkCase (ci,pi_constr,c_constr,ac_constr)*)
    | _ -> assert false

let native_norm env c ty =
  let kns = compile (pre_env env) c in
  let file_names = env_name^".ml "^terms_name^".ml" in
  let _ = Unix.system ("touch "^env_name^".ml") in
  print_endline "Compilation...";
  let comp_cmd =
    "ocamlopt.opt -rectypes "^include_dirs^include_libs^file_names
  in
  let res = Unix.system comp_cmd in
  let _ = Unix.system ("rm "^file_names) in
  match res with
    | Unix.WEXITED 0 ->
      print_endline "Normalizing...";
      let ch_in = open_process_in "./a.out" in
      let nf = Marshal.from_channel ch_in in
        rebuild_constr 0 kns env ty nf
    | _ -> anomaly "Compilation failure" 
