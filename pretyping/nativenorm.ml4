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

(* Required to make camlp5 happy. *)
let loc = Ploc.dummy

let compile env c =
  if Sys.file_exists (env_name^".ml") then
    anomaly (env_name ^".ml already exists");
  if Sys.file_exists (terms_name^".ml") then
    anomaly (terms_name ^".ml already exists");
  let code = translate env c in
    Pcaml.input_file := "/dev/null";
    let dump = dump_env [c] env in
    Nbeconv.print_implem (env_name^".ml") (compute_loc dump);
    Nbeconv.print_implem (terms_name^".ml")
	 [(<:str_item< open Nativelib >>, loc);
	  (<:str_item< open $list: [env_name]$ >>, loc);
	  (<:str_item< value c = $code$ >>, loc);
	  (<:str_item< value _ = print_nf c >>, loc)]

let decompose_prod env t =
  let (name,dom,codom as res) = destProd (whd_betadeltaiota env t) in
  if name = Anonymous then (Name (id_of_string "x"),dom,codom)
  else res

let find_rectype_args env c =
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

let rec app_construct_args n env t ty args =
  let (_,xs) =
    Array.fold_right
        (fun arg (ty,args) ->
           let _,dom,codom = try decompose_prod env ty with _ -> exit 124 in
           let t = rebuild_constr (n+1) env dom arg in
           (subst1 t codom, t::args))
        args (ty,[])
  in
    mkApp (t,Array.of_list xs)

and rebuild_constr n env ty t =
  match t with
    | Set -> mkSet
    | Prop -> mkProp
    | Type u -> mkType (type1_univ)
    | Lambda st ->
        let name,dom,codom  = decompose_prod env ty in
        mkLambda (name,dom,rebuild_constr (n+1) env codom st)
    | Rel i -> mkRel (i+1)
    | Var id -> mkVar id
    | App (f::l) ->
        let ft = rebuild_constr n env mkSet f in
        let lt = List.map (rebuild_constr n env mkSet) l in
          mkApp (ft,Array.of_list lt)
    | Const (i,args) ->
      let (mind,_ as ind), allargs = find_rectype_args env ty in
      let mib,mip = lookup_mind_specif env ind in
      let nparams = mib.mind_nparams in
      let params = Array.sub allargs 0 nparams in
      let ctyp = type_constructor mind mib (mip.mind_nf_lc.(i-1)) params in
      let t = mkApp(mkConstruct(ind,i), params) in
        app_construct_args n env t ctyp args
    | _ -> assert false

let native_norm env c ty =
  let _ = compile (pre_env env) c in
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
        rebuild_constr 0 env ty nf
    | _ -> anomaly "Compilation failure" 
