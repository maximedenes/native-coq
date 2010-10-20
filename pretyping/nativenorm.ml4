(*i camlp4use: "q_MLast.cmo" i*)
open Term
open Environ
open Reduction
open Univ
open Declarations
open Names
open Inductive
open Util
open Unix
open Nativelib
open Nativecode
open Inductiveops
open Closure

exception Find_at of int

(* Required to make camlp5 happy. *)
let loc = Ploc.dummy

let compile env c =
  let mp = fst (Lib.current_prefix ()) in
  let code,annots = translate mp env "t1" c in
  let code =
    code @ [<:str_item< value _ = rnorm.val := lazy_norm (lazy $lid:"t1"$) >>]
  in
  let res,filename,mod_name = call_compiler code in
    res, filename, mod_name

let nf_betadeltaiotazeta env t =
  norm_val (create_clos_infos betadeltaiota env) (inject t)

let decompose_prod env t =
  let (name,dom,codom) = destProd (whd_betadeltaiota env t) in
  let dom = nf_betadeltaiotazeta env dom in
  if name = Anonymous then (Name (id_of_string "x"),dom,codom)
  else (name,dom,codom)

let find_rectype_a env c =
  let (t, l) =
    let t = whd_betadeltaiota env c in
    try destApp t with _ -> (t,[||]) in
  match kind_of_term t with
  | Term.Ind ind -> (ind, l)
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

let build_branch_type env (mind,_ as _ind) mib mip params p i =
  let rtbl = mip.mind_reloc_tbl in
  let cty = mip.mind_nf_lc.(i) in
  (* [build_one_branch i cty] construit le type de la ieme branche (commence
     a 0) et les lambda correspondant aux realargs *)
  let typi = type_constructor mind mib cty params in
  let decl,indapp = Term.decompose_prod typi in
  let ind,cargs = find_rectype_a env indapp in
  let nparams = Array.length params in
  let carity = snd (rtbl.(i)) in
  let crealargs = Array.sub cargs nparams (Array.length cargs - nparams) in
  let codom =
  let papp = mkApp(lift (List.length decl) p,crealargs) in
  let cstr = ith_constructor_of_inductive ind (i+1) in
  let relargs = Array.init carity (fun i -> mkRel (carity-i)) in
  let dep_cstr = mkApp(mkApp(mkConstruct cstr,params),relargs) in
    mkApp(papp,[|dep_cstr|])
  in
  decl, codom

let rec app_construct_args n kns env t ty args =
  let (_,xs) =
    Array.fold_left
        (fun (ty,args) arg ->
           let _,dom,codom = try decompose_prod env ty with _ -> exit 124 in
           let t,_ = rebuild_constr (n+1) kns env dom arg in
           (subst1 t codom, t::args))
        (ty,[]) args
  in
    Term.mkApp (t,Array.of_list (List.rev xs))

and rebuild_constr n kns env ty t =
  match t with
  | Lam st ->
      let name,dom,codom  = decompose_prod env ty in
      let env = push_rel (name,None,dom) env in
      let t, _ = rebuild_constr (n+1) kns env codom st in
      mkLambda (name,dom,t),ty
  | Rel i ->
      let l = n - i in
      let (_,_,ty) = lookup_rel l env in
      mkRel l, lift l ty
  | Constant c ->
      mkConst c, Typeops.type_of_constant env c
  | App (f,args) ->
      let f,t = rebuild_constr n kns env mkSet f in
      let aux (args,ty) arg =
        let _,dom,codom = decompose_prod env ty in
        let c,_ = rebuild_constr n kns env dom arg in
        (c::args,subst1 c codom)
      in
      let args,ty = Array.fold_left aux ([],t) args in
      mkApp(f,Array.of_list (List.rev args)), ty
  | Const_int tag ->
    fst (construct_of_constr true env tag ty), ty
  | Const_block (tag,args) ->
      let capp,ctyp = construct_of_constr false env tag ty in
      app_construct_args n kns env capp ctyp args, ty
  | Ind ind ->
    let ty = type_of_inductive env ind in
    mkInd ind, ty
  | Sort s ->
      mkSort s, ty
  | Var id ->
      let (_,_,ty) = lookup_named id env in
      mkVar id, ty
  | Case (p,c,ac,ci) ->
      print_endline "Case in normal form";
      let c_constr,match_ty = rebuild_constr n kns env mkSet c in
      print_endline "Reification of c done";
      let (mind,_ as ind),allargs = find_rectype_a env match_ty in
      let (mib,mip) = Inductive.lookup_mind_specif env ind in
      let nparams = mib.mind_nparams in
      let params,realargs = Util.array_chop nparams allargs in
      let ind_family = make_ind_family (ind,Array.to_list params) in
      let pT = arity_of_case_predicate env ind_family true set_sort in 
      let p_constr,_ = rebuild_constr n kns env pT p in
      print_endline "Reification of predicate done";
      let aux i x =
        print_endline ("Reification of branch nr "^string_of_int i);
        let decl,codom = build_branch_type env ind mib mip params p_constr i in
	let env,m =
	  List.fold_right
	    (fun (name,t) (env,m) -> push_rel (name,None,t) env, (m+1)) decl (env,0)
        in
        let b,_ =
          rebuild_constr (n+m) (* + nparams + nrealargs ? *) kns env codom x
        in
        let res = compose_lam decl b in print_endline "done"; res
      in
      let ac_constr = Array.mapi aux ac in
        mkCase (ci,p_constr,c_constr,ac_constr), ty
  | Prod (x,dom,codom) ->
      print_endline "Product in normal form";
      let dom,_ = rebuild_constr n kns env mkSet dom in
      let env = push_rel (x,None,dom) env in
      let codom,_ = rebuild_constr (n+1) kns env mkSet codom in
      mkProd (x,dom,codom), ty
  | Fix (l,rec_pos,ty,t) -> (* TODO : reification of mutual fixpoints *)
      print_endline "Fix in normal form";
      let ty,_ = rebuild_constr n kns env mkSet ty in
      let env = push_rel (l,None,ty) env in
      let t,_ = rebuild_constr (n+1) kns env ty t in
      mkFix (([|rec_pos|],0),([|l|],[|ty|],[|t|])), ty

let native_norm env c ty =
  let res, filename, mod_name = compile (pre_env env) c in
  match res with
    | 0 ->
      print_endline "Normalizing...";
      call_linker filename mod_name;
        fst (rebuild_constr 0 NbeAnnotTbl.empty env ty !Nativelib.rnorm)
    | _ -> anomaly "Compilation failure" 
