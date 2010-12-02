open Term
open Names
open Declarations
open Nativevalues
open Nativelambda

(*s Local names *)

type lname = { lname : name; luid : int }

let dummy_lname = { lname = Anonymous; luid = -1 }

let lname_ctr = ref (-1)

let reset_lname = lname_ctr := -1

let fresh_lname n = 
  incr lname_ctr;
  { lname = n; luid = !lname_ctr }

(*s Global names *)
type gname = 
  | Gind of inductive
  | Gconstruct of constructor
  | Gconstant of constant
  | Gcase of int
  | Gpred of int
  | Gfixtype of int
  | Gnorm of int
  | Ginternal of string

let case_ctr = ref (-1)

let reset_gcase () = case_ctr := -1

let fresh_gcase () =
  incr case_ctr;
  Gcase !case_ctr

let pred_ctr = ref (-1)

let reset_gpred () = pred_ctr := -1

let fresh_gpred () = 
  incr pred_ctr;
  Gpred !pred_ctr

let fixtype_ctr = ref (-1)

let reset_gfixtype () = fixtype_ctr := -1

let fresh_gfixtype () =
  incr fixtype_ctr;
  Gfixtype !fixtype_ctr

(*s Mllambda *)
  
type primitive =
  | Mk_prod of name
  | Mk_sort of sorts
  | Mk_ind of mutual_inductive
  | Mk_const of constant
  | Mk_sw of annot_sw
  | Is_accu
  | Is_int

type mllambda =
  | MLlocal        of lname 
  | MLglobal       of gname 
  | MLprimitive    of primitive
  | MLlam          of lname array * mllambda 
  | MLletrec       of (lname * lname array * mllambda) array * mllambda
  | MLlet          of lname * mllambda * mllambda
  | MLapp          of mllambda * mllambda array
  | MLif           of mllambda * mllambda * mllambda
  | MLmatch        of annot_sw * mllambda * mllambda * mllam_branches
                               (* argument, accu branch, branches *)
  | MLconstruct    of constructor * mllambda array
  | MLint          of int
  | MLparray       of mllambda array
  | MLval          of Nativevalues.t
  | MLsetref       of string * mllambda

and mllam_branches = (constructor * lname array * mllambda) array

let mkMLlam params body =
  if Array.length params = 0 then body 
  else
    match body with
    | MLlam (params', body) -> MLlam(Array.append params params', body)
    | _ -> MLlam(params,body)

let mkMLapp f args =
  if Array.length args = 0 then f
  else
    match f with
    | MLapp(f,args') -> MLapp(f,Array.append args' args)
    | _ -> MLapp(f,args)

(*s Global declaration *)
type global =
  | Gtblname of gname * identifier array
  | Gtblnorm of gname * lname array * mllambda array 
  | Gtblfixtype of gname * lname array * mllambda array
  | Glet of gname * mllambda
  | Gopen of string
  
let global_stack = ref ([] : global list)

let push_global_let gn body =
  global_stack := Glet(gn,body) :: !global_stack

let push_global_fixtype gn params body =
  global_stack := Gtblfixtype(gn,params,body) :: !global_stack

(*s Compilation environment *)

type env =
    { env_rel : mllambda list; (* (MLlocal lname) list *)
      env_bound : int; (* length of env_rel *)
      (* free variables *)
      env_urel : (int * mllambda) list ref; (* list of unbound rel *)
      env_named : (identifier * mllambda) list ref }

let empty_env () =
  { env_rel = [];
    env_bound = 0;
    env_urel = ref [];
    env_named = ref []
  }

let push_rel env id = 
  let local = fresh_lname id in
  local, { env with 
	   env_rel = MLlocal local :: env.env_rel;
	   env_bound = env.env_bound + 1
	 }

let push_rels env ids =
  let lnames, env_rel = 
    Array.fold_left (fun (names,env_rel) id ->
      let local = fresh_lname id in
      (local::names, MLlocal local::env_rel)) ([],env.env_rel) ids in
  Array.of_list lnames, { env with 
			  env_rel = env_rel;
			  env_bound = env.env_bound + Array.length ids
			}

let get_rel env id i =
  if i <= env.env_bound then
    List.nth env.env_rel (i-1)
  else 
    let i = i - env.env_bound in
    try List.assoc i !(env.env_urel)
    with Not_found ->
      let local = MLlocal (fresh_lname id) in
      env.env_urel := (i,local) :: !(env.env_urel);
      local

let get_var env id =
  try List.assoc id !(env.env_named)
  with Not_found ->
    let local = MLlocal (fresh_lname (Name id)) in
    env.env_named := (id, local)::!(env.env_named);
    local
   
(*s Traduction of lambda to mllambda *)

let get_prod_name codom = 
  match codom with
  | MLlam(ids,_) -> ids.(0).lname
  | _ -> assert false

let empty_params = [||]

let get_name (_,l) = 
  match l with
  | MLlocal id -> id
  | _ -> raise (Invalid_argument "Nativecode.get_name")

let fv_params env = 
  let fvn, fvr = !(env.env_named), !(env.env_urel) in 
  let size = List.length fvn + List.length fvr in
  if size = 0 then empty_params 
  else begin
    let params = Array.make size dummy_lname in
    let fvn = ref fvn in
    let i = ref 0 in
    while !fvn <> [] do
      params.(!i) <- get_name (List.hd !fvn);
      fvn := List.tl !fvn;
      incr i
    done;
    let fvr = ref fvr in
    while !fvr <> [] do
      params.(!i) <- get_name (List.hd !fvr);
      fvr := List.tl !fvr;
      incr i
    done;
    params
  end

let generalize_fv env body = 
  mkMLlam (fv_params env) body

let empty_args = [||]

let fv_args env fvn fvr =
  let size = List.length fvn + List.length fvr in
  if size = 0 then empty_args 
  else 
    begin
      let args = Array.make size (MLint 0) in
      let fvn = ref fvn in
      let i = ref 0 in
      while !fvn <> [] do
	args.(!i) <- get_var env (fst (List.hd !fvn));
	fvn := List.tl !fvn;
	incr i
      done;
      let fvr = ref fvr in
      while !fvr <> [] do
	args.(!i) <- get_rel env Anonymous (fst (List.hd !fvr));
	fvr := List.tl !fvr;
	incr i
      done;
      args
    end

let rec ml_of_lam env l =
  match l with
  | Lrel(id ,i) -> get_rel env id i
  | Lvar id -> get_var env id
  | Lprod(dom,codom) ->
      let dom = ml_of_lam env dom in
      let codom = ml_of_lam env codom in
      let n = get_prod_name codom in
      MLapp(MLprimitive(Mk_prod n), [|dom;codom|])
  | Llam(ids,body) ->
    let lnames,env = push_rels env ids in
    MLlam(lnames, ml_of_lam env body)
  | Lrec(id,body) ->
      let ids,body = decompose_Llam body in
      let lname, env = push_rel env id in
      let lnames, env = push_rels env ids in
      MLletrec([|lname, lnames, ml_of_lam env body|], MLlocal lname)
  | Llet(id,def,body) ->
      let def = ml_of_lam env def in
      let lname, env = push_rel env id in
      let body = ml_of_lam env body in
      MLlet(lname,def,body)
  | Lapp(f,args) ->
      MLapp(ml_of_lam env f, Array.map (ml_of_lam env) args)
  | Lconst c -> MLglobal(Gconstant c)
  | Lprim _ | Lcprim _ -> assert false
  | Lcase (annot,p,a,bs) ->
      (* let predicate_uid fv_pred = compilation of p 
         let rec case_uid fv a_uid = 
           match a_uid with
           | Accu _ => mk_sw (predicate_uid fv_pred) (case_uid fv) a_uid
           | Ci argsi => compilation of branches 
         compile case = case_uid fv (compilation of a) *)
      (* Compilation of the predicate *)
         (* Remark: if we do not want to compile the predicate we 
            should a least compute the fv, then store the lambda representation
            of the predicate (not the mllambda) *)
      let env_p = empty_env () in
      let pn = fresh_gpred () in
      let mlp = ml_of_lam env_p p in
      let mlp = generalize_fv env_p mlp in
      let (pfvn,pfvr) = !(env_p.env_named), !(env_p.env_urel) in
      push_global_let pn mlp; 
      (* Compilation of the case *)
      let env_c = empty_env () in
      let a_uid = fresh_lname Anonymous in
      let la_uid = MLlocal a_uid in
      (* compilation of branches *)
      let ml_br (c,params, body) = 
	let lnames, env = push_rels env_c params in
	(c,lnames, ml_of_lam env body) in
      let bs = Array.map ml_br bs in
      let cn = fresh_gcase () in
      (* Compilation of accu branch *)
      let pred = MLapp(MLglobal pn, fv_args env_c pfvn pfvr) in  
      let (fvn, fvr) = !(env_c.env_named), !(env_c.env_urel) in
      let cn_fv = mkMLapp (MLglobal cn) (fv_args env_c fvn fvr) in
         (* remark : the call to fv_args does not add free variables in env_c *)
      let accu = MLapp(MLprimitive (Mk_sw annot), [| pred; cn_fv; la_uid |]) in
      let body = MLlam([|a_uid|], MLmatch(annot, la_uid, accu, bs)) in
      let case = generalize_fv env_c body in
      push_global_let cn case;
      (* Final result *)
      mkMLapp cn_fv [|ml_of_lam env a|]
  | Lareint _ -> assert false
  | Lif(t,bt,bf) -> 
      MLif(ml_of_lam env t, ml_of_lam env bt, ml_of_lam env bf)
  | Lfix ((rec_pos,start), fdecl) -> assert false
      (* let type_f fvt = [| type fix |] 
         let norm_f1 fv f1 .. fn params1 = body1
	 ..
         let norm_fn fv f1 .. fn paramsn = bodyn
         let norm fv f1 .. fn = 
	    [|norm_f1 fv f1 .. fn; ..; norm_fn fv f1 .. fn|]
         compile fix = 
	   let rec f1 params1 = 
             if is_accu rec_pos.(1) then mk_fix (type_f fvt) (norm fv) params1
	     else norm_f1 fv f1 .. fn params1
           and .. and fn paramsn = 
	     if is_accu rec_pos.(n) then mk_fix (type_f fvt) (norm fv) paramsn
             else norm_fn fv f1 .. fv paramsn in
	   start
      *)
      (* Compilation of type *)
    (*  let env_t = empty_env () in
      let ml_t = Array.map (fun (_,t,_) -> ml_of_lam env_t t) fdecl in
      let params_t = fv_params env_t in
      let args_t = fv_args env !(env_t.env_named) !(env_t.env_urel) in
      let gft = fresh_gfixtype () in
      push_global_fixtype gft params_t ml_t;
      (* Compilation of norm_i *)
      let ids = Array.map (fun (id,_,_) -> id) fdecl in
      let lf,env_n = push_rels (fresh_env ()) ids in
      let t_params = Array.make (Array.length fdecl) [||] in
      let t_norm_f = Array.make (Array.length fdecl) (Gnorm (-1)) in
      let ml_of_fix i (_,_,body) =
	let idsi,bodyi = decompose_Llam body in
	let paramsi, envi = push_rels env_n idsi in
	let norm_fi = fresh_gnorm () in
	t_norm_f.(i) <- norm_fi;
	let bodyi = ml_of_lam envi bodyi in
	t_params.(i) <- paramsi;
	mkMLlam paramsi bodyi in
      let tnorm = Array.mapi ml_of_fix fdecl in
      let fvn,fvr = !(env_n.env_named), !(env_n.env_urel) in
      let fv_params = fv_params env_n in
      let fv_args = fv_args env_n fvn fvr in
      let norm_params = Array.append fv_params lf in
      let norm_args = 
        Array.append fv_args (Array.map (fun id -> MLlocal id) lf) in
      Array.iteri (fun i body ->
	push_global_let (t_norm_f.(i)) (mkMLlam norm_params body));
      let norm = fresh_gtblnorm () in
      push_global_tbl norm norm_params 
         (Array.map (fun g -> mkMLapp (MLglobal g) norm_args) t_norm_f);
      let mkrec i lname = 
	let paramsi = t_params.(i) in
	let reci = t_paramsi.(rec_pos.(i)) in
	let body = 
	  MLif(MLapp(MLprimitive Is_accu,[|reci|]),
	       MLapp(MLprimitve Mk_fix, [|MLapp(MLglobal gft, args_t);
					  MLapp(MLglobal norm, fv_args);
					  
      MLletrec(,) *)

      
      
      

      


  | Lcofix _ -> assert false
  | Lmakeblock (cn,_,args) ->
      MLconstruct(cn,Array.map (ml_of_lam env) args)
  | Lconstruct cn ->
      MLglobal (Gconstruct cn)
  | Lint i -> MLint i
  | Lparray t -> MLparray(Array.map (ml_of_lam env) t)
  | Lval v -> MLval v
  | Lsort s -> MLprimitive(Mk_sort s)
  | Lind i -> MLglobal (Gind i)

let mllambda_of_lambda auxdefs l =
  let env = empty_env () in
  global_stack := auxdefs;
  let ml = ml_of_lam env l in
  let fv_rel = !(env.env_urel) in
  let fv_named = !(env.env_named) in
  (* build the free variables *)
  let get_name (_,l) = 
   match l with
   | MLlocal x -> x
   | _ -> assert false in
  let params = 
    List.append (List.map get_name fv_rel) (List.map get_name fv_named) in
  (* final result : global list, fv, ml *)
  (!global_stack, (fv_named, fv_rel), mkMLlam (Array.of_list params) ml)


(** Printing to ocaml **)
(* Redefine a bunch of functions in module Names to generate names
   acceptable to OCaml. *)
let string_of_dirpath = function
  | [] -> "_"
  | sl -> String.concat "_" (List.map string_of_id (List.rev sl))

let mod_uid_of_dirpath dir = string_of_dirpath (repr_dirpath dir)

let string_of_kn kn =
  let (mp,dp,l) = repr_kn kn in
  (*string_of_dirpath dp ^*) string_of_label l


let string_of_name x =
  match x with
    | Anonymous -> "anonymous" (* assert false *)
    | Name id -> string_of_id id

(* Relativization of module paths *)
let rec list_of_mp acc = function
  | MPdot (mp,l) -> list_of_mp (string_of_label l::acc) mp
  | MPfile dp ->
      let dp = repr_dirpath dp in
      string_of_dirpath dp :: acc
  | MPbound mbid -> string_of_label (label_of_mbid mbid)::acc

let list_of_mp mp = list_of_mp [] mp

let rec strip_common_prefix l1 l2 =
  match l1, l2 with
  | [], _
  | _, [] -> l1, l2
  | hd1::tl1, hd2::tl2 ->
      if hd1 = hd2 then strip_common_prefix tl1 tl2 else hd1::tl1, hd2::tl2

let mk_relative_id base_mp (mp,id) =
  let base_l = list_of_mp base_mp in
  let l = list_of_mp mp in
  let _,l = strip_common_prefix base_l l in
  match l with
  | [] -> id
  | hd1::tl1 ->
      let s = List.fold_left (fun acc x -> acc^"."^x) hd1 tl1 in
      s^"."^id

let pp_gname base_mp fmt g =
  match g with
  | Gind (mind,i) ->
      let (mp,dp,l) = repr_kn (canonical_mind mind) in
      let id = Format.sprintf "ind_%s_%i" (string_of_label l) i in
      Format.fprintf fmt "%s" (mk_relative_id base_mp (mp,id))
  | Gconstruct ((mind,i),j) ->
      let (mp,dp,l) = repr_kn (canonical_mind mind) in
      let id = Format.sprintf "Construct_%s_%i_%i" (string_of_label l) i j in
      Format.fprintf fmt "%s" (mk_relative_id base_mp (mp,id))
  | Gconstant c ->
      Format.fprintf fmt "const_%s" (string_of_kn (canonical_con c))
  | Gcase i ->
      Format.fprintf fmt "case_%i" i
  | Gpred i ->
      Format.fprintf fmt "pred_%i" i
  | Gfixtype _ -> assert false
  | Gnorm _ -> assert false
  | Ginternal s -> Format.fprintf fmt "%s" s

(*let pp_rel cenv id fmt i =
  assert (i>0);
  let lvl = cenv.env_bound - i in
  match List.nth cenv.env_rel (i-1) with
    | MLlocal id' ->
      assert (id == id');
      let s = string_of_name id.lname in
      Format.fprintf fmt "r_%i_%s" lvl s
    | _ -> assert false*)

let pp_lname fmt ln =
  Format.fprintf fmt "x%s%i" (string_of_name ln.lname) ln.luid

let pp_primitive fmt = function
  | Mk_prod id -> Format.fprintf fmt "mk_prod_accu %s" (string_of_name id)
  | Mk_sort s -> 
      Format.fprintf fmt "mk_sort_accu (str_decode \"%s\")" (str_encode s)
  | Mk_ind ind -> 
      Format.fprintf fmt "mk_ind_accu (str_decode \"%s\")" (str_encode ind)
  | Mk_const kn -> 
      Format.fprintf fmt "mk_constant_accu (str_decode \"%s\")" (str_encode kn)
  | Mk_sw asw -> 
      Format.fprintf fmt "mk_sw_accu"
  | Is_accu -> Format.fprintf fmt "is_accu"
  | Is_int -> Format.fprintf fmt "is_int"

let pp_ldecls fmt ids =
  let len = Array.length ids in
  for i = 0 to len - 1 do
    Format.fprintf fmt " %a" pp_lname ids.(i)
  done

let pp_mllam base_mp fmt l =
let rec pp_mllam fmt l =
  match l with
  | MLlocal ln -> Format.fprintf fmt "@[%a@]" pp_lname ln
  | MLglobal g -> Format.fprintf fmt "@[%a@]" (pp_gname base_mp) g
  | MLprimitive p -> Format.fprintf fmt "@[%a@]" pp_primitive p
  | MLlam(ids,body) ->
    Format.fprintf fmt "@[(fun%a@ ->@\n %a)@]"
      pp_ldecls ids pp_mllam body
  | MLletrec(defs, body) ->
      Format.fprintf fmt "@[%a@ in@\n%a@]" pp_letrec defs 
      pp_mllam body
  | MLlet(id,def,body) ->
      Format.fprintf fmt "@[let@ %a@ =@\n %a@ in@\n%a@]"
         pp_lname id pp_mllam def pp_mllam body
  | MLapp(f, args) ->
      Format.fprintf fmt "@[%a@ %a@]" pp_mllam f (pp_args true) args
  | MLif(t,l1,l2) ->
      Format.fprintf fmt "@[if %a then@\n  %a@\nelse@\n  %a@]"
	pp_mllam t pp_mllam l1 pp_mllam l2 
  | MLmatch (asw, c, accu_br, br) ->
      let mind,i = asw.asw_ind in
      let (mp,dp,l) = repr_kn (canonical_mind mind) in
      let accu = Format.sprintf "Accu_%s_%i" (string_of_label l) i in
      let accu = mk_relative_id base_mp (mp,accu) in
      Format.fprintf fmt "@[begin match %a with |%s -> %a %a@\nend@]"
	pp_mllam c accu pp_mllam accu_br pp_branches br

     (* of annot_sw * mllambda * mllambda *
  mllam_branches *)
                               (* argument, accu branch, branches *)
  | MLconstruct(cn,args) -> assert false
(*      Format.fprintf fmt "@[%s%a@]" cn (pp_cargs cenv) args *)
  | MLint i -> Format.fprintf fmt "%i" i
  | MLparray _ -> assert false
  | MLval _ -> assert false 
  | MLsetref (s, body) ->
      Format.fprintf fmt "@[%s@ :=@\n %a@]" s pp_mllam body

(*  | Lmatch(a,bs) ->
      Format.fprintf fmt "@[begin match %a with%a@\nend@]"
	(pp_mllam cenv) a (pp_branches cenv) bs
  *)

and pp_letrec fmt defs =
  let len = Array.length defs in
  let pp_one_rec i (fn, argsn, body) =
    let len' = Array.length argsn in
    Format.fprintf fmt "%a%a =@\n  %a"
      pp_lname fn 
      pp_ldecls argsn pp_mllam body in
  Format.fprintf fmt "letrec ";
  pp_one_rec 0 defs.(0);
  for i = 1 to len - 1 do
    Format.fprintf fmt "and ";
    pp_one_rec i defs.(i)
  done

and pp_blam fmt l =
  match l with
  | MLprimitive (Mk_prod _ | Mk_sort _) 
  | MLlam _ | MLletrec _ | MLlet _ | MLapp _ | MLif _ ->
      Format.fprintf fmt "(%a)" pp_mllam l
  | MLconstruct(_,args) when Array.length args > 0 ->
      Format.fprintf fmt "(%a)" pp_mllam l
  | _ -> pp_mllam fmt l

and pp_args sep fmt args =
  let pp_mllam = if sep then pp_blam else pp_mllam in
  let sep = if sep then " " else "," in
  let len = Array.length args in
  if len > 0 then begin
    Format.fprintf fmt "%a" pp_mllam args.(0);
    for i = 1 to len - 1 do
      Format.fprintf fmt "%s%a" sep pp_mllam args.(i)
    done
  end 

and pp_cargs fmt args =
  let len = Array.length args in
  match len with
  | 0 -> ()
  | 1 -> Format.fprintf fmt " %a" pp_blam args.(0)
  | _ -> Format.fprintf fmt "(%a)" (pp_args false) args

and pp_branches fmt bs =
  let pp_branch (cn,args,body) =
(*    let cenv = push_rels cenv argsn in*)
    (* let args = Array.mapi (fun i id -> MLrel(id,len-i)) argsn in *)
    let args = Array.map (fun ln -> MLlocal ln) args in
    Format.fprintf fmt "@\n| %a%a ->@\n  %a" 
	(pp_gname base_mp) (Gconstruct cn) pp_cargs args pp_mllam body
  in
  Array.iter pp_branch bs

in
  (* Opens a global box and flushes output *)
  Format.fprintf fmt "@[%a@]@." pp_mllam l
  


(*
type comp = global list

let globals = ref ([] : comp)

let mk_rel cenv i = assert false

let rec mllambda_of_constr cenv c =
  match kind_of_term c with
  | Rel i -> Lrel (mk_rel cenv i)
  | Lambda _ -> assert false
(*      let params, body = decompose_lam c in
      let ids = get_names (List.rev params) in
      let ln,cenv = push_rels ids cenv in
      let lb = mllambda_of_constr cenv body in
      mkLlam ids lb*)
  | App(f, args) -> assert false (* mllambda_of_app cenv f args *)
(*
  | Var id -> Lglobal (get_var cenv id)
  | Sort s -> Lprimitive (Mk_sort s)
  | Ind ind -> Lglobal (get_ind cenv ind)
  | Prod(x, dom, codom) ->
      let ld = mllambda_of_constr cenv dom in
      let lx, cenv = push_rel x cenv in
      let lc = mllambda_of_constr cenv codom in
      Lapp(Lprimitive (Mk_prod x), [|ld; Llam([|lx|],lc)|])
	
  | LetIn(x, def, _, body) ->
      let ld = mllambda_of_constr cenv def in
      let lx,cenv = push_rel x cenv in 
      let lb = mllambda_of_constr cenv body in
      Llet(lx, ld, lb)

  | Const _ -> mllambda_of_app cenv c empty_args

  | Construct _ -> mllambda_of_app cenv c empty_args

  | Case(ci,t,a,branches) ->  
      (* generation de la def global ---> fv, match_toto *)
      (* *)
      let la = mllambda_of_constr cenv a in
      Lapp(match_toto, [| fv; la|])

  | Fix(rec_init,(names,type_bodies,rec_bodies)) ->
      (* generation de norm --> fv, norm_toto*)
      (* 
      let norm_toto_i fv totos = fun params_i -> body_i 
      let norm_toto fv totos = 
        [| norm_toto_i fv |]
      let type_toto fv =
        Lazy [| types |] 
      
      let rec toto_i = 
        fun params_i ->
         if is_accu rec_arg then mk_fix_accu (norm_toto fv) (types fv) params
	 else norm_toto_i fv totos params
       and toto_j = ...
       in toto_rec_init
      *)
	
  | CoFix(init,(names,type_bodies,rec_bodies)) -> ...

  | NativeInt i -> Lint i
  | NativeArr(_,p) -> makearray (mllambda_of_args env 0 p)

(*  
(*
  | Lprim         of constant option * Native.prim_op * mllambda array
	(* No check if None *)
  | Lcprim        of constant * Native.caml_prim * mllambda array *)
  | Lcase         of annot_sw * mllambda * mllambda * lam_branches 
  | Lareint       of mllambda array 

  | Lfix          of (int array * int) * fix_decl 
  | Lcofix        of int * fix_decl 
  | Lmakeblock    of int * mllambda array
  | Lint          of int
  | Lval          of values
  | Lsort         of sorts
  | Lind          of inductive

Prod(x,dom,codom) -->
  mkprodaccu "x" dom (fun x -> codom)

*)
*)
*)

let pp_global base_mp fmt g =
  match g with
(*  | Gtblname of gname * identifier array
  | Gtblnorm of gname * lname array * mllambda array 
  | Gtblfixtype of gname * lname array * mllambda array*)
  | Glet (gn, c) ->
      Format.fprintf fmt "@[let %a = %a@]@." (pp_gname base_mp) gn (pp_mllam
      base_mp) c
  | Gopen s ->
      Format.fprintf fmt "@[open %s@]@." s
  | _ -> assert false


let pp_globals base_mp fmt l = List.iter (pp_global base_mp fmt) l

(* Compilation of elements in environment *)
let compile_constant env auxdefs mp l cb =
  match cb.const_body with
  | Def t ->
      let t = Declarations.force t in
      let code = lambda_of_constr env t in
      let auxdefs,_,code = mllambda_of_lambda auxdefs code in
      Glet(Gconstant (make_con mp empty_dirpath l),code), auxdefs
  | _ -> 
      let kn = make_con mp empty_dirpath l in
      Glet(Gconstant kn, MLprimitive (Mk_const kn)), []


let compile_mind mb mind =
  Glet(Gind (mind,0), MLprimitive(Mk_ind mind))

let mk_opens l =
  List.map (fun s -> Gopen s) l

let mk_internal_let s code =
  Glet(Ginternal s, code)


(* ML Code for conversion function *)
let conv_main_code =
  let g1 = MLglobal (Ginternal "t1") in
  let g2 = MLglobal (Ginternal "t2") in
  [Glet(Ginternal "_", MLsetref("rt1",g1));
  Glet(Ginternal "_", MLsetref("rt2",g2));]
