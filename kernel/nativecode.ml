open Term
open Names

type constr_name = string

type lname = string

type global_name = string

(* **)

type primitive =
  | Mk_prod of lname
  | Mk_sort of sorts
  | Is_accu
  | Is_int

type mllambda =
  | Lrel          of (lname * int)
  | Lglobal       of global_name 
  | Lprimitive    of primitive
  | Llam          of lname array * mllambda 
  | Lletrec       of (lname * lname array * mllambda) array * mllambda
  | Llet          of lname * mllambda * mllambda
  | Lapp          of mllambda * mllambda array
  | Lif           of mllambda * mllambda * mllambda
  | Lmatch        of mllambda * (constr_name * lname array * mllambda) array
  | Lconstruct    of constr_name * mllambda array
  | Lint          of int
  | Lparray       of mllambda array

type global =
(*  | Gmatch of ...
  | Gtblname of global_name * lname array
  | Gtblfixtype of global_name * lamba array (* add Lazy for ocaml *)
  | Gtblnorm of global_name * mllambda array *)
  | Glet of global_name * mllambda
  

(* Compilation environment *)
type cenv = 
  { cenv_rel  : lname list;
    cenv_size : int (* the lenght of cenv_rel *)
  }

let empty_cenv = { cenv_rel = []; cenv_size = 0 }


(* functions used for printing *)
let push_lname cenv id = 
  { cenv_rel = id::cenv.cenv_rel;
    cenv_size = cenv.cenv_size + 1 }

let push_lnames = Array.fold_left push_lname 

(* functions used for mllambda_of_constr *)
let lname_of_name x = 
  match x with
  | Name id -> Names.string_of_id id
  | Anonymous -> "__"
  
let push_rel cenv x = push_lname cenv (lname_of_name x)

let push_rels = List.fold_left push_rel 

(** Printing to ocaml **)

let pp_global fmt g = Format.fprintf fmt "%s" g

let pp_rel cenv id fmt i =
  assert (i>0);
  let lvl = cenv.cenv_size - i in
  let id' = List.nth cenv.cenv_rel (i-1) in
  assert (id == id');
  Format.fprintf fmt "r_%i_%s" lvl id'

(** TODO move to lib *)
let str_encode s = assert false 

let pp_primitive fmt = function
  | Mk_prod id -> Format.fprintf fmt "mk_prod_accu %s" id
  | Mk_sort s -> 
      Format.fprintf fmt "mk_sort_accu (str_decode %s)" (str_encode s)
  | Is_accu -> Format.fprintf fmt "is_accu"
  | Is_int -> Format.fprintf fmt "is_int"

let pp_ldecls cenv fmt ids =
  let len = Array.length ids in
  for i = 0 to len - 1 do
    Format.fprintf fmt " %a" (pp_rel cenv ids.(i)) (len - i)
  done

let rec pp_lam cenv fmt l =
  match l with
  | Lrel(id,i) -> pp_rel cenv id fmt i 
  | Lglobal g -> pp_global fmt g
  | Lprimitive p -> pp_primitive fmt p
  | Llam(ids,body) -> 
      let cenv = push_lnames cenv ids in
      Format.fprintf fmt "@[fun%a ->@\n  %a@]"
	(pp_ldecls cenv) ids (pp_lam cenv) body
  | Lletrec(defs,body) ->
      let cenv_rec = push_lnames cenv (Array.map (fun (id,_,_) -> id) defs) in
      Format.fprintf fmt "@[%a in@\n%a@]" (pp_letrec cenv_rec) defs 
      (pp_lam cenv_rec) body
  | Llet(id,def,body) ->
      let cenv' = push_lname cenv id in
      Format.fprintf fmt "@[let %a =@\n  %a in@\n%a@]"
         (pp_rel cenv' id) 1 (pp_lam cenv) def (pp_lam cenv') body
  | Lapp(f, args) ->
      Format.fprintf fmt "@[%a %a@]" (pp_lam cenv) f (pp_args cenv true) args
  | Lif(t,l1,l2) ->
      Format.fprintf fmt "@[if %a then@\n  %a@\nelse@\n  %a@]"
	(pp_lam cenv) t (pp_lam cenv) l1 (pp_lam cenv) l2 
  | Lmatch(a,bs) ->
      Format.fprintf fmt "@[begin match %a with%a@\nend@]"
	(pp_lam cenv) a (pp_branches cenv) bs
  | Lconstruct(cn,args) ->
      Format.fprintf fmt "@[%s%a@]" cn (pp_cargs cenv) args
  | Lint i -> Format.fprintf fmt "%i" i
  | Lparray _ -> assert false

and pp_letrec cenv fmt defs =
  let len = Array.length defs in
  let pp_one_rec i (fn, argsn, body) =
    let len' = Array.length argsn in
    let cenv = push_lnames cenv argsn in
    Format.fprintf fmt "%a%a =@\n  %a"
      (pp_rel cenv fn) (len - i + len') 
      (pp_ldecls cenv) argsn (pp_lam cenv) body in
  Format.fprintf fmt "letrec ";
  pp_one_rec 0 defs.(0);
  for i = 1 to len - 1 do
    Format.fprintf fmt "and ";
    pp_one_rec i defs.(i)
  done

and pp_blam cenv fmt l =
  match l with
  | Lprimitive (Mk_prod _ | Mk_sort _) 
  | Llam _ | Lletrec _ | Llet _ | Lapp _ | Lif _ ->
      Format.fprintf fmt "(%a)" (pp_lam cenv) l
  | Lconstruct(_,args) when Array.length args > 0 ->
      Format.fprintf fmt "(%a)" (pp_lam cenv) l
  | _ -> pp_lam cenv fmt l

and pp_args cenv sep fmt args =
  let pp_lam = if sep then pp_blam else pp_lam in
  let sep = if sep then " " else "," in
  let len = Array.length args in
  if len > 0 then begin
    Format.fprintf fmt "%a" (pp_lam cenv) args.(0);
    for i = 1 to len - 1 do
      Format.fprintf fmt "%s%a" sep (pp_lam cenv) args.(i)
    done
  end 

and pp_cargs cenv fmt args =
  let len = Array.length args in
  match len with
  | 0 -> ()
  | 1 -> Format.fprintf fmt " %a" (pp_blam cenv) args.(0)
  | _ -> Format.fprintf fmt "(%a)" (pp_args cenv false) args
  
and pp_branches cenv fmt bs =
  let pp_branch (cn,argsn,body) =
    let cenv = push_lnames cenv argsn in
    let len = Array.length argsn in
    let args = Array.mapi (fun i id -> Lrel(id,len-i)) argsn in
    Format.fprintf fmt "@\n| %s%a ->@\n  %a" 
	cn (pp_cargs cenv) args (pp_lam cenv) body in
  Array.iter pp_branch bs


      
    
  

(* *)

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
