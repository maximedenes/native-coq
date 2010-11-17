open Term
open Names

type constr_name = string

type lname = string

type global_name = string

(* **)

type primitive =
  | Mk_prod of name
  | Mk_sort of sorts
  | Is_accu
  | Is_int

type lambda =
  | Lrel          of (lname * int )
  | Lglobal       of global_name 
  | Lprimitive    of primitive
  | Llam          of lname array * lambda 
  | Lletrec       of (lname * lname array * lambda) array * lambda
  | Llet          of lname * lambda * lambda
  | Lapp          of lambda * lambda array
  | Lif           of lambda * lambda * lambda
  | Lmatch        of lambda * (constr_name * lname array * lambda) array
  | Lconstruct    of constr_name * lambda array
  | Lint          of int
  | Lparray       of lambda array

type global =
(*  | Gmatch of ...
  | Gtblname of global_name * lname array
  | Gtblfixtype of global_name * lamba array (* add Lazy for ocaml *)
  | Gtblnorm of global_name * lambda array *)
  | Glet of global_name * lambda
  

(* *)

type comp = global list

let globals = ref []

let rec lambda_of_constr cenv c =
  match c with
  | Rel i -> Lrel (mk_rel cenv i)
  | Lambda _ ->
      let params, body = decompose_lam c in
      let ids = get_names (List.rev params) in
      let ln,cenv = push_rels ids cenv in
      let lb = lambda_of_constr cenv body in
      mkLlam ids lb
  | App(f, args) -> lambda_of_app cenv f args
(*
  | Var id -> Lglobal (get_var cenv id)
  | Sort s -> Lprimitive (Mk_sort s)
  | Ind ind -> Lglobal (get_ind cenv ind)
  | Prod(x, dom, codom) ->
      let ld = lambda_of_constr cenv dom in
      let lx, cenv = push_rel x cenv in
      let lc = lambda_of_constr cenv codom in
      Lapp(Lprimitive (Mk_prod x), [|ld; Llam([|lx|],lc)|])
	
  | LetIn(x, def, _, body) ->
      let ld = lambda_of_constr cenv def in
      let lx,cenv = push_rel x cenv in 
      let lb = lambda_of_constr cenv body in
      Llet(lx, ld, lb)

  | Const _ -> lambda_of_app cenv c empty_args

  | Construct _ -> lambda_of_app cenv c empty_args

  | Case(ci,t,a,branches) ->  
      (* generation de la def global ---> fv, match_toto *)
      (* *)
      let la = lambda_of_constr cenv a in
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
  | NativeArr(_,p) -> makearray (lambda_of_args env 0 p)

(*  
(*
  | Lprim         of constant option * Native.prim_op * lambda array
	(* No check if None *)
  | Lcprim        of constant * Native.caml_prim * lambda array *)
  | Lcase         of annot_sw * lambda * lambda * lam_branches 
  | Lareint       of lambda array 

  | Lfix          of (int array * int) * fix_decl 
  | Lcofix        of int * fix_decl 
  | Lmakeblock    of int * lambda array
  | Lint          of int
  | Lval          of values
  | Lsort         of sorts
  | Lind          of inductive

Prod(x,dom,codom) -->
  mkprodaccu "x" dom (fun x -> codom)

*)
*)
