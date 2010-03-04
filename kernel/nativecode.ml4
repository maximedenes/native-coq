(*i camlp4use: "q_MLast.cmo" i*)

open Names
open Term
open Environ
open Pre_env
open Pcaml
open Declarations
open Util


(** One of the optimizations performed on the target code is
    uncurrying, meaning collapsing functions into n-ary functions and
    introducing a family of application operators that apply an n-ary
    function to m arguments in one go. This constant defines the
    maximum arity of functions, hence bounding the number of
    application operators required.

    BEWARE: changing the value of this constant requires changing
    nbe.ml accordingly to have at least as many abstraction
    constructors and application operators. *)
let max_arity = 6

(* Required to make camlp5 happy. *)
let loc = Ploc.dummy

(* Flag to signal whether recompilation is needed. *)
let env_updated = ref false

(* Bringert and Ranta's 'descend' operator for OCaml representations
   of the target code. *)
let descend_ast f t = match t with
  | <:expr< Con $_$ >> -> t
  | <:expr< Lam (fun $x$ -> $body$) >> -> <:expr< Lam (fun $x$ -> $f body$) >>
  | <:expr< Prod $dom$ (fun $lid:x$ -> $cod$) >> -> <:expr< Prod $f dom$ (fun $lid:x$ -> $f cod$) >>
  | <:expr< app $t1$ $t2$ >> -> <:expr< app $f t1$ $f t2$ >>
  | <:expr< Const $i$ [| $list:args$ |] >> ->
      <:expr< Const $i$ [| $list:List.fold_right (fun t ts -> f t :: ts) args []$ |] >>
  | <:expr< Set >> -> t
  | <:expr< Prop >> -> t
  | <:expr< Type $_$ >> -> t
  | <:expr< $lid:x$ >> -> t
  | <:expr< match $scrutinee$ with [ $list:branches$ ] >> ->
      let bs = List.fold_right (fun (p, w, body) bs -> (p, w, f body) :: bs) branches [] in
	<:expr< match $f scrutinee$ with [ $list:bs$ ] >>
  | <:expr< let $flag:r$ $list:defs$ in $t$ >> ->
      let defs' = List.map (fun (p, t) -> (p, f t)) defs in
	<:expr< let $flag:r$ $list:defs'$ in $f t$ >>
  | <:expr< bug x >> -> t
  | _ -> raise (Invalid_argument "descend_ast")

let subst rho x = try List.assoc x rho with Not_found -> x

(** A shrinking reduction. This is essentially eta-reduction. Whenever
    a lambda is applied to a variable then beta-reduce. The size of the
    resulting term is strictly smaller. *)
let rec shrink rho = function
  | <:expr< app $t1$ $lid:y$ >> ->
    (match shrink rho t1 with
       | <:expr< Lam (fun $lid:x$ -> $body$) >> ->
	 shrink ((x, y) :: rho) body
       | t -> <:expr< app $t$ $lid:subst rho y$ >>)
  | <:expr< $lid:x$ >> -> <:expr< $lid:subst rho x$ >>
  | t -> descend_ast (shrink rho) t

let rec pop_abstractions n =
  if n > 0 then function
    | <:expr< Lam (fun $x$ -> $t$) >> ->
      let vars, body = pop_abstractions (n - 1) t in
	(x :: vars, body)
    | t -> ([], t)
  else function t -> ([], t)

let rec pop_applications n t =
  let rec aux n args =
    if n > 0 then function
      | <:expr< app $t1$ $t2$ >> ->
	aux (n - 1) (t2 :: args) t1
      | f -> (f, args)
    else function f -> (f, args)
  in aux n [] t

let push_applications f args =
  let n = List.length args in
    List.fold_left (fun e arg -> <:expr< $e$ $arg$ >>)
      <:expr< $lid:"app" ^ string_of_int n$ $f$ >> args

let rec collapse_abstractions t =
  let vars, body = pop_abstractions max_arity t in
    if List.length vars = 0 then uncurrify body else
      let func =
	List.fold_right (fun x t -> <:expr< fun $x$ -> $t$ >>)
	  vars (collapse_abstractions body)
      in <:expr< $uid:"Lam" ^ string_of_int (List.length vars)$ $func$ >>

and collapse_applications t =
  let f, args = pop_applications max_arity t in
  let f, args = uncurrify f, List.map uncurrify args in
    push_applications f args

(* Uncurrification optimization. This consists in replacing

   Lam (fun x1 => ... (Lam (fun xn => ...)

   with

   Lam_n (fun x1 xn => ...)

   and replacing unary applications with n-ary applications where possible.

*)
and uncurrify t = match t with
  | <:expr< Lam $_$ >> -> collapse_abstractions t
  | <:expr< app $_$ $_$ >> -> collapse_applications t
  | _ -> descend_ast uncurrify t

let lid_of_string s = "x" ^ s
let uid_of_string s = "X" ^ s

let lid_of_name = function
  | Name id -> lid_of_string (string_of_id id)
  | Anonymous -> "_"

(* Redefine a bunch of functions in module Names to generate names
   acceptable to OCaml. *)
let string_of_dirpath = function
  | [] -> "_"
  | sl -> String.concat "_" (List.map string_of_id (List.rev sl))

let rec string_of_mp = function
  | MPfile sl -> string_of_dirpath (repr_dirpath sl)
  | MPbound uid -> string_of_mbid uid
  | MPdot (mp,l) -> string_of_mp mp ^ "." ^ string_of_label l

let string_of_kn kn =
  let (modpath, _dirpath, label) = repr_kn kn in
    string_of_mp modpath ^ "_" ^ string_of_label label

let string_of_con con =
  let (modpath, _dirpath, label) = repr_con con in
    string_of_mp modpath ^ "_" ^ string_of_label label

let string_of_inductive (mind, i) =
  string_of_mind mind ^ string_of_int i

let string_of_constructor (ind, i) =
  string_of_inductive ind ^ "c" ^ string_of_int i

(* First argument the index of the constructor *)
let make_constructor_pattern i args =
  let f arg = <:patt< $lid:arg$ >> in
    <:patt< Const $int:string_of_int i$ [| $list:List.map f args$ |] >>

let lid_of_index n = "x" ^ string_of_int n

let rec gen_names start len =
  if len = 0 then []
  else if len > 0 then
    lid_of_index start :: gen_names (start + 1) (len - 1)
  else raise (Invalid_argument "gen_names")

let rec push_value id body env =
  env_updated := true;
  let kind = lookup_named_val id (pre_env env) in
    match !kind with
      | VKvalue (v, _) -> ()
      | VKnone -> kind := VKvalue (values (translate env body), Idset.empty)

and translate_constant env c =
  let cb = lookup_constant c (pre_env env) in
    match cb.const_body with
      | Some body -> begin
	  match cb.const_body_ast with
	    | Some _ -> <:expr< $lid:lid_of_string (string_of_con c)$ >>
	    | None ->
		let ast = translate env (Declarations.force body) in
		  cb.const_body_ast <- Some (values (uncurrify (shrink [] ast)));
		  env_updated := true;
		  <:expr< $lid:lid_of_string (string_of_con c)$ >>
	end
      | None -> <:expr< Con () >>	(* xxx *)

(** The side-effect of translate is to add the translated construction
    to the value environment. *)
(* A simple counter is used for fresh variables. We effectively encode
   de Bruijn indices as de Bruijn levels. *)
and translate env t =
  let rec translate n t =
    match kind_of_term t with
      | Rel x -> <:expr< $lid:lid_of_index (n-x)$ >>
      | Var id ->
	  let v = <:expr< $lid:lid_of_string (string_of_id id)$ >> in
            (match named_body id env with
		 (* Add compiled form of definition to environment if not already present. *)
		    | Some body -> push_value id body env; v
		    | None -> v)
      | Sort (Prop Null) -> <:expr< Prop >>
      | Sort (Prop Pos) -> <:expr< Set >>
      | Sort (Type _) -> <:expr< Type 0 >> (* xxx: check universe constraints *)
      | Cast (c, _, ty) -> translate n c
      | Prod (_, t, c) ->
	  <:expr< Prod $translate n t$ (fun $lid:lid_of_index n$ -> $translate (n + 1) c$) >>
      | Lambda (_, t, c) ->
	  <:expr< Lam (fun $lid:lid_of_index n$ -> $translate (n + 1) c$) >>
      | LetIn (_, b, t, c) ->
	  <:expr< let $lid:lid_of_index n$ = $translate n b$ in $translate (n + 1) c$ >>
      | App (c, args) ->
	  (match kind_of_term c with
	     | Construct cstr ->
		 let f arg vs = translate n arg :: vs in
		 let i = index_of_constructor cstr in
		 let ind = inductive_of_constructor cstr in
		 let mb = lookup_mind (fst ind) (pre_env env) in
		 let ob = mb.mind_packets.(snd ind) in
		 let nparams = rel_context_length ob.mind_arity_ctxt in
		 let nargs = Array.length args in
		 let vs = list_skipn (min nparams nargs) (Array.fold_right f args []) in
		 let missing = ob.mind_consnrealdecls.(i-1) - nargs + nparams in
		 let underscores = max (nparams - nargs) 0 in
		 let names = gen_names n (missing - underscores) in
		 let pad = List.map (fun x -> <:expr< $lid:x$ >>) names in
		 let prefix =
		   let rec aux n z =
		     if n = 0
		     then z
		     else aux (n - 1) <:expr< Lam (fun _ -> $z$) >>
		   in aux underscores
			(List.fold_left (fun e x -> <:expr< Lam (fun $lid:x$ -> $e$) >>)
			 <:expr< Const $int:string_of_int i$ [| $list: vs @ pad$ |] >>
			 names)
		 in assert (List.length vs + List.length pad = ob.mind_consnrealdecls.(i-1)); prefix
	     | _ ->
		 let zero = translate n c in
		 let f apps x = <:expr< app $apps$ $translate n x$ >> in
		   Array.fold_left f zero args)
      | Const c -> translate_constant env c
      | Ind c -> <:expr< Con () >>	(* xxx *)
      | Construct cstr ->
	  let i = index_of_constructor cstr in
	    <:expr< Const $int:string_of_int i$ [||] >>
      | Case (ci, p, c, branches) ->
	  let default = (<:patt< x >>, None, <:expr< bug x >>) in
	  let vs =
	    let f i =
	      let args = gen_names n ci.ci_cstr_nargs.(i) in
	      let apps = List.fold_left (fun e arg -> <:expr< app $e$ $lid:arg$ >>) in
	      let pat = make_constructor_pattern (i + 1) args in
		(pat, None, apps (translate n branches.(i)) args)
	    in Array.to_list (Array.init (Array.length branches) f)
	  in <:expr< match $translate n c$ with [$list: vs @ [default]$] >>
      | Fix ((recargs, i), (_, _, bodies)) ->
	  let m = Array.length bodies in
	  let f i =
	      (<:patt< $lid:lid_of_index (n + i)$ >>, translate (n + m) bodies.(i))
	  in let functions = Array.to_list (Array.init m f)
	  in <:expr< let rec $list:functions$ in $lid:lid_of_index (n + i)$ >>
      | CoFix(ln, (_, tl, bl)) -> invalid_arg "translate"
      | _ -> invalid_arg "translate"
  in translate 0 t

(** Collect all variables and constants in the term. *)
let assums t =
  let rec aux xs t =
    match kind_of_term t with
      | Var id -> string_of_id id :: xs
      | Const c -> string_of_con c :: xs
      | _ -> fold_constr aux xs t
  in aux [] t

let add_value env (id, value) xs =
  match !value with
    | VKvalue (v, _) ->
	let sid = string_of_id id in
	let ast = (<:str_item< value $lid:lid_of_string sid$ = $expr_of_values v$ >>, loc) in
	let deps = match named_body id (env_of_pre_env env) with
	  | Some body -> assums body
	  | None -> []
	in Stringmap.add sid (ast, deps) xs
    | VKnone -> xs

let add_constant c ck xs =
  match (fst ck).const_body_ast with
    | Some v ->
	let sc = string_of_con c in
	let ast = (<:str_item< value $lid:lid_of_string sc$ = $expr_of_values v$ >>, loc) in
	let deps = match (fst ck).const_body with
	  | Some body -> assums (Declarations.force body)
	  | None -> []
	in Stringmap.add sc (ast, deps) xs
    | None -> xs

let topological_sort init xs =
  let visited = ref Stringset.empty in
  let rec aux s result =
    if Stringset.mem s !visited
    then result
    else begin
      try
	let (x, deps) = Stringmap.find s xs in
	  visited := Stringset.add s !visited;
	  x :: List.fold_right aux deps result
      with Not_found -> result
    end
  in List.rev (List.fold_right aux init [])

let dump_env t1 t2 env =
  let vars = List.fold_right (add_value env) env.env_named_vals Stringmap.empty in
  let vars_and_cons = Cmap_env.fold add_constant env.env_globals.env_constants vars in
  let initial_set = assums t1 @ assums t2
  in (<:str_item< open Nbe >>, loc) :: topological_sort initial_set vars_and_cons

let compile env t1 t2 =
  let code1 = translate env (it_mkLambda_or_LetIn t1 (rel_context env)) in
  let code2 = translate env (it_mkLambda_or_LetIn t2 (rel_context env)) in
    Pcaml.input_file := "/dev/null";
    if !env_updated then begin
	Pcaml.output_file := Some "env.ml";
	!Pcaml.print_implem (dump_env t1 t2 (pre_env env));
      end;
    Pcaml.output_file := Some "terms.ml";
    !Pcaml.print_implem
    	 [(<:str_item< open Nbe >>, loc);
    	  (<:str_item< open Env >>, loc);
    	  (<:str_item< value t1 = $code1$ >>, loc);
    	  (<:str_item< value t2 = $code2$ >>, loc);
    	  (<:str_item< value _ = compare 0 t1 t2 >>, loc)];
    env_updated := false;
    (values code1, values code2)

let compare (v1, v2) cu = cu		(* xxx *)
