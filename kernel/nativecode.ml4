(*i camlp4use: "q_MLast.cmo" i*)

open Names
open Term
open Environ
open Pre_env
open Pcaml
open Declarations
open Util


let max_arity = 8
let id = ref 0
let uniq = ref 256

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
  | <:expr< do { $list:_$ } >> -> t
  | _ -> let s = Eprinter.apply Pcaml.pr_expr Pprintf.empty_pc t in
      print_endline s; raise (Invalid_argument "descend_ast")

let subst rho x = try List.assoc x rho with Not_found -> x

(* Shrinking reduction. This is essentially eta-reduction. *)
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
    List.fold_left (fun e arg -> <:expr< $e$ $arg$ >>) <:expr< $lid:"app" ^ string_of_int n$ f >> args

let rec collapse_abstractions t =
  let vars, body = pop_abstractions max_arity t in
    if List.length vars = 0 then uncurrify body else
      let func = List.fold_right (fun x t -> <:expr< fun $x$ -> $t$ >>) vars (collapse_abstractions body) in
	<:expr< $uid:"Lam" ^ string_of_int (List.length vars)$ $func$ >>

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

let lid_of_string s = print_endline ("lid: " ^ ("z" ^ s)); "z" ^ s
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

exception NonNat
exception Pass

let rec is_nat_literal ind c =
  let rec f c = match c with
    | App (c', args) when isConstruct c' -> 1 + f (kind_of_term args.(0))
    | Construct cstr -> 0
    | _ -> raise NonNat in
    match string_of_inductive ind with
      | "Coq_Init_Datatype_nat" -> f c
      | _ -> raise NonNat

let rec gen_names = function
  | 0 -> []
  | n when n > 0 ->
      let xs = gen_names (n - 1) in
	uniq := !uniq + 1;
	("x" ^ string_of_int !uniq) :: xs
  | _ -> raise (Invalid_argument "gen_names")

exception Bound

let is_bound x env =
  try
    List.iter (fun (y, _, _) -> if x = y then raise Bound else ())
      (pre_env env).env_rel_context; false
  with Bound -> true

let rec push_value id body env =
  env_updated := true;
  let kind = lookup_named_val id (pre_env env) in
    match !kind with
    | VKvalue (v, _) -> ()
    | VKnone -> kind := VKvalue (values (translate env body), Idset.empty)

and translate_constant env c =
  let cb = lookup_constant c (pre_env env) in
    match cb.const_body with
      | Some body -> (match cb.const_body_ast with
	  | Some _ ->
	      (* <:expr< do { print_endline $str:string_of_con c$; $lid:lid_of_string (string_of_con c)$ } >> *)
	      <:expr< $lid:lid_of_string (string_of_con c)$ >>
	  | None -> print_endline ("translating: " ^ string_of_con c);
	      let ast = translate env (Declarations.force body) in
	      cb.const_body_ast <- Some (values (uncurrify (shrink [] ast)));
	      env_updated := true;
	      (* <:expr< do { print_endline $str:string_of_con c$; $lid:lid_of_string (string_of_con c)$ } >>) *)
	      <:expr< $lid:lid_of_string (string_of_con c)$ >>)
      | None -> <:expr< Con () (* $str:string_of_con c$ *) >>

(** The side-effect of translate is to add the translated construction
    to the value environment. *)
(* A simple counter is used for fresh variables. We effectively encode
   de Bruijn indices as de Bruijn levels. *)
and translate (env : Environ.env) t =
  try (
    match kind_of_term t with
    | Rel x ->
	print_endline ("rel: " ^ lid_of_name (let name, _, _ = lookup_rel x env in name));
	<:expr< $lid: lid_of_name (match lookup_rel x env with name, _, _ -> name)$ >>
    | Var id ->
	print_endline ("variable: " ^ string_of_id id);
	let v = <:expr< $lid:lid_of_string (string_of_id id)$ >> in
	  (match named_body id env with
	       (* Add compiled form of definition to environment if not already present. *)
	     | Some body -> push_value id body env; v
	     | None -> v)
    | Sort (Prop Null) -> <:expr< Prop >>
    | Sort (Prop Pos) -> <:expr< Set >>
    | Sort (Type _) -> <:expr< Type 0 >>
    | Cast (c, _, ty) ->
	translate env c
    | Prod (x, t, c) ->
	let x' = if is_bound x env then
	  (match x with
	     | Name id -> uniq := !uniq + 1; Name (id_of_string (string_of_id id ^ string_of_int !uniq))
	     | Anonymous -> Anonymous) else x in
	let newenv = Environ.push_rel (x', None, t) env in
	  <:expr< Prod $translate env t$ (fun $lid:lid_of_name x'$ -> $translate newenv c$) >>
    | Lambda (x, t, c) ->
	let x' = if is_bound x env then
	  (match x with
	     | Name id -> uniq := !uniq + 1; Name (id_of_string (string_of_id id ^ string_of_int !uniq))
	     | Anonymous -> Anonymous) else x in
	let newenv = Environ.push_rel (x', None, t) env in
	  <:expr< Lam (fun $lid:lid_of_name x'$ -> $translate newenv c$) >>
    | LetIn (x, b, t, c) ->
	let x' = if is_bound x env then
	  (match x with
	     | Name id -> uniq := !uniq + 1; Name (id_of_string (string_of_id id ^ string_of_int !uniq))
	     | Anonymous -> Anonymous) else x in
	let newenv = Environ.push_rel (x', Some b, t) env in
	  <:expr< let $lid:lid_of_name x'$ = $translate env b$ in $translate newenv c$ >>
    | App (c, args) ->
	(match kind_of_term c with
	   | Construct cstr ->
	       let f arg vs = translate env arg :: vs in
	       let i = index_of_constructor cstr in
	       let ind = inductive_of_constructor cstr in
	       let mb = lookup_mind (fst ind) (pre_env env) in
	       let ob = mb.mind_packets.(snd ind) in
	       let nparams = rel_context_length ob.mind_arity_ctxt in
	       let nargs = Array.length args in
	       let vs = list_skipn (min nparams nargs) (Array.fold_right f args []) in
	       let missing = ob.mind_consnrealdecls.(i-1) - nargs + nparams in
	       let underscores = max (nparams - nargs) 0 in
	       let names = gen_names (missing - underscores) in
	       let pad = List.map (fun x -> <:expr< $lid:x$ >>) names in
	       print_endline ("app constructor " ^ string_of_constructor cstr ^ string_of_int i ^ string_of_int ob.mind_consnrealdecls.(i-1));
	       print_endline ("app constructor nparams " ^ string_of_int nparams);
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
  		 (* (try let n = is_nat_literal ind t in *)
		 (*    <:expr< __from_nat $int:string_of_int n$ >> *)
		 (*  with NonNat -> <:expr< Const $int:string_of_int i$ [| $list:vs'$ |] >>) *)
	   | Const name ->
	       let zero = translate env c in
	       (* let f apps x = <:expr< do { print_endline $str:string_of_con name$; app $apps$ $translate env x$ } >> in *)
	       let f apps x = <:expr< app $apps$ $translate env x$ >> in
		 Array.fold_left f zero args
	   | _ ->
	       let zero = translate env c in
	       let f apps x = <:expr< app $apps$ $translate env x$ >> in
		 Array.fold_left f zero args)
    | Const c ->
	print_endline ("constant " ^ string_of_con c);
	translate_constant (env_of_pre_env { pre_env env with env_rel_context = [] }) c
    | Ind c ->
	print_endline ("inductive " ^ string_of_inductive c);
	<:expr< Con () (* $str:string_of_inductive c$ *) >>
    | Construct cstr ->
	print_endline ("constructor " ^ string_of_constructor cstr);
	let i = index_of_constructor cstr in
	  <:expr< Const $int:string_of_int i$ [||] >>
    | Case (ci, p, c, branches) ->
	id := !id + 1;
	let default = (<:patt< x >>, None, <:expr< do {print_endline $str:string_of_int !id$; bug x} >>) in
	let vs =
	  (* let mib = lookup_mind (fst ci.ci_ind) env in *)
	  (* let oib = mib.mind_packets.(snd ci.ci_ind) in *)
	  (* default branch *)
	  let f i =
	    print_endline (string_of_inductive ci.ci_ind);
	    print_endline ("ci_npar " ^ string_of_int ci.ci_npar);
	    print_endline ("ci_cstr_nargs " ^ string_of_int ci.ci_cstr_nargs.(i));
	    let args = gen_names ci.ci_cstr_nargs.(i) in
	    let apps = List.fold_left (fun e arg -> <:expr< app $e$ $lid:arg$ >>) in
	    let pat = make_constructor_pattern (i + 1) args in
	      (pat, None, apps (translate env branches.(i)) args)
	  in Array.to_list (Array.init (Array.length branches) f)
	in <:expr< match $translate env c$ with [$list: vs @ [default]$] >>
    | Fix ((recargs, i), (names, types, bodies)) ->
	let n = Array.length names in
	let fix_context = Array.to_list (Array.init n (fun i -> (names.(i), Some bodies.(i), types.(i)))) in
	let f i =
	  let newenv = Environ.push_rel_context fix_context env in
	    (<:patt< $lid:lid_of_name names.(i)$ >>, translate newenv bodies.(i))
	in let functions = Array.to_list (Array.init n f)
	in <:expr< let rec $list:functions$ in $lid:lid_of_name names.(i)$ >>
    | CoFix(ln, (_, tl, bl)) -> print_endline "cofix"; invalid_arg "translate"
    | _ -> print_endline "invalid arg"; invalid_arg "translate"
  ) with
    | Pass -> raise Pass
    | e ->
	print_endline "exception!";
	print_endline (Printexc.to_string e);
	print_endline "rel_context";
	Environ.fold_rel_context (fun env (n, _, _) _ -> print_endline (lid_of_name n)) env ~init:();
	print_endline "named_context";
	Environ.fold_named_context_reverse (fun () (n, _, _) -> print_endline (string_of_id n)) ~init:() env;
	raise Pass

module StringOrdered =
struct
  type t = string
  let compare = Pervasives.compare
end

module Smap = Map.Make(StringOrdered)
module Sset = Set.Make(StringOrdered)

(* Collect all variables and constants in the term. *)
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
	in Smap.add sid (ast, deps) xs
    | VKnone -> xs

let add_constant c ck xs =
  match (fst ck).const_body_ast with
    | Some v ->
	let sc = string_of_con c in
	let ast = (<:str_item< value $lid:lid_of_string sc$ = $expr_of_values v$ >>, loc) in
	let deps = match (fst ck).const_body with
	  | Some body -> assums (Declarations.force body)
	  | None -> []
	in Smap.add sc (ast, deps) xs
    | None -> xs

let topological_sort init xs =
  let visited = ref Sset.empty in
  let rec aux s result =
    if Sset.mem s !visited
    then result
    else begin
      try
	let (x, deps) = Smap.find s xs in
	  visited := Sset.add s !visited;
	  x :: List.fold_right aux deps result
      with Not_found -> result
	| _ -> print_endline "exception in tsort!"; invalid_arg "bleh"
    end
  in List.rev (List.fold_right aux init [])

let dump_env t1 t2 env =
  let vars = List.fold_right (add_value env) env.env_named_vals Smap.empty in
  let vars_and_cons = Cmap_env.fold add_constant env.env_globals.env_constants vars in
  let initial_set = assums t1 @ assums t2
  in (<:str_item< open Nbe >>, loc) :: topological_sort initial_set vars_and_cons

let ocaml_version = "3.11.1"
let ast_impl_magic_number = "Caml1999M012"
let ast_intf_magic_number = "Caml1999N011"

let print_implem fname ast =
  let pt = Ast2pt.implem fname (List.map fst ast) in
  let oc = open_out_bin fname in
  output_string oc ast_impl_magic_number;
  output_value oc fname;
  output_value oc pt;
  close_out oc

let compute_loc xs =
  let rec f n = function
    | [] -> []
    | (str_item, _) :: xs -> (str_item, Ploc.make n 0 (0, 0)) :: f (n + 1) xs
  in f 0 xs

let compile env t1 t2 =
  print_endline "compile";
  let code1 = translate env (it_mkLambda_or_LetIn t1 (rel_context env)) in
  let code2 = translate env (it_mkLambda_or_LetIn t2 (rel_context env)) in
    print_endline "done translate";
    if !env_updated then
      begin
	Pcaml.input_file := "envi.ml";
	Pcaml.output_file := Some "envpr.ml";
	!Pcaml.print_implem (dump_env t1 t2 (pre_env env));
	print_implem "env.ml" (compute_loc (dump_env t1 t2 (pre_env env)))
      end;
    print_endline "done env";
    Pcaml.input_file := "termsi.ml";
    Pcaml.output_file := Some "termspr.ml";
    !Pcaml.print_implem
    	 [(<:str_item< open Nbe >>, loc);
    	  (<:str_item< open Env >>, loc);
    	  (<:str_item< value t1 = $code1$ >>, loc);
    	  (<:str_item< value t2 = $code2$ >>, loc);
    	  (<:str_item< value _ = compare 0 t1 t2 >>, loc)];
    print_implem "terms.ml"
	 [(<:str_item< open Nbe >>, loc);
	  (<:str_item< open Env >>, loc);
	  (<:str_item< value t1 = $code1$ >>, loc);
	  (<:str_item< value t2 = $code2$ >>, loc);
	  (<:str_item< value _ = compare 0 t1 t2 >>, loc)];
    print_endline "done term";
    print_endline "done compile";
    env_updated := false;
    (values code1, values code2)

let compare (v1, v2) cu = cu
