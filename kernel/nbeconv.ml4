(*i camlp4use: "q_MLast.cmo" i*)

open Names
open Term
open Pre_env
open Pcaml
open Declarations
open Util
open Nativecode
(*open Reduction*)

exception NotConvertible

(*  *)
let ast_impl_magic_number = "Caml1999M012"
let ast_intf_magic_number = "Caml1999N011"

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

let uniq = ref 256

(* Required to make camlp5 happy. *)
let loc = Ploc.dummy

(* Flag to signal whether recompilation is needed. *)

(* Required to make camlp5 happy. *)
let loc = Ploc.dummy

(* Flag to signal whether recompilation is needed. *)
let env_updated = ref false


let lid_of_string s = "x" ^ s

(* Redefine a bunch of functions in module Names to generate names
   acceptable to OCaml. *)
let string_of_dirpath = function
  | [] -> "_"
  | sl -> String.concat "_" (List.map string_of_id (List.rev sl))

let rec string_of_mp = function
  | MPfile sl -> string_of_dirpath (repr_dirpath sl)
  | MPbound uid -> string_of_mbid uid
  | MPdot (mp,l) -> string_of_mp mp ^ "." ^ string_of_label l

let string_of_con con =
  let (modpath, _dirpath, label) = repr_con con in
    string_of_mp modpath ^ "_" ^ string_of_label label

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
        let (_, b, _) = Sign.lookup_named id env.env_named_context in
	let deps = (match b with
          | None -> [] 
	  | Some body -> let res = assums body in print_endline (sid^"(named_val) assums "^String.concat "," res); res)
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
    | None -> (print_endline ("Const body AST not found: "^string_of_con c); xs)

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
  let code1 = translate env t1 in
  let code2 = translate env t2 in
    Pcaml.input_file := "/dev/null";
    if true (* TODO : dump env for whole vo file *) then begin
        Pcaml.output_file := Some "envpr.ml";
        !Pcaml.print_implem (dump_env t1 t2 env);
	print_implem "env.ml" (compute_loc (dump_env t1 t2 env))
      end;
    Pcaml.output_file := Some "termspr.ml";
    !Pcaml.print_implem
    	 [(<:str_item< open Nbe >>, loc);
    	  (<:str_item< open Env >>, loc);
    	  (<:str_item< value t1 = $code1$ >>, loc);
    	  (<:str_item< value t2 = $code2$ >>, loc);
    	  (<:str_item< value _ = print_endline (string_of_term 0 t1) >>, loc);
    	  (<:str_item< value _ = print_endline (string_of_term 0 t2) >>, loc);
    	  (<:str_item< value _ = compare 0 t1 t2 >>, loc)];
    print_implem "terms.ml"
	 [(<:str_item< open Nbe >>, loc);
	  (<:str_item< open Env >>, loc);
	  (<:str_item< value t1 = $code1$ >>, loc);
	  (<:str_item< value t2 = $code2$ >>, loc);
    	  (<:str_item< value _ = print_endline (string_of_term 0 t1) >>, loc);
    	  (<:str_item< value _ = print_endline (string_of_term 0 t2) >>, loc);
	  (<:str_item< value _ = compare 0 t1 t2 >>, loc)];
    env_updated := false;
    (values code1, values code2)

let compare (v1, v2) cu =
  let _ = Unix.system "touch env.ml" in
  match Unix.system "ocamlopt nbe.ml env.ml terms.ml" with
    | Unix.WEXITED 0 ->
      begin
      match Unix.system "./a.out" with
        | Unix.WEXITED 0 -> cu
        | _ -> (print_endline "Conversion test failure"; raise NotConvertible)
      end
    | _ -> (print_endline "Compilation failure"; raise NotConvertible)
