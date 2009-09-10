(*i camlp4use: "q_MLast.cmo" i*)

open Names
open Term
open Environ
open Pre_env
open Pcaml
open Declarations


let loc = Ploc.dummy

(* Flag to signal whether recompilation is needed. *)
let env_updated = ref false

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
  | MPself uid -> string_of_msid uid
  | MPdot (mp,l) -> string_of_mp mp ^ "." ^ string_of_label l

let string_of_kn kn =
  let (modpath, _dirpath, label) = repr_kn kn in
    string_of_mp modpath ^ "_" ^ string_of_label label

let string_of_con con =
  let (modpath, _dirpath, label) = repr_con con in
    string_of_mp modpath ^ "_" ^ string_of_label label

let string_of_inductive (kn, i) =
  string_of_kn kn ^ string_of_int i

let string_of_constructor (ind, i) =
  string_of_inductive ind ^ "c" ^ string_of_int i

(* First argument the index of the constructor *)
let make_constructor_pattern i args =
  let f arg = <:patt< $lid:lid_of_name arg$ >> in
    <:patt< Const $int:string_of_int i$ [| $list:List.rev (List.map f args)$ |] >>

let rec push_value id body env =
  print_endline ("adding " ^ string_of_id id);
  env_updated := true;
  let kind = lookup_named_val id (pre_env env) in
    match !kind with
    | VKvalue (v, _) -> ()
    | VKnone -> kind := VKvalue (values (translate env body), Idset.empty)

and translate_constant env c =
  let cb = lookup_constant c (pre_env env) in
    match cb.const_body with
      | Some body -> (match cb.const_body_ast with
	  | Some _ -> <:expr< $lid:lid_of_string (string_of_con c)$ >>
	  | None -> let ast = translate env (Declarations.force body) in
	      cb.const_body_ast <- Some (values ast);
	      env_updated := true;
	      <:expr< $lid:lid_of_string (string_of_con c)$ >>)
      | None -> <:expr< Con $str:string_of_con c$ >>

(** The side-effect of translate is to add the translated construction
    to the value environment. *)
(* A simple counter is used for fresh variables. We effectively encode
   de Bruijn indices as de Bruijn levels. *)
and translate (env : Environ.env) t =
  try (
  match kind_of_term t with
  | Rel x -> print_endline ("rel " ^ lid_of_name (match lookup_rel x env with name, _, _ -> name));
      <:expr< $lid: lid_of_name (match lookup_rel x env with name, _, _ -> name)$ >>
  | Var id -> let v = <:expr< $lid:lid_of_string (string_of_id id)$ >> in
      print_endline ("adding " ^ string_of_id id);
      (match named_body id env with
	  (* Add compiled form of definition to environment if not already present. *)
	 | Some body -> push_value id body env; v
	 | None -> v)
  | Sort (Prop Null) -> <:expr< Prop >>
  | Sort (Prop Pos) -> <:expr< Set >>
  | Sort (Type _) -> <:expr< Type >>
  | Cast (c, _, ty) -> print_endline "cast";
      translate env c
  | Prod (x, t, c) -> print_endline "prod";
      let newenv = Environ.push_rel (x, None, t) env in
	<:expr< Prod ($translate env t$, (fun $lid:lid_of_name x$ -> $translate newenv c$)) >>
  | Lambda (x, t, c) -> print_endline "lambda";
      let newenv = Environ.push_rel (x, None, t) env in
	<:expr< Lam (fun $lid:lid_of_name x$ -> $translate newenv c$) >>
  | LetIn (x, b, t, c) -> print_endline "letin";
      let newenv = Environ.push_rel (x, Some b, t) env in
	<:expr< let $lid:lid_of_name x$ = $translate env b$
                in $translate newenv c$ >>
  | App (c, args) -> (match kind_of_term c with
      | Construct cstr -> print_endline "construct app";
	  let f arg vs = translate env arg :: vs in
	  let vs = Array.fold_right f args [] in
	  let i = index_of_constructor cstr in
  	    <:expr< Const $int:string_of_int i$ [| $list:vs$ |] >>
      | _ -> print_endline "app";
	  let zero = translate env c in
	  let f apps x = <:expr< app $apps$ $translate env x$ >> in
	    Array.fold_left f zero args)
  | Const c -> print_endline ("const " ^ string_of_con c);
      translate_constant env c
  | Ind c -> print_endline ("ind " ^ string_of_inductive c);
      <:expr< Con $str:string_of_inductive c$ >>
  | Construct cstr -> print_endline ("construct " ^ string_of_constructor cstr);
      let i = index_of_constructor cstr in
      <:expr< Const $int:string_of_int i$ [||] >>
  | Case (ci, p, c, branches) -> print_endline "case";
      let default = (<:patt< x >>, None, <:expr< bug x >>) in
      let vs =
	(* let mib = lookup_mind (fst ci.ci_ind) env in *)
	(* let oib = mib.mind_packets.(snd ci.ci_ind) in *)
	(* default branch *)
	let rec f i =
	  if i < 0 then [] else
	    let (args, b) =
	      decompose_lam_n_assum ci.ci_cstr_nargs.(i) branches.(i) in
	    let name (n, _, _) = n in
	    let pat = make_constructor_pattern (i + 1) (List.map name args) in
	    let newenv = push_rel_context args env in
	      (pat, None, translate newenv b) :: f (i - 1) in
	  f (Array.length branches - 1) in
	<:expr< match $translate env c$ with [$list: vs @ [default]$] >>
  | Fix ((recargs, i), (names, types, bodies)) -> print_endline "fix";
      let rec f i =
	if i < 0 then []
	else let newenv = Environ.push_rel (names.(i), Some bodies.(i), types.(i)) env in
	  (<:patt< $lid:lid_of_name names.(i)$ >>, translate newenv bodies.(i)) :: f (i - 1)
      in <:expr< let rec $list:f i$ in $lid:lid_of_name names.(i)$ >>
  | CoFix(ln, (_, tl, bl)) -> print_endline "cofix"; invalid_arg "translate"
  | _ -> print_endline "invalid arg"; invalid_arg "translate"
  ) with Not_found -> print_endline "not found"; invalid_arg "bleh"
    | _ -> print_endline "exception!"; invalid_arg "bleh"

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
    print_endline s;
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
  in List.fold_right aux init []

let dump_env t1 t2 env =
  let vars = List.fold_right (add_value env) env.env_named_vals Smap.empty in
  let vars_and_cons = Cmap.fold add_constant env.env_globals.env_constants vars in
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

let compile env t1 t2 =
  print_endline "compile";
  let code1 = translate env t1 in
  let code2 = translate env t2 in
    print_endline "done translate";
    if !env_updated then
      print_implem "env.ml" (structure_of_env (pre_env env));
    print_endline "done env";
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
