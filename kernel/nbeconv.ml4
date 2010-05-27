(*i camlp4use: "q_MLast.cmo" i*)

open Names
open Term
open Pre_env
open Pcaml
open Nativelib
open Declarations
open Util
open Nativecode
(*open Reduction*)

exception NotConvertible

let env_name = "Coq_conv_env"
let terms_name = "Coq_conv_terms"

let include_dirs =
  "-I "^Coq_config.camllib^"/camlp5 -I "^Coq_config.coqlib^"/config -I "
  ^Coq_config.coqlib^"/lib -I "^Coq_config.coqlib^"/kernel "

let include_libs =
  "camlp5.cmxa coq_config.cmx lib.cmxa kernel.cmxa "


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

let add_value env (id, value) xs =
  match !value with
    | VKvalue (v, _) ->
	let sid = string_of_id id in
	let ast = (<:str_item< value $lid:lid_of_string sid$ = $expr_of_values v$ >>, loc) in
        let (_, b, _) = Sign.lookup_named id env.env_named_context in
	let deps = (match b with
          | None -> [] 
	  | Some body -> let res = assums body in
             (*print_endline (sid^"(named_val) assums "^String.concat "," res);*)
              res)
        in Stringmap.add sid (VarKey id, NbeAnnotTbl.empty, ast, deps) xs
    | VKnone -> xs

let add_constant c ck xs =
  match (fst ck).const_body_ast with
    | Some v ->
	let sc = Nativecode.string_of_con c in
	let ast = (<:str_item< value $lid:lid_of_string sc$ = $expr_of_values v$ >>, loc) in
	let deps = match (fst ck).const_body_deps with
	  | Some l -> (*print_endline (sc^" assums "^String.concat "," l);*) l 
	  | None -> []
        in
	let annots = match (fst ck).const_body_annots with
          | Some t -> t
          | None -> NbeAnnotTbl.empty
        in
	Stringmap.add sc (ConstKey c, annots, ast, deps) xs
    | None ->
        ((*print_endline ("Const body AST not found: "^Nativecode.string_of_con c);*) xs)

let add_ind env c ind xs =
  let mb = lookup_mind c env in
  (*let ob = ind.mind_packets.(snd ind) in*)
  let ob = ind.mind_packets.(0) in
  let ast = translate_ind env (c,0) (mb,ob) in
  Stringmap.add (string_of_mind c) (RelKey (-1), NbeAnnotTbl.empty, ast, []) xs

let topological_sort init xs =
  let visited = ref Stringset.empty in
  let rec aux s (result,kns) =
    if Stringset.mem s !visited
    then (result,kns)
    else begin
      try
	let (c, annots, x, deps) = Stringmap.find s xs in
	  visited := Stringset.add s !visited;
          let (l,kns) = List.fold_right aux deps (result,kns) in
          let kns = Stringmap.add s (c,annots) kns in
	  (x :: l, kns)
      with Not_found -> (result,kns)
    end
  in
    let kns = Stringmap.empty in
    let (res, kns) = List.fold_right aux init ([],kns) in
      List.rev res, kns

let dump_env terms env =
  let vars = List.fold_right (add_value env) env.env_named_vals Stringmap.empty in
  let vars_and_cons = Cmap_env.fold add_constant env.env_globals.env_constants vars in
  let vars_cons_ind = Mindmap_env.fold (add_ind env) env.env_globals.env_inductives vars_and_cons
  in
  let initial_set = List.fold_left (fun acc t -> assums t @ acc) [] terms in
  print_endline (String.concat "," initial_set);
  let header =
    [(<:str_item< open Nativelib >>, loc);
     (<:str_item< open Nativevalues >>, loc)]
  in
  let (l,kns) = topological_sort initial_set vars_cons_ind in
    (header @ l,kns)

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
  if Sys.file_exists (env_name^".ml") then
    anomaly (env_name ^".ml already exists");
  if Sys.file_exists (terms_name^".ml") then
    anomaly (terms_name ^".ml already exists");
  (*print_endline "Translating t1";*)
  let (code1,_) = translate env (RelKey (-1)) t1 in
  (*print_endline "Translating t2";*)
  let (code2,_) = translate env (RelKey (-1)) t2 in
    Pcaml.input_file := "/dev/null";
    if true (* TODO : dump env for whole vo file *) then begin
        (*print_endline "Dumping env";*)
        let (dump,_) = dump_env [t1;t2] env in
        (*print_endline "Dumped env.";
        Pcaml.output_file := Some "envpr.ml";
        !Pcaml.print_implem (dump);
        print_endline "Generated envpr.ml";*)
	print_implem (env_name^".ml") (compute_loc dump)(*;
        print_endline "Generated env.ml";*)
      end;
    (*Pcaml.output_file := Some "termspr.ml";
    !Pcaml.print_implem
    	 [(<:str_item< open Nbe >>, loc);
    	  (<:str_item< open Env >>, loc);
    	  (<:str_item< value t1 = $code1$ >>, loc);
    	  (<:str_item< value t2 = $code2$ >>, loc);
    	  (<:str_item< value _ = print_endline (string_of_term 0 t1) >>, loc);
    	  (<:str_item< value _ = print_endline (string_of_term 0 t2) >>, loc);
    	  (<:str_item< value _ = compare 0 t1 t2 >>, loc)];*)
    print_implem (terms_name^".ml")
	 [(<:str_item< open Nativelib >>, loc);
	  (<:str_item< open $list:[env_name]$ >>, loc);
	  (<:str_item< value t1 = $code1$ >>, loc);
	  (<:str_item< value t2 = $code2$ >>, loc);
    	  (*(<:str_item< value _ = print_endline (string_of_term 0 t1) >>, loc);*)
    	  (*(<:str_item< value _ = print_endline (string_of_term 0 t2) >>, loc);*)
	  (<:str_item< value _ = compare 0 t1 t2 >>, loc)];
    env_updated := false;
    (values code1, values code2)

let compare (v1, v2) cu =
  let file_names = env_name^".ml "^terms_name^".ml" in
  let _ = Unix.system ("touch "^env_name^".ml") in
  print_endline "Compilation...";
  let comp_cmd =
    "ocamlopt.opt -rectypes "^include_dirs^include_libs^file_names
  in
  let res = Unix.system comp_cmd in
  match res with
    | Unix.WEXITED 0 ->
      begin
      let _ = Unix.system ("rm "^file_names) in
      print_endline "Running conversion test...";
      let res = Unix.system "./a.out" in
      let _ = Unix.system "rm a.out" in
      match res with
        | Unix.WEXITED 0 -> cu
        | _ -> (print_endline "Conversion test failure"; raise NotConvertible)
      end
    | _ -> (print_endline "Compilation failure"; raise NotConvertible)
