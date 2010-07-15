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

let compile env t1 t2 =
  let (code1,_) = translate env "t1" t1 in
  let (code2,_) = translate env "t2" t2 in
  let (dump,_) = dump_env [t1;t2] env in
  let terms_code =
    code1 @ code2 @ [<:str_item< value _ = compare 0 t1 t2 >>]
  in
    call_compiler dump terms_code

let compare cu =
  cu
  (*let file_names = env_name^".ml "^terms_name^".ml" in
  let _ = Sys.command ("touch "^env_name^".ml") in
  print_endline "Compilation...";
  let comp_cmd =
    "ocamlopt.opt -rectypes "^include_dirs^include_libs^file_names
  in
  let res = Sys.command comp_cmd in
  match res with
    | 0 ->
      begin
      let _ = Sys.command ("rm "^file_names) in
      print_endline "Running conversion test...";
      let res = Sys.command "./a.out" in
      let _ = Sys.command "rm a.out" in
      match res with
        | 0 -> cu
        | _ -> (print_endline "Conversion test failure"; raise NotConvertible)
      end
    | _ -> (print_endline "Compilation failure"; raise NotConvertible)*)
