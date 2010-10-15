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

let compare env t1 t2 cu =
  let mp = env.current_mp in
  let (code1,_) = translate mp env "t1" t1 in
  let (code2,_) = translate mp env "t2" t2 in
  let terms_code =
    code1 @ code2 @ [<:str_item< value _ = (*let t0 = Unix.time () in *)
      (*do {*)try conv_val 0 t1 t2 with _ -> exit 1 (*;
    Format.fprintf Format.std_formatter
    "Test running time: %.5fs\n" (Unix.time() -. t0);
    flush_all() }*)
    >>]
  in
    match call_compiler terms_code with
    | 0,_,_ ->
      begin
        print_endline "Running test...";
        let res = Sys.command "time ./a.out" in
        match res with
          | 0 -> cu
          | _ -> raise NotConvertible
      end
    | _ -> anomaly "Compilation failure" 

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
