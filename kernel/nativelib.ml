(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Names
open Term
open Util
open Nativevalues
open Declarations
open Nativecode
open Pre_env

(* This file provides facilities to access the native code compiler *)

let load_paths = ref ([] : string list)
let imports = ref ([] : string list)

let init_opens = List.map mk_open ["Nativevalues";"Nativecode";"Nativelib";
				   "Nativeconv";"Declaremods"]
let open_header = ref (init_opens : global list)

(* Global settings and utilies for interface with OCaml *)
let compiler_name =
  if Dynlink.is_native then "ocamlopt"
  else "ocamlc"

let include_dirs =
  let coqroot = !Flags.coqlib in
  "-I "^Coq_config.camllib^"/camlp5 -I "^coqroot^"/config -I "
  ^coqroot^"/lib -I "^coqroot^"/kernel -I "^coqroot^"/library "
  ^"-I "^Filename.temp_dir_name^" "

(* Pointer to the function linking an ML object into coq's toplevel *)
let load_obj = ref (fun x -> () : string -> unit)

let rt1 = ref (dummy_value ())
let rt2 = ref (dummy_value ())

let get_ml_filename () =
  let filename = Filename.temp_file "Coq_native" ".ml" in
  let prefix = Filename.chop_extension (Filename.basename filename) ^ "." in
  filename, prefix

let call_compiler ml_filename code =
  let code =
    !open_header@code
  in
  let ch_out = open_out ml_filename in
  let fmt = Format.formatter_of_out_channel ch_out in
  pp_globals fmt code;
  close_out ch_out;
  print_endline "Compilation...";
  let include_dirs =
    include_dirs^"-I " ^ (String.concat " -I " !load_paths) ^ " "
  in
  let link_filename = Filename.temp_file "coq_native" ".cmo" in
  let link_filename = Dynlink.adapt_filename link_filename in
  let comp_cmd =
    Format.sprintf "%s -%s -o %s -rectypes -w -A %s %s"
      compiler_name (if Dynlink.is_native then "shared" else "c")
      link_filename include_dirs ml_filename
  in
  let res = Sys.command comp_cmd in
  res, link_filename

let call_linker env f upds =
  rt1 := dummy_value ();
  rt2 := dummy_value ();
  (if Dynlink.is_native then Dynlink.loadfile f
  else !load_obj f);
  match upds with Some upds -> update_locations upds | _ -> ()

let extern_state s =
  let f = Dynlink.adapt_filename (s^".cma") in
  let include_dirs = "-I " ^ (String.concat " -I " !load_paths) ^ " " in
  let aux =
    if Dynlink.is_native then (fun s -> s^".cmx") else (fun s -> s^".cmo")
  in
  let imports = List.map aux !imports in
  let imports = String.concat " " imports in
  let comp_cmd =
    Format.sprintf "%s -%s -o %s -rectypes %s %s"
      compiler_name (if Dynlink.is_native then "shared" else "a") f
      include_dirs imports
  in
  let _ = Sys.command comp_cmd in ()

let intern_state s =
  (** WARNING TODO: if a state with the same file name has already been loaded   **)
  (** Dynlink will ignore it, possibly desynchronizing values in the environment **)
(*  let temp = Filename.temp_file s ".cmxs" in*)
  call_linker empty_env (Dynlink.adapt_filename (s^".cma")) None
