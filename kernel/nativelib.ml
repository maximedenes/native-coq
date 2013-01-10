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
open Errors

(* This file provides facilities to access the native code compiler *)

let get_load_paths =
  ref (fun _ -> anomaly "get_load_paths not initialized" : unit -> string list)

let open_header = List.map mk_open ["Nativevalues";"Nativecode";"Nativelib";
				   "Nativeconv";"Declaremods"]

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

let write_ml_code ml_filename ?(header=[]) code =
  let header = open_header@header in
  let ch_out = open_out ml_filename in
  let fmt = Format.formatter_of_out_channel ch_out in
  List.iter (pp_global fmt) (header@code);
  close_out ch_out

let call_compiler ml_filename load_path =
  let include_dirs =
    if load_path <> [] then
      include_dirs^"-I " ^ (String.concat " -I " load_path) ^ " "
    else include_dirs
  in
  let f = Filename.chop_extension ml_filename in
  let link_filename = f ^ ".cmo" in
  let link_filename = Dynlink.adapt_filename link_filename in
  let comp_cmd =
    Format.sprintf "%s -%s -o %s -rectypes -w -A %s %s"
      compiler_name (if Dynlink.is_native then "shared" else "c")
      link_filename include_dirs ml_filename
  in
  let res = Sys.command comp_cmd in
  Sys.rename (f^".ml") (f^".native");
  res, link_filename

let compile ml_filename code =
  write_ml_code ml_filename code;
  call_compiler ml_filename (!get_load_paths())

let call_linker prefix f upds =
  rt1 := dummy_value ();
  rt2 := dummy_value ();
  (try
    if Dynlink.is_native then Dynlink.loadfile f else !load_obj f;
    register_native_file prefix
  with Dynlink.Error e -> anomaly ("Dynlink error, " ^ Dynlink.error_message e));
  match upds with Some upds -> update_locations upds | _ -> ()
