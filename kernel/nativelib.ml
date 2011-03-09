open Names
open Term
open Util
open Nativevalues
open Declarations
open Nativecode

exception NotConvertible

let load_paths = ref ([] : string list)
let imports = ref ([] : string list)

let open_header = ref ([] : mllambda list)
let comp_stack = ref ([] : mllambda list)

let comp_result = ref (None : (int * string * string) option)

(* Global settings and utilies for interface with OCaml *)
let compiler_name =
  if Dynlink.is_native then "ocamlopt.opt"
  else "ocamlc"

let env_name = "Coq_conv_env"

let include_dirs =
  "-I "^Coq_config.camllib^"/camlp5 -I "^Coq_config.coqlib^"/config -I "
  ^Coq_config.coqlib^"/lib -I "^Coq_config.coqlib^"/kernel "
  ^"-I "^Filename.temp_dir_name^" "

(* Pointer to the function linking an ML object into coq's toplevel *)
let load_obj = ref (fun x -> () : string -> unit)

let push_comp_stack e =
  comp_stack := !comp_stack@e

let emit_comp_stack () =
  let res = !comp_stack in
  comp_stack := []; res

let compile_terms base_mp terms_code =
(*  let ast = emit_comp_stack () in *)
(*  let terms_code =
    [<:str_item< open Nativelib >>;
     <:str_item< open Nativevalues >>;
     <:str_item< open Names >>] @ (List.rev !open_header) @ ast @ terms_code
  in*)
  let mod_name = Filename.temp_file "Coq_native" ".ml" in
  let ch_out = open_out mod_name in
  let fmt = Format.formatter_of_out_channel ch_out in
  pp_globals base_mp fmt terms_code;
  close_out ch_out;
  print_endline "Compilation...";
  let include_dirs =
    include_dirs^"-I " ^ (String.concat " -I " !load_paths) ^ " "
  in
  let filename = Filename.temp_file "coq_native" ".cmo" in
  let filename = Dynlink.adapt_filename filename in
  let comp_cmd =
    Format.sprintf "%s -%s -o %s -rectypes %s %s"
      compiler_name (if Dynlink.is_native then "shared" else "c")
      filename include_dirs mod_name
  in
  let res = Sys.command comp_cmd in
  let mod_name = Filename.chop_extension (Filename.basename mod_name) in
    comp_result := Some (res, filename, mod_name);
    res, filename, mod_name

let call_linker f =
  if Dynlink.is_native then
  try Dynlink.loadfile f
  with Dynlink.Error e -> print_endline (Dynlink.error_message e)
  else (!load_obj f; ())

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
	  ((List.rev x) @ l, kns)
      with Not_found -> (result,kns)
    end
  in
    let kns = Stringmap.empty in
    let (res, kns) = List.fold_right aux init ([],kns) in
      List.rev res, kns

exception Bug of string

type nbe_annotation =
  | CaseAnnot of case_info
  | SortAnnot of sorts

module NbeAnnotTbl =
  struct
   type t = {max_index : int; tbl : nbe_annotation Intmap.t}

   let empty = {max_index = 0; tbl = Intmap.empty}
   let add x t =
     let i = t.max_index in
     {max_index = i+1; tbl = Intmap.add i x t.tbl}, i

   let find x t = Intmap.find x t.tbl

  end


let rt1 = ref (mk_accu dummy_atom)
let rt2 = ref (mk_accu dummy_atom)

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
  call_linker (Dynlink.adapt_filename (s^".cma"))
