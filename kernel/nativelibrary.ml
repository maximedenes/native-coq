(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Declarations
open Environ
open Mod_subst
open Modops
open Nativecode
open Nativelib

type mod_sig_field =
  | MSFglobal of gname
  | MSFtype of global
  | MSFmodule of module_path * label * mod_sig_expr

and mod_sig_expr =
  | MSEsig of mod_sig_field list
  | MSEfunctor of string * mod_sig_expr * mod_sig_expr

type mod_field =
  | MFglobal of global * global list 
  | MFmodule of module_path * label * mod_expr
  | MFmodtype of module_path * label * mod_sig_expr

and mod_expr =
  | MEident of string
  | MEapply of mod_expr * mod_expr
  | MEstruct of mod_field list
  | MEfunctor of string * mod_sig_expr * mod_expr

let rec translate_mod prefix mp env mod_expr acc =
  match mod_expr with
  | SEBident mp' -> assert false
  | SEBstruct msb ->
      let env' = add_signature mp msb empty_delta_resolver env in
      List.fold_right (translate_fields prefix mp env') msb acc
  | SEBfunctor (mbid,mtb,meb) -> acc
  | SEBapply (f,x,_) -> assert false
  | SEBwith _ -> assert false
and translate_fields prefix mp env (l,x) (trs,values,upds as acc) =
  match x with
  | SFBconst cb ->
      let gl, values, upd =
        compile_constant_field (pre_env env) prefix mp l values cb
      in
      let gl = optimize_stk gl in
      let tr, auxdefs = List.hd gl, List.rev (List.tl gl) in (* TODO: can we
      avoid this? *)
      MFglobal(tr,auxdefs)::trs, values, upd::upds
  | SFBmind mb ->
      let tr, values, upd = compile_mind_field prefix mp l values mb in
      List.fold_left (fun acc g -> MFglobal(g,[])::acc) trs tr, values,
      upd::upds
  | SFBmodule md ->
      translate_mod prefix md.mod_mp env md.mod_type acc
  | SFBmodtype mdtyp ->
      translate_mod prefix mdtyp.typ_mp env mdtyp.typ_expr acc

let dump_library mp dp env mod_expr =
  Flags.if_verbose print_endline "Compiling library...";
  match mod_expr with
  | SEBstruct msb ->
      let env = add_signature mp msb empty_delta_resolver env in
      let prefix = mod_uid_of_dirpath dp ^ "." in
      let t0 = Sys.time () in 
      let mlcode, values, upds =
        List.fold_right (translate_fields prefix mp env) msb ([],[],[])
      in
      let t1 = Sys.time () in
(*      let mlopt = optimize_stk mlcode in
      let t2 = Sys.time () in*)
      Flags.if_verbose (Format.eprintf "Compiled library. ml %.5f@.") (t1-.t0);
      mlcode, Array.of_list (List.rev values), upds
  | _ -> assert false


let pp_mod_field fmt t =
  match t with
  | MFglobal (g,auxdefs) -> pp_global_aux fmt g auxdefs
  | _ -> assert false

let pp_toplevel_field fmt t =
  match t with
  | MFglobal (g,auxdefs) ->
    List.iter (pp_global fmt) auxdefs;
    pp_global fmt g 
  | _ -> pp_mod_field fmt t

let compile_library dir code load_paths f =
  let header = mk_library_header dir init_opens in
  let ch_out = open_out (f^".ml") in
  let fmt = Format.formatter_of_out_channel ch_out in
  pp_globals fmt header;
  List.iter (pp_toplevel_field fmt) code;
  Format.fprintf fmt "@.";
  let load_paths = "-I " ^ (String.concat " -I " load_paths) ^ " " in
  close_out ch_out;
  let comp_cmd =
    Format.sprintf "%s%s -%s -o %s -rectypes -w -A %s %s %s.ml"
      (if Flags.is_verbose () then "time " else "")
      Nativelib.compiler_name (if Dynlink.is_native then "shared" else "c")
      (Dynlink.adapt_filename (f^".cmo")) include_dirs load_paths f
  in
  Flags.if_verbose print_endline "Compiling module...";
  let res = Sys.command comp_cmd in
  Sys.rename (f^".ml") (f^".native");
  Flags.if_verbose print_endline "Compiled"; res
