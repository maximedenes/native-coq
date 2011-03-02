(*i camlp4use: "q_MLast.cmo" i*)

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

let rec translate_mod mp env mod_expr acc =
  match mod_expr with
  | SEBident mp' -> assert false
  | SEBstruct msb ->
      let env' = add_signature mp msb empty_delta_resolver env in
      List.fold_right (translate_fields mp env') msb acc
  | SEBfunctor (mbid,mtb,meb) -> acc
  | SEBapply (f,x,_) -> assert false
  | SEBwith _ -> assert false
and translate_fields mp env (l,x) acc =
  match x with
  | SFBconst cb ->
      let tr, auxdefs = compile_constant (pre_env env) mp l cb in
      let l = optimize_stk (tr::auxdefs) in
      let tr, auxdefs = List.hd l, List.rev (List.tl l) in
      MFglobal(tr,auxdefs)::acc
  | SFBmind mb ->
      let kn = make_mind mp empty_dirpath l in
      let tr = compile_mind mb kn [] in
      List.fold_left (fun acc g -> MFglobal(g,[])::acc) acc tr
  | SFBmodule md ->
      translate_mod md.mod_mp env md.mod_type acc
  | SFBmodtype mdtyp ->
      translate_mod mdtyp.typ_mp env mdtyp.typ_expr acc

let dump_library mp env mod_expr =
  print_endline "Compiling library...";
  match mod_expr with
  | SEBstruct msb ->
      let env = add_signature mp msb empty_delta_resolver env in
      let t0 = Sys.time ()in 
      let mlcode = List.fold_right (translate_fields mp env) msb [] in
      let t1 = Sys.time () in
(*      let mlopt = optimize_stk mlcode in
      let t2 = Sys.time () in*)
      Format.eprintf "Compiled library. ml %.5f@." (t1-.t0);
      mlcode
  | _ -> assert false


let rec pp_mod_type_expr mp fmt mse =
  match mse with
  | MSEsig l -> Format.fprintf fmt "@[sig@ %a@ end@]" (pp_mod_sig_fields mp) l
  | MSEfunctor (l, mst, mse) ->
      Format.fprintf fmt "functor (%s : %a) ->@ @[%a@]" l (pp_mod_type_expr mp) mst
      (pp_mod_type_expr mp) mse


and pp_mod_sig_field mp fmt t =
  match t with
  | MSFglobal gn ->
      Format.fprintf fmt "val %a : Nativevalues.t@\n" (pp_gname None) gn 
  | MSFtype g ->
      pp_global mp fmt g
  | MSFmodule (mp',l,mse) ->
      Format.fprintf fmt "module %s : @,%a@\n" (string_of_label l)
      (pp_mod_type_expr mp') mse

and pp_mod_sig_fields mp fmt l =
  List.iter (pp_mod_sig_field mp fmt) l

let rec pp_mod_expr mp fmt me =
  match me with
  | MEident s ->
      Format.fprintf fmt "%s" s
  | MEapply(f,x) ->
      Format.fprintf fmt "%a(%a)" (pp_mod_expr mp) f (pp_mod_expr mp) x
  | MEstruct l -> Format.fprintf fmt "@[struct@ %a@ end@]" (pp_mod_fields mp) l
  | MEfunctor(l, mse, me) ->
      Format.fprintf fmt "functor (%s : %a) ->@ @[%a@]" l (pp_mod_type_expr mp)
      mse (pp_mod_expr mp) me

and pp_mod_field mp fmt t =
  match t with
  | MFglobal (g,auxdefs) -> pp_global_aux mp fmt g auxdefs
  | MFmodule (mp',l,me) ->
      Format.fprintf fmt "module %s =@,%a@\n" (string_of_label l)
      (pp_mod_expr mp') me
  | MFmodtype (mp',l,mse) ->
      Format.fprintf fmt "module type %s =@,%a@\n" (string_of_label l)
      (pp_mod_type_expr mp') mse

and pp_mod_fields mp fmt l =
  List.iter (pp_mod_field mp fmt) l

let pp_toplevel_field mp fmt t =
  match t with
  | MFglobal (g,auxdefs) ->
    List.iter (pp_global mp fmt) auxdefs;
    pp_global mp fmt g 
  | _ -> pp_mod_field mp fmt t

let compile_module code mp load_paths f =
  let header = mk_opens ["Nativevalues";"Nativecode";"Nativeconv"] in
(*  let code =
    [<:str_item< open Nativelib >>; <:str_item< open Nativevalues >>;
     <:str_item< open Names >>]
    @ code
  in*)
  let ch_out = open_out (f^".ml") in
  let fmt = Format.formatter_of_out_channel ch_out in
  pp_globals mp fmt header;
  List.iter (pp_toplevel_field mp fmt) code;
  Format.fprintf fmt "@.";
  let load_paths = "-I " ^ (String.concat " -I " load_paths) ^ " " in
  close_out ch_out;
  let comp_cmd =
    "time ocamlopt.opt -shared -o "^f^".cmxs -rectypes "^include_dirs^load_paths^f^".ml"
  in
  print_endline "Compiling module...";
  let res = Sys.command comp_cmd in print_endline "Compiled"; res

