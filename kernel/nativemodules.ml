(*i camlp4use: "q_MLast.cmo" i*)

open Names
open Declarations
open Environ
open Mod_subst
open Modops
open Nativecode
open Nativelib

type mod_field =
  | MFglobal of global
  | MFmodule of label * mod_expr
  | MFmodtype

and mod_expr =
  | MEident
  | MEstruct of mod_field list
  | MEfunctor

let rec translate_mod_type mp env typ_expr =
  assert false
(*  match typ_expr with
  | SEBident mp ->
      <:module_type< $uid:string_of_mp mp$ >>
  | SEBstruct expr_list ->
      let ast = List.map (translate_fields_type mp env) expr_list in
      <:module_type< sig $list:ast$ end >>
  | SEBfunctor (mbid, mtb, mtb') ->
      let mp' = MPbound mbid in
      let env' = add_module (module_body_of_type mp' mtb) env in
      let (_,mbid,_) = repr_mbid mbid in
      let ast = translate_mod_type mp env' mtb' in
      let typ_ast = translate_mod_type mp' env mtb.typ_expr in
      <:module_type< functor ($uid:mbid$ : $typ_ast$) -> $ast$ >>
  | _ -> assert false*)

and translate_fields_type mp env (l,e) =
  assert false
(*  match e with
  | SFBconst cb ->
      let _,lid = const_lid mp (make_con mp empty_dirpath l) in
      <:sig_item< value $lid:lid$ : Nativevalues.t >>
  | SFBmodule md ->
      let mod_type_expr = translate_mod_type md.mod_mp env md.mod_type in
      let uid = string_of_label l in
      <:sig_item< module $uid:uid$ : $mod_type_expr$ >>
  | SFBmind mb ->
      let _,lid = mind_lid mp (mp,id_of_label l) in
      <:sig_item< value $lid:lid$ : Nativevalues.t >>
(*  | SFBmodtype mdtyp ->
      let tr = translate_mod_type mp env mdtyp.typ_expr in
      <:str_item< module type $uid:string_of_label l$ = $tr$ >>*)
  | _ -> assert false*)


let rec translate_mod mp env mod_expr =
  match mod_expr with
(*  | SEBident mp' ->
      let uid = relative_mp_of_mp mp mp' in
      <:module_expr< $uid$ >>, annots*)
  | SEBstruct msb ->
      let env' = add_signature mp msb empty_delta_resolver env in
      let ast =
        List.fold_left (translate_fields mp env') [] msb
      in
      MEstruct ast
(*  | SEBfunctor (mbid,mtb,meb) ->
      let mp' = MPbound mbid in
      let env' = add_module (module_body_of_type mp' mtb) env in
      let (_,mbid,_) = repr_mbid mbid in
      let ast, annots = translate_mod mp env' annots meb in
      let typ_ast = translate_mod_type mp' env mtb.typ_expr in
      let e = <:module_expr< functor ($uid:mbid$ : $typ_ast$) -> $ast$ >> in
      e, annots
  | SEBapply (f,x,_) ->
      let tr_f, annots = translate_mod mp env annots f in
      let tr_x, annots = translate_mod mp env annots x in
      <:module_expr< $tr_f$ $tr_x$ >>, annots
  | SEBwith _ -> assert false*)
and translate_fields mp env acc (l,x) =
  match x with
  | SFBconst cb ->
      let tr,auxdefs = compile_constant (pre_env env) [] mp l cb in
      List.fold_right (fun g acc -> MFglobal g::acc) (tr::auxdefs) acc
  | SFBmind mb ->
      let kn = make_mind mp empty_dirpath l in
      let tr = compile_mind mb kn [] in
      List.fold_right (fun g acc -> MFglobal g::acc) tr acc
  | SFBmodule md ->
      begin
        match md.mod_expr with
        | Some e ->
            MFmodule(l,translate_mod md.mod_mp env e)::acc
        | None -> assert false
      end
  | SFBmodtype mdtyp ->
      assert false
(*      let tr = translate_mod_type mp env mdtyp.typ_expr in
      <:str_item< module type $uid:string_of_label l$ = $tr$ >>::ast, annots*)

let dump_library mp env mod_expr =
  print_endline "Compiling library...";
  match mod_expr with
  | SEBstruct msb ->
      let env = add_signature mp msb empty_delta_resolver env in
      let mlcode = List.fold_left (translate_fields mp env) [] msb in
      print_endline "Compiled library."; List.rev mlcode
  | _ -> assert false

let pp_mod_field mp fmt t =
  match t with
  | MFglobal g -> pp_global mp fmt g
  | _ -> assert false

let pp_mod_fields mp fmt l =
  List.iter (pp_mod_field mp fmt) l

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
  pp_mod_fields mp fmt code;
  let load_paths = "-I " ^ (String.concat " -I " load_paths) ^ " " in
  close_out ch_out;
  let comp_cmd =
    "ocamlopt.opt -shared -o "^f^".cmxs -rectypes "^include_dirs^load_paths^f^".ml"
  in
  print_endline "Compiling module...";
  let res = Sys.command comp_cmd in print_endline "Compiled"; res

