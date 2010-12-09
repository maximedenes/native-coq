(*i camlp4use: "q_MLast.cmo" i*)

open Names
open Declarations
open Environ
open Mod_subst
open Modops
open Nativecode
open Nativelib

type mod_sig_field =
  | MSFconst of label

and mod_sig_expr =
  MSEsig of mod_sig_field list

type mod_field =
  | MFglobal of global
  | MFmodule of label * mod_expr
  | MFmodtype of label * mod_sig_expr

and mod_expr =
  | MEident of string
  | MEapply of mod_expr * mod_expr
  | MEstruct of mod_field list
  | MEfunctor of string * mod_sig_expr * mod_expr

let rec translate_mod_type mp env typ_expr =
  match typ_expr with
  | SEBident mp -> assert false
(*      <:module_type< $uid:string_of_mp mp$ >>*)
  | SEBstruct expr_list ->
      MSEsig (List.map (translate_fields_type mp env) expr_list)
  | SEBfunctor (mbid, mtb, mtb') -> assert false
      (*
      let mp' = MPbound mbid in
      let env' = add_module (module_body_of_type mp' mtb) env in
      let (_,mbid,_) = repr_mbid mbid in
      let ast = translate_mod_type mp env' mtb' in
      let typ_ast = translate_mod_type mp' env mtb.typ_expr in
      <:module_type< functor ($uid:mbid$ : $typ_ast$) -> $ast$ >> *)
  | _ -> assert false

and translate_fields_type mp env (l,e) =
  match e with
  | SFBconst cb -> MSFconst l
  | SFBmodule md -> assert false
(*      let mod_type_expr = translate_mod_type md.mod_mp env md.mod_type in
      let uid = string_of_label l in
      <:sig_item< module $uid:uid$ : $mod_type_expr$ >>*)
  | SFBmind mb -> assert false
(*      let _,lid = mind_lid mp (mp,id_of_label l) in
      <:sig_item< value $lid:lid$ : Nativevalues.t >>*)
(*  | SFBmodtype mdtyp ->
      let tr = translate_mod_type mp env mdtyp.typ_expr in
      <:str_item< module type $uid:string_of_label l$ = $tr$ >>*)
  | _ -> assert false


let rec translate_mod mp env mod_expr =
  match mod_expr with
  | SEBident mp' ->
      MEident (String.concat "." (relative_list_of_mp mp mp'))
  | SEBstruct msb ->
      let env' = add_signature mp msb empty_delta_resolver env in
      let ast =
        List.fold_left (translate_fields mp env') [] msb
      in
      MEstruct ast
  | SEBfunctor (mbid,mtb,meb) ->
      let mp' = MPbound mbid in
      let env' = add_module (module_body_of_type mp' mtb) env in
      let (_,mbid,_) = repr_mbid mbid in
      let ast = translate_mod mp env' meb in
      let typ_ast = translate_mod_type mp' env mtb.typ_expr in
      MEfunctor(mbid,typ_ast,ast)
  | SEBapply (f,x,_) ->
      let tr_f = translate_mod mp env f in
      let tr_x = translate_mod mp env x in
      MEapply(tr_f,tr_x)
  | SEBwith _ -> assert false
and translate_fields mp env acc (l,x) =
  match x with
  | SFBconst cb ->
      let tr,auxdefs = compile_constant (pre_env env) [] mp l cb in
      let l = optimize_stk (tr::auxdefs) in
      List.fold_right (fun g acc -> MFglobal g::acc) l acc
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
      MFmodtype(l,translate_mod_type mp env mdtyp.typ_expr)::acc

let dump_library mp env mod_expr =
  print_endline "Compiling library...";
  match mod_expr with
  | SEBstruct msb ->
      let env = add_signature mp msb empty_delta_resolver env in
      let t0 = Sys.time ()in 
      let mlcode = List.fold_left (translate_fields mp env) [] msb in
      let t1 = Sys.time () in
(*      let mlopt = optimize_stk mlcode in
      let t2 = Sys.time () in*)
      Format.eprintf "Compiled library. ml %.5f@." (t1-.t0);
      List.rev mlcode
  | _ -> assert false


let rec pp_mod_type_expr mp fmt mse =
  match mse with
  | MSEsig l -> Format.fprintf fmt "@[sig@ %a@ end@]" (pp_mod_sig_fields mp) l

and pp_mod_sig_field mp fmt t =
  match t with
  | MSFconst l -> Format.fprintf fmt "val %s : Nativevalues.t@," (string_of_label l)

and pp_mod_sig_fields mp fmt l =
  List.iter (pp_mod_sig_field mp fmt) l

let rec pp_mod_expr mp fmt me =
  match me with
  | MEident s ->
      Format.fprintf fmt "%s" s
  | MEapply(f,x) ->
      Format.fprintf fmt "%a.%a" (pp_mod_expr mp) f (pp_mod_expr mp) x
  | MEstruct l -> Format.fprintf fmt "@[struct@ %a@ end@]" (pp_mod_fields mp) l
  | MEfunctor(l, mse, me) ->
      Format.fprintf fmt "functor (%s : %a) ->@ @[%a@]" l (pp_mod_type_expr mp)
      mse (pp_mod_expr mp) me

and pp_mod_field mp fmt t =
  match t with
  | MFglobal g -> pp_global mp fmt g
  | MFmodule (l,me) -> Format.fprintf fmt "module %s =@,%a@\n" (string_of_label l) (pp_mod_expr mp) me
  | MFmodtype (l,mse) ->
      Format.fprintf fmt "module type %s =@,%a@\n" (string_of_label l)
      (pp_mod_type_expr mp) mse

and pp_mod_fields mp fmt l =
  List.iter (pp_mod_field mp fmt) l

let compile_module code mp load_paths f =
  let header = mk_opens ["Nativevalues";"Nativecode";"Nativeconv"] in
(*  let code =
    [<:str_item< open Nativelib >>; <:str_item< open Nativevalues >>;
     <:str_item< open Names >>]
    @ code
  in*)
  print_endline "Dumping library...";
  let t0 = Sys.time () in
  let ch_out = open_out (f^".ml") in
  let fmt = Format.formatter_of_out_channel ch_out in
  pp_globals mp fmt header;
  pp_mod_fields mp fmt code;
  Format.fprintf fmt "@.";
  close_out ch_out;
  let t1 = Sys.time () in
  Format.eprintf "Library dumped %.5f@." (t1-.t0);
  let load_paths = "-I " ^ (String.concat " -I " load_paths) ^ " " in
  let comp_cmd =
    "ocamlopt.opt -shared -o "^f^".cmxs -rectypes "^include_dirs^load_paths^f^".ml"
  in
  print_endline "Compiling library...";
  let res = Sys.command comp_cmd in print_endline "Compiled"; res

