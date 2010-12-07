(*i camlp4use: "q_MLast.cmo" i*)

open Names
open Declarations
open Environ
open Mod_subst
open Modops
open Nativecode

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


let rec translate_mod mp env annots mod_expr =
  assert false
(*  match mod_expr with
  | SEBident mp' ->
      let uid = relative_mp_of_mp mp mp' in
      <:module_expr< $uid$ >>, annots
  | SEBstruct msb ->
      let env' = add_signature mp msb empty_delta_resolver env in
      let ast, annots =
        List.fold_right (translate_fields mp env') msb ([],annots)
      in
      let e = <:module_expr< struct $list:ast$ end >> in
      e, annots
  | SEBfunctor (mbid,mtb,meb) ->
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
and translate_fields mp env mlcode (l,x) =
  match x with
  | SFBconst cb ->
      let tr,mlcode = compile_constant (pre_env env) mlcode mp l cb in
      tr::mlcode
  | SFBmind mb ->
      let kn = make_mind mp empty_dirpath l in
      compile_mind mb kn mlcode
(*  | SFBmodule md ->
      begin
        match md.mod_expr with
        | Some e ->
            let mod_expr,annots =
              translate_mod md.mod_mp env annots e
            in
            let mod_ast =
              <:str_item< module $uid:string_of_label l$ = $mod_expr$ >>
            in
            mod_ast::ast, annots
        | None -> assert false
      end
  | SFBmodtype mdtyp ->
      let tr = translate_mod_type mp env mdtyp.typ_expr in
      <:str_item< module type $uid:string_of_label l$ = $tr$ >>::ast, annots*)

let dump_library mp env mod_expr =
  print_endline "Compiling library...";
  match mod_expr with
  | SEBstruct msb ->
      let env = add_signature mp msb empty_delta_resolver env in
      let t0 = Sys.time ()in 
      let mlcode = List.fold_left (translate_fields mp env) [] msb in
      let t1 = Sys.time () in
      let mlopt = optimize_stk mlcode in
      let t2 = Sys.time () in
      Format.eprintf "Compiled library. ml %.5f; opt %.5f@." (t1-.t0) (t2-.t1);
      List.rev mlopt
  | _ -> assert false
