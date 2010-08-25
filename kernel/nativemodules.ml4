(*i camlp4use: "q_MLast.cmo" i*)

open Names
open Declarations
open Environ
open Mod_subst
open Modops
open Nativelib
open Nativecode

(* Required to make camlp5 happy. *)
let loc = Ploc.dummy


let rec translate_mod_type mp env typ_expr =
  match typ_expr with
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
  | _ -> assert false

and translate_fields_type mp env (l,e) =
  match e with
  | SFBconst cb ->
      let _,lid = const_lid mp (make_con mp empty_dirpath l) in
      <:sig_item< value $lid:lid$ : Nativevalues.t >>
  | SFBmodule md ->
      begin
        match md.mod_expr with
        | Some e ->
            let mod_type_expr = translate_mod_type md.mod_mp env e in
            let uid = string_of_label l in
            <:sig_item< module $uid:uid$ : $mod_type_expr$ >>
        | None -> assert false
      end
(*  | SFBmodtype mdtyp ->
      let tr = translate_mod_type mp env mdtyp.typ_expr in
      <:str_item< module type $uid:string_of_label l$ = $tr$ >>*)
  | _ -> assert false


let rec translate_mod mp env annots mod_expr =
  match mod_expr with
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
  | SEBwith _ -> assert false
and translate_fields mp env (l,x) (ast,annots) =
  match x with
  | SFBconst cb ->
      begin
        let kn = make_con mp empty_dirpath l in
        let _,lid = const_lid mp kn in
        match cb.const_body with
        | Some t -> 
            let env = pre_env env in
            let t = Declarations.force t in
            let tr,annots = translate ~annots mp env lid t in tr@ast,annots
        | None ->
            let tr = opaque_const mp kn in 
            tr@ast,annots
      end
  | SFBmind mb ->
      let tr = translate_mind mb in
      tr@ast,annots
  | SFBmodule md ->
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
      <:str_item< module type $uid:string_of_label l$ = $tr$ >>::ast, annots

let dump_library mp env mod_expr =
  let mod_ast,annots = translate_mod mp env NbeAnnotTbl.empty mod_expr in
  match mod_ast with
  | <:module_expr< struct $list:ast$ end >> -> ast, annots
  | _ -> assert false
