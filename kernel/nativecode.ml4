(*i camlp4use: "q_MLast.cmo" i*)

open Names
open Nativelib
open Term
open Pre_env
open Pcaml
open Declarations
open Util
open Nativevalues

exception NotConvertible

(* Required to make camlp5 happy. *)
let loc = Ploc.dummy

(* Bringert and Ranta's 'descend' operator for OCaml representations
   of the target code. *)
let descend_ast f t = match t with
  | <:expr< Con $_$ >> -> t
  | <:expr< Var $_$ >> -> t
  | <:expr< Rel $_$ >> -> t
  | <:expr< Lam1 (fun $x$ -> $body$) >> ->
      <:expr< Lam1 (fun $x$ -> $f body$) >>
  | <:expr< Prod ($dom$,(fun $lid:x$ -> $cod$)) >> ->
      <:expr< Prod ($f dom$,(fun $lid:x$ -> $f cod$)) >>
  | <:expr< app $t1$ $t2$ >> -> <:expr< app $f t1$ $f t2$ >>
  | <:expr< App $_$ >> -> t 
  | <:expr< Const ($i$,[| $list:args$ |]) >> ->
      let f t ts = f t :: ts in
      <:expr< Const ($i$,[| $list:List.fold_right f args []$ |]) >>
  | <:expr< Set >> -> t
  | <:expr< Prop >> -> t
  | <:expr< Type $_$ >> -> t
  | <:expr< Match $_$ >> -> t
  | <:expr< $lid:x$ >> -> t
  | <:expr< match $scrutinee$ with [ $list:branches$ ] >> ->
      let bs =
        List.fold_right (fun (p, w, body) bs -> (p, w, f body)::bs) branches []
      in
	<:expr< match $f scrutinee$ with [ $list:bs$ ] >>
  | <:expr< let $flag:r$ $list:defs$ in $t$ >> ->
      let defs' = List.map (fun (p, t) -> (p, f t)) defs in
	<:expr< let $flag:r$ $list:defs'$ in $f t$ >>
  | <:expr< ($list:l$) >> -> <:expr< ($list:List.map f l$) >>
  | <:expr< bug x >> -> t
  | <:expr< fun $x$ -> $body$ >> -> <:expr< fun $x$ -> $f body$ >>
  | <:expr< $app$ $arg$ >> -> <:expr< $f app$ $f arg$ >>
  | _ -> begin
           (*Pcaml.input_file := "/dev/null";
           Pcaml.output_file := Some "debug_descend.ml";
           !Pcaml.print_implem ([(<:str_item< value _ = $t$ >>,loc)]);*)
           raise (Invalid_argument "descend_ast")
         end

let subst rho x = try List.assoc x rho with Not_found -> x

(** A shrinking reduction. This is essentially eta-reduction. Whenever
    a lambda is applied to a variable then beta-reduce. The size of the
    resulting term is strictly smaller. *)
let rec shrink rho = function
  | <:expr< app $t1$ $lid:y$ >> ->
    (match shrink rho t1 with
       | <:expr< Lam1 (fun $lid:x$ -> $body$) >> ->
	 shrink ((x, y) :: rho) body
       | t -> <:expr< app $t$ $lid:subst rho y$ >>)
  | <:expr< $lid:x$ >> -> <:expr< $lid:subst rho x$ >>
  | t -> descend_ast (shrink rho) t

(* Redefine a bunch of functions in module Names to generate names
   acceptable to OCaml. *)
let string_of_dirpath = function
  | [] -> "_"
  | sl -> String.concat "_" (List.map string_of_id (List.rev sl))

let rec string_of_mp = function
  | MPfile sl -> string_of_dirpath (repr_dirpath sl)
  | MPbound mbid -> string_of_label (label_of_mbid mbid)
  | MPdot (mp,l) -> string_of_mp mp ^ "." ^ string_of_label l

let rec in_same_library mp1 mp2 =
  match mp1, mp2 with
  | MPbound _, _ -> assert false
  | _, MPbound _ -> true
  | MPfile dp1, MPfile dp2 -> dp1 = dp2
  | MPdot (mp1,_), MPdot (mp2,_) -> in_same_library mp1 mp2
  | MPdot (mp,_), _ -> in_same_library mp mp2
  | _, MPdot (mp,_) -> in_same_library mp1 mp

let rec list_of_mp acc = function
  | MPdot (mp,l) -> list_of_mp (string_of_label l::acc) mp
  | MPfile dp ->
      let dp = repr_dirpath dp in
      string_of_dirpath dp :: acc
  | MPbound mbid -> string_of_label (label_of_mbid mbid)::acc

let list_of_mp mp = list_of_mp [] mp

let rec strip_common_prefix l1 l2 =
  match l1, l2 with
  | [], _
  | _, [] -> l1, l2
  | hd1::tl1, hd2::tl2 ->
      if hd1 = hd2 then strip_common_prefix tl1 tl2 else hd1::tl1, hd2::tl2

let mk_relative_id base_mp (mp,id) f g =
  let base_l = list_of_mp base_mp in
  let l = list_of_mp mp in
  let _,l = strip_common_prefix base_l l in
  match l with
  | [] -> id
  | hd1::tl1 ->
      let e = List.fold_left (fun acc x -> f acc (g x)) (g hd1) tl1 in
      f e id

let relative_id_of_mp base_mp (mp,lid) =
 let f acc e = <:expr< $acc$.$e$ >> in
 let g x = <:expr< $uid:x$ >> in
 mk_relative_id base_mp (mp,lid) f g

let relative_patt_of_mp base_mp (mp,lid) =
 let f acc e = <:patt< $acc$.$e$ >> in
 let g x = <:patt< $uid:x$ >> in
  mk_relative_id base_mp (mp,lid) f g

let relative_type_of_mp base_mp (mp,lid) =
 let f acc e = <:ctyp< $acc$.$e$ >> in
 let g x = <:ctyp< $uid:x$ >> in
  mk_relative_id base_mp (mp,lid) f g

let relative_mp_of_mp base_mp mp =
  let base_l = list_of_mp base_mp in
  let l = list_of_mp mp in
  let _,l = strip_common_prefix base_l l in
  match l with
  | [] -> assert false
  | hd::tl ->
      let f acc x = <:module_expr< $acc$.$uid:x$ >> in
      List.fold_left f <:module_expr< $uid:hd$ >> tl

let translate_kn base_mp prefix kn =
  let (modpath, _dirpath, label) = repr_kn kn in
  let lid = <:expr< $lid:prefix^string_of_label label$>> in
  let short_name = prefix^string_of_label label in
  relative_id_of_mp base_mp (modpath,lid), short_name

let mod_uid_of_dirpath dir = string_of_dirpath (repr_dirpath dir)

let const_lid base_mp con =
  translate_kn base_mp "const_" (user_con con)

let var_lid id =
  let lid = "var_"^string_of_id id in
  <:expr< $lid:lid$ >>, lid

let mind_lid base_mp (mp,id) =
  let prefix = "mind_" in
  let lid = <:ctyp< $uid:prefix^string_of_id id$>> in
  let short_name = prefix^string_of_id id in
  relative_type_of_mp base_mp (mp,lid), short_name

let construct_uid ?(accu=false) base_mp (mp,id) =
  let prefix = if accu then "Accu_" else "Construct_" in
  let uid = <:expr< $uid:prefix^string_of_id id$>> in
  let short_name = prefix^string_of_id id in
  relative_id_of_mp base_mp (mp,uid), short_name

let construct_uid_patt ?(accu=false) base_mp (mp,id) =
  let prefix = if accu then "Accu_" else "Construct_" in
  let uid = <:patt< $uid:prefix^string_of_id id$>> in
  let short_name = prefix^string_of_id id in
  relative_patt_of_mp base_mp (mp,uid), short_name

let ind_lid ind i =
  let (mind,i) = ind in
  "ind_"^string_of_int i^"_"^string_of_mind mind

let match_lid id i =
  "match_"^string_of_int i^"_"^id

let fix_lid id n i =
  "_"^string_of_int n^"_"^string_of_int i^"_"^id

let atom_lid id n i =
  "atom"^fix_lid id n i

let norm_lid id n i =
  "norm"^fix_lid id n i

let rec_lid id n i =
  "rec"^fix_lid id n i

let expr_of_name x =
  match x with
  | Anonymous -> <:expr< Anonymous >>
  | Name s -> <:expr< Name (id_of_string $str:string_of_id s$) >>

(* First argument the index of the constructor *)
let make_constructor_pattern base_mp mp ob i args =
  let uid,_ = construct_uid_patt base_mp (mp,ob.mind_consnames.(i)) in
  List.fold_left (fun e arg -> <:patt< $e$ $lid:arg$ >>) uid args

let lid_of_index n = "x" ^ string_of_int n
let code_lid_of_index p = "b" ^ string_of_int p

let rec gen_names start len =
  if len = 0 then []
  else if len > 0 then
    lid_of_index start :: gen_names (start + 1) (len - 1)
  else raise (Invalid_argument "gen_names")

let rec gen_rels start len =
  if len = 0 then []
  else if len > 0 then
    <:expr< Rel 0 >> :: gen_rels (start + 1) (len - 1)
  else raise (Invalid_argument "gen_rels")

let rec push_abstractions start n e =
  if n = 0 then e
  else if n > 0 then
    let e = push_abstractions (start+1) (n-1) e in
    <:expr< fun $lid:lid_of_index start$ -> $e$ >>
  else raise (Invalid_argument "push_abstractions")


let free_vars_acc n xs t =
  let rec aux m xs t =
    match kind_of_term t with
      | Rel i ->
          let j = m-i in
          if (j >= n || List.mem j xs) then xs else j::xs
      | Prod (_,t,c) -> aux (m+1) (aux m xs t) c
      | Lambda (_,t,c) -> aux (m+1) (aux m xs t) c
      | LetIn (_,b,t,c) -> aux (m+1) (aux m (aux m xs b) t) c
      | Fix (_,(lna,tl,bl)) ->
          let i = Array.length tl in
          let fd = array_map3 (fun na t b -> (na,t,b)) lna tl bl in
          Array.fold_left (fun xs (na,t,b) -> aux (m+i) (aux m xs t) b) xs fd
      | CoFix (_,(lna,tl,bl)) ->
          let i = Array.length tl in
          let fd = array_map3 (fun na t b -> (na,t,b)) lna tl bl in
          Array.fold_left (fun xs (na,t,b) -> aux (m+i) (aux m xs t) b) xs fd
      | _ -> fold_constr (aux m) xs t
  in (aux n xs t)

let free_vars n t = free_vars_acc n [] t

let dump_reloc_tbl tbl =
  let f (tag,arity) =
    <:expr< ($int:string_of_int (tag+1)$,$int:string_of_int arity$) >>
  in
  <:expr< [| $list:Array.to_list (Array.map f tbl)$ |] >>

(* A simple counter is used for fresh variables. We effectively encode
   de Bruijn indices as de Bruijn levels. *)
let rec translate ?(annots=NbeAnnotTbl.empty) ?(lift=0) mp env t_id t =
  (let rec translate ?(global=false) auxdefs annots n t =
    match kind_of_term t with
      | Rel x -> <:expr< $lid:lid_of_index (n-x)$ >>, auxdefs, annots
      | Var id ->
          begin
          let (_, b, _) = Sign.lookup_named id env.env_named_context in
	      match b with
		| None ->
                    let id_app =
                      <:expr< Names.id_of_string $str:string_of_id id$ >>
                    in
                      <:expr< mk_var_accu $id_app$>>, auxdefs, annots
		| Some body ->
	            let v,_ = var_lid id in
                    compile_value mp env id body;
                    v, auxdefs, annots
          end
      | Sort s -> (* TODO: check universe constraints *)
          let e =
            <:expr< mk_sort_accu (str_decode $str:str_encode s$) >>
          in
          e, auxdefs, annots
      | Cast (c, _, ty) -> translate auxdefs annots n c
      | Prod (x, t, c) ->
          let vt,auxdefs,annots = translate auxdefs annots n t in
          let vc,auxdefs,annots = translate auxdefs annots (n + 1) c in
          let x = expr_of_name x in
          let e =
            <:expr< mk_prod_accu $x$ $vt$ (fun $lid:lid_of_index n$ -> $vc$) >>
          in
            e, auxdefs, annots
      | Lambda (_, t, c) ->
          let v,auxdefs,annots = translate auxdefs annots (n + 1) c in
	  <:expr< fun ($lid:lid_of_index n$ : Nativevalues.t) -> $v$ >>, auxdefs, annots
      | LetIn (_, b, t, c) ->
          let vb,auxdefs,annots = translate auxdefs annots n b in
          let vc,auxdefs,annots = translate auxdefs annots (n + 1) c in
	  <:expr< let $lid:lid_of_index n$ = $vb$ in $vc$ >>, auxdefs, annots
      | App (c, args) ->
          translate_app auxdefs annots n c args
      | Const c ->
          let e,_ = const_lid mp c in
          e, auxdefs, annots
      | Ind c ->
          <:expr< mk_ind_accu (str_decode $str:str_encode c$) >>, auxdefs, annots
      | Construct cstr ->
          let i = index_of_constructor cstr in
          let ind = inductive_of_constructor cstr in
          let mb = lookup_mind (fst ind) env in
          let ob = mb.mind_packets.(snd ind) in
          let nparams = mb.mind_nparams in
          let _,arity = ob.mind_reloc_tbl.(i-1) in
          if nparams+arity = 0 then
            let mp' = ind_modpath ind in
            let cons_expr,_ =
              construct_uid mp (mp',ob.mind_consnames.(i-1))
            in
            let e = <:expr< (Obj.magic $cons_expr$ : Nativevalues.t) >> in
            e, auxdefs, annots
          else translate_app auxdefs annots n t [||]
      | Case (ci, p, c, branches) ->
          let u = (ci, p, c, branches) in
          let ast, auxdefs, annots, _ = translate_case auxdefs annots n u None in
            ast, auxdefs, annots
      | Fix ((recargs, i), (names, types, bodies)) ->
          let m = Array.length bodies in
          let abs_over_bodies e = push_abstractions n m e in
          let rec map_bodies acc i =
            if i >= 0 then
              let body_lid = lid_of_index (n+i) in
              let rec_lid = rec_lid t_id n i in
              let x = (<:patt< $lid:body_lid$>>, <:expr< $lid:rec_lid$ >>) in
              map_bodies (x::acc) (i-1)
            else acc
          in
          let mappings = map_bodies [] (m-1) in
          let f i (recs,norms,atoms,updates,auxdefs,annots) =
            let norm_lid = norm_lid t_id n i in
            let rec_lid = rec_lid t_id n i in
            let atom_lid = atom_lid t_id n i in
            let rec traverse_lambdas app abs lvl t =
              match kind_of_term t with
              | Lambda (_, _, c) ->
                  let app e =
                    <:expr< $app e$ $lid:lid_of_index (n+m+lvl)$ >>
                  in
                  let abs e =
                    abs <:expr< fun $lid:lid_of_index (n+m+lvl)$ -> $e$ >>
                  in
                  traverse_lambdas app abs (lvl+1) c
              | Case (ci, p, c, branches)
              when kind_of_term c = Rel (lvl-recargs.(i)) ->
                let u = (ci, p, c, branches) in
                let atom_app = app <:expr< mk_accu $lid:atom_lid$ >> in
                let tr_norm, auxdefs, annots, tr_rec =
                  translate_case auxdefs annots (n+m+lvl) u (Some atom_app)
                in
                let tr_rec = <:expr< let $list:mappings$ in $tr_rec$>> in
                  abs tr_rec, abs tr_norm, auxdefs, annots
              | _ ->
                  let atom_app = app <:expr< mk_accu $lid:atom_lid$ >> in
                  let norm_app = app <:expr< $lid:norm_lid$ $lid:rec_lid$>> in
                  let tr_norm, auxdefs, annots =
                    translate auxdefs annots (n+m+lvl) t
                  in
                  let tr_rec =
                    <:expr< if is_accu $lid:lid_of_index (n+m+recargs.(i))$ then
                      $atom_app$ else let $list:mappings$ in $tr_norm$ >>
                  in
                  abs tr_rec, abs tr_norm, auxdefs, annots
            in
            let tr_rec, tr_norm, auxdefs, annots =
              let id x = x in traverse_lambdas id id 0 bodies.(i)
            in
            let tr_norm = abs_over_bodies tr_norm in
            let norms = (<:patt< $lid:norm_lid$>>, tr_norm)::norms in
            let arg_str = string_of_int recargs.(i) in
            let name_expr =
              <:expr< str_decode $str:str_encode names.(i)$ >>
            in
            let tr_ty, auxdefs, annots = translate auxdefs annots n types.(i) in
            let atom =
              <:expr< dummy_atom_fix $lid:norm_lid$ $int:arg_str$
                $name_expr$ $tr_ty$ >> in
            let atoms = (<:patt< $lid:atom_lid$ >>, atom)::atoms in
            let upd = <:expr< upd_fix_atom $lid:atom_lid$ $lid:rec_lid$ >> in
            let updates = (<:patt< _ >>, upd)::updates in
            let recs = (<:patt< $lid:rec_lid$ >>, tr_rec)::recs in
            recs, norms, atoms, updates, auxdefs, annots
          in
          let recs,norms,atoms,updates,auxdefs,annots =
            Array.fold_right f (Array.init m (fun i -> i)) ([],[],[],[],auxdefs,annots)
          in
          if global then
            let atoms = <:str_item< value $list:atoms$ >> in
            let norms = <:str_item< value $list:norms$ >> in
            let updates = <:str_item< value $list:updates$ >> in
            let recs = <:str_item< value rec $list:recs$ >> in
            let e = <:expr< mk_fix_accu $lid:atom_lid t_id n i$ >> in
            e, updates::recs::atoms::norms::auxdefs, annots
          else
            let e = <:expr< $lid:lid_of_index (n+i)$ >> in
            let e = <:expr< let $list:updates$ in $e$ >> in
            let e = <:expr< let rec $list:recs$ in $e$ >> in
            let e = <:expr< let $lid:lid_of_index (n+i)$ =
              mk_fix_accu $lid:atom_lid t_id n i$ in $e$ >>
            in
            let e = <:expr< let $list:atoms$ in $e$ >> in
            <:expr< let $list:norms$ in $e$ >>, auxdefs, annots
      | CoFix(ln, (_, tl, bl)) ->
          <:expr< mk_rel_accu $int:"-1"$ >>, auxdefs, annots(* invalid_arg "translate"*)
      | NativeInt i -> 
          <:expr< mk_uint $int:Native.Uint31.to_string i$ >>, auxdefs, annots
      | NativeArr _ ->
          <:expr< mk_rel_accu $int:"-1"$ >>, auxdefs, annots(* invalid_arg "translate"*)
      | _ -> assert false
and translate_app auxdefs annots n c args =
  match kind_of_term c with
     | Construct cstr ->
	 let f arg (vs,auxdefs,annots) = 
           let v,auxdefs,annots = translate auxdefs annots n arg in
             (v :: vs),auxdefs,annots
         in
	 let i = index_of_constructor cstr in
	 let ind = inductive_of_constructor cstr in
     let mp' = ind_modpath ind in
	 let mb = lookup_mind (fst ind) env in
	 let ob = mb.mind_packets.(snd ind) in
	 let nparams = mb.mind_nparams in
	 let nargs = Array.length args in
         let vs,auxdefs,annots = Array.fold_right f args ([],auxdefs,annots) in
	 let vs = list_skipn (min nparams nargs) vs in
         let _,arity = ob.mind_reloc_tbl.(i-1) in
	 let missing = arity + nparams - nargs in
	 let underscores = max (nparams - nargs) 0 in
	 let names = gen_names n (missing - underscores) in
	 let pad = List.map (fun x -> <:expr< $lid:x$ >>) names in
	 let prefix =
	   let rec aux n z =
	     if n = 0
	     then z
	     else aux (n - 1) <:expr< fun _ -> $z$ >>
	   in
       let tr_constr,_ = construct_uid mp (mp',ob.mind_consnames.(i-1)) in
       let apps =
         List.fold_left (fun e x -> <:expr< $e$ $x$ >>) tr_constr (vs@pad)
       in
       aux underscores
       (List.fold_right (fun x e -> <:expr< fun $lid:x$ -> $e$ >>)
       names apps)
     in
     <:expr< (Obj.magic $prefix$ : Nativevalues.t) >>, auxdefs, annots
     | _ ->
         let zero = translate auxdefs annots n c in
         let f (apps,auxdefs,annots) x =
           let tr,auxdefs,annots = translate auxdefs annots n x in
           <:expr< $apps$ $tr$ >>, auxdefs, annots
         in
         Array.fold_left f zero args
  and translate_case auxdefs annots n (ci,p,c,branches) aux_neutral =
    let mb = lookup_mind (fst ci.ci_ind) env in
    let ob = mb.mind_packets.(snd ci.ci_ind) in
    let mp' = ind_modpath ci.ci_ind in
    let f i br (xs1,auxdefs,annots) =
      let args = gen_names n ci.ci_cstr_ndecls.(i) in
      let apps = List.fold_left (fun e arg -> <:expr< $e$ $lid:arg$ >>) in
      let pat1 = make_constructor_pattern mp mp' ob i args in
      let (tr,auxdefs,annots) = translate auxdefs annots n br in
      let body = apps tr args in
      ((pat1, None, body)::xs1,auxdefs,annots)
    in
    let (bodies,auxdefs,annots) =
      array_fold_right_i f branches ([],auxdefs,annots)
    in
    let annots,annot_i = NbeAnnotTbl.add (CaseAnnot ci) annots in
    let match_lid = match_lid t_id annot_i in
    let (p_tr, auxdefs, annots) = translate auxdefs annots n p in
    let tbl = dump_reloc_tbl ob.mind_reloc_tbl in
    let fv = free_vars_acc n [] p in
    let fv = Array.fold_left (free_vars_acc n) fv branches in
    let fv = List.map (fun i -> lid_of_index i) fv in 
    let match_app =
      List.fold_right (fun arg e -> <:expr< $e$ $lid:arg$ >>)
        fv <:expr< $lid:match_lid$ >>
    in
    let neutral_match =
      <:expr< mk_sw_accu (cast_accu c) $p_tr$ $match_app$ $tbl$
        (str_decode $str:str_encode ci$) >>
    in
    let ind_lid,ind_str = mind_lid mp (mp',ob.mind_typename) in
    let accu_id = id_of_string ind_str in
    let accu_expr,_ = construct_uid_patt ~accu:true mp (mp',accu_id) in
    let default = (<:patt< $accu_expr$ _ >>, None, neutral_match) in
    let (tr,auxdefs,annots) = translate auxdefs annots n c in
    let match_body =
      <:expr< match (Obj.magic c : $ind_lid$) with
      [$list:default::bodies$] >>
    in
    let match_body =
      List.fold_left (fun e arg -> <:expr< fun $lid:arg$ -> $e$ >>)
      match_body ("c"::fv)
    in
    let aux_body = match aux_neutral with
      | Some e ->
        let default = (<:patt< $accu_expr$ _ >>, None, e) in
        <:expr< match (Obj.magic $tr$ : $ind_lid$) with
          [$list:default::bodies$] >>
        (*List.fold_left (fun e arg -> <:expr< fun $lid:arg$ -> $e$ >>) r fv*)
      | None -> match_body
    in
    let auxdefs =
      <:str_item< value rec $lid:match_lid$ = $match_body$>>::auxdefs
    in
      <:expr< $match_app$ $tr$ >>, auxdefs, annots, aux_body

  in
  let tr,auxdefs,annots = translate ~global:true [] annots lift t in
    List.rev (<:str_item< value $lid:t_id$ = $tr$ >>::auxdefs), annots)

and compile_value mp env id body =
  let _,lid = var_lid id in
  let ast = fst (translate mp env lid body) in
  push_comp_stack ast

let opaque_const mp kn =
  let _,lid = const_lid mp kn in
  [<:str_item< value $lid:lid$ = mk_constant_accu
     (str_decode $str:str_encode kn$) >>]

(** Collect all variables and constants in the term. *)
(* TODO : vars in fix annotations ? *)
let assums mp env t =
  let rec aux xs t =
    match kind_of_term t with
      | Var id ->
          snd (var_lid id)::xs
      | Const c ->
          if in_same_library mp (con_modpath c) then
            snd (const_lid mp c)::xs
          else
            xs
      | Construct cstr ->
          let i = index_of_constructor cstr in
          let (mind,_) = inductive_of_constructor cstr in
          if in_same_library mp (mind_modpath mind) then
            string_of_mind mind :: xs
          else
            xs
      | Case (ci, pi, c, branches) ->
          let type_str = string_of_mind (fst ci.ci_ind) in
          if in_same_library mp (mind_modpath (fst ci.ci_ind)) then
            fold_constr aux (type_str::xs) t
          else
            fold_constr aux xs t
      | _ -> fold_constr aux xs t
  in aux [] t

let translate_mind mb =
  let rec build_const_sig acc n = match n with
  | 0 -> acc
  | _ -> build_const_sig (<:ctyp< Nativevalues.t >>::acc) (n-1)
  in
  let dummy_mp = MPfile (empty_dirpath) in
  let aux x n =
    let _,s = construct_uid dummy_mp (dummy_mp,x) in
    let const_sig = build_const_sig [] n in (loc,s,const_sig)
  in
  let f acc ob =
    let _,type_str = mind_lid dummy_mp (dummy_mp,ob.mind_typename) in
      let const_ids =
        Array.to_list (array_map2 aux ob.mind_consnames ob.mind_consnrealdecls)
      in
      let const_ids = (loc,"Accu_"^type_str,[<:ctyp< Nativevalues.t >>])::const_ids in
      <:str_item< type $lid:type_str$ = [ $list:const_ids$ ] >>::acc
  in
  Array.fold_left f [] mb.mind_packets

let compile_constant mp env kn ck =
  let ast = match ck.const_body with
    | Def cb ->
        let _,lid = const_lid mp kn in
        let cb = Declarations.force cb in
        fst (translate mp env lid cb)
    | _ ->
        let _,lid = const_lid mp kn in
        opaque_const mp kn
  in
  push_comp_stack ast 

let compile_mind mb  =
  let ast = translate_mind mb in
  push_comp_stack ast

let dump_rel_env mp env = 
  let aux (i,acc) (_,t,_) =
    let lid = lid_of_index (-i) in
    match t with
    | None -> (i+1,<:str_item< value $lid:lid$ = mk_rel_accu
                $int:string_of_int (-i)$ >>::acc)
    | Some body -> 
        let (tr, annots) = translate (~lift:-i) mp env lid body in
        (i+1,tr@acc)
  in
  snd (List.fold_left aux (1,[]) env.env_rel_context)

let native_constant mp kn f =
  match f with
    | Native.Oprim Native.Int31add ->
       let _,lid = const_lid mp kn in
       [<:str_item< value $lid:lid$ =
         let add_accu = mk_constant_accu (str_decode $str:str_encode kn$) in
          Nativevalues.add add_accu>>]
    | _ -> assert false

let translate_constant env mp l cb =
  let kn = make_con mp empty_dirpath l in
  let _,lid = const_lid mp kn in
  match cb.const_body with
  | Def t -> 
      let t = Declarations.force t in
      translate mp env lid t
  | Primitive f ->
      native_constant mp kn f, NbeAnnotTbl.empty
  | _ ->
      opaque_const mp kn, NbeAnnotTbl.empty

