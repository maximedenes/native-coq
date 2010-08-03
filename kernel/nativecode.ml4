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

let var_lid_of_id id = "var_"^string_of_id id
let mind_lid_of_id id = "mind_"^string_of_id id
let construct_lid_of_id id = "Construct_"^string_of_id id
let const_lid_of_id id = "const_"^string_of_id id

(* Redefine a bunch of functions in module Names to generate names
   acceptable to OCaml. *)
let string_of_dirpath = function
  | [] -> "_"
  | sl -> String.concat "_" (List.map string_of_id (List.rev sl))

let rec string_of_mp = function
  | MPfile sl -> string_of_dirpath (repr_dirpath sl)
  | MPbound uid -> string_of_mbid uid
  | MPdot (mp,l) -> string_of_mp mp ^ "." ^ string_of_label l

let string_of_kn kn =
  let (modpath, _dirpath, label) = repr_kn kn in
    string_of_mp modpath ^ "_" ^ string_of_label label

let mod_uid_of_dirpath dir = string_of_dirpath (repr_dirpath dir)

let lid_of_con con =
  "const_"^string_of_kn (user_con con)

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

(* First argument the index of the constructor *)
let make_constructor_pattern ob i args =
  let f = <:patt< $uid:construct_lid_of_id ob.mind_consnames.(i)$ >> in 
  List.fold_left (fun e arg -> <:patt< $e$ $lid:arg$ >>) f args

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
    <:expr< ($int:string_of_int tag$,$int:string_of_int arity$) >>
  in
  <:expr< [| $list:Array.to_list (Array.map f tbl)$ |] >>

let rec push_value id body env =
  let kind = lookup_named_val id env in
    match !kind with
      | VKvalue (v, _) -> ()
      | VKnone ->
         let (tr, annots) = translate env (var_lid_of_id id) body in
	 let v,d = (values tr, Idset.empty) (* TODO : compute actual idset *)
         in kind := VKvalue (v,d)

(** The side-effect of translate is to add the translated construction
    to the value environment. *)
(* A simple counter is used for fresh variables. We effectively encode
   de Bruijn indices as de Bruijn levels. *)
and translate ?(annots=NbeAnnotTbl.empty) env t_id t =
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
	            let v = <:expr< $lid:var_lid_of_id id$ >> in
                      push_value id body env; v, auxdefs, annots
          end
      | Sort s -> (* TODO: check universe constraints *)
          let annots,i = NbeAnnotTbl.add (SortAnnot s) annots in
          let e = <:expr< mk_sort_accu ($str:t_id$,$int:string_of_int i$) >> in
          e, auxdefs, annots
      | Cast (c, _, ty) -> translate auxdefs annots n c
      | Prod (_, t, c) ->
          let vt,auxdefs,annots = translate auxdefs annots n t in
          let vc,auxdefs,annots = translate auxdefs annots (n + 1) c in
          let e = <:expr< mk_prod_accu $vt$ (fun $lid:lid_of_index n$ -> $vc$) >> in
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
          <:expr< $lid:lid_of_con c$ >>, auxdefs, annots
      | Ind c ->
          <:expr< mk_id_accu $str:string_of_mind (fst c)$ >>, auxdefs, annots (* xxx *)
      | Construct cstr ->
	  let i = index_of_constructor cstr in
	  let ind = inductive_of_constructor cstr in
	  let mb = lookup_mind (fst ind) env in
	  let ob = mb.mind_packets.(snd ind) in
	  let nparams = mb.mind_nparams in
          let _,arity = ob.mind_reloc_tbl.(i-1) in
          if nparams+arity = 0 then
            let cons_str = construct_lid_of_id ob.mind_consnames.(i-1) in
	    let e = <:expr< (Obj.magic $uid:cons_str$ : Nativevalues.t) >> in
              e, auxdefs, annots
          else translate_app auxdefs annots n t [||]
      | Case (ci, p, c, branches) ->
          let u = (ci, p, c, branches) in
          let ast, auxdefs, annots, _ = translate_case auxdefs annots n u None in
            ast, auxdefs, annots
      | Fix ((recargs, i), (_, _, bodies)) -> (* TODO : compile mutual fixpoints *)
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
                  let tr_rec =
                    <:expr< if is_accu $lid:lid_of_index (n+m)$ then
                      $atom_app$ else $norm_app$ >>
                  in
                  let tr_norm, auxdefs, annots =
                    translate auxdefs annots (n+m+lvl) t
                  in
                  abs tr_rec, abs tr_norm, auxdefs, annots
            in
            let tr_rec, tr_norm, auxdefs, annots =
              let id x = x in traverse_lambdas id id 0 bodies.(i)
            in
            let tr_norm = abs_over_bodies tr_norm in
            let norms = (<:patt< $lid:norm_lid$>>, tr_norm)::norms in
            let arg_str = string_of_int recargs.(i) in
            let atom = <:expr< dummy_atom_fix $lid:norm_lid$ $int:arg_str$>> in
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
          <:expr< mk_id_accu $str:"cofix"$ >>, auxdefs, annots(* invalid_arg "translate"*)
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
           let tr_constr =
             <:expr< $uid:construct_lid_of_id ob.mind_consnames.(i-1)$ >>
           in
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
	  let f i br (xs1,auxdefs,annots) =
	    let args = gen_names n ci.ci_cstr_nargs.(i) in
            let apps = List.fold_left (fun e arg -> <:expr< $e$ $lid:arg$ >>) in
	    let pat1 = make_constructor_pattern ob i args in
            let (tr,auxdefs,annots) = translate auxdefs annots n br in
            let body = apps tr args in
                ((pat1, None, body)::xs1,auxdefs,annots)
          in
          let annots,annot_i = NbeAnnotTbl.add (CaseAnnot ci) annots in
          let (bodies,auxdefs,annots) =
            array_fold_right_i f branches ([],auxdefs,annots)
          in
          let match_lid = match_lid t_id annot_i in
          let (p_tr, auxdefs, annots) = translate auxdefs annots n p in
          let tbl = dump_reloc_tbl ob.mind_reloc_tbl in
          let annot =
            <:expr< ($str:t_id$,$int:string_of_int annot_i$,$tbl$) >>
          in
          let neutral_match =
            <:expr< mk_sw_accu (cast_accu c) $p_tr$ $lid:match_lid$ $annot$ >>
          in
          let ind_str = mind_lid_of_id ob.mind_typename in
          let accu_str = "Accu"^ind_str in
          let default = (<:patt< $uid:accu_str $ _ >>, None, neutral_match) in
          let (tr,auxdefs,annots) = translate auxdefs annots n c in
          let fv = free_vars_acc n [] p in
          let fv = Array.fold_left (free_vars_acc n) fv branches in
          let fv = List.map (fun i -> lid_of_index i) fv in 
          let match_body =
            <:expr< match (Obj.magic c : $lid:ind_str$) with
                      [$list:default::bodies$] >>
          in
          let match_body =
            List.fold_left (fun e arg -> <:expr< fun $lid:arg$ -> $e$ >>)
              match_body ("c"::fv)
          in
          let aux_body = match aux_neutral with
            | Some e ->
                let default = (<:patt< $uid:accu_str $ _ >>, None, e) in
                <:expr< match (Obj.magic $tr$ : $lid:ind_str$) with
                          [$list:default::bodies$] >>
                (*List.fold_left (fun e arg -> <:expr< fun $lid:arg$ -> $e$ >>) r fv*)
            | None -> match_body
          in
          let auxdefs =
            <:str_item< value rec $lid:match_lid$ = $match_body$>>::auxdefs
          in
          let match_app =
            List.fold_right (fun arg e -> <:expr< $e$ $lid:arg$ >>)
              fv <:expr< $lid:match_lid$ >>
          in
          <:expr< $match_app$ $tr$ >>, auxdefs, annots, aux_body

  in
  let tr,auxdefs,annots = translate ~global:true [] annots 0 t in
    List.rev (<:str_item< value $lid:t_id$ = $tr$ >>::auxdefs), annots)

let opaque_const kn =
  [<:str_item< value $lid:lid_of_con kn$ = mk_id_accu $str:lid_of_con kn$ >>]

(** Collect all variables and constants in the term. *)
let assums env t =
  let rec aux xs t =
    match kind_of_term t with
      | Var id -> var_lid_of_id id :: xs
      | Const c -> lid_of_con c :: xs
      | Construct cstr ->
          let i = index_of_constructor cstr in
	  let (mind,_) = inductive_of_constructor cstr in
          string_of_mind mind :: xs
      | Case (ci, pi, c, branches) ->
          let type_str = string_of_mind (fst ci.ci_ind) in
          fold_constr aux (type_str::xs) t
      | _ -> fold_constr aux xs t
  in aux [] t

let translate_mind mb =
  let rec build_const_sig acc n = match n with
  | 0 -> acc
  | _ -> build_const_sig (<:ctyp< Nativevalues.t >>::acc) (n-1)
  in
  let aux x n =
    let const_sig = build_const_sig [] n in (loc,construct_lid_of_id x,const_sig)
  in
  let f acc ob =
    let type_str = mind_lid_of_id ob.mind_typename in
      let const_ids =
        Array.to_list (array_map2 aux ob.mind_consnames ob.mind_consnrealdecls)
      in
      let const_ids = (loc,"Accu"^type_str,[<:ctyp< Nativevalues.t >>])::const_ids in
      <:str_item< type $lid:type_str$ = [ $list:const_ids$ ] >>::acc
  in
  Array.fold_left f [] mb.mind_packets

(* Code dumping functions *)
let add_value env (id, value) xs =
  match !value with
    | VKvalue (v, _) ->
	let sid = var_lid_of_id id in
        let ast = expr_of_values v in
        let (_, b, _) = Sign.lookup_named id env.env_named_context in
	let deps = (match b with
          | None -> [] 
	  | Some body -> let res = assums env body in
             (*print_endline (sid^"(named_val) assums "^String.concat "," res);*)
              res)
        in Stringmap.add sid (VarKey id, NbeAnnotTbl.empty, ast, deps) xs
    | VKnone -> xs

let add_constant c ck xs =
  match (fst ck).const_body_ast with
    | Some v ->
	let sc = lid_of_con c in
        let ast = expr_of_values v in
	let deps = match (fst ck).const_body_deps with
	  | Some l -> (*print_endline (sc^" assums "^String.concat "," l);*) l 
	  | None -> []
        in
	let annots = match (fst ck).const_body_annots with
          | Some t -> t
          | None -> NbeAnnotTbl.empty
        in
	Stringmap.add sc (ConstKey c, annots, ast, deps) xs
    | None ->
        ((*print_endline ("Const body AST not found: "^lid_of_con c);*) xs)

let add_ind env c ind xs =
  let mb = lookup_mind c env in
  let ast = translate_mind mb in
  Stringmap.add (string_of_mind c) (IndKey (c,0), NbeAnnotTbl.empty, ast, []) xs

let dump_env terms env =
  let vars =
    List.fold_right (add_value env) env.env_named_vals Stringmap.empty
  in
  let vars_and_cons =
    Cmap_env.fold add_constant env.env_globals.env_constants vars
  in
  let vars_cons_ind =
    Mindmap_env.fold (add_ind env) env.env_globals.env_inductives vars_and_cons
  in
  let initial_set =
    List.fold_left (fun acc t -> assums env t @ acc) [] terms
  in
  print_endline (String.concat "," initial_set);
  let header =
    [<:str_item< open Nativelib >>;
     <:str_item< open Nativevalues >>]
  in
  let (l,kns) = topological_sort initial_set vars_cons_ind in
    (header @ l,kns)
