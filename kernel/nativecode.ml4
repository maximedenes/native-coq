(*i camlp4use: "q_MLast.cmo" i*)

open Names
open Nativelib
open Term
open Pre_env
open Pcaml
open Declarations
open Util

exception NotConvertible

(*  *)
let ast_impl_magic_number = "Caml1999M012"
let ast_intf_magic_number = "Caml1999N011"

(** One of the optimizations performed on the target code is
    uncurrying, meaning collapsing functions into n-ary functions and
    introducing a family of application operators that apply an n-ary
    function to m arguments in one go. This constant defines the
    maximum arity of functions, hence bounding the number of
    application operators required.

    BEWARE: changing the value of this constant requires changing
    nbe.ml accordingly to have at least as many abstraction
    constructors and application operators. *)

let max_arity = 6

let uniq = ref 256

(* Required to make camlp5 happy. *)
let loc = Ploc.dummy

(* Flag to signal whether recompilation is needed. *)

(* Required to make camlp5 happy. *)
let loc = Ploc.dummy

(* Flag to signal whether recompilation is needed. *)
let env_updated = ref false

(* Bringert and Ranta's 'descend' operator for OCaml representations
   of the target code. *)
let descend_ast f t = match t with
  | <:expr< Con $_$ >> -> t
  | <:expr< Var $_$ >> -> t
  | <:expr< Rel $_$ >> -> t
  | <:expr< Lam1 (fun $x$ -> $body$) >> -> <:expr< Lam1 (fun $x$ -> $f body$) >>
  | <:expr< Prod ($dom$,(fun $lid:x$ -> $cod$)) >> -> <:expr< Prod ($f dom$,(fun $lid:x$ -> $f cod$)) >>
  | <:expr< app $t1$ $t2$ >> -> <:expr< app $f t1$ $f t2$ >>
  | <:expr< App $_$ >> -> t 
  | <:expr< Const ($i$,[| $list:args$ |]) >> ->
      <:expr< Const ($i$,[| $list:List.fold_right (fun t ts -> f t :: ts) args []$ |]) >>
  | <:expr< Set >> -> t
  | <:expr< Prop >> -> t
  | <:expr< Type $_$ >> -> t
  | <:expr< Match $_$ >> -> t
  | <:expr< $lid:x$ >> -> t
  | <:expr< match $scrutinee$ with [ $list:branches$ ] >> ->
      let bs = List.fold_right (fun (p, w, body) bs -> (p, w, f body) :: bs) branches [] in
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

let rec pop_abstractions n =
  if n > 0 then function
    | <:expr< Lam1 (fun $x$ -> $t$) >> ->
      let vars, body = pop_abstractions (n - 1) t in
	(x :: vars, body)
    | t -> ([], t)
  else function t -> ([], t)

let rec pop_applications n t =
  let rec aux n args =
    if n > 0 then function
      | <:expr< app $t1$ $t2$ >> ->
	aux (n - 1) (t2 :: args) t1
      | f -> (f, args)
    else function f -> (f, args)
  in aux n [] t

let push_applications f args =
  let n = List.length args in
    List.fold_left (fun e arg -> <:expr< $e$ $arg$ >>)
      <:expr< $lid:"app" ^ string_of_int n$ $f$ >> args

let rec collapse_abstractions t =
  let vars, body = pop_abstractions max_arity t in
    if List.length vars = 0 then uncurrify body else
      let func =
	List.fold_right (fun x t -> <:expr< fun $x$ -> $t$ >>)
	  vars (collapse_abstractions body)
      in <:expr< $uid:"Lam" ^ string_of_int (List.length vars)$ $func$ >>

and collapse_applications t =
  let f, args = pop_applications max_arity t in
  let f, args = uncurrify f, List.map uncurrify args in
    push_applications f args

(* Uncurrification optimization. This consists in replacing

   Lam1 (fun x1 => ... (Lam1 (fun xn => ...)

   with

   Lam_n (fun x1 xn => ...)

   and replacing unary applications with n-ary applications where possible.

*)
and uncurrify t = match t with
  | <:expr< Lam1 $_$ >> -> collapse_abstractions t
  | <:expr< app $_$ $_$ >> -> collapse_applications t
  | _ -> descend_ast uncurrify t

let lid_of_string s = "x" ^ s
let uid_of_string s = "X" ^ s

let lid_of_name = function
  | Name id -> lid_of_string (string_of_id id)
  | Anonymous -> "_"

(* Redefine a bunch of functions in module Names to generate names
   acceptable to OCaml. *)
let string_of_dirpath = function
  | [] -> "_"
  | sl -> String.concat "_" (List.map string_of_id (List.rev sl))

let rec string_of_mp = function
  | MPfile sl -> string_of_dirpath (repr_dirpath sl)
  | MPbound uid -> string_of_mbid uid
  | MPdot (mp,l) -> string_of_mp mp ^ "." ^ string_of_label l

(*let string_of_kn kn =
  let (modpath, _dirpath, label) = repr_kn kn in
    string_of_mp modpath ^ "_" ^ string_of_label label*)

let string_of_con con =
  string_of_kn (canonical_con con)

let string_of_inductive (mind, i) =
  string_of_mind mind ^ string_of_int i

let string_of_constructor (ind, i) =
  string_of_inductive ind ^ "c" ^ string_of_int i

(* First argument the index of the constructor *)
let make_constructor_pattern i args =
  let f arg = <:patt< $lid:arg$ >> in
    <:patt< Const ($int:string_of_int i$,[| $list:List.map f args$ |]) >>

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

let rec patch_fix l n =
  if n > 0 then function
    | <:expr< Lam1 (fun $x$ -> $t$) >> ->
          <:expr< Lam1 (fun $x$ -> $patch_fix l (n-1) t$) >>
    | _ -> invalid_arg "translate.patch_fix"
  else
  function
    | <:expr< Lam1 (fun $lid:x$ -> $t$) >> ->
      let mk_patt x = <:patt< $lid:x$>> in
      let mk_expr x = <:expr< $lid:x$>> in
      let mk_eta_expr x = <:expr< Lam1 (fun x -> App [Rel 0;x])>> in
      let const_branch =
        (<:patt< Const _ >>, None, <:expr< ($list:(List.map mk_expr l)$) >>)
      in
      (* TODO : ensure Var below is fresh *)
      let default =
        (<:patt< _ >>, None, <:expr< ($list:List.map mk_eta_expr l$) >>)
      in
      let capture =
        let match_body = <:expr< match $lid:x$ with [$list:[const_branch;default]$] >> in
        <:expr< let ($list:List.map mk_patt l$) = $match_body$  in $t$ >>
      in
        <:expr< Lam1 (fun $lid:x$ -> $capture$) >>
    | _ -> invalid_arg "translate.patch_fix.2"


let rec push_value id body env =
  env_updated := true;
  let kind = lookup_named_val id env in
    match !kind with
      | VKvalue (v, _) -> ()
      | VKnone ->
         let (tr, annots) = translate env (VarKey id) body in
	 let v,d = (values tr, Idset.empty) (* TODO : compute actual idset *)
         in kind := VKvalue (v,d)

(** The side-effect of translate is to add the translated construction
    to the value environment. *)
(* A simple counter is used for fresh variables. We effectively encode
   de Bruijn indices as de Bruijn levels. *)
and translate env ik t =
  (let rec translate annots n t =
    match kind_of_term t with
      | Rel x -> <:expr< $lid:lid_of_index (n-x)$ >>, annots
      | Var id ->
	  (let v = <:expr< $lid:lid_of_string (string_of_id id)$ >> in
          let (_, b, _) = Sign.lookup_named id env.env_named_context in
	      match b with
		| None ->
                    <:expr< Var (Names.id_of_string $str:string_of_id id$) >>, annots
		| Some body -> push_value id body env; v, annots)
      | Sort (Prop Null) -> <:expr< Prop >>, annots
      | Sort (Prop Pos) -> <:expr< Set >>, annots
      | Sort (Type _) -> <:expr< Type 0 >>, annots (* xxx: check universe constraints *)
      | Cast (c, _, ty) -> translate annots n c
      | Prod (_, t, c) ->
          let vt,annots = translate annots n t in
          let vc,annots = translate annots (n + 1) c in
            <:expr< Prod ($vt$,(fun $lid:lid_of_index n$ -> $vc$)) >>, annots
      | Lambda (_, t, c) ->
          let v,annots = translate annots (n + 1) c in
	  <:expr< Lam1 (fun $lid:lid_of_index n$ -> $v$) >>, annots
      | LetIn (_, b, t, c) ->
          let vb,annots = translate annots n b in
          let vc,annots = translate annots (n + 1) c in
	  <:expr< let $lid:lid_of_index n$ = $vb$ in $vc$ >>, annots
      | App (c, args) ->
          translate_app annots n c args
      | Const c -> <:expr< $lid:lid_of_string (string_of_con c)$ >>, annots
      | Ind c -> <:expr< Con $str:string_of_inductive c$ >>, annots (* xxx *)
      | Construct cstr ->
	  let i = index_of_constructor cstr in
	  let ind = inductive_of_constructor cstr in
	  let mb = lookup_mind (fst ind) env in
	  let ob = mb.mind_packets.(snd ind) in
	  let nparams = mb.mind_nparams in
          let _,arity = ob.mind_reloc_tbl.(i-1) in
          if nparams+arity = 0 then
	    <:expr< Const ($int:string_of_int i$,[||]) >>, annots
          else translate_app annots n t [||]
      | Case (ci, pi, c, branches) ->
	  let f i br (xs1,xs2,xs3,annots) =
            let b = code_lid_of_index (i+1) in
	    let args = gen_names n ci.ci_cstr_ndecls.(i) in
            let rels = gen_rels n  ci.ci_cstr_ndecls.(i) in
    	    let caml_apps = List.fold_left (fun e arg -> <:expr< $e$ $lid:arg$ >>) in
    	    let caml_apps_var = List.fold_left (fun e var -> <:expr< $e$ $var$ >>) in
            let apps = List.fold_left (fun e arg -> <:expr< app $e$ $lid:arg$ >>) in
       	    let abs = List.fold_right (fun arg e -> <:expr< fun $lid:arg$ -> $e$ >>) in
	    let pat1 = make_constructor_pattern (i + 1) args in
            let pat2 = <:patt< $lid:b$ >> in
            let (tr,annots) = translate annots n br in
            let body = abs args (apps tr args) in
	      ((pat1, None, caml_apps <:expr< $lid:b$ >> args)::xs1,
                (pat2,body)::xs2, caml_apps_var <:expr< $lid:b$ >> rels :: xs3,
                 annots)
          in
          let annots,annot_i = NbeAnnotTbl.add (CaseAnnot ci) annots in
          let (vs,bodies,neutrals,annots) =
            array_fold_right_i f branches ([],[],[],annots)
          in
          let annot_i_str = string_of_int annot_i in
          let annot_ik = string_of_id_key ik in
          let (pi_tr, annots) = translate annots n pi in
          let neutral_match =
            <:expr< Match ($str:annot_ik$, $int:annot_i_str$, $pi_tr$, $lid:code_lid_of_index 0$, [| $list:neutrals$ |]) >> in
          let default = (<:patt< x >>, None, neutral_match) in
          let match_body =
            <:expr< match $lid:code_lid_of_index 0$ with [$list:vs@[default]$] >>
          in
          let (tr,annots) = translate annots n c in
          let letdefs = (<:patt< $lid:code_lid_of_index 0$ >>, tr)::bodies in
          <:expr< let $list:letdefs$ in $match_body$ >>, annots
      | Fix ((recargs, i), (_, _, bodies)) ->
	  let m = Array.length bodies in
	  let f i  =
              let (trans,annots) = translate annots (n + m) bodies.(i) in
              let fix_lid = lid_of_index (n + i) in
              let lids = (gen_names n m) in
	      (<:patt< $lid:fix_lid$ >>, patch_fix lids recargs.(i) trans)
	  in let functions = Array.to_list (Array.init m f)
	  in <:expr< let rec $list:functions$ in $lid:lid_of_index (n + i)$ >>, annots
      | CoFix(ln, (_, tl, bl)) -> <:expr< Con $str:"cofix"$ >>, annots(* invalid_arg "translate"*)
      | _ -> <:expr< Con $str:"other"$ >>, annots(* invalid_arg "translate"*)
and translate_app annots n c args =
  match kind_of_term c with
     | Construct cstr ->
	 let f arg (vs,annots) = 
           let v,annots = translate annots n arg in (v :: vs),annots
         in
	 let i = index_of_constructor cstr in
	 let ind = inductive_of_constructor cstr in
	 let mb = lookup_mind (fst ind) env in
	 let ob = mb.mind_packets.(snd ind) in
	 let nparams = mb.mind_nparams in
	 let nargs = Array.length args in
         let vs,annots = Array.fold_right f args ([],annots) in
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
	     else aux (n - 1) <:expr< Lam1 (fun _ -> $z$) >>
	   in aux underscores
		(List.fold_right (fun x e -> <:expr< Lam1 (fun $lid:x$ -> $e$) >>)
		 names <:expr< Const ($int:string_of_int i$,[| $list: vs @ pad$ |]) >>
		 )
	 in assert (List.length vs + List.length pad = ob.mind_consnrealdecls.(i-1)); prefix, annots
     | _ ->
	 let zero = translate annots n c in
	 let f (apps,annots) x =
           let tr,annots = translate annots n x in
             <:expr< app $apps$ $tr$ >>, annots
         in
	   Array.fold_left f zero args
  in
  let tr,annots = translate NbeAnnotTbl.empty 0 t in
    uncurrify tr, annots)

let opaque_const kn =
  <:expr< Con $str:string_of_con kn$ >>

(** Collect all variables and constants in the term. *)
let assums t =
  let rec aux xs t =
    match kind_of_term t with
      | Var id -> string_of_id id :: xs
      | Const c -> string_of_con c :: xs
      | _ -> fold_constr aux xs t
  in aux [] t

