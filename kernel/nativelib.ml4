(*i camlp4use: "q_MLast.cmo" i*)

open Names
open Term
open Util
open Nativevalues

(* Required to make camlp5 happy. *)
let loc = Ploc.dummy

(* Global settings and utilies for interface with OCaml *)
let env_name = "Coq_conv_env"
let terms_name = "Coq_conv_terms"

let include_dirs =
  "-I "^Coq_config.camllib^"/camlp5 -I "^Coq_config.coqlib^"/config -I "
  ^Coq_config.coqlib^"/lib -I "^Coq_config.coqlib^"/kernel "

let include_libs =
  "camlp5.cmxa coq_config.cmx lib.cmxa kernel.cmxa "

let ocaml_version = "3.11.1"
let ast_impl_magic_number = "Caml1999M012"
let ast_intf_magic_number = "Caml1999N011"

let print_implem fname ast =
  let pt = Ast2pt.implem fname (List.map fst ast) in
  let oc = open_out_bin fname in
  output_string oc ast_impl_magic_number;
  output_value oc fname;
  output_value oc pt;
  close_out oc

let compute_loc xs =
  let rec f n = function
    | [] -> []
    | str_item :: xs -> (str_item, Ploc.make n 0 (0, 0)) :: f (n + 1) xs
  in f 0 xs

let compile_module ast imports load_paths f =
  let code = List.flatten (List.map expr_of_values ast) in
  (* let imports = List.map (fun id -> <:str_item< open $mod_ident:id$ >>) imports in *)
  print_endline ("Imports: "^(String.concat "," imports));
  let imports = List.map (fun id -> <:str_item< open $list:[id]$ >>) imports in
  let code =
    [<:str_item< open Nativelib >>; <:str_item< open Nativevalues >>]
     @ imports @ code
  in
  let code = compute_loc code in
    Pcaml.input_file := "/dev/null";
    Pcaml.output_file := Some f;
    Pcaml.inter_phrases := Some "\n";
    !Pcaml.print_implem code;
    (*print_implem f code;*)
  let imports = "-I " ^ (String.concat " -I " load_paths) ^ " " in
  let comp_cmd =
    "ocamlopt.opt -c -rectypes "^include_dirs^imports^include_libs^f
  in
  Sys.command comp_cmd


let call_compiler env_code terms_code =
  if Sys.file_exists (env_name^".ml") then
    anomaly (env_name ^".ml already exists");
  if Sys.file_exists (terms_name^".ml") then
    anomaly (terms_name ^".ml already exists");
  let terms_code =
    [<:str_item< open Nativelib >>;
     <:str_item< open Nativevalues >>;
     <:str_item< open $list: [env_name]$ >>] @ terms_code
  in
  Pcaml.input_file := "/dev/null";
  Pcaml.output_file := Some "envpr.ml";
  Pcaml.inter_phrases := Some "\n";
  !Pcaml.print_implem (compute_loc env_code);
  Pcaml.output_file := Some "termspr.ml";
  !Pcaml.print_implem (compute_loc terms_code);
  print_implem (env_name^".ml") (compute_loc env_code);
  print_implem (terms_name^".ml") (compute_loc terms_code);
  let file_names = env_name^".ml "^terms_name^".ml" in
  let _ = Sys.command ("touch "^env_name^".ml") in
  print_endline "Compilation...";
  let comp_cmd =
    "ocamlopt.opt -rectypes "^include_dirs^include_libs^file_names
  in
  let res = Sys.command comp_cmd in
  let _ = Sys.command ("rm "^file_names) in
    res

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
	  (x @ l, kns)
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


type tag = int

type lam = 
  | Lam of lam
  | Rel of int
  | Id of string
  | Var of identifier
  | App of lam * lam array
  | Const_int of int
  | Const_block of int * lam array
  | Case of string * int * lam * lam * lam array
  | Prod of lam * lam
  | Fix of int * lam 

let pp_var fmt x =
  Format.fprintf fmt "v%i" x

(*let rec pp_lam fmt l n =
 match l with 
 | Lam l ->
     Format.fprintf fmt "@[(fun %a => @\n @[%a@])@]"
       pp_var n pp_lam l
 | Var x -> 
     pp_var fmt x
 | App (f, args) ->
     Format.fprintf fmt "@[(%a %a)@]" 
       pp_lam f (pp_args " ") (Array.to_list args)
 | Const_int i -> 
     Format.fprintf fmt "#%i" i
 | Const_block(i,args) ->
     Format.fprintf fmt "@[[%i: %a]@]" i (pp_args "; ") (Array.to_list args)
 | Case(l,b) -> 
     Format.fprintf fmt "@[case %a of@\n%aend@]"
       pp_lam l pp_branches (Array.to_list b)
 | Fix (x,l) ->
     Format.fprintf fmt "@[(fix %a =@\n @[%a@])@]"
       pp_var x pp_lam l

and pp_args s fmt args =
  match args with
  | [] -> ()
  | [a] -> pp_lam fmt a
  | a::args -> Format.fprintf fmt "%a%s%a" pp_lam a s (pp_args s) args

and pp_branches fmt bs =
  match bs with
  | [] -> ()
  | (tag,ids,l)::bs -> 
      Format.fprintf fmt "@[| %a =>@\n  @[%a@]@]@\n%a"
	pp_branch_head (tag,ids) pp_lam l pp_branches bs

and pp_branch_head fmt (tag,ids) =
  let l = 
    if Array.length ids = 0 then (Const_int tag)
    else Const_block(tag, Array.map (fun v -> Var v) ids) in
  pp_lam fmt l*)

let mkApp f args =
  if Array.length args = 0 then f
  else App(f,args)

let mk_block lvl tag arity =
  let ids = Array.init arity (fun i -> lvl + i) in
  ids,Nativevalues.mk_block tag (Array.map mk_rel_accu ids)

let rec norm_val lvl v =
  match Nativevalues.kind_of_value v with
  | Vaccu k ->
      norm_accu lvl k
  | Vfun f ->
      let arg = Nativevalues.mk_rel_accu lvl in
      Lam (norm_val (lvl+1) (f arg))
  | Vconst n -> 
      Const_int n
  | Vblock b ->
      let tag = Nativevalues.block_tag b in
      let nargs = Nativevalues.block_size b in
      let args =
	Array.init nargs (fun i -> norm_val lvl (Nativevalues.block_field b i)) in
      Const_block(tag,args)

and norm_accu lvl k =
  let a = Nativevalues.atom_of_accu k in
  let nargs = Nativevalues.accu_nargs k in
  let args = 
    Array.init nargs (fun i -> norm_val lvl (Nativevalues.arg_of_accu k i)) in
  mkApp (norm_atom lvl a) args

and norm_atom lvl a =
  match a with
  | Arel i ->
      Rel i
  | Aid s ->
      Id s
  | Avar id ->
      Var id
  | Acase (c,p,ac,(s,i,tbl)) ->
      let lc = norm_accu lvl c in
      let lp = norm_val lvl p in
      let lac = Array.map (norm_branch lvl ac) tbl in
      Case(s,i,lp,lc,lac)
  | Aprod (dom,codom) ->
      let rel = mk_rel_accu lvl in
      Prod(norm_val lvl dom, norm_val (lvl+1) (codom rel))
  | Afix(_,f,_) ->
      let fr = mk_rel_accu lvl in
      Fix(lvl, norm_val (lvl+1) (f fr))

and norm_branch lvl f (tag,arity) =
  match arity with
  | 0 ->
      norm_val lvl (f (Nativevalues.mk_const tag))
  | _ ->
      let _, v = mk_block lvl tag arity in
      norm_val (lvl + arity) (f v)

let lazy_norm lv =
  let v = Lazy.force lv in
  norm_val 0 v

let print_nf c = Marshal.to_channel stdout (lazy_norm c) []

