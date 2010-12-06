open Names
open Term
open Util
open Nativevalues
open Declarations
open Nativecode

exception NotConvertible

let load_paths = ref ([] : string list)
let imports = ref ([] : string list)

let open_header = ref ([] : mllambda list)
let comp_stack = ref ([] : mllambda list)

(* Global settings and utilies for interface with OCaml *)
let env_name = "Coq_conv_env"

let include_dirs =
  "-I "^Coq_config.camllib^"/camlp5 -I "^Coq_config.coqlib^"/config -I "
  ^Coq_config.coqlib^"/lib -I "^Coq_config.coqlib^"/kernel "
  ^"-I "^Filename.temp_dir_name^" "

let include_libs =
  "camlp5.cmxa coq_config.cmx lib.cmxa kernel.cmxa "

let compile_module code mp load_paths f =
  let header = mk_opens ["Nativevalues";"Nativecode";"Nativeconv"] in
(*  let code =
    [<:str_item< open Nativelib >>; <:str_item< open Nativevalues >>;
     <:str_item< open Names >>]
    @ code
  in*)
  let ch_out = open_out (f^".ml") in
  let fmt = Format.formatter_of_out_channel ch_out in
  pp_globals mp fmt (header@code);
  let load_paths = "-I " ^ (String.concat " -I " load_paths) ^ " " in
  close_out ch_out;
  let comp_cmd =
    "ocamlopt.opt -shared -o "^f^".cmxs -rectypes "^include_dirs^load_paths^f^".ml"
  in
  print_endline "Compiling module...";
  let res = Sys.command comp_cmd in print_endline "Compiled"; res

let push_comp_stack e =
  comp_stack := !comp_stack@e

let emit_comp_stack () =
  let res = !comp_stack in
  comp_stack := []; res

let compile_terms base_mp terms_code =
  let ast = emit_comp_stack () in
(*  let terms_code =
    [<:str_item< open Nativelib >>;
     <:str_item< open Nativevalues >>;
     <:str_item< open Names >>] @ (List.rev !open_header) @ ast @ terms_code
  in*)
  let mod_name = Filename.temp_file "Coq_native" ".ml" in
  let ch_out = open_out mod_name in
  let fmt = Format.formatter_of_out_channel ch_out in
  pp_globals base_mp fmt terms_code;
  close_out ch_out;
  print_endline "Compilation...";
  let include_dirs =
    include_dirs^"-I " ^ (String.concat " -I " !load_paths) ^ " "
  in
  let filename = Filename.temp_file "coq_native" ".cmxs" in
  let comp_cmd =
    "ocamlopt.opt -shared -o "^filename^" -rectypes "^include_dirs^mod_name
  in
  let res = Sys.command comp_cmd in
  let mod_name = Filename.chop_extension (Filename.basename mod_name) in
    res, filename, mod_name

let call_linker f mod_name =
  (try Dynlink.loadfile f
  with Dynlink.Error e -> print_endline (Dynlink.error_message e)); ()
  (* open_header := <:str_item< open $list:[mod_name]$ >>::!open_header *)

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
	  ((List.rev x) @ l, kns)
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
  | Constant of constant
  | Ind of inductive
  | Sort of sorts
  | Var of identifier
  | App of lam * lam array
  | Const_int of int
  | Const_block of int * lam array
  | Case of annot_sw *lam * lam * lam array 
  | Prod of name * lam * lam
  | Fix of (*name *) lam array * lam array * rec_pos * int
  | Array of lam array

let rnorm = ref (Rel (-1))
let rt1 = ref (mk_accu dummy_atom)
let rt2 = ref (mk_accu dummy_atom)

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

let rec push_abstractions n t =
  if n = 0 then t else Lam (push_abstractions (n-1) t)

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
  | Varray t ->
      let len = Native.Parray.length t in
      let def = norm_val lvl (Native.Parray.default t) in
      let lt = Array.make (Native.Uint31.to_int len + 1) def in 
      for i = 0 to Native.Uint31.to_int len - 1 do
        lt.(i) <- norm_val lvl (Native.Parray.get t (Native.Uint31.of_int i))
      done;
      Array lt
      

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
  | Aconstant c ->
      Constant c
  | Aind ind ->
      Ind ind
  | Asort s ->
      Sort s
  | Avar id ->
      Var id
  | Acase (annot,c,p,ac) ->
      let lc = norm_accu lvl c in
      let lp = norm_val lvl p in
      let lac = Array.map (norm_branch lvl ac) annot.asw_reloc in
      Case(annot,lp,lc,lac)
  | Aprod (x,dom,codom) ->
      let rel = mk_rel_accu lvl in
      Prod(x, norm_val lvl dom, norm_val (lvl+1) (codom rel))
  | Afix(types,bodies,rec_pos,pos) ->
      let types = Array.map (norm_val lvl) types in
      let bodies = Array.map (norm_val lvl) bodies in
      Fix (types,bodies,rec_pos, pos)

(** Reifies a branch in a case.                                          **)
(** Does not build abstractions for binders under construtors, they will **)
(** be added in the final constr.                                        **)
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

let extern_state s =
  let f = s^".cmxs" in
  let include_dirs = "-I " ^ (String.concat " -I " !load_paths) ^ " " in
  let imports = List.map (fun s -> s^".cmx") !imports in
  let imports = String.concat " " imports in
  let comp_cmd =
    "ocamlopt.opt -shared -o "^f^" -rectypes "^include_dirs^imports
  in
  let _ = Sys.command comp_cmd in ()

let intern_state s =
  (** WARNING TODO: if a state with the same file name has already been loaded   **)
  (** Dynlink will ignore it, possibly desynchronizing values in the environment **)
(*  let temp = Filename.temp_file s ".cmxs" in*)
  try Dynlink.loadfile (s^".cmxs")
  with Dynlink.Error e -> print_endline (Dynlink.error_message e)

  (*
let compile_constant mp env kn ck =
  let ast = match ck.const_body with
    | Def cb -> assert false
(*      let _,lid = const_lid mp kn in
      let cb = Declarations.force cb in
        fst (translate mp env lid cb)
        *)
    | _ -> assert false
(*      let _,lid = const_lid mp kn in
      opaque_const mp kn*)
  in
  push_comp_stack ast
  *)

let compile_mind mb kn =
  assert false
(*  let ast = translate_mind mb kn in
  push_comp_stack ast *)
