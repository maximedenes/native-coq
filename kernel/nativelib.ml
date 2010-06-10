open Names
open Term
open Util
open Nativevalues

exception Bug of string

type nbe_annotation =
  | CaseAnnot of case_info

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

