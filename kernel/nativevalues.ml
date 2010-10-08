open Term
open Names

type t = t -> t
    
type accumulator (* = t (* a bloc [0:code;atom;arguments] *) *)

type tag = int
 
type arity = int

type reloc_table = (tag * arity) array

(*type kind_of_constructor =
  | KOCconst of tag
  | KOCblock of tag * arity*)
    
type sort_annot = string * int

type rec_pos = int

type atom = 
  | Arel of int
  | Aconstant of constant
  | Aind of inductive
  | Asort of sorts
  | Avar of identifier
  | Acase of accumulator * t * (t -> t) * reloc_table * case_info
  | Afix of t * (t -> t) * rec_pos
  | Aprod of name * t * (t -> t)

type atom_fix = atom
let dummy_atom_fix f rec_pos (*ntbl ti*)= Afix ((fun x -> x), f, rec_pos(*,ntbl,ti*))
let upd_fix_atom af frec =
     (Obj.set_field (Obj.magic af) 0 (Obj.magic frec))

let accumulate_tag = 0

let accumulate_code (k:accumulator) (x:t) =
  let o = Obj.repr k in
  let osize = Obj.size o in
  let r = Obj.new_block accumulate_tag (osize + 1) in
  for i = 0 to osize - 1 do
    Obj.set_field r i (Obj.field o i)
  done;
  Obj.set_field r osize (Obj.repr x);
  (Obj.obj r:t)

let rec accumulate (x:t) =
  accumulate_code (Obj.magic accumulate) x

let raccumulate = ref accumulate 

let mk_accu_gen rcode (a:atom) =
  let r = Obj.new_block 0 2 in
  Obj.set_field r 0 (Obj.field (Obj.magic !rcode) 0);
  Obj.set_field r 1 (Obj.magic a);
  (Obj.magic r:t);;

let mk_accu (a:atom) = mk_accu_gen raccumulate a

let mk_rel_accu i = 
  mk_accu (Arel i)

let mk_constant_accu kn = 
  mk_accu (Aconstant kn)

let mk_ind_accu s = 
  mk_accu (Aind s)

let mk_sort_accu s =
  mk_accu (Asort s)

let mk_var_accu id = 
  mk_accu (Avar id)

let mk_sw_accu c p ac tbl ci = 
  mk_accu (Acase(c,p,ac,tbl,ci))

let mk_prod_accu s dom codom =
  mk_accu (Aprod (s,dom,codom))

let atom_of_accu (k:accumulator) =
  (Obj.magic (Obj.field (Obj.magic k) 1) : atom)
    
let arg_of_accu (k:accumulator) (i:int) =
  (Obj.magic (Obj.field (Obj.magic k) (i + 2)) : t)

let accu_nargs (k:accumulator) =
  let nargs = Obj.size (Obj.magic k) - 2 in
  assert (nargs >= 0);
  nargs

let is_accu x =
  let o = Obj.repr x in
  Obj.is_block o && Obj.tag o = accumulate_tag

let accumulate_fix_code (k:accumulator) (a:t) =
  match atom_of_accu k with
  | Afix(frec,_,rec_pos) ->
      let nargs = accu_nargs k in
      if nargs <> rec_pos || is_accu a then
	accumulate_code k a
      else
        let r = ref frec in
        for i = 0 to nargs - 1 do
	  r := !r (arg_of_accu k i)
        done;
        !r a
  | _ -> assert false


let rec accumulate_fix (x:t) =
  accumulate_fix_code (Obj.magic accumulate_fix) x

let raccumulate_fix = ref accumulate_fix 

let is_atom_fix (a:atom) =
  match a with
  | Afix _ -> true
  | _ -> false

let mk_fix_accu (a:atom) =
  assert (is_atom_fix a);
  mk_accu_gen raccumulate_fix a

let mk_const tag = Obj.magic tag

let mk_block tag args =
  let nargs = Array.length args in
  let r = Obj.new_block tag nargs in
  for i = 0 to nargs - 1 do
    Obj.set_field r i (Obj.magic args.(i))
  done;
  (Obj.magic r : t)

let dummy_atom = Arel (-1)

let cast_accu v = (Obj.magic v:accumulator)

type block

let block_size (b:block) =
  Obj.size (Obj.magic b)

let block_field (b:block) i = (Obj.magic (Obj.field (Obj.magic b) i) : t)

let block_tag (b:block) = 
  Obj.tag (Obj.magic b)

type kind_of_value =
  | Vaccu of accumulator
  | Vfun of (t -> t)
  | Vconst of int
  | Vblock of block
	
let kind_of_value (v:t) =
  let o = Obj.repr v in
  if Obj.is_int o then Vconst (Obj.magic v)
  else
    let tag = Obj.tag o in
    if tag = accumulate_tag then Vaccu (Obj.magic v)
    else 
      if (tag < Obj.lazy_tag) then Vblock (Obj.magic v)
      else
        (* assert (tag = Obj.closure_tag || tag = Obj.infix_tag); 
           or ??? what is 1002*)
        Vfun v
