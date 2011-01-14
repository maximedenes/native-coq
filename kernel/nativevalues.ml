open Term
open Names

type t = t -> t
    
type accumulator (* = t (* a bloc [0:code;atom;arguments] *) *)

type tag = int
 
type arity = int

type reloc_table = (tag * arity) array

type annot_sw = {
    asw_ind : inductive;
    asw_ci : case_info;
    asw_reloc : reloc_table;
    asw_finite : bool
  }

type sort_annot = string * int

type rec_pos = int array

type atom = 
  | Arel of int
  | Aconstant of constant
  | Aind of inductive
  | Asort of sorts
  | Avar of identifier
  | Acase of annot_sw * accumulator * t * (t -> t)
  | Afix of  t array * t array * rec_pos * int
  | Acofix of t array * t array * int * t
  | Acofixe of t array * t array * int * t
  | Aprod of name * t * (t -> t)

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

let rel_tbl_size = 100 
let rel_tbl = Array.init rel_tbl_size mk_rel_accu

let mk_rel_accu i = 
  if i < rel_tbl_size then rel_tbl.(i)
  else mk_rel_accu i

let mk_rels_accu lvl len =
  Array.init len (fun i -> mk_rel_accu (lvl + i))

let napply (f:t) (args: t array) =
  Array.fold_left (fun f a -> f a) f args

let mk_constant_accu kn = 
  mk_accu (Aconstant kn)

let mk_ind_accu s = 
  mk_accu (Aind s)

let mk_sort_accu s =
  mk_accu (Asort s)

let mk_var_accu id = 
  mk_accu (Avar id)

let mk_sw_accu annot c p ac = 
  mk_accu (Acase(annot,c,p,ac))

let mk_prod_accu s dom codom =
  mk_accu (Aprod (s,dom,codom))

let atom_of_accu (k:accumulator) =
  (Obj.magic (Obj.field (Obj.magic k) 1) : atom)

let set_atom_of_accu (k:accumulator) (a:atom) =
  Obj.set_field (Obj.magic k) 1 (Obj.magic a)
    
let arg_of_accu (k:accumulator) (i:int) =
  (Obj.magic (Obj.field (Obj.magic k) (i + 2)) : t)

let accu_nargs (k:accumulator) =
  let nargs = Obj.size (Obj.magic k) - 2 in
  assert (nargs >= 0);
  nargs

let is_accu x =
  let o = Obj.repr x in
  Obj.is_block o && Obj.tag o = accumulate_tag

(*let accumulate_fix_code (k:accumulator) (a:t) =
  match atom_of_accu k with
  | Afix(frec,_,rec_pos,_,_) ->
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

let raccumulate_fix = ref accumulate_fix *)

let is_atom_fix (a:atom) =
  match a with
  | Afix _ -> true
  | _ -> false

let mk_fix_accu rec_pos pos types bodies =
  mk_accu_gen raccumulate (Afix(types,bodies,rec_pos, pos))

let mk_cofix_accu pos types norm =
  mk_accu_gen raccumulate (Acofix(types,norm,pos,(Obj.magic 0 : t)))

let upd_cofix (cofix :t) (cofix_fun : t) =
  let atom = atom_of_accu (Obj.magic cofix) in
  match atom with
  | Acofix (typ,norm,pos,_) ->
      set_atom_of_accu (Obj.magic cofix) (Acofix(typ,norm,pos,cofix_fun))
  | _ -> assert false
  
let force_cofix (cofix : t) = 
  if is_accu cofix then
    let accu = (Obj.magic cofix : accumulator) in
    let atom = atom_of_accu accu in
    match atom with
    | Acofix(typ,norm,pos,f) ->
	let f = ref f in
	let nargs = accu_nargs accu in
	for i = 0 to nargs - 1 do 
	  f := !f (arg_of_accu accu i)
	done;
	let v = !f (Obj.magic ()) in
	set_atom_of_accu accu (Acofixe(typ,norm,pos,v));
	v
    | Acofixe(_,_,_,v) -> v 
    | _ -> cofix
  else cofix

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

let mk_int x = Obj.magic x

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
  | Varray of t Native.Parray.t 
	
let kind_of_value (v:t) =
  let o = Obj.repr v in
  if Obj.is_int o then Vconst (Obj.magic v)
  else
    let tag = Obj.tag o in
    if tag = accumulate_tag then 
      if Obj.size o = 1 then Varray (Obj.magic v)
      else Vaccu (Obj.magic v)
    else 
      if (tag < Obj.lazy_tag) then Vblock (Obj.magic v)
      else
        (* assert (tag = Obj.closure_tag || tag = Obj.infix_tag); 
           or ??? what is 1002*)
        Vfun v



(*** Operations pour les entiers **)

let val_of_int x = Obj.magic x 
let val_to_int x = Obj.magic x


let is_int (x:t) = Obj.is_int (Obj.repr x)
let to_uint (x:t) = (Obj.magic x : Uint31.t)
let of_uint (x: Uint31.t) = (Obj.magic x : t)

let no_check_head0 x =
 of_uint (Uint31.head0 (to_uint x))

let head0 accu x =
 if is_int x then  no_check_head0 x
 else accu x

let no_check_tail0 x =
  of_uint (Uint31.tail0 (to_uint x))

let tail0 accu x =
 if is_int x then no_check_tail0 x
 else accu x

let no_check_add  x y =
  of_uint (Uint31.add (to_uint x) (to_uint y))

let add accu x y =
  if is_int x && is_int y then no_check_add x y 
  else accu x y

let no_check_sub x y =
     of_uint (Uint31.sub (to_uint x) (to_uint y))

let sub accu x y =
  if is_int x && is_int y then no_check_sub x y
  else accu x y

let no_check_mul x y =
  of_uint (Uint31.mul (to_uint x) (to_uint y))

let mul accu x y =
  if is_int x && is_int y then no_check_mul x y
  else accu x y

let no_check_div x y =
  of_uint (Uint31.div (to_uint x) (to_uint y))

let div accu x y =
  if is_int x && is_int y then no_check_div x y 
  else accu x y

let no_check_rem x y =
  of_uint (Uint31.rem (to_uint x) (to_uint y))

let rem accu x y =
  if is_int x && is_int y then no_check_rem x y
  else accu x y

let no_check_l_sr x y =
  of_uint (Uint31.l_sr (to_uint x) (to_uint y))

let l_sr accu x y =
  if is_int x && is_int y then no_check_l_sr x y
  else accu x y

let no_check_l_sl x y =
  of_uint (Uint31.l_sl (to_uint x) (to_uint y))

let l_sl accu x y =
  if is_int x && is_int y then no_check_l_sl x y
  else accu x y

let no_check_l_and x y =
  of_uint (Uint31.l_and (to_uint x) (to_uint y))

let l_and accu x y =
  if is_int x && is_int y then no_check_l_and x y
  else accu x y

let no_check_l_xor x y =
  of_uint (Uint31.l_xor (to_uint x) (to_uint y))

let l_xor accu x y =
  if is_int x && is_int y then no_check_l_xor x y
  else accu x y

let no_check_l_or x y =
  of_uint (Uint31.l_or (to_uint x) (to_uint y))

let l_or accu x y =
  if is_int x && is_int y then no_check_l_or x y
  else accu x y

type coq_carry = 
  | Caccu of t
  | C0 of t
  | C1 of t

type coq_pair = 
  | Paccu of t
  | PPair of t * t

let mkCarry b i =
  if b then (Obj.magic (C1(of_uint i)):t)
  else (Obj.magic (C0(of_uint i)):t)

let no_check_addc x y =
  let s = Uint31.add (to_uint x) (to_uint y) in
  mkCarry (Uint31.lt s (to_uint x)) s

let addc accu x y =
  if is_int x && is_int y then no_check_addc x y
  else accu x y

let no_check_subc x y =
  let s = Uint31.sub (to_uint x) (to_uint y) in
  mkCarry (Uint31.lt (to_uint x) (to_uint y)) s

let subc accu x y =
  if is_int x && is_int y then no_check_subc x y
  else accu x y

let no_check_addCarryC x y =
  let s = 
    Uint31.add (Uint31.add (to_uint x) (to_uint y))
      (Uint31.of_int 1) in
  mkCarry (Uint31.le s (to_uint x)) s

let addCarryC accu x y =
  if is_int x && is_int y then no_check_addCarryC x y
  else accu x y 

let no_check_subCarryC x y =
  let s = 
    Uint31.sub (Uint31.sub (to_uint x) (to_uint y))
      (Uint31.of_int 1) in
  mkCarry (Uint31.le (to_uint x) (to_uint y)) s

let subCarryC accu x y =
  if is_int x && is_int y then no_check_subCarryC x y
  else accu x y 

let of_pair (x, y) =
  (Obj.magic (PPair(of_uint x, of_uint y)):t)

let no_check_mulc x y =
    of_pair(Uint31.mulc (to_uint x) (to_uint y))

let mulc accu x y =
  if is_int x && is_int y then no_check_mulc x y
  else accu x y

let no_check_diveucl x y =
  let i1, i2 = to_uint x, to_uint y in
  of_pair(Uint31.div i1 i2, Uint31.rem i1 i2)

let diveucl accu x y =
  if is_int x && is_int y then no_check_diveucl x y
  else accu x y

let no_check_div21 x y z =
  let i1, i2, i3 = to_uint x, to_uint y, to_uint z in
  of_pair (Uint31.div21 i1 i2 i3)

let div21 accu x y z =
  if is_int x && is_int y && is_int z then no_check_div21 x y z
  else accu x y z

let no_check_addMulDiv x y z =
  let p, i, j = to_uint x, to_uint y, to_uint z in
  let p' = Uint31.to_int p in
  of_uint (Uint31.l_or 
	     (Uint31.l_sl i p) 
	     (Uint31.l_sr j (Uint31.of_int (31 - p'))))

let addMulDiv accu x y z =
  if is_int x && is_int y && is_int z then no_check_addMulDiv x y z
  else accu x y z


type coq_bool =
  | Baccu of t
  | Btrue
  | Bfalse

type coq_cmp =
  | CmpAccu of t
  | CmpEq 
  | CmpLt
  | CmpGt

let of_bool b = 
  if b then (Obj.magic Btrue:t)
  else (Obj.magic Bfalse:t)

let no_check_eq x y =     
  of_bool (Uint31.eq (to_uint x) (to_uint y))

let eq accu x y =
  if is_int x && is_int y then no_check_eq x y
  else accu x y

let no_check_lt x y =
  of_bool (Uint31.lt (to_uint x) (to_uint y))

let lt accu x y =
  if is_int x && is_int y then no_check_lt x y
  else accu x y

let no_check_le x y =
  of_bool (Uint31.le (to_uint x) (to_uint y))

let le accu x y =
  if is_int x && is_int y then no_check_le x y
  else accu x y

let no_check_compare x y =
  match Uint31.compare (to_uint x) (to_uint y) with
  | x when x < 0 -> (Obj.magic CmpLt:t)
  | 0 -> (Obj.magic CmpEq:t)
  | _ -> (Obj.magic CmpGt:t)

let compare accu x y =
  if is_int x && is_int y then no_check_compare x y
  else accu x y

type coq_eq = 
  | EqAccu of t
  | EqRefl

let eqb_correct accu x y heq =
  if is_int x then (Obj.magic EqRefl:t)
  else accu x y heq

let print accu x = 
  if is_int x then 
    begin
      Printf.fprintf stderr "%s" (Uint31.to_string (to_uint x));
      flush stderr;
      x
    end
  else accu x 

let foldi_cont accu _A _B f min max cont =
  if is_int min && is_int max then
    let imin, imax = to_uint min, to_uint max in
    if Uint31.le imin imax then
      let rec aux i a =
        f (of_uint i) 
         (if Uint31.lt i imax then
	   aux (Uint31.add i (Uint31.of_int 1))
	 else cont) a in
      aux imin
    else cont
  else accu _A _B f min max cont

let foldi_down_cont accu _A _B f max min cont =
  if is_int max && is_int min then
    let imax, imin = to_uint max, to_uint min in
    if Uint31.le imin imax then
      let rec aux i a =
        f (of_uint i) 
         (if Uint31.lt imin i then
	   aux (Uint31.sub i (Uint31.of_int 1))
	 else cont) a in
      aux imax
    else cont
  else accu _A _B f max min cont

let is_parray t =
  let t = Obj.magic t in
  Obj.is_block t && Obj.size t = 1

let to_parray t = Obj.magic t
let of_parray t = Obj.magic t

let arraymake accu vA n def = 
  if is_int n then 
    of_parray (Native.Parray.make (to_uint n) def)
  else accu vA n def

let arrayget accu vA t n =
  if is_parray t && is_int n then
    Native.Parray.get (to_parray t) (to_uint n)
  else accu vA t n

let arraydefault accu vA t =
  if is_parray t then  
    Native.Parray.default (to_parray t) 
  else accu vA t 

let arrayset accu vA t n v =
  if is_parray t && is_int n then
    of_parray (Native.Parray.set (to_parray t) (to_uint n) v)
  else accu vA t n v

let arraycopy accu vA t = 
  if is_parray t then
    of_parray (Native.Parray.copy (to_parray t))
  else accu vA t 

let arrayreroot accu vA t =
  if is_parray t then
    of_parray (Native.Parray.reroot (to_parray t))
  else accu vA t 

let arraylength accu vA t =
  if is_parray t then
    of_uint (Native.Parray.length (to_parray t))
  else accu vA t

let parray_of_array t =
  (Obj.magic (Native.Parray.of_array t) : t)




let lt_b x y =
  Uint31.lt (to_uint x) (to_uint y)
 
let le_b x y =
  Uint31.le (to_uint x) (to_uint y)













 
let hobcnv = Array.init 256 (fun i -> Printf.sprintf "%.2x" i)
let bohcnv = Array.init 256 (fun i -> i -
                                      (if 0x30 <= i then 0x30 else 0) -
                                      (if 0x41 <= i then 0x7 else 0) -
                                      (if 0x61 <= i then 0x20 else 0))

let hex_of_bin ch = hobcnv.(int_of_char ch)
let bin_of_hex s = char_of_int (bohcnv.(int_of_char s.[0]) * 16 + bohcnv.(int_of_char s.[1]))

let str_encode expr =
  let mshl_expr = Marshal.to_string expr [] in
  let payload = Buffer.create (String.length mshl_expr * 2) in
  String.iter (fun c -> Buffer.add_string payload (hex_of_bin c)) mshl_expr;
  Buffer.contents payload

let str_decode s =
  let mshl_expr_len = String.length s / 2 in
  let mshl_expr = Buffer.create mshl_expr_len in
  let buf = String.create 2 in
  for i = 0 to mshl_expr_len - 1 do
    String.blit s (2*i) buf 0 2;
    Buffer.add_char mshl_expr (bin_of_hex buf)
  done;
  Marshal.from_string (Buffer.contents mshl_expr) 0


