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
  | Afix of t * (t -> t) * rec_pos * name * t
  | Aprod of name * t * (t -> t)

type atom_fix = atom
let dummy_atom_fix f rec_pos ls tys = Afix ((fun x -> x), f, rec_pos, ls, tys)
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

let mk_uint x = Obj.magic x


let is_int (x:t) = Obj.is_int (Obj.repr x)
let to_uint (x:t) = (Obj.magic x : Native.Uint31.t)
let of_uint (x: Native.Uint31.t) = (Obj.magic x : t)

let head0 accu x =
 if is_int x then  of_uint (Native.Uint31.head0 (to_uint x))
 else accu x

let tail0 accu x =
 if is_int x then  of_uint (Native.Uint31.tail0 (to_uint x))
 else accu x

let add accu x y =
  if is_int x && is_int y then 
     of_uint (Native.Uint31.add (to_uint x) (to_uint y))
  else accu x y

let sub accu x y =
  if is_int x && is_int y then 
     of_uint (Native.Uint31.sub (to_uint x) (to_uint y))
  else accu x y

let mul accu x y =
  if is_int x && is_int y then 
     of_uint (Native.Uint31.mul (to_uint x) (to_uint y))
  else accu x y

let div accu x y =
  if is_int x && is_int y then 
     of_uint (Native.Uint31.div (to_uint x) (to_uint y))
  else accu x y

let rem accu x y =
  if is_int x && is_int y then 
     of_uint (Native.Uint31.rem (to_uint x) (to_uint y))
  else accu x y

let l_sr accu x y =
  if is_int x && is_int y then 
     of_uint (Native.Uint31.l_sr (to_uint x) (to_uint y))
  else accu x y

let l_sl accu x y =
  if is_int x && is_int y then 
     of_uint (Native.Uint31.l_sl (to_uint x) (to_uint y))
  else accu x y

let l_and accu x y =
  if is_int x && is_int y then 
     of_uint (Native.Uint31.l_and (to_uint x) (to_uint y))
  else accu x y

let l_xor accu x y =
  if is_int x && is_int y then 
     of_uint (Native.Uint31.l_xor (to_uint x) (to_uint y))
  else accu x y

let l_or accu x y =
  if is_int x && is_int y then 
     of_uint (Native.Uint31.l_or (to_uint x) (to_uint y))
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

let addc accu x y =
  if is_int x && is_int y then
    let s = Native.Uint31.add (to_uint x) (to_uint y) in
    mkCarry (Native.Uint31.lt s (to_uint x)) s
  else accu x y

let subc accu x y =
  if is_int x && is_int y then
    let s = Native.Uint31.sub (to_uint x) (to_uint y) in
    mkCarry (Native.Uint31.lt (to_uint x) (to_uint y)) s
  else accu x y

let addCarryC accu x y =
  if is_int x && is_int y then
    let s = 
      Native.Uint31.add (Native.Uint31.add (to_uint x) (to_uint y))
	(Native.Uint31.of_int 1) in
    mkCarry (Native.Uint31.le s (to_uint x)) s
  else accu x y 

let subCarryC accu x y =
  if is_int x && is_int y then
    let s = 
      Native.Uint31.sub (Native.Uint31.sub (to_uint x) (to_uint y))
	(Native.Uint31.of_int 1) in
    mkCarry (Native.Uint31.le (to_uint x) (to_uint y)) s
  else accu x y 

let of_pair (x, y) =
  (Obj.magic (PPair(of_uint x, of_uint y)):t)

let mulc accu x y =
  if is_int x && is_int y then
    of_pair(Native.Uint31.mulc (to_uint x) (to_uint y))
  else accu x y

let diveucl accu x y =
  if is_int x && is_int y then
    let i1, i2 = to_uint x, to_uint y in
    of_pair(Native.Uint31.div i1 i2, Native.Uint31.rem i1 i2)
  else accu x y

let div21 accu x y z =
  if is_int x && is_int y && is_int z then
    let i1, i2, i3 = to_uint x, to_uint y, to_uint z in
    of_pair (Native.Uint31.div21 i1 i2 i3)
  else accu x y z

let addMulDiv accu x y z =
  if is_int x && is_int y && is_int z then
    let p, i, j = to_uint x, to_uint y, to_uint z in
    let p' = Native.Uint31.to_int p in
    of_uint (Native.Uint31.l_or 
	       (Native.Uint31.l_sl i p) 
	       (Native.Uint31.l_sr j (Native.Uint31.of_int (31 - p'))))
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

let eq accu x y =
  if is_int x && is_int y then 
    of_bool (Native.Uint31.eq (to_uint x) (to_uint y))
  else accu x y

let lt accu x y =
  if is_int x && is_int y then 
     of_bool (Native.Uint31.lt (to_uint x) (to_uint y))
  else accu x y
 
let le accu x y =
  if is_int x && is_int y then 
     of_bool (Native.Uint31.le (to_uint x) (to_uint y))
  else accu x y

let compare accu x y =
  if is_int x && is_int y then 
    match Native.Uint31.compare (to_uint x) (to_uint y) with
    | x when x < 0 -> (Obj.magic CmpLt:t)
    | 0 -> (Obj.magic CmpEq:t)
    | _ -> (Obj.magic CmpGt:t)
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
      Printf.fprintf stderr "%s" (Native.Uint31.to_string (to_uint x));
      flush stderr;
      x
    end
  else accu x 

let foldi_cont accu _A _B f min max cont =
  if is_int min && is_int max then
    let imin, imax = to_uint min, to_uint max in
    if Native.Uint31.le imin imax then
      let rec aux i a =
        f (of_uint i) 
         (if Native.Uint31.lt i imax then
	   aux (Native.Uint31.add i (Native.Uint31.of_int 1))
	 else cont) a in
      aux imin
    else cont
  else accu _A _B f min max cont

let foldi_down_cont accu _A _B f max min cont =
  if is_int max && is_int min then
    let imax, imin = to_uint max, to_uint min in
    if Native.Uint31.le imin imax then
      let rec aux i a =
        f (of_uint i) 
         (if Native.Uint31.lt imin i then
	   aux (Native.Uint31.sub i (Native.Uint31.of_int 1))
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


