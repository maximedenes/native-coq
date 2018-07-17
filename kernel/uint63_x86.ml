(* Invariant: the msb should be 0 *)
type t = Int64.t

let _ = assert (Sys.word_size = 32)

let uint_size = 63

let maxuint63 = Int64.of_string "0x7FFFFFFFFFFFFFFF"
let maxuint31 = Int64.of_string "0x7FFFFFFF"
(* let sign_bit = Int64.of_string "0x4000000000000000" *)

    (* conversion from an int *)
let mask63 i = Int64.logand i maxuint63
let of_int i = Int64.of_int i
let to_intint i = (Int64.to_int (Int64.shift_right_logical i 31), Int64.to_int i)
let of_int64 i = i

    (* conversion of an uint63 to a string *)
let to_string i = Int64.to_string i

let of_string s = 
  let i64 = Int64.of_string s in
  if Int64.compare Int64.zero i64 <= 0
      && Int64.compare i64 maxuint63 <= 0 
  then i64
  else raise (Failure "Int63.of_string")

(* Compiles an unsigned int to OCaml code *)
let compile i = Printf.sprintf "Uint63.of_int64 (%LiL)" i

    (* comparison *)
let lt x y =
  Int64.compare x y < 0

let le x y =
  Int64.compare x y <= 0

    (* logical shift *)
let l_sl x y =
  if le 0L y && lt y 63L then mask63 (Int64.shift_left x (Int64.to_int y)) else 0L

(* TODO: is shift_right or shift_right logical faster everywhere? *)
let l_sr x y = 
  if le 0L y && lt y 63L then Int64.shift_right x (Int64.to_int y) else 0L

let l_and x y = Int64.logand x y
let l_or x y = Int64.logor x y
let l_xor x y = Int64.logxor x y

    (* addition of int63 *)
let add x y = mask63 (Int64.add x y)

    (* subtraction *)
let sub x y = mask63 (Int64.sub x y)

    (* multiplication *)
let mul x y = mask63 (Int64.mul x y)

    (* division *)
let div x y =
  if y = 0L then 0L else Int64.div x y

    (* modulo *)
let rem x y =
  if y = 0L then 0L else Int64.rem x y

    (* division of two numbers by one *)
let div21 xh xl y = 0L, 0L

     (* exact multiplication *)
(* TODO: check that none of these additions could be a logical or *)
let mulc x y =
  let lx = ref (Int64.logand x maxuint31) in
  let ly = ref (Int64.logand y maxuint31) in
  let hx = Int64.shift_right x 31 in
  let hy = Int64.shift_right y 31 in
  let hr = ref (Int64.mul hx hy) in
  let lr = ref (Int64.logor (Int64.mul !lx !ly) (Int64.shift_left !hr 62)) in
  hr := (Int64.shift_right_logical !hr 1);
  lx := Int64.mul !lx hy;
  ly := Int64.mul hx !ly;
  hr := Int64.logor !hr (Int64.add (Int64.shift_right !lx 32) (Int64.shift_right !ly 32));
  lr := Int64.add !lr (Int64.shift_left !lx 31);
  hr := Int64.add !hr (Int64.shift_right_logical !lr 63);
  lr := Int64.add (Int64.shift_left !ly 31) (mask63 !lr);
  hr := Int64.add !hr (Int64.shift_right_logical !lr 63);
  (!hr, !lr)

let eq x y = mask63 x = mask63 y

let compare x y = Int64.compare x y

(* Number of leading zeroes *)
let head0 x =
  let r = ref 0 in
  let x = ref x in
  if Int64.logand !x 0x7FFFFFFF00000000L = 0L then r := !r + 31
  else x := Int64.shift_right !x 31;
  if Int64.logand !x 0xFFFF0000L = 0L then (x := Int64.shift_left !x 16; r := !r + 16);
  if Int64.logand !x 0xFF000000L = 0L then (x := Int64.shift_left !x 8; r := !r + 8);
  if Int64.logand !x 0xF0000000L = 0L then (x := Int64.shift_left !x 4; r := !r + 4);
  if Int64.logand !x 0xC0000000L = 0L then (x := Int64.shift_left !x 2; r := !r + 2);
  if Int64.logand !x 0x80000000L = 0L then (x := Int64.shift_left !x 1; r := !r + 1);
  if Int64.logand !x 0x80000000L = 0L then (               r := !r + 1);
  Int64.of_int !r

(* Number of trailing zeroes *)
let tail0 x =
  let r = ref 0 in
  let x = ref x in
  if Int64.logand !x 0xFFFFFFFFL = 0L then (x := Int64.shift_right !x 32; r := !r + 32);
  if Int64.logand !x 0xFFFFL = 0L then (x := Int64.shift_right !x 16; r := !r + 16);
  if Int64.logand !x 0xFFL = 0L   then (x := Int64.shift_right !x 8;  r := !r + 8);
  if Int64.logand !x 0xFL = 0L    then (x := Int64.shift_right !x 4;  r := !r + 4);
  if Int64.logand !x 0x3L = 0L    then (x := Int64.shift_right !x 2;  r := !r + 2);
  if Int64.logand !x 0x1L = 0L    then (                r := !r + 1);
  Int64.of_int !r

let rec foldi_cont f min max cont a =
  if lt min max then f min (foldi_cont f (add min 1) max cont) a
  else if min = max then f min cont a 
  else cont a 

let rec foldi_down_cont f max min cont a =
  if lt min max then
    f max (foldi_down_cont f (sub max 1) min cont) a
  else if min = max then f min cont a
  else cont a

let print_uint x =
  Printf.fprintf stderr "%s" (to_string x);
  flush stderr;
  x