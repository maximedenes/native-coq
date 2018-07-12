type t = int

let _ = assert (Sys.word_size = 64)

let uint_size = 63

let maxuint63 = Int64.of_string "0x7FFFFFFFFFFFFFFF"
let maxuint31 = 0x7FFFFFFF

    (* conversion from an int *)
let to_uint64 i = Int64.logand (Int64.of_int i) maxuint63
let of_int i = i
let to_int i = i
let to_int2 i = (0,i)
let of_int64 i = assert false

    (* conversion of an uint63 to a string *)
let to_string i = Int64.to_string (to_uint64 i)

let of_string s = 
  let i64 = Int64.of_string s in
  if Int64.compare Int64.zero i64 <= 0
      && Int64.compare i64 maxuint63 <= 0 
  then Int64.to_int i64
  else raise (Failure "Int64.of_string")

(* Compiles an unsigned int to OCaml code *)
let compile i = Printf.sprintf "Uint63.of_int (%i)" i

let zero = 0

    (* logical shift *)
let l_sl x y =
  if 0 <= y && y < 63 then x lsl y else 0

let l_sr x y = 
  if 0 <= y && y < 63 then x lsr y else 0

let l_and x y = x land y
let l_or x y = x lor y
let l_xor x y = x lxor y

    (* addition of int63 *)
let add x y = x + y

    (* subtraction *)
let sub x y = x - y

    (* multiplication *)
let mul x y = x * y

    (* division *)
let div (x : int) (y : int) =
  if y = 0 then 0 else Int64.to_int (Int64.div (to_uint64 x) (to_uint64 y))

    (* modulo *)
let rem (x : int) (y : int) =
  if y = 0 then 0 else Int64.to_int (Int64.rem (to_uint64 x) (to_uint64 y))

let addmuldiv p x y =
  l_or (l_sl x p) (l_sr y (uint_size - p))

    (* comparison *)
let lt (x : int) (y : int) =
  (x lxor 0x4000000000000000) < (y lxor 0x4000000000000000)

let le (x : int) (y : int) =
  (x lxor 0x4000000000000000) <= (y lxor 0x4000000000000000)

(* A few helper functions on 128 bits *)
let lt128 xh xl yh yl =
  lt xh yh || (xh = yh && lt xl yl)

let le128 xh xl yh yl =
  lt xh yh || (xh = yh && le xl yl)

    (* division of two numbers by one *)
let div21 xh xl y =
  let maskh = ref 0 in
  let maskl = ref 1 in
  let dh = ref 0 in
  let dl = ref y in
  let cmp = ref true in
  while !dh >= 0 && !cmp do
    cmp := lt128 !dh !dl xh xl;
    (* We don't use addmuldiv below to avoid checks on 1 *)
    dh := (!dh lsl 1) lor (!dl lsr (uint_size - 1));
    dl := !dl lsl 1;
    maskh := (!maskh lsl 1) lor (!maskl lsr (uint_size - 1));
    maskl := !maskl lsl 1
  done; (* mask = 2^N, d = 2^N * d, d >= x *)
  let remh = ref xh in
  let reml = ref xl in
  let quotient = ref 0 in
  while !maskh lor !maskl <> 0 do
    if le128 !dh !dl !remh !reml then begin (* if rem >= d, add one bit and subtract d *)
      quotient := !quotient lor !maskl;
      remh := if lt !reml !dl then !remh - !dh - 1 else !remh - !dh;
      reml := !reml - !dl;
    end;
    maskl := (!maskl lsr 1) lor (!maskh lsl (uint_size - 1));
    maskh := !maskh lsr 1;
    dl := (!dl lsr 1) lor (!dh lsl (uint_size - 1));
    dh := !dh lsr 1;
  done;
  !quotient, !reml

     (* exact multiplication *)
(* TODO: check that none of these additions could be a logical or *)


(* size = 32 + 31 
   (hx << 31 + lx) * (hy << 31 + ly) =
   hxhy << 62 + (hxly + lxhy) << 31 + lxly
*)

(* precondition : (x lsr 62 = 0 || y lsr 62 = 0) *)
let mulc_aux x y = 
  let lx = x land maxuint31 in
  let ly = y land maxuint31 in
  let hx = x lsr 31  in
  let hy = y lsr 31 in
    (* hx and hy are 32 bits value but at most one is 32 *)
  let hxy  = hx * hy in (* 63 bits *)
  let hxly = hx * ly in (* 63 bits *)
  let lxhy = lx * hy in (* 63 bits *)
  let lxy  = lx * ly in (* 62 bits *)
  let l  = lxy lor (hxy lsl 62) (* 63 bits *) in
  let h  = hxy lsr 1 in (* 62 bits *) 
  let hl = hxly + lxhy in (* We can have a carry *)
  let h  = if lt hl hxly then h + (1 lsl 31) else h in
  let hl'= hl lsl 31 in
  let l  = l + hl' in
  let h  = if lt l hl' then h + 1 else h in
  let h  = h + (hl lsr 32) in
  (h,l)

let mulc x y = 
  if (x lsr 62 = 0 || y lsr 62 = 0) then mulc_aux x y
  else
    let yl = y lxor (1 lsl 62) in
    let (h,l) = mulc_aux x yl in
    (* h << 63 + l = x * yl 
       x * y = x * (1 << 62 + yl)  =
       x << 62 + x*yl = x << 62 + h << 63 + l *)
    let l' = l + (x lsl 62) in
    let h = if lt l' l then h + 1 else h in
    (h + (x lsr 1), l')

let eq (x : int) (y : int) = x = y

let compare (x:int) (y:int) =
  let x = x lxor 0x4000000000000000 in
  let y = y lxor 0x4000000000000000 in
  if x > y then 1
  else if y > x then -1
  else 0

    (* head tail *)

let head0 x =
  let r = ref 0 in
  let x = ref x in
  if !x land 0x7FFFFFFF00000000 = 0 then r := !r + 31
  else x := !x lsr 31;
  if !x land 0xFFFF0000 = 0 then (x := !x lsl 16; r := !r + 16);
  if !x land 0xFF000000 = 0 then (x := !x lsl 8; r := !r + 8);
  if !x land 0xF0000000 = 0 then (x := !x lsl 4; r := !r + 4);
  if !x land 0xC0000000 = 0 then (x := !x lsl 2; r := !r + 2);
  if !x land 0x80000000 = 0 then (x := !x lsl 1; r := !r + 1);
  if !x land 0x80000000 = 0 then (               r := !r + 1);
  !r;;

let tail0 x =
  let r = ref 0 in
  let x = ref x in
  if !x land 0xFFFFFFFF = 0 then (x := !x lsr 32; r := !r + 32);
  if !x land 0xFFFF = 0 then (x := !x lsr 16; r := !r + 16);
  if !x land 0xFF = 0   then (x := !x lsr 8;  r := !r + 8);
  if !x land 0xF = 0    then (x := !x lsr 4;  r := !r + 4);
  if !x land 0x3 = 0    then (x := !x lsr 2;  r := !r + 2);
  if !x land 0x1 = 0    then (                r := !r + 1);
  !r

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