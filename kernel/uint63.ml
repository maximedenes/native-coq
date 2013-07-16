type t = int 

let uint_size = 63
    
  (* to be used only on 32 bits achitectures *)
let maxuint63 = Int64.of_string "0x7FFFFFFFFFFFFFFF"
let maxuint31 = Int64.to_int (Int64.of_string "0x7FFFFFFF")
    
    (* conversion from an int *)
let to_uint64 i = Int64.logand (Int64.of_int i) maxuint63
let of_int i = i
let to_int i = i

    (* conversion of an uint31 to a string *)
let to_string i = Int64.to_string (to_uint64 i)

let of_string s = 
  let i64 = Int64.of_string s in
  if Int64.compare Int64.zero i64 <= 0
      && Int64.compare i64 maxuint63 <= 0 
  then Int64.to_int i64
  else raise (Failure "int_of_string")

    (* logical shift *)
let l_sl x y =
  if 0 <= y && y < 63 then x lsl y else 0
    
let l_sr x y = 
  if 0 <= y && y < 63 then x lsr y else 0
    
let l_and x y = x land y
let l_or x y = x lor y
let l_xor x y = x lxor y

    (* addition of int31 *)
let add x y = x + y
 
    (* subtraction *)
let sub x y = x - y
   
    (* multiplication *)
let mul x y = x * y
    
    (* exact multiplication *)
let mulc x y =
  let lx = x land maxuint31 in
  let ly = y land maxuint31 in
  let hx = x lsr 31 in
  let hy = y lsr 31 in
  let r0 = lx * hy in
  let r1 = hx * ly in
  let hr = hx * hy in
  let lr = lx * ly + (hr lsl 62) in
  let hr = (lx land ly land 0x4000000000000000) + (hr lsr 1) in
  let lr0 = r0 lsl 31 in
  let lr1 = r1 lsl 31 in
  let lr = lr + lr0 in
  let c0 = lr < lr0 in (* TODO: unsigned compare? *)
  let lr = lr + lr1 in
  let c1 = lr < lr1 in
  let hr = hr + (r0 lsr 32) + (r1 lsr 32) in
  let hr =
    match c0, c1 with
    | false, false -> hr
    | true, true -> hr + 2
    | _ -> hr + 1
  in (hr, lr)

    (* division *)
let div (x : int) (y : int) = if y = 0 then 0 else x / y
    
    (* modulo *)
let rem (x : int) (y : int) = if y = 0 then 0 else x mod y
    
    (* division of two numbers by one *)
(* TODO *)
let div21 xh xl y = 0, 0
    
    (* comparison *)
let lt x y =
  (x lxor 0x4000000000000000) < (y lxor 0x4000000000000000)

let le x y =
  (x lxor 0x4000000000000000) <= (y lxor 0x4000000000000000)

let eq (x : int) (y : int) = x = y
    
let compare (x:int) (y:int) = compare x y (* TODO: unsigned compare *)
  
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


 
