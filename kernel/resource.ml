
(* -------------------------------------------------------------------- *)
module RP = ResourcePosix

(* -------------------------------------------------------------------- *)
module H = Weak.Make(struct
  type key = int * int
  type t   = key * RP.mmap option

  let equal ((k1, _) : t) ((k2, _) : t) =
    Pervasives.(=) k1 k2

  let hash ((k, _) : t) =
    Hashtbl.hash k
end)

let htable = H.create 0

(* -------------------------------------------------------------------- *)
type t = RP.mmap

let eq      = (Pervasives.(=)     : t -> t -> bool)
let compare = (Pervasives.compare : t -> t -> int)
let hash    = (Hashtbl.hash       : t -> int)

(* -------------------------------------------------------------------- *)
let create (name : string) =
  let st =
    try  Unix.stat name
    with Unix.Unix_error _ -> raise RP.InvalidResource
  in

  let key = (st.Unix.st_dev, st.Unix.st_ino) in

  try
    match H.find htable (key, None) with
    | (_, Some mmap) -> mmap
    | (_, None     ) -> assert false

  with Not_found ->
    let mmap = ResourcePosix.create name in
    H.add htable (key, Some mmap); mmap

(* -------------------------------------------------------------------- *)
let make (name:Uint63.t array) =
  let len = Array.length name in
  let sname = String.create len in
  for i = 0 to len - 1 do
    let k = Uint63.to_int name.(i) in
    let kc = k land 0xFF  in
    let kc = if kc = 0 then 1 else kc in
    sname.[i] <- Char.chr kc
  done;
  create sname

(* -------------------------------------------------------------------- *)
let getc (mmap : t) (offset : Uint63.t) =
  try  Uint63.of_int (ResourcePosix.get1 mmap (Uint63.to_int offset))
  with Invalid_argument _ -> Uint63.of_int 0

(* -------------------------------------------------------------------- *)
let geti32 (mmap : t) (offset : Uint63.t) =
  try  Uint63.of_int (ResourcePosix.getle32 mmap (Uint63.to_int offset))
  with Invalid_argument _ -> Uint63.of_int 0
