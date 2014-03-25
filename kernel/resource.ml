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
let get1 (mmap : t) (offset : int64) =
  ResourcePosix.get1 mmap offset

(* -------------------------------------------------------------------- *)
let getle32 (mmap : t) (offset : int64) =
  ResourcePosix.getle32 mmap offset
