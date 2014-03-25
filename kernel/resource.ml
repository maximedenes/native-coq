(* -------------------------------------------------------------------- *)
type t = {
  name   : string;
  source : ResourcePosix.mmap;
}

let eq      = (Pervasives.(=)     : t -> t -> bool)
let compare = (Pervasives.compare : t -> t -> int)
let hash    = (Hashtbl.hash       : t -> int)

(* -------------------------------------------------------------------- *)
let create (name : string) =
  let mmap = ResourcePosix.create name in
  { name = name; source = mmap; }

(* -------------------------------------------------------------------- *)
let get1 { source = mmap } =
  ResourcePosix.get1 mmap

(* -------------------------------------------------------------------- *)
let getle32 { source = mmap } =
  ResourcePosix.getle32 mmap
