let max_array_length32 = 4194303 (* Sys.max_array_length on arch32 *) 
type 'a t = ('a kind) ref
and 'a kind =
  | Array of 'a array 
	(* | Matrix of 'a array array *)
  | Updated of int * 'a * 'a t

let of_array t = ref (Array t)
      
let warn s =
  if Flags.vm_array_warn () then
    (Printf.fprintf stderr "WARNING %s\n" s; flush stderr)
      
let rec length p =
  match !p with
  | Array t -> Uint31.of_int (Array.length t - 1) (* The default value *)
  | Updated (_, _, p) -> length p
	
let length p = 
  match !p with
  | Array t -> Uint31.of_int (Array.length t - 1)
  | Updated (_, _, p) -> warn "Array.length"; length p
	
let rec get_updated p n =
  match !p with
  | Array t ->
      let l =  Array.length t in
      if 0 <= n && n < l then Array.unsafe_get t n
      else (warn "Array.get: out of bound";Array.unsafe_get t (l-1))
  | Updated (k,e,p) -> if n = k then e else get_updated p n
      
let get p n =
  let n = Uint31.to_int n in
  match !p with
  | Array t ->
      let l = Array.length t in
      if 0 <= n && n < l then Array.unsafe_get t n
      else (warn "Array.get: out of bound";Array.unsafe_get t (l-1))
  | Updated _ -> warn "Array.get";get_updated p n
	
let set p n e =
  let kind = !p in
  let n = Uint31.to_int n in
  match kind with
  | Array t ->
      if 0 <= n && n < Array.length t - 1 then
	let res = ref kind in
	p := Updated (n, Array.unsafe_get t n, res);
	Array.unsafe_set t n e;
	res
      else (warn "Array.set: out of bound"; p)
  | Updated _ ->
      warn "Array.set";
      if 0 <= n && n < Uint31.to_int (length p) then
	ref (Updated(n, e, p))   
      else (warn "Array.set: out of bound"; p)
	  
let rec default_updated p =
  match !p with
  | Array t -> Array.unsafe_get t (Array.length t - 1)
  | Updated (_,_,p) -> default_updated p
	
let default p =
  match !p with
  | Array t -> Array.unsafe_get t (Array.length t - 1)
  | Updated (_,_,p) -> warn "Array.default";default_updated p
	
let make n def = 
  let n = Uint31.to_int n in
  let n = 
    if 0 <= n && n < max_array_length32 then n + 1 
    else max_array_length32 in
  ref (Array (Array.make n def))
	
let init n f def =
  let n = Uint31.to_int n in
  let n = 
    if 0 <= n && n < max_array_length32 then n + 1 
    else max_array_length32 in
  let t = Array.make n def in
  for i = 0 to n - 2 do t.(i) <- f i done;
  ref (Array t)
    
let rec copy_updated p =
  match !p with
  | Array t -> Array.copy t
  | Updated (n,e,p) -> 
      let t = copy_updated p in 
      Array.unsafe_set t n e; t 
	
let copy p =
  let t = 
    match !p with
    | Array t -> Array.copy t
    | Updated _ -> warn "Array.copy"; copy_updated p in
  ref (Array t)
    
let rec rerootk t k = 
  match !t with
  | Array _ -> k ()
  | Updated (i, v, t') -> 
      let k' () =
	begin match !t' with
	| Array a as n ->
	    let v' = a.(i) in
	    a.(i) <- v;
	    t := n;
	    t' := Updated (i, v', t)
	| Updated _ -> assert false 
	end; k() in
      rerootk t' k'
	
let reroot t = rerootk t (fun () -> t)
    
let map f p =
  match !p with
  | Array t -> ref (Array (Array.map f t))
  | _ ->
      let len = Uint31.to_int (length p) in
      ref (Array 
	     (Array.init (len + 1) 
		(fun i -> f (get p (Uint31.of_int i)))))
	
