open Term
open Names
open Declarations
open Util
open Nativevalues
open Nativelambda
open Pre_env
open Sign

(*s Local names *)

type lname = { lname : name; luid : int }

let dummy_lname = { lname = Anonymous; luid = -1 }

module LNord = 
  struct 
    type t = lname 
    let compare l1 l2 = l1.luid - l2.luid
  end
module LNmap = Map.Make(LNord)
module LNset = Set.Make(LNord)

let lname_ctr = ref (-1)

let reset_lname = lname_ctr := -1

let fresh_lname n = 
  incr lname_ctr;
  { lname = n; luid = !lname_ctr }

(*s Global names *)
type gname = 
  | Gind of inductive
  | Gconstruct of constructor
  | Gconstant of constant
  | Gcase of label option * int
  | Gpred of label option * int
  | Gfixtype of label option * int
  | Gnorm of label option * int
  | Gnormtbl of label option * int
  | Ginternal of string
  | Gval of label option * int
  | Grel of int
  | Gnamed of identifier

let gname_of_con c =
  Gconstant c

let case_ctr = ref (-1)

let reset_gcase () = case_ctr := -1

let fresh_gcase l =
  incr case_ctr;
  Gcase (l,!case_ctr)

let pred_ctr = ref (-1)

let reset_gpred () = pred_ctr := -1

let fresh_gpred l = 
  incr pred_ctr;
  Gpred (l,!pred_ctr)

let fixtype_ctr = ref (-1)

let reset_gfixtype () = fixtype_ctr := -1

let fresh_gfixtype l =
  incr fixtype_ctr;
  Gfixtype (l,!fixtype_ctr)

let norm_ctr = ref (-1)

let reset_norm () = norm_ctr := -1

let fresh_gnorm l =
  incr norm_ctr;
  Gnorm (l,!norm_ctr)

let normtbl_ctr = ref (-1)

let reset_normtbl () = normtbl_ctr := -1

let fresh_gnormtbl l =
  incr normtbl_ctr;
  Gnormtbl (l,!normtbl_ctr)

let val_ctr = ref (-1)

let reset_gval () = val_ctr := -1

let fresh_gval l =
  incr val_ctr;
  Gval (l,!val_ctr)
(*s Mllambda *)
  
type primitive =
  | Mk_prod of name
  | Mk_sort of sorts
  | Mk_ind of inductive
  | Mk_const of constant
  | Mk_sw of annot_sw
  | Mk_fix of rec_pos * int 
  | Mk_cofix of int
  | Mk_rel of int
  | Mk_var of identifier
  | Is_accu
  | Is_int
  | Is_array
  | Cast_accu
  | Upd_cofix
  | Force_cofix
  | Val_to_int
  | Val_of_int
  (* Coq primitive with check *)
  | Chead0 of constant option
  | Ctail0 of constant option
  | Cadd of constant option
  | Csub of constant option
  | Cmul of constant option
  | Cdiv of constant option
  | Crem of constant option
  | Clsr of constant option
  | Clsl of constant option
  | Cand of constant option
  | Cor of constant option
  | Cxor of constant option
  | Caddc of constant option
  | Csubc of constant option
  | CaddCarryC of constant option
  | CsubCarryC of constant option
  | Cmulc of constant option
  | Cdiveucl of constant option
  | Cdiv21 of constant option
  | CaddMulDiv of constant option
  | Ceq of constant option
  | Clt of constant option
  | Cle of constant option
  | Clt_b 
  | Cle_b
  | Ccompare of constant option
  | Cprint of constant option
  | Carraymake of constant option
  | Carrayget of constant option
  | Carraydefault of constant option
  | Carrayset of constant option
  | Carraycopy of constant option
  | Carrayreroot of constant option
  | Carraylength of constant option
  | Carrayinit of constant option
  | Carraymap of constant option
  (* Caml primitive *)
  | MLand
  | MLle
  | MLlt
  | MLinteq
  | MLlsl
  | MLlsr
  | MLland
  | MLlor
  | MLlxor
  | MLadd
  | MLsub
  | MLmul

type mllambda =
  | MLlocal        of lname 
  | MLglobal       of gname 
  | MLprimitive    of primitive
  | MLlam          of lname array * mllambda 
  | MLletrec       of (lname * lname array * mllambda) array * mllambda
  | MLlet          of lname * mllambda * mllambda
  | MLapp          of mllambda * mllambda array
  | MLif           of mllambda * mllambda * mllambda
  | MLmatch        of annot_sw * mllambda * mllambda * mllam_branches
                               (* argument, accu branch, branches *)
  | MLconstruct    of constructor * mllambda array
  | MLint          of bool * int   (* true if the type sould be int *)
  | MLparray       of mllambda array
  | MLval          of Nativevalues.t
  | MLsetref       of string * mllambda
  | MLsequence     of mllambda * mllambda

and mllam_branches = ((constructor * lname option array) list * mllambda) array

let fv_lam l =
  let rec aux l bind fv =
    match l with
    | MLlocal l ->
	if LNset.mem l bind then fv else LNset.add l fv
    | MLglobal _ | MLprimitive _  | MLint _   | MLval _ -> fv
    | MLlam (ln,body) ->
	let bind = Array.fold_right LNset.add ln bind in
	aux body bind fv
    | MLletrec(bodies,def) ->
	let bind = 
	  Array.fold_right (fun (id,_,_) b -> LNset.add id b) bodies bind in
	let fv_body (_,ln,body) fv =
	  let bind = Array.fold_right LNset.add ln bind in
	  aux body bind fv in
	Array.fold_right fv_body bodies (aux def bind fv)
    | MLlet(l,def,body) ->
	aux body (LNset.add l bind) (aux def bind fv)
    | MLapp(f,args) ->
	let fv_arg arg fv = aux arg bind fv in
	Array.fold_right fv_arg args (aux f bind fv)
    | MLif(t,b1,b2) ->
	aux t bind (aux b1 bind (aux b2 bind fv))
    | MLmatch(_,a,p,bs) ->
      let fv = aux a bind (aux p bind fv) in
      let fv_bs (cargs, body) fv =
	let bind = 
	  List.fold_right (fun (_,args) bind ->
	    Array.fold_right 
	      (fun o bind -> match o with 
	      | Some l -> LNset.add l bind 
	      | _ -> bind) args bind) 
	    cargs bind in
	aux body bind fv in
      Array.fold_right fv_bs bs fv
          (* argument, accu branch, branches *)
    | MLconstruct (_,p) | MLparray p -> 
	Array.fold_right (fun a fv -> aux a bind fv) p fv
    | MLsetref(_,l) -> aux l bind fv
    | MLsequence(l1,l2) -> aux l1 bind (aux l2 bind fv) in
  aux l LNset.empty LNset.empty


let mkMLlam params body =
  if Array.length params = 0 then body 
  else
    match body with
    | MLlam (params', body) -> MLlam(Array.append params params', body)
    | _ -> MLlam(params,body)

let mkMLapp f args =
  if Array.length args = 0 then f
  else
    match f with
    | MLapp(f,args') -> MLapp(f,Array.append args' args)
    | _ -> MLapp(f,args)

let empty_params = [||]

let decompose_MLlam c =
  match c with
  | MLlam(ids,c) -> ids,c
  | _ -> empty_params,c

(*s Global declaration *)
type global =
(*  | Gtblname of gname * identifier array *)
  | Gtblnorm of gname * lname array * mllambda array 
  | Gtblfixtype of gname * lname array * mllambda array
  | Glet of gname * mllambda
  | Gletcase of 
      gname * lname array * annot_sw * mllambda * mllambda * mllam_branches
  | Gopen of string
  | Gtype of inductive * int array
    (* ind name, arities of constructors *)
  | Gletval of gname * Nativevalues.t
  
let global_stack = ref ([] : global list)

let push_global_let gn body =
  global_stack := Glet(gn,body) :: !global_stack

let push_global_fixtype gn params body =
  global_stack := Gtblfixtype(gn,params,body) :: !global_stack

let push_global_norm name params body =
  global_stack := Gtblnorm(name, params, body)::!global_stack

let push_global_case name params annot a accu bs =
  global_stack := Gletcase(name,params, annot, a, accu, bs)::!global_stack

let push_global_val name v =
  global_stack := Gletval(name,v)::!global_stack

(*s Compilation environment *)

type env =
    { env_rel : mllambda list; (* (MLlocal lname) list *)
      env_bound : int; (* length of env_rel *)
      (* free variables *)
      env_urel : (int * mllambda) list ref; (* list of unbound rel *)
      env_named : (identifier * mllambda) list ref }

let empty_env () =
  { env_rel = [];
    env_bound = 0;
    env_urel = ref [];
    env_named = ref []
  }

let push_rel env id = 
  let local = fresh_lname id in
  local, { env with 
	   env_rel = MLlocal local :: env.env_rel;
	   env_bound = env.env_bound + 1
	 }

let push_rels env ids =
  let lnames, env_rel = 
    Array.fold_left (fun (names,env_rel) id ->
      let local = fresh_lname id in
      (local::names, MLlocal local::env_rel)) ([],env.env_rel) ids in
  Array.of_list (List.rev lnames), { env with 
			  env_rel = env_rel;
			  env_bound = env.env_bound + Array.length ids
			}

let get_rel env id i =
  if i <= env.env_bound then
    List.nth env.env_rel (i-1)
  else 
    let i = i - env.env_bound in
    try List.assoc i !(env.env_urel)
    with Not_found ->
      let local = MLlocal (fresh_lname id) in
      env.env_urel := (i,local) :: !(env.env_urel);
      local

let get_var env id =
  try List.assoc id !(env.env_named)
  with Not_found ->
    let local = MLlocal (fresh_lname (Name id)) in
    env.env_named := (id, local)::!(env.env_named);
    local
   
(*s Traduction of lambda to mllambda *)

let get_prod_name codom = 
  match codom with
  | MLlam(ids,_) -> ids.(0).lname
  | _ -> assert false

let empty_params = [||]

let get_name (_,l) = 
  match l with
  | MLlocal id -> id
  | _ -> raise (Invalid_argument "Nativecode.get_name")

let fv_params env = 
  let fvn, fvr = !(env.env_named), !(env.env_urel) in 
  let size = List.length fvn + List.length fvr in
  if size = 0 then empty_params 
  else begin
    let params = Array.make size dummy_lname in
    let fvn = ref fvn in
    let i = ref 0 in
    while !fvn <> [] do
      params.(!i) <- get_name (List.hd !fvn);
      fvn := List.tl !fvn;
      incr i
    done;
    let fvr = ref fvr in
    while !fvr <> [] do
      params.(!i) <- get_name (List.hd !fvr);
      fvr := List.tl !fvr;
      incr i
    done;
    params
  end

let generalize_fv env body = 
  mkMLlam (fv_params env) body

let empty_args = [||]

let fv_args env fvn fvr =
  let size = List.length fvn + List.length fvr in
  if size = 0 then empty_args 
  else 
    begin
      let args = Array.make size (MLint (false,0)) in
      let fvn = ref fvn in
      let i = ref 0 in
      while !fvn <> [] do
	args.(!i) <- get_var env (fst (List.hd !fvn));
	fvn := List.tl !fvn;
	incr i
      done;
      let fvr = ref fvr in
      while !fvr <> [] do
	let (k,_ as kml) = List.hd !fvr in
	let n = get_name kml in 
	args.(!i) <- get_rel env n.lname k;
	fvr := List.tl !fvr;
	incr i
      done;
      args
    end

type rlist =
  | Rnil 
  | Rcons of (constructor * lname option array) list ref * LNset.t * mllambda * rlist' 
and rlist' = rlist ref

let rm_params fv params = 
  Array.map (fun l -> if LNset.mem l fv then Some l else None) params 

let rec insert cargs body rl =
 match !rl with
 | Rnil ->
     let fv = fv_lam body in
     let (c,params) = cargs in
     let params = rm_params fv params in
     rl:= Rcons(ref [(c,params)], fv, body, ref Rnil)
 | Rcons(l,fv,body',rl) ->
     if body = body' then 
       let (c,params) = cargs in
       let params = rm_params fv params in
       l := (c,params)::!l
     else insert cargs body rl

let rec to_list rl =
  match !rl with
  | Rnil -> []
  | Rcons(l,_,body,tl) -> (!l,body)::to_list tl

let merge_branches t =
  let newt = ref Rnil in
  Array.iter (fun (c,args,body) -> insert (c,args) body newt) t;
  Array.of_list (to_list newt)

let mlprim_of_prim p o =
  match p with
  | Native.Int31head0       -> Chead0 o
  | Native.Int31tail0       -> Ctail0 o
  | Native.Int31add         -> Cadd o
  | Native.Int31sub         -> Csub o
  | Native.Int31mul         -> Cmul o
  | Native.Int31div         -> Cdiv o
  | Native.Int31mod         -> Crem o
  | Native.Int31lsr         -> Clsr o
  | Native.Int31lsl         -> Clsl o
  | Native.Int31land        -> Cand o
  | Native.Int31lor         -> Cor o
  | Native.Int31lxor        -> Cxor o
  | Native.Int31addc        -> Caddc o
  | Native.Int31subc        -> Csubc o
  | Native.Int31addCarryC   -> CaddCarryC o
  | Native.Int31subCarryC   -> CsubCarryC o
  | Native.Int31mulc        -> Cmulc o
  | Native.Int31diveucl     -> Cdiveucl o
  | Native.Int31div21       -> Cdiv21 o
  | Native.Int31addMulDiv   -> CaddMulDiv o
  | Native.Int31eq          -> Ceq o
  | Native.Int31lt          -> Clt o
  | Native.Int31le          -> Cle o
  | Native.Int31compare     -> Ccompare o
  | Native.Int31eqb_correct -> assert false
      
let mlprim_of_cprim p kn =
  match p with
  | Native.Int31print      -> Cprint (Some kn)
  | Native.ArrayMake       -> Carraymake (Some kn)
  | Native.ArrayGet        -> Carrayget (Some kn)
  | Native.ArrayGetdefault -> Carraydefault (Some kn)
  | Native.ArraySet        -> Carrayset (Some kn)
  | Native.ArrayCopy       -> Carraycopy (Some kn)
  | Native.ArrayReroot     -> Carrayreroot (Some kn)
  | Native.ArrayLength     -> Carraylength (Some kn)
  | Native.ArrayInit       -> Carrayinit (Some kn)
  | Native.ArrayMap        -> Carraymap (Some kn)

type prim_aux = 
  | PAprim of constant option * Native.prim_op * prim_aux array
  (*| PAcprim of constant * Native.caml_prim * prim_aux array *)
  | PAml of mllambda

let add_check cond args =
  let aux cond a = 
    match a with
    | PAml(MLint _ | MLval _) -> cond
    | PAml ml -> if List.mem ml cond then cond else ml::cond 
    | _ -> cond
  in
  Array.fold_left aux cond args
  
let extract_prim ml_of l =
  let decl = ref [] in
  let cond = ref [] in
  let rec aux l = 
    match l with
    | Lprim(o,p,args) ->
	assert (p <> Native.Int31eqb_correct);
	let args = Array.map aux args in
	if o <> None then cond := add_check !cond args;
	PAprim(o,p,args)
    | Lrel _ | Lvar _ | Lint _ | Lval _ | Lconst _ -> PAml (ml_of l)
    | _ -> 
	let x = fresh_lname Anonymous in
	decl := (x,ml_of l)::!decl;
	PAml (MLlocal x) in
  let res = aux l in
  (!decl, !cond, res)

let app_prim p args = MLapp(MLprimitive p, args)
let select f32 f64 = if Sys.word_size = 64 then f64 else f32

let mk_of_int32 i = i
let mk_of_int64 i = app_prim MLland [|i;MLint(true,0x7FFFFFFF)|]
let mk_of_int = select mk_of_int32 mk_of_int64

let (*rec*) to_int v =
  match v with
  | MLint(false,i) -> MLint(true,i)
  | MLint _ -> v 
(*  | MLapp(MLprimitive (MLlsl |  MLlsr | MLland | MLlor | MLlxor | MLadd | MLsub | MLmul), _) -> v *)
  | MLapp(MLprimitive Val_of_int, t) -> t.(0)
(*  | MLif(e,b1,b2) -> MLif(e,to_int b1, to_int b2) *)
  | _ -> MLapp(MLprimitive Val_to_int, [|v|]) 

let (*rec*) of_int v = 
  match v with
  | MLint(true,i) -> MLint(false,i)
  | MLint _ -> v
  | MLapp(MLprimitive Val_to_int, t) -> t.(0)
(*  | MLif(e,b1,b2) -> MLif(e,of_int b1, of_int b2) *)
  | _ -> MLapp(MLprimitive Val_of_int,[|v|]) 


let check_bound v b1 b2 =
  match v with
  | MLint(_,x) -> if 0 <= x && x < 31 then b1 else b2
  | _ -> 
      let t1 = app_prim MLle [|MLint(true,0); v|] in
      let t2 = app_prim MLlt [|v; MLint(true,31)|] in
      MLif(app_prim MLand [|t1;t2|], b1, b2)
      
let mk_lsl args = 
  mk_of_int (check_bound args.(1) (app_prim MLlsl args) (MLint(true,0)))

let mk_lsr args = 
  (check_bound args.(1) (app_prim MLlsr args) (MLint(true,0)))

let mk_land args = app_prim MLland args
let mk_lor args = app_prim MLlor args
let mk_lxor args = app_prim MLlxor args

let mk_add args = mk_of_int (app_prim MLadd args)
let mk_sub args = mk_of_int (app_prim MLsub args)
let mk_mul args = mk_of_int (app_prim MLmul args)
let mk_inteq args = app_prim MLinteq args
  
let compile_prim decl cond paux =
  let args_to_int args = 
    for i = 0 to Array.length args - 1 do
      args.(i) <- to_int args.(i)
    done;
    args in
  let rec opt_prim_aux paux =
    match paux with
    | PAprim(o, op, args) ->
	let args = Array.map opt_prim_aux args in
	begin match o, op with
	| None, Native.Int31lt -> MLapp(MLprimitive Clt_b, args)
	| None, Native.Int31le -> MLapp(MLprimitive Cle_b, args)
	| _, Native.Int31lsl  -> of_int (mk_lsl (args_to_int args))
	| _, Native.Int31lsr  -> of_int (mk_lsr (args_to_int args))
	| _, Native.Int31land -> of_int (mk_land (args_to_int args))
	| _, Native.Int31lor  -> of_int (mk_lor (args_to_int args))
	| _, Native.Int31lxor -> of_int (mk_lxor (args_to_int args))
	| _, Native.Int31add  -> of_int (mk_add (args_to_int args))
	| _, Native.Int31sub  -> of_int (mk_sub (args_to_int args))
	| _, Native.Int31mul  -> of_int (mk_mul (args_to_int args))
(*	| _, Native.Int31eq -> mk_inteq (args_to_int args) *)
	| _, _ -> MLapp(MLprimitive (mlprim_of_prim op None) ,args) 
	end
    | PAml ml -> ml 
  and naive_prim_aux paux = 
    match paux with
    | PAprim(o, op, args) ->
	MLapp(MLprimitive (mlprim_of_prim op o),Array.map naive_prim_aux args)
    | PAml ml -> ml in

  let compile_cond cond paux = 
    match cond with
    | [] -> opt_prim_aux paux 
    | c1::cond ->
	let cond = 
	  List.fold_left 
	    (fun ml c ->
	      MLapp(MLprimitive MLand, [|ml; MLapp(MLprimitive Is_int,[|c|])|]))
	    (MLapp(MLprimitive Is_int, [|c1|])) cond in
	MLif(cond, opt_prim_aux paux, naive_prim_aux paux) in
  let add_decl decl body =
    List.fold_left (fun body (x,d) -> MLlet(x,d,body)) body decl in
  add_decl decl (compile_cond cond paux)

let compile_cprim kn p args =
  match p with
  | Native.ArrayGet when Array.length args = 3 -> 
      let t = fresh_lname Anonymous in
      let mlt = MLlocal t in
      let i = fresh_lname Anonymous in
      let mli = MLlocal i in
      MLlet(t, args.(1),
      MLlet(i, args.(2),
      MLif (
	    MLapp(MLprimitive MLand,
  		  [|MLapp(MLprimitive Is_int,[|mli|]);
		    MLapp(MLprimitive Is_array,[|mlt|]) |]),
	    MLapp(MLprimitive (Carrayget None),[|mlt;mli|]),
	    MLapp(MLglobal (Gconstant kn),[|args.(0);mlt;mli|]))))
  | Native.ArraySet when Array.length args = 4 -> 
      let t = fresh_lname Anonymous in
      let mlt = MLlocal t in
      let i = fresh_lname Anonymous in
      let mli = MLlocal i in
      let v = fresh_lname Anonymous in
      let mlv = MLlocal v in
      MLlet(t, args.(1),
      MLlet(i, args.(2),
      MLlet(v, args.(3),
      MLif (
	    MLapp(MLprimitive MLand,
  		  [|MLapp(MLprimitive Is_int,[|mli|]);
		    MLapp(MLprimitive Is_array,[|mlt|]) |]),
	    MLapp(MLprimitive (Carrayset None),[|mlt;mli;mlv|]),
	    MLapp(MLglobal (Gconstant kn),[|args.(0);mlt;mli;mlv|])))))
  | _ ->
      MLapp(MLprimitive (mlprim_of_cprim p kn), args)

 
	  


let rec ml_of_lam env l t =
  match t with
  | Lrel(id ,i) -> get_rel env id i
  | Lvar id -> get_var env id
  | Lprod(dom,codom) ->
      let dom = ml_of_lam env l dom in
      let codom = ml_of_lam env l codom in
      let n = get_prod_name codom in
      MLapp(MLprimitive(Mk_prod n), [|dom;codom|])
  | Llam(ids,body) ->
    let lnames,env = push_rels env ids in
    MLlam(lnames, ml_of_lam env l body)
  | Lrec(id,body) ->
      let ids,body = decompose_Llam body in
      let lname, env = push_rel env id in
      let lnames, env = push_rels env ids in
      MLletrec([|lname, lnames, ml_of_lam env l body|], MLlocal lname)
  | Llet(id,def,body) ->
      let def = ml_of_lam env l def in
      let lname, env = push_rel env id in
      let body = ml_of_lam env l body in
      MLlet(lname,def,body)
  | Lapp(f,args) ->
      MLapp(ml_of_lam env l f, Array.map (ml_of_lam env l) args)
  | Lconst c -> MLglobal(Gconstant c)
  | Lprim _ ->
      let decl,cond,paux = extract_prim (ml_of_lam env l) t in
      compile_prim decl cond paux
  | Lcprim (kn,p,args) ->
      compile_cprim kn p (Array.map (ml_of_lam env l) args)
  | Lcase (annot,p,a,bs) ->
      (* let predicate_uid fv_pred = compilation of p 
         let rec case_uid fv a_uid = 
           match a_uid with
           | Accu _ => mk_sw (predicate_uid fv_pred) (case_uid fv) a_uid
           | Ci argsi => compilation of branches 
         compile case = case_uid fv (compilation of a) *)
      (* Compilation of the predicate *)
         (* Remark: if we do not want to compile the predicate we 
            should a least compute the fv, then store the lambda representation
            of the predicate (not the mllambda) *)
      let env_p = empty_env () in
      let pn = fresh_gpred l in
      let mlp = ml_of_lam env_p l p in
      let mlp = generalize_fv env_p mlp in
      let (pfvn,pfvr) = !(env_p.env_named), !(env_p.env_urel) in
      push_global_let pn mlp; 
      (* Compilation of the case *)
      let env_c = empty_env () in
      let a_uid = fresh_lname Anonymous in
      let la_uid = MLlocal a_uid in
      (* compilation of branches *)
      let ml_br (c,params, body) = 
	let lnames, env = push_rels env_c params in
	(c,lnames, ml_of_lam env l body) in
      let bs = Array.map ml_br bs in
      let cn = fresh_gcase l in
      (* Compilation of accu branch *)
      let pred = MLapp(MLglobal pn, fv_args env_c pfvn pfvr) in  
      let (fvn, fvr) = !(env_c.env_named), !(env_c.env_urel) in
      let cn_fv = mkMLapp (MLglobal cn) (fv_args env_c fvn fvr) in
         (* remark : the call to fv_args does not add free variables in env_c *)
      let accu = 
	MLapp(MLprimitive (Mk_sw annot), 
	      [| MLapp (MLprimitive Cast_accu, [|la_uid|]);
		 pred; 
		 cn_fv |]) in
(*      let body = MLlam([|a_uid|], MLmatch(annot, la_uid, accu, bs)) in
      let case = generalize_fv env_c body in *)
      push_global_case cn 
	(Array.append (fv_params env_c) [|a_uid|]) annot la_uid accu (merge_branches bs);

      (* Final result *)
      let arg = ml_of_lam env l a in
      let force =
	if annot.asw_finite then arg
	else MLapp(MLprimitive Force_cofix, [|arg|]) in
      mkMLapp (MLapp (MLglobal cn, fv_args env fvn fvr)) [|force|]
  | Lareint args -> 
      let res = ref (MLapp(MLprimitive Is_int, [|ml_of_lam env l args.(0)|]))in
      for i = 1 to Array.length args - 1 do
	let t = MLapp(MLprimitive Is_int, [|ml_of_lam env l args.(i)|]) in
	res := MLapp(MLprimitive MLand, [|!res;t|])
      done;
      !res
  | Lif(t,bt,bf) -> 
      MLif(ml_of_lam env l t, ml_of_lam env l bt, ml_of_lam env l bf)
  | Lfix ((rec_pos,start), (ids, tt, tb)) ->
      (* let type_f fvt = [| type fix |] 
         let norm_f1 fv f1 .. fn params1 = body1
	 ..
         let norm_fn fv f1 .. fn paramsn = bodyn
         let norm fv f1 .. fn = 
	    [|norm_f1 fv f1 .. fn; ..; norm_fn fv f1 .. fn|]
         compile fix = 
	   let rec f1 params1 = 
             if is_accu rec_pos.(1) then mk_fix (type_f fvt) (norm fv) params1
	     else norm_f1 fv f1 .. fn params1
           and .. and fn paramsn = 
	     if is_accu rec_pos.(n) then mk_fix (type_f fvt) (norm fv) paramsn
             else norm_fn fv f1 .. fv paramsn in
	   start
      *)
      (* Compilation of type *)
      let env_t = empty_env () in
      let ml_t = Array.map (ml_of_lam env_t l) tt in
      let params_t = fv_params env_t in
      let args_t = fv_args env !(env_t.env_named) !(env_t.env_urel) in
      let gft = fresh_gfixtype l in
      push_global_fixtype gft params_t ml_t;
      let mk_type = MLapp(MLglobal gft, args_t) in
      (* Compilation of norm_i *)
      let ndef = Array.length ids in
      let lf,env_n = push_rels (empty_env ()) ids in
      let t_params = Array.make ndef [||] in
      let t_norm_f = Array.make ndef (Gnorm (l,-1)) in
      let ml_of_fix i body =
	let idsi,bodyi = decompose_Llam body in
	let paramsi, envi = push_rels env_n idsi in
	t_norm_f.(i) <- fresh_gnorm l;
	let bodyi = ml_of_lam envi l bodyi in
	t_params.(i) <- paramsi;
	mkMLlam paramsi bodyi in
      let tnorm = Array.mapi ml_of_fix tb in
      let fvn,fvr = !(env_n.env_named), !(env_n.env_urel) in
      let fv_params = fv_params env_n in
      let fv_args' = Array.map (fun id -> MLlocal id) fv_params in
      let norm_params = Array.append fv_params lf in
      Array.iteri (fun i body ->
	push_global_let (t_norm_f.(i)) (mkMLlam norm_params body)) tnorm;
      let norm = fresh_gnormtbl l in
      push_global_norm norm fv_params 
         (Array.map (fun g -> mkMLapp (MLglobal g) fv_args') t_norm_f);
      (* Compilation of fix *)
      let fv_args = fv_args env fvn fvr in      
      let lf, env = push_rels env ids in
      let lf_args = Array.map (fun id -> MLlocal id) lf in
      let mk_norm = MLapp(MLglobal norm, fv_args) in
      let mkrec i lname = 
	let paramsi = t_params.(i) in
	let reci = MLlocal (paramsi.(rec_pos.(i))) in
	let pargsi = Array.map (fun id -> MLlocal id) paramsi in
	let body = 
	  MLif(MLapp(MLprimitive Is_accu,[|reci|]),
	       mkMLapp 
		 (MLapp(MLprimitive (Mk_fix(rec_pos,i)), 
			[|mk_type; mk_norm|]))
		 pargsi,
	       MLapp(MLglobal t_norm_f.(i), 
		     Array.concat [fv_args;lf_args;pargsi])) 
	in
	(lname, paramsi, body) in
      MLletrec(Array.mapi mkrec lf, lf_args.(start))
  | Lcofix (start, (ids, tt, tb)) -> 
      (* Compilation of type *)
      let env_t = empty_env () in
      let ml_t = Array.map (ml_of_lam env_t l) tt in
      let params_t = fv_params env_t in
      let args_t = fv_args env !(env_t.env_named) !(env_t.env_urel) in
      let gft = fresh_gfixtype l in
      push_global_fixtype gft params_t ml_t;
      let mk_type = MLapp(MLglobal gft, args_t) in
      (* Compilation of norm_i *) 
      let ndef = Array.length ids in
      let lf,env_n = push_rels (empty_env ()) ids in
      let t_params = Array.make ndef [||] in
      let t_norm_f = Array.make ndef (Gnorm (l,-1)) in
      let ml_of_fix i body =
	let idsi,bodyi = decompose_Llam body in
	let paramsi, envi = push_rels env_n idsi in
	t_norm_f.(i) <- fresh_gnorm l;
	let bodyi = ml_of_lam envi l bodyi in
	t_params.(i) <- paramsi;
	mkMLlam paramsi bodyi in
      let tnorm = Array.mapi ml_of_fix tb in
      let fvn,fvr = !(env_n.env_named), !(env_n.env_urel) in
      let fv_params = fv_params env_n in
      let fv_args' = Array.map (fun id -> MLlocal id) fv_params in
      let norm_params = Array.append fv_params lf in
      Array.iteri (fun i body ->
	push_global_let (t_norm_f.(i)) (mkMLlam norm_params body)) tnorm;
      let norm = fresh_gnormtbl l in
      push_global_norm norm fv_params 
        (Array.map (fun g -> mkMLapp (MLglobal g) fv_args') t_norm_f);
      (* Compilation of fix *)
      let fv_args = fv_args env fvn fvr in      
      let mk_norm = MLapp(MLglobal norm, fv_args) in
      let lnorm = fresh_lname Anonymous in
      let ltype = fresh_lname Anonymous in
      let lf, env = push_rels env ids in
      let lf_args = Array.map (fun id -> MLlocal id) lf in
      let upd i lname cont =
	let paramsi = t_params.(i) in
	let pargsi = Array.map (fun id -> MLlocal id) paramsi in
	let uniti = fresh_lname Anonymous in
	let body =
	  MLlam(Array.append paramsi [|uniti|],
		MLapp(MLglobal t_norm_f.(i),
		      Array.concat [fv_args;lf_args;pargsi])) in
	MLsequence(MLapp(MLprimitive Upd_cofix, [|lf_args.(i);body|]),
		   cont) in
      let upd = Util.array_fold_right_i upd lf lf_args.(start) in
      let mk_let i lname cont =
	MLlet(lname,
	      MLapp(MLprimitive(Mk_cofix i),[| MLlocal ltype; MLlocal lnorm|]),
	      cont) in
      let init = Util.array_fold_right_i mk_let lf upd in 
      MLlet(lnorm, mk_norm, MLlet(ltype, mk_type, init))
  (*    	    
      let mkrec i lname = 
	let paramsi = t_params.(i) in
	let pargsi = Array.map (fun id -> MLlocal id) paramsi in
	let uniti = fresh_lname Anonymous in
	let body = 
	  MLapp( MLprimitive(Mk_cofix i),
		 [|mk_type;mk_norm; 
		   MLlam([|uniti|],
			 MLapp(MLglobal t_norm_f.(i),
			       Array.concat [fv_args;lf_args;pargsi]))|]) in
	(lname, paramsi, body) in
      MLletrec(Array.mapi mkrec lf, lf_args.(start)) *)
   
  | Lmakeblock (cn,_,args) ->
      MLconstruct(cn,Array.map (ml_of_lam env l) args)
  | Lconstruct cn ->
      MLglobal (Gconstruct cn)
  | Lint i -> MLint (false,Uint31.to_int i)
  | Lparray t -> MLparray(Array.map (ml_of_lam env l) t)
  | Lval v ->
      let gn = fresh_gval l in
      push_global_val gn v;
      MLglobal gn
  | Lsort s -> MLprimitive(Mk_sort s)
  | Lind i -> MLglobal (Gind i)

let mllambda_of_lambda auxdefs l t =
  let env = empty_env () in
  global_stack := auxdefs;
  let ml = ml_of_lam env l t in
  let fv_rel = !(env.env_urel) in
  let fv_named = !(env.env_named) in
  (* build the free variables *)
  let get_name (_,t) = 
   match t with
   | MLlocal x -> x
   | _ -> assert false in
  let params = 
    List.append (List.map get_name fv_rel) (List.map get_name fv_named) in
  if params = [] then
    (!global_stack, ([],[]), ml)
  (* final result : global list, fv, ml *)
  else
    (!global_stack, (fv_named, fv_rel), mkMLlam (Array.of_list params) ml)

let rec compile_with_fv env auxdefs l t =
  let (auxdefs,(fv_named,fv_rel),ml) = mllambda_of_lambda auxdefs l t in
  if fv_named = [] && fv_rel = [] then (auxdefs,ml)
  else apply_fv env (fv_named,fv_rel) auxdefs ml

and apply_fv env (fv_named,fv_rel) auxdefs ml =
  let get_rel_val (n,_) auxdefs =
    match !(lookup_rel_native_val n env) with
    | NVKnone ->
        compile_rel env auxdefs n
    | NVKvalue (v,d) -> assert false
  in
  let get_named_val (id,_) auxdefs =
    match !(lookup_named_native_val id env) with
    | NVKnone ->
        compile_named env auxdefs id
    | NVKvalue (v,d) -> assert false
  in
  let auxdefs = List.fold_right get_rel_val fv_rel auxdefs in
  let auxdefs = List.fold_right get_named_val fv_named auxdefs in
  let lvl = rel_context_length env.env_rel_context in
  let fv_rel = List.map (fun (n,_) -> MLglobal (Grel (lvl-n))) fv_rel in
  let fv_named = List.map (fun (id,_) -> MLglobal (Gnamed id)) fv_named in
  let aux_name = fresh_lname Anonymous in
  auxdefs, MLlet(aux_name, ml, mkMLapp (MLlocal aux_name) (Array.of_list (fv_rel@fv_named)))

and compile_rel env auxdefs n =
  let (_,body,_) = lookup_rel n env.env_rel_context in
  let n = rel_context_length env.env_rel_context - n in
  match body with
  | Some t ->
      let code = lambda_of_constr ~opt:true env t in
      let auxdefs,code = compile_with_fv env auxdefs None code in
      Glet(Grel n, code)::auxdefs
  | None -> 
      Glet(Grel n, MLprimitive (Mk_rel n))::auxdefs

and compile_named env auxdefs id =
  let (_,body,_) = lookup_named id env.env_named_context in
  match body with
  | Some t ->
      let code = lambda_of_constr ~opt:true env t in
      let auxdefs,code = compile_with_fv env auxdefs None code in
      Glet(Gnamed id, code)::auxdefs
  | None -> 
      Glet(Gnamed id, MLprimitive (Mk_var id))::auxdefs



(** Optimization of match and fix *)

let can_subst l = 
  match l with
  | MLlocal _ | MLint _ | MLval _ | MLglobal _ -> true
  | _ -> false

let subst s l =
  if LNmap.is_empty s then l 
  else
    let rec aux l =
      match l with
      | MLlocal id -> (try LNmap.find id s with _ -> l)
      | MLglobal _ | MLprimitive _ | MLint _ | MLval _ -> l
      | MLlam(params,body) -> MLlam(params, aux body)
      | MLletrec(defs,body) ->
	let arec (f,params,body) = (f,params,aux body) in
	MLletrec(Array.map arec defs, aux body)
      | MLlet(id,def,body) -> MLlet(id,aux def, aux body)
      | MLapp(f,args) -> MLapp(aux f, Array.map aux args)
      | MLif(t,b1,b2) -> MLif(aux t, aux b1, aux b2)
      | MLmatch(annot,a,accu,bs) ->
	  let auxb (cargs,body) = (cargs,aux body) in
	  MLmatch(annot,a,aux accu, Array.map auxb bs)
      | MLconstruct(c,args) -> MLconstruct(c,Array.map aux args)
      | MLparray p -> MLparray(Array.map aux p)
      | MLsetref(s,l1) -> MLsetref(s,aux l1) 
      | MLsequence(l1,l2) -> MLsequence(aux l1, aux l2) in  
    aux l

let add_subst id v s =
  match v with
  | MLlocal id' when id.luid = id'.luid -> s
  | _ -> LNmap.add id v s

let subst_norm params args s =
  let len = Array.length params in
  assert (Array.length args = len && Util.array_for_all can_subst args);
  let s = ref s in
  for i = 0 to len - 1 do
    s := add_subst params.(i) args.(i) !s
  done;
  !s

let subst_case params args s =
  let len = Array.length params in
  assert (len > 0 && 
	  Array.length args = len && 
	  let r = ref true and i = ref 0 in
	  (* we test all arguments excepted the last *)
	  while !i < len - 1  && !r do r := can_subst args.(!i); incr i done;
	  !r);
  let s = ref s in
  for i = 0 to len - 2 do
    s := add_subst params.(i) args.(i) !s
  done;
  !s, params.(len-1), args.(len-1)
    
    
let empty_gdef = Intmap.empty, Intmap.empty
let get_norm (gnorm, _) i = Intmap.find i gnorm
let get_case (_, gcase) i = Intmap.find i gcase

let optimize gdef l =   
  let rec optimize s l =
    match l with
    | MLlocal id -> (try LNmap.find id s with _ -> l)
    | MLglobal _ | MLprimitive _ | MLint _ | MLval _ -> l
    | MLlam(params,body) -> 
	MLlam(params, optimize s body)
    | MLletrec(decls,body) ->
	let opt_rec (f,params,body) = (f,params,optimize s body ) in 
	MLletrec(Array.map opt_rec decls, optimize s body)
    | MLlet(id,def,body) ->
	let def = optimize s def in
	if can_subst def then optimize (add_subst id def s) body 
	else MLlet(id,def,optimize s body)
    | MLapp(f, args) ->
	let args = Array.map (optimize s) args in
	begin match f with
	| MLglobal (Gnorm (_,i)) ->
	    (try
	      let params,body = get_norm gdef i in
	      let s = subst_norm params args s in
	      optimize s body	    
	    with Not_found -> MLapp(optimize s f, args))
	| MLglobal (Gcase (_,i)) ->
	    (try 
	      let params,body = get_case gdef i in
	      let s, id, arg = subst_case params args s in
	      if can_subst arg then optimize (add_subst id arg s) body
	      else MLlet(id, arg, optimize s body)
	    with Not_found ->  MLapp(optimize s f, args))
	| _ -> MLapp(optimize s f, args)
	end
    | MLif(t,b1,b2) ->
	let t = optimize s t in
	let b1 = optimize s b1 in
	let b2 = optimize s b2 in
	begin match t, b2 with
	| MLapp(MLprimitive Is_accu,[| l1 |]), MLmatch(annot, l2, _, bs)
	    when l1 = l2 -> MLmatch(annot, l1, b1, bs)
        | _, _ -> MLif(t, b1, b2)
	end
    | MLmatch(annot,a,accu,bs) ->
	let opt_b (cargs,body) = (cargs,optimize s body) in
	MLmatch(annot, optimize s a, subst s accu, Array.map opt_b bs)
    | MLconstruct(c,args) ->
	MLconstruct(c,Array.map (optimize s) args)
    | MLparray p -> MLparray (Array.map (optimize s) p)
    | MLsetref(r,l) -> MLsetref(r, optimize s l) 
    | MLsequence(l1,l2) -> MLsequence(optimize s l1, optimize s l2) in
  optimize LNmap.empty l

let optimize_stk stk =
  let add_global gdef g =
    match g with
    | Glet (Gnorm (_,i), body) ->
	let (gnorm, gcase) = gdef in
	(Intmap.add i (decompose_MLlam body) gnorm, gcase)
    | Gletcase(Gcase (_,i), params, annot,a,accu,bs) ->
	let (gnorm,gcase) = gdef in
	(gnorm, Intmap.add i (params,MLmatch(annot,a,accu,bs)) gcase)
    | Gletcase _ -> assert false
    | _ -> gdef in
  let gdef = List.fold_left add_global empty_gdef stk in
  let optimize_global g = 
    match g with
    | Glet(Gconstant c, body) -> Glet(Gconstant c, optimize gdef body)
    | _ -> g in
  List.map optimize_global stk

(** Printing to ocaml **)
(* Redefine a bunch of functions in module Names to generate names
   acceptable to OCaml. *)
let string_of_dirpath = function
  | [] -> "_"
  | sl -> String.concat "_" (List.map string_of_id (List.rev sl))

(* The first letter of the file name has to be a capital to be accepted by *)
(* OCaml as a module identifier.                                           *)
let string_of_dirpath s = "N"^string_of_dirpath s

let mod_uid_of_dirpath dir = string_of_dirpath (repr_dirpath dir)

let string_of_name x =
  match x with
    | Anonymous -> "anonymous" (* assert false *)
    | Name id -> string_of_id id

let string_of_label_def l =
  match l with
    | None -> ""
    | Some l -> string_of_label l

(* Relativization of module paths *)
let rec list_of_mp acc = function
  | MPdot (mp,l) -> list_of_mp (string_of_label l::acc) mp
  | MPfile dp ->
      let dp = repr_dirpath dp in
      string_of_dirpath dp :: acc
  | MPbound mbid -> ("X"^string_of_label (label_of_mbid mbid))::acc

let rec head_of_mp x = match x with
  | MPdot (mp,l) -> head_of_mp mp
  | _ -> x

let list_of_mp mp = list_of_mp [] mp

let string_of_kn kn =
  let (mp,dp,l) = repr_kn kn in
  let mp = list_of_mp mp in
  String.concat "_" mp ^ "_" ^ string_of_label l

let string_of_con c = string_of_kn (canonical_con c)
let string_of_mind mind = string_of_kn (canonical_mind mind)

let rec strip_common_prefix l1 l2 =
  match l1, l2 with
  | [], _
  | _, [] -> l1, l2
  | hd1::tl1, hd2::tl2 ->
      if hd1 = hd2 then strip_common_prefix tl1 tl2 else hd1::tl1, hd2::tl2

let mk_relative_id base_mp (mp,id) =
  let base_h = head_of_mp base_mp in
  let h = head_of_mp mp in
  match base_h, h with
    | MPfile dp1, MPfile dp2 when not (dp1 = dp2) ->
        let dp = repr_dirpath dp2 in
        string_of_dirpath dp ^ "." ^ id
    | _ -> id

let relative_list_of_mp base_mp mp =
  let base_l = list_of_mp base_mp in
  let l = list_of_mp mp in
  snd (strip_common_prefix base_l l)

let pp_gname base_mp fmt g =
  let relativize =
    match base_mp with
    | Some mp -> mk_relative_id mp
    | None -> snd
  in
  match g with
  | Gind (mind,i) ->
      let (mp,dp,l) = repr_kn (canonical_mind mind) in
      let id = Format.sprintf "indaccu_%s_%i" (string_of_mind mind) i in
      Format.fprintf fmt "%s" (relativize (mp,id))
  | Gconstruct ((mind,i),j) ->
      let (mp,dp,l) = repr_kn (canonical_mind mind) in
      let id = Format.sprintf "construct_%s_%i_%i" (string_of_mind mind) i (j-1) in
      Format.fprintf fmt "%s" (relativize (mp,id))
  | Gconstant c ->
      let (mp,dp,l) = repr_kn (canonical_con c) in 
      let id = Format.sprintf "const_%s" (string_of_con c) in
      Format.fprintf fmt "%s" (relativize (mp,id))
  | Gcase (l,i) ->
      Format.fprintf fmt "case_%s_%i" (string_of_label_def l) i
  | Gpred (l,i) ->
      Format.fprintf fmt "pred_%s_%i" (string_of_label_def l) i
  | Gfixtype (l,i) ->
      Format.fprintf fmt "fixtype_%s_%i" (string_of_label_def l) i
  | Gnorm (l,i) ->
      Format.fprintf fmt "norm_%s_%i" (string_of_label_def l) i
  | Ginternal s -> Format.fprintf fmt "%s" s
  | Gnormtbl (l,i) -> 
      Format.fprintf fmt "normtbl_%s_%i" (string_of_label_def l) i
  | Gval (l,i) -> 
      Format.fprintf fmt "val_%s_%i" (string_of_label_def l) i
  | Grel i ->
      Format.fprintf fmt "rel_%i" i
  | Gnamed id ->
      Format.fprintf fmt "named_%s" (string_of_id id)

(*let pp_rel cenv id fmt i =
  assert (i>0);
  let lvl = cenv.env_bound - i in
  match List.nth cenv.env_rel (i-1) with
    | MLlocal id' ->
      assert (id == id');
      let s = string_of_name id.lname in
      Format.fprintf fmt "r_%i_%s" lvl s
    | _ -> assert false*)

let pp_lname fmt ln =
  let s = ascii_of_ident (string_of_name ln.lname) in
  Format.fprintf fmt "x_%s_%i" s ln.luid



let pp_ldecls fmt ids =
  let len = Array.length ids in
  for i = 0 to len - 1 do
    Format.fprintf fmt " (%a : Nativevalues.t)" pp_lname ids.(i)
  done

let string_of_construct base_mp ((mind,i),j) =
  let (mp,dp,l) = repr_kn (canonical_mind mind) in
  let id = Format.sprintf "Construct_%s_%i_%i" (string_of_mind mind) i (j-1) in
  (mk_relative_id base_mp (mp,id))
   
let pp_int fmt i =
  if i < 0 then Format.fprintf fmt "(%i)" i else Format.fprintf fmt "%i" i

let pp_mllam base_mp fmt l =

  let rec pp_mllam fmt l =
    match l with
    | MLlocal ln -> Format.fprintf fmt "@[%a@]" pp_lname ln
    | MLglobal g -> Format.fprintf fmt "@[%a@]" (pp_gname (Some base_mp)) g
    | MLprimitive p -> Format.fprintf fmt "@[%a@]" pp_primitive p
    | MLlam(ids,body) ->
	Format.fprintf fmt "@[(fun%a@ ->@\n %a)@]"
	  pp_ldecls ids pp_mllam body
    | MLletrec(defs, body) ->
	Format.fprintf fmt "@[%a@ in@\n%a@]" pp_letrec defs 
	  pp_mllam body
    | MLlet(id,def,body) ->
	Format.fprintf fmt "@[(let@ %a@ =@\n %a@ in@\n%a)@]"
          pp_lname id pp_mllam def pp_mllam body
    | MLapp(f, args) ->
	Format.fprintf fmt "@[%a@ %a@]" pp_mllam f (pp_args true) args
    | MLif(t,l1,l2) ->
	Format.fprintf fmt "@[(if %a then@\n  %a@\nelse@\n  %a)@]"
	  pp_mllam t pp_mllam l1 pp_mllam l2 
    | MLmatch (asw, c, accu_br, br) ->
	let mind,i = asw.asw_ind in
	let (mp,dp,l) = repr_kn (canonical_mind mind) in
	let accu = Format.sprintf "Accu_%s_%i" (string_of_mind mind) i in
	let accu = mk_relative_id base_mp (mp,accu) in
	Format.fprintf fmt 
	  "@[begin match Obj.magic (%a) with@\n| %s _ ->@\n  %a@\n%aend@]"
	  pp_mllam c accu pp_mllam accu_br pp_branches br
	  
    | MLconstruct(c,args) ->
	Format.fprintf fmt "@[(Obj.magic (%s%a) : Nativevalues.t)@]" 
	  (string_of_construct base_mp c) pp_cargs args
    | MLint(int, i) ->
	if int then pp_int fmt i
	else Format.fprintf fmt "(val_of_int %a)" pp_int i
    | MLparray p ->
	Format.fprintf fmt "@[(parray_of_array@\n  [|";
	for i = 0 to Array.length p - 2 do
	  Format.fprintf fmt "%a;" pp_mllam p.(i)
	done;
	Format.fprintf fmt "%a|])@]" pp_mllam p.(Array.length p - 1)
    | MLval v -> Format.fprintf fmt "(str_decode \"%s\")" (str_encode v)
    | MLsetref (s, body) ->
	Format.fprintf fmt "@[%s@ :=@\n %a@]" s pp_mllam body
    | MLsequence(l1,l2) ->
	Format.fprintf fmt "@[%a;@\n%a@]" pp_mllam l1 pp_mllam l2 

  and pp_letrec fmt defs =
    let len = Array.length defs in
    let pp_one_rec i (fn, argsn, body) =
      Format.fprintf fmt "%a%a =@\n  %a"
	pp_lname fn 
	pp_ldecls argsn pp_mllam body in
    Format.fprintf fmt "@[let rec ";
    pp_one_rec 0 defs.(0);
    for i = 1 to len - 1 do
      Format.fprintf fmt "@\nand ";
      pp_one_rec i defs.(i)
    done;

  and pp_blam fmt l =
    match l with
    | MLprimitive (Mk_prod _ | Mk_sort _) 
    | MLlam _ | MLletrec _ | MLlet _ | MLapp _ | MLif _ ->
	Format.fprintf fmt "(%a)" pp_mllam l
    | MLconstruct(_,args) when Array.length args > 0 ->
	Format.fprintf fmt "(%a)" pp_mllam l
    | _ -> pp_mllam fmt l

  and pp_args sep fmt args =
    let sep = if sep then " " else "," in
    let len = Array.length args in
    if len > 0 then begin
      Format.fprintf fmt "%a" pp_blam args.(0);
      for i = 1 to len - 1 do
	Format.fprintf fmt "%s%a" sep pp_blam args.(i)
      done
    end 

  and pp_cargs fmt args =
    let len = Array.length args in
    match len with
    | 0 -> ()
    | 1 -> Format.fprintf fmt " %a" pp_blam args.(0)
    | _ -> Format.fprintf fmt "(%a)" (pp_args false) args

  and pp_cparam fmt param = 
    match param with
    | Some l -> pp_mllam fmt (MLlocal l)
    | None -> Format.fprintf fmt "_"

  and pp_cparams fmt params =
    let len = Array.length params in
    match len with
    | 0 -> ()
    | 1 -> Format.fprintf fmt " %a" pp_cparam params.(0)
    | _ -> 
	let aux fmt params =
	  Format.fprintf fmt "%a" pp_cparam params.(0);
	  for i = 1 to len - 1 do
	    Format.fprintf fmt ",%a" pp_cparam params.(i)
	  done in 
	Format.fprintf fmt "(%a)" aux params

  and pp_branches fmt bs =
    let pp_branch (cargs,body) =
      let pp_c fmt (cn,args) = 
	Format.fprintf fmt "| %s%a " 
	  (string_of_construct base_mp cn) pp_cparams args in
      let rec pp_cargs fmt cargs =
	match cargs with
	| [] -> ()
	| cargs::cargs' -> 
	    Format.fprintf fmt "%a%a" pp_c cargs pp_cargs cargs' in
      Format.fprintf fmt "%a ->@\n  %a@\n" 
	pp_cargs cargs pp_mllam body
    in
    Array.iter pp_branch bs

  and pp_vprim o s = 
    match o with
    | None -> Format.fprintf fmt "no_check_%s" s
    | Some kn -> Format.fprintf fmt "%s %a" s pp_mllam (MLglobal (Gconstant kn))

  and pp_primitive fmt = function
    | Mk_prod id -> Format.fprintf fmt "mk_prod_accu (str_decode \"%s\")" 
	  (str_encode id)
    | Mk_sort s -> 
	Format.fprintf fmt "mk_sort_accu (str_decode \"%s\")" (str_encode s)
    | Mk_ind ind -> 
	Format.fprintf fmt "mk_ind_accu (str_decode \"%s\")" (str_encode ind)
    | Mk_const kn -> 
	Format.fprintf fmt 
	  "mk_constant_accu (str_decode \"%s\")" (str_encode kn)
    | Mk_sw asw -> 
	Format.fprintf fmt "mk_sw_accu (str_decode \"%s\")" (str_encode asw)
    | Mk_fix(rec_pos,start) -> 
	let pp_rec_pos fmt rec_pos = 
	  Format.fprintf fmt "@[[| %i" rec_pos.(0);
	  for i = 1 to Array.length rec_pos - 1 do
	    Format.fprintf fmt "; %i" rec_pos.(i) 
	  done;
	  Format.fprintf fmt " |]@]" in
	Format.fprintf fmt "mk_fix_accu %a %i" pp_rec_pos rec_pos start
    | Mk_cofix(start) -> Format.fprintf fmt "mk_cofix_accu %i" start
    | Mk_rel i -> Format.fprintf fmt "mk_rel_accu %i" i
    | Mk_var id ->
        Format.fprintf fmt "mk_var_accu (Names.id_of_string \"%s\")" (string_of_id id)
    | Is_accu -> Format.fprintf fmt "is_accu"
    | Is_int -> Format.fprintf fmt "is_int"
    | Is_array -> Format.fprintf fmt "is_parray"
    | Cast_accu -> Format.fprintf fmt "cast_accu"
    | Upd_cofix -> Format.fprintf fmt "upd_cofix"
    | Force_cofix -> Format.fprintf fmt "force_cofix"
    | Val_to_int -> Format.fprintf fmt "val_to_int"
    | Val_of_int -> Format.fprintf fmt "val_of_int"
    | Chead0 o -> pp_vprim o "head0" 
    | Ctail0 o -> pp_vprim o "tail0"
    | Cadd o -> pp_vprim o "add"
    | Csub o -> pp_vprim o "sub"
    | Cmul o -> pp_vprim o "mul"
    | Cdiv o -> pp_vprim o "div"
    | Crem o -> pp_vprim o "rem"
    | Clsr o -> pp_vprim o "l_sr"
    | Clsl o -> pp_vprim o "l_sl"
    | Cand o -> pp_vprim o "l_and"
    | Cor o -> pp_vprim o "l_or"
    | Cxor o -> pp_vprim o "l_xor"
    | Caddc o -> pp_vprim o "addc"
    | Csubc o -> pp_vprim o "subc"
    | CaddCarryC o -> pp_vprim o "addCarryC"
    | CsubCarryC o -> pp_vprim o "subCarryC"
    | Cmulc o -> pp_vprim o "mulc"
    | Cdiveucl o -> pp_vprim o "diveucl"
    | Cdiv21 o -> pp_vprim o "div21"
    | CaddMulDiv o -> pp_vprim o "addMulDiv"
    | Ceq o -> pp_vprim o "eq"
    | Clt o -> pp_vprim o "lt"
    | Cle o -> pp_vprim o "le"
    | Clt_b  -> Format.fprintf fmt "lt_b"
    | Cle_b -> Format.fprintf fmt "le_b"
    | Ccompare o -> pp_vprim o "compare"
    | Cprint o -> pp_vprim o "print"
    | Carraymake o -> pp_vprim o "arraymake"
    | Carrayget o -> pp_vprim o "arrayget"
    | Carraydefault o -> pp_vprim o "arraydefault"
    | Carrayset o -> pp_vprim o "arrayset"
    | Carraycopy o -> pp_vprim o "arraycopy"
    | Carrayreroot o -> pp_vprim o "arrayreroot"
    | Carraylength o -> pp_vprim o "arraylength"
    | Carrayinit o -> pp_vprim o "arrayinit"
    | Carraymap o -> pp_vprim o "arraymap"
	  (* Caml primitive *)
    | MLand -> Format.fprintf fmt "(&&)"
    | MLle -> Format.fprintf fmt "(<=)"
    | MLlt -> Format.fprintf fmt "(<)"
    | MLinteq -> Format.fprintf fmt "(==)"
    | MLlsl -> Format.fprintf fmt "(lsl)"
    | MLlsr -> Format.fprintf fmt "(lsr)"
    | MLland -> Format.fprintf fmt "(land)"
    | MLlor -> Format.fprintf fmt "(lor)"
    | MLlxor -> Format.fprintf fmt "(lxor)"
    | MLadd -> Format.fprintf fmt "(+)"
    | MLsub -> Format.fprintf fmt "(-)"
    | MLmul -> Format.fprintf fmt "( * )"
    

  in
  Format.fprintf fmt "@[%a@]" pp_mllam l
  

let pp_array base_mp fmt t =
  let len = Array.length t in
  Format.fprintf fmt "@[[|";
  for i = 0 to len - 2 do
    Format.fprintf fmt "%a; " (pp_mllam base_mp) t.(i)
  done;
  if len > 0 then
    Format.fprintf fmt "%a" (pp_mllam base_mp) t.(len - 1);
  Format.fprintf fmt "|]@]"
  
let pp_global base_mp fmt g =
  match g with
  | Glet (gn, c) ->
      let ids, c = decompose_MLlam c in
      Format.fprintf fmt "@[let %a%a =@\n  %a@]@\n@." (pp_gname None) gn 
	pp_ldecls ids
	(pp_mllam base_mp) c
  | Gopen s ->
      Format.fprintf fmt "@[open %s@]@." s
  | Gtype ((mind, i), lar) ->
      let (_,_,l) = repr_kn (canonical_mind mind) in
      let l = string_of_mind mind in
      let rec aux s ar = 
	if ar = 0 then s else aux (s^" * Nativevalues.t") (ar-1) in
      let pp_const_sig i fmt j ar =
        let sig_str = if ar > 0 then aux "of Nativevalues.t" (ar-1) else "" in
        Format.fprintf fmt "  | Construct_%s_%i_%i %s@\n" l i j sig_str
      in
      let pp_const_sigs i fmt lar =
        Format.fprintf fmt "  | Accu_%s_%i of Nativevalues.t@\n" l i;
        Array.iteri (pp_const_sig i fmt) lar
      in
      Format.fprintf fmt "@[type ind_%s_%i =@\n%a@]@\n@." l i (pp_const_sigs i) lar
  | Gtblfixtype (g, params, t) ->
      Format.fprintf fmt "@[let %a %a =@\n  %a@]@\n@." (pp_gname None) g
	pp_ldecls params (pp_array base_mp) t
  | Gtblnorm (g, params, t) ->
      Format.fprintf fmt "@[let %a %a =@\n  %a@]@\n@." (pp_gname None) g
	pp_ldecls params (pp_array base_mp) t 
  | Gletcase(g,params,annot,a,accu,bs) ->
      Format.fprintf fmt "@[let rec %a %a =@\n  %a@]@\n@."
	(pp_gname None) g pp_ldecls params 
	(pp_mllam base_mp) (MLmatch(annot,a,accu,bs))
  | Gletval(g,v) ->
      Format.fprintf fmt "@[let %a =@\n  %a@]@\n@."
	(pp_gname None) g (pp_mllam base_mp) (MLval v)


let pp_global_aux base_mp fmt g auxdefs = 
  if auxdefs = [] then pp_global base_mp fmt g
  else
    match g with
    | Glet(gn, c) ->
	let pp_auxdefs fmt auxdefs =
	  List.iter (Format.fprintf fmt "  %a   in@\n"  (pp_global base_mp)) auxdefs in
	Format.fprintf fmt "@[let %a =@\n%a  %a@]@\n@." 
	  (pp_gname None) gn pp_auxdefs auxdefs (pp_mllam base_mp) c
    | _ -> assert false

(*let pp_global_aux base_mp fmt g auxdefs = 
  List.iter (pp_global base_mp fmt) auxdefs;
  pp_global base_mp fmt g *)

let pp_globals base_mp fmt l = List.iter (pp_global base_mp fmt) l

(* Compilation of elements in environment *)
let compile_constant env mp l cb =
  match cb.const_body with
  | Def t ->
      let t = Declarations.force t in
      let code = lambda_of_constr ~opt:true env t in
      let auxdefs,code = compile_with_fv env [] (Some l) code in
      let l =
        optimize_stk (Glet(Gconstant (make_con mp empty_dirpath l),code)::auxdefs)
      in
      List.hd l, List.tl l
  | _ -> 
      let kn = make_con mp empty_dirpath l in
      Glet(Gconstant kn, MLprimitive (Mk_const kn)), []

let param_name = Name (id_of_string "params")
let arg_name = Name (id_of_string "arg")

let compile_mind mb mind stack =
  let f i acc ob =
    let gtype = Gtype((mind, i), Array.map snd ob.mind_reloc_tbl) in
    let accu = Glet(Gind (mind,i), MLprimitive(Mk_ind (mind,i))) in
    let nparams = mb.mind_nparams in
    let params = 
      Array.init nparams (fun i -> {lname = param_name; luid = i}) in
    let add_construct j acc (_,arity) = 
      let args = Array.init arity (fun k -> {lname = arg_name; luid = k}) in 
      let c = (mind,i), (j+1) in
	  Glet(Gconstruct c,
	     mkMLlam (Array.append params args)
	       (MLconstruct(c, Array.map (fun id -> MLlocal id) args)))::acc
    in
    array_fold_left_i add_construct (gtype::accu::acc) ob.mind_reloc_tbl
  in
  array_fold_left_i f stack mb.mind_packets

let compile_mind_sig mb mind stack =
  let f i acc ob =
    let gtype = Gtype((mind, i), Array.map snd ob.mind_reloc_tbl) in
    let accu = Gind (mind,i) in
    let n = Array.length ob.mind_reloc_tbl in
    let constructs = Array.init n (fun j -> Gconstruct ((mind,i),j+1)) in
    (gtype, accu::Array.to_list constructs)::acc
  in
  array_fold_left_i f stack mb.mind_packets

let mk_open s = Gopen s

let mk_internal_let s code =
  Glet(Ginternal s, code)


(* ML Code for conversion function *)
let conv_main_code =
  let g1 = MLglobal (Ginternal "t1") in
  let g2 = MLglobal (Ginternal "t2") in
  [Glet(Ginternal "_", MLsetref("rt1",g1));
  Glet(Ginternal "_", MLsetref("rt2",g2))]

let norm_main_code = 
  let g1 = MLglobal (Ginternal "t1") in
  [Glet(Ginternal "_", MLsetref("rt1",g1))]
