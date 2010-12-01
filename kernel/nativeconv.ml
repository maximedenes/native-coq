open Names
open Term
open Pre_env
open Pcaml
open Nativelib
open Declarations
open Util
open Nativevalues
open Nativelambda
open Nativecode 

exception NotConvertible

let rec conv_val lvl v1 v2 = 
  if not (v1 == v2) then 
    match kind_of_value v1, kind_of_value v2 with
    | Vaccu k1, Vaccu k2 ->
	conv_accu lvl k1 k2
    | Vfun f1, Vfun f2 -> 
	conv_fun lvl f1 f2
    | Vconst i1, Vconst i2 -> 
(*        print_endline ("Vconst: "^string_of_int i1);*)
	if i1 <> i2 then raise NotConvertible
    | Vblock b1, Vblock b2 ->
	let n1 = block_size b1 in
	if block_tag b1 <> block_tag b2 || n1 <> block_size b2 then
	  raise NotConvertible;
        for i = 0 to n1 - 1 do 
	  conv_val lvl (block_field b1 i) (block_field b2 i) 
	done
    | Varray t1, Varray t2 ->
      let len = Native.Parray.length t1 in
      if len <> Native.Parray.length t2 then
      raise NotConvertible;
      for i = 0 to Native.Uint31.to_int len - 1 do
        conv_val lvl (Native.Parray.get t1 (Native.Uint31.of_int i))
           (Native.Parray.get t2 (Native.Uint31.of_int i))
      done;
      conv_val lvl (Native.Parray.default t1) (Native.Parray.default t2)   
    | _, _ -> raise NotConvertible
and conv_accu lvl k1 k2 = 
  let n1 = accu_nargs k1 in
  if n1 <> accu_nargs k2 then raise NotConvertible;
(*  print_endline ("nargs: "^string_of_int n1);*)
  conv_atom lvl (atom_of_accu k1) (atom_of_accu k2);
  for i = 0 to n1 - 1 do
    conv_val lvl (arg_of_accu k1 i) (arg_of_accu k2 i) 
  done

and conv_atom lvl a1 a2 =
  if not (a1 == a2) then
    match a1, a2 with
    | Arel i1, Arel i2 -> 
	if i1 <> i2 then raise NotConvertible
    | Aind ind1, Aind ind2 ->
        if not (eq_ind ind1 ind2) then raise NotConvertible
(* TODO    | Aconstruct(_,_,i1), Aconstruct(_,_,i2) -> 
	if i1 <> i2 then raise NotConvertible*)
(* TODO    | Acase(k1,f1,tbl1,_,it1), Acase(k2,f2,tbl2,_,it2) ->
	let t1,t2 = get_type_of_index it1, get_type_of_index it2 in
        if not (eq_type t1 t2) then raise NotConvertible;
	conv_accu lvl k1 k2;
	assert (tbl1==tbl2);
	for i = 0 to Array.length tbl1 - 1 do
	  let (tag,arity) = tbl1.(i) in
	  let ci =
 	    if arity = 0 then mk_const tag 
	    else 
	      let args = Array.init arity (fun i -> mk_rel_accu (lvl+i)) in
	      mk_block tag args in
	  conv_val (lvl+arity) (f1 ci) (f2 ci)
	done*)
(* TODO    | Afix(_,f1,rp1,_,it1), Afix(_,f2,rp2,_,it2) ->
	let t1, t2= get_type_of_index it1, get_type_of_index it2 in
	if not (eq_type t1 t2) then raise NotConvertible;
	if rp1 <> rp2 then raise NotConvertible;
	conv_fun lvl f1 f2 *)
    | _, _ -> raise NotConvertible

and conv_fun lvl f1 f2 = 
  let x = mk_rel_accu lvl in
  conv_val (lvl+1) (f1 x) (f2 x)

let conv_val t1 t2 = conv_val 0 t1 t2


let compare env t1 t2 cu =
  let mp = env.current_mp in
  let code1 = lambda_of_constr env t1 in
  let code2 = lambda_of_constr env t2 in
  let (gl1,_,code1) = mllambda_of_lambda code1 in
  let (gl2,_,code2) = mllambda_of_lambda code2 in
  let g1 = MLglobal (Ginternal "t1") in
  let g2 = MLglobal (Ginternal "t2") in
  let conv_val = MLglobal (Ginternal "conv_val") in
  let header = [Gopen "Nativevalues";Gopen "Nativecode"; Gopen "Nativeconv"] in
  let main = Glet(Ginternal "_", MLapp(conv_val,[|g1;g2|])) in
  let code = header@gl1@gl2@[Glet(Ginternal "t1", code1);Glet(Ginternal "t2", code2);main] in
(*  let (code1,_) = translate mp env "t1" t1 in
  let (code2,_) = translate mp env "t2" t2 in *)
(*@ [<:str_item< value _ = (*let t0 = Unix.time () in *)
      (*do {*)try conv_val 0 t1 t2 with _ -> exit 1 (*;
    Format.fprintf Format.std_formatter
    "Test running time: %.5fs\n" (Unix.time() -. t0);
    flush_all() }*)
    >>] *)
  print_endline "code:" ;
  Nativecode.pp_globals mp Format.std_formatter code;
  print_newline ();
  match compile_terms mp code with
    | 0,fn,modname ->
      begin
        print_endline "Running test...";
        try call_linker fn modname; cu with
          | _ -> raise NotConvertible
      end
    | _ -> anomaly "Compilation failure" 

  (*let file_names = env_name^".ml "^terms_name^".ml" in
  let _ = Sys.command ("touch "^env_name^".ml") in
  print_endline "Compilation...";
  let comp_cmd =
    "ocamlopt.opt -rectypes "^include_dirs^include_libs^file_names
  in
  let res = Sys.command comp_cmd in
  match res with
    | 0 ->
      begin
      let _ = Sys.command ("rm "^file_names) in
      print_endline "Running conversion test...";
      let res = Sys.command "./a.out" in
      let _ = Sys.command "rm a.out" in
      match res with
        | 0 -> cu
        | _ -> (print_endline "Conversion test failure"; raise NotConvertible)
      end
    | _ -> (print_endline "Compilation failure"; raise NotConvertible)*)
  
