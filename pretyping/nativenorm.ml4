(*i camlp4use: "q_MLast.cmo" i*)
open Term
open Environ
open Util
open Nativecode
open Nbegen
open Nbeconv
open Unix

type term = | Rel of int
            | Con of string
	    | Lam1 of (term -> term)
            | Lam2 of (term -> term -> term)
            | Lam3 of (term -> term -> term -> term)
            | Lam4 of (term -> term -> term -> term -> term)
            | Lam5 of (term -> term -> term -> term -> term -> term)
            | Lam6 of (term -> term -> term -> term -> term -> term -> term)
	    | Prod of (term * (term -> term))
	    | App of term list
            | Match of term array
	    | Set
	    | Prop
	    | Type of int
	    | Const of (int * (term array))
            | Var of int
            | Lambda of term
            | Product of term


let compile env c =
  if Sys.file_exists (nbe_name^".ml") then
    anomaly (nbe_name ^".ml already exists");
  if Sys.file_exists (env_name^".ml") then
    anomaly (env_name ^".ml already exists");
  if Sys.file_exists (terms_name^".ml") then
    anomaly (terms_name ^".ml already exists");
  let code = translate env c in
    Pcaml.input_file := "/dev/null";
    print_implem (nbe_name^".ml") nbe_implem; 
    let dump = dump_env [c] env in
    print_implem (env_name^".ml") (compute_loc dump);
    print_implem (terms_name^".ml")
	 [(<:str_item< open $list: [nbe_name]$ >>, loc);
	  (<:str_item< open $list: [env_name]$ >>, loc);
	  (<:str_item< value c = $code$ >>, loc);
	  (<:str_item< value _ = print_nf c >>, loc)]

let rec rebuild_constr n t ty =
  match t with
    | Set -> mkSet
    | Prop -> mkProp
    | Lambda -> mkLambda Anonymous (rebuild)
    | _ -> assert false

let native_norm env c ty =
  let _ = compile (pre_env env) c in
  let file_names = nbe_name^".ml "^env_name^".ml "^terms_name^".ml" in
  let _ = Unix.system ("touch "^env_name^".ml") in
  print_endline "Compilation...";
  let res = Unix.system ("time ocamlopt.opt "^file_names) in
  let _ = Unix.system ("rm "^file_names) in
  match res with
    | Unix.WEXITED 0 ->
      begin
      print_endline "Normalizing...";
      let ch_in = open_process_in "./a.out" in
      let nf = Marshal.from_channel ch_in in
      (*let (fd_in,fd_out) = Unix.pipe() in
      match Unix.fork() with
        | 0 ->
          dup2 fd_out strdout;
          close fd_in;
          execvp "a.out"
        | _ ->
          close fd_out;
          let nf = Narshal.from_channel *)
      match nf with
        | Set ->
           mkSet
        | _ ->
           mkProp
(*      match Unix.system "time ./a.out; rm a.out" with
        | Unix.WEXITED 0 -> cu
        | _ -> (print_endline "Conversion test failure"; raise NotConvertible)*)
      end
    | _ -> anomaly "Compilation failure" 
