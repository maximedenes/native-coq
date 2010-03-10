exception Bug of string

type term = Con of unit
	    | Lam1 of (term -> term)
            | Lam2 of (term -> term -> term)
            | Lam3 of (term -> term -> term -> term)
            | Lam4 of (term -> term -> term -> term -> term)
            | Lam5 of (term -> term -> term -> term -> term -> term)
            | Lam6 of (term -> term -> term -> term -> term -> term -> term)
	    | Prod of term * (term -> term)
	    | App of term list
	    | Set
	    | Prop
	    | Type of int
	    | Const of int * term array
            | Var of int

let rec string_of_term n = function
  | Con c -> "Con " ^ "" (* c *)
  | Lam1 f -> (try
      ("Lam " ^ (string_of_int n) ^ ". (" ^ string_of_term (n + 1) (f (Con ())) ^ ")")
      with Bug _ -> 
         ("Lam " ^ (string_of_int n) ^ ". (...)"))
  | Prod (ty, f) -> "Prod " ^ string_of_term n ty ^ " <f>"
  | App xs -> "App" ^ List.fold_left (fun xs x -> xs ^ ", " ^ string_of_term n x) "" xs
  | Set -> "Set"
  | Prop -> "Prop"
  | Type i -> "Type " ^ string_of_int i
  | Const (i, args) -> "Const " ^ string_of_int i ^ " [" ^ Array.fold_right (fun x xs -> string_of_term n x ^ ", " ^ xs) args "" ^ "]"
  | _ -> "nopp"

let bug x = print_endline (string_of_term 0 x); raise (Bug (string_of_term 0 x))

let app1 t1 t2 = match t1 with
  | Lam1 f -> f t2
  | Lam2 f -> Lam1 (f t2)
  | Lam3 f -> Lam2 (f t2)
  | Lam4 f -> Lam3 (f t2)
  | Lam5 f -> Lam4 (f t2)
  | Lam6 f -> Lam5 (f t2)
  | Con x ->  App (Con x :: [t2])
  | Var x ->  App (Var x :: [t2])
  | App xs -> App (xs @ [t2])
  | _ -> print_endline "impossible happened in app."; bug t1
let app2 t1 t2 t3 = match t1 with
  | Lam1 f -> app1 (f t2) t3
  | Lam2 f -> f t2 t3
  | Lam3 f -> Lam1 (f t2 t3)
  | Lam4 f -> Lam2 (f t2 t3)
  | Lam5 f -> Lam3 (f t2 t3)
  | Lam6 f -> Lam4 (f t2 t3)
  | Con x ->  App (Con x :: [t2; t3])
  | App xs -> App (xs @ [t2; t3])
  | _ -> print_endline "impossible happened in app."; bug t1
let app3 t1 t2 t3 t4 = match t1 with
  | Lam1 f -> app2 (f t2) t3 t4
  | Lam2 f -> app1 (f t2 t3) t4
  | Lam3 f -> f t2 t3 t4
  | Lam4 f -> Lam1 (f t2 t3 t4)
  | Lam5 f -> Lam2 (f t2 t3 t4)
  | Lam6 f -> Lam3 (f t2 t3 t4)
  | Con x ->  App (Con x :: [t2; t3; t4])
  | App xs -> App (xs @ [t2; t3; t4])
  | _ -> print_endline "impossible happened in app."; bug t1
let app4 t1 t2 t3 t4 t5 = match t1 with
  | Lam1 f -> app3 (f t2) t3 t4 t5
  | Lam2 f -> app2 (f t2 t3) t4 t5
  | Lam3 f -> app1 (f t2 t3 t4) t5
  | Lam4 f -> f t2 t3 t4 t5
  | Lam5 f -> Lam1 (f t2 t3 t4 t5)
  | Lam6 f -> Lam2 (f t2 t3 t4 t5)
  | Con x ->  App (Con x :: [t2; t3; t4; t5])
  | App xs -> App (xs @ [t2; t3; t4; t5])
  | _ -> print_endline "impossible happened in app."; bug t1
let app5 t1 t2 t3 t4 t5 t6 = match t1 with
  | Lam1 f -> app4 (f t2) t3 t4 t5 t6
  | Lam2 f -> app3 (f t2 t3) t4 t5 t6
  | Lam3 f -> app2 (f t2 t3 t4) t5 t6
  | Lam4 f -> app1 (f t2 t3 t4 t5) t6
  | Lam5 f -> f t2 t3 t4 t5 t6
  | Lam6 f -> Lam1 (f t2 t3 t4 t5 t6)
  | Con x ->  App (Con x :: [t2; t3; t4; t5; t6])
  | App xs -> App (xs @ [t2; t3; t4; t5; t6])
  | _ -> print_endline "impossible happened in app."; bug t1
let app6 t1 t2 t3 t4 t5 t6 t7 = match t1 with
  | Lam1 f -> app5 (f t2) t3 t4 t5 t6 t7
  | Lam2 f -> app4 (f t2 t3) t4 t5 t6 t7
  | Lam3 f -> app3 (f t2 t3 t4) t5 t6 t7
  | Lam4 f -> app2 (f t2 t3 t4 t5) t6 t7
  | Lam5 f -> app1 (f t2 t3 t4 t5 t6) t7
  | Lam6 f -> f t2 t3 t4 t5 t6 t7
  | Con x ->  App (Con x :: [t2; t3; t4; t5; t6; t7])
  | App xs -> App (xs @ [t2; t3; t4; t5; t6; t7])
  | _ -> print_endline "impossible happened in app."; bug t1
let app = app1

let rec compare n t1 t2 = match t1, t2 with
  | Con c, Con c' when c = c' -> ()
  | Var c, Var c' when c = c' -> ()
  | Prod (t, f), Prod (t', f') ->
      compare n t t';
      compare (n + 1) (f (Con ())) (f' (Con ()))
  | App xs, App xs' -> List.iter2 (compare n) xs xs'
  | Set, Set -> ()
  | Prop, Prop -> ()
  | Type i, Type i' when i = i' -> ()
  | Const (i, args), Const (i', args') when i = i' ->
      Array.iteri (fun i _ -> compare n args.(i) args'.(i)) args
  | Lam1 f, Lam1 g -> compare (n+1) (f (Var n)) (g (Var n))
  | _ -> print_endline (string_of_term n t1); print_endline (string_of_term n t2); exit 1
