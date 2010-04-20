(*i camlp4use: "q_MLast.cmo" i*)

let loc = Ploc.dummy

let nbe_implem = [(<:str_item< exception Bug of string >>,loc);

(<:str_item< type term = [ Con of string
	    | Lam1 of (term -> term)
            | Lam2 of (term -> term -> term)
            | Lam3 of (term -> term -> term -> term)
            | Lam4 of (term -> term -> term -> term -> term)
            | Lam5 of (term -> term -> term -> term -> term -> term)
            | Lam6 of (term -> term -> term -> term -> term -> term -> term)
	    | Prod of (term * (term -> term))
	    | App of list term
            | Match of array term
	    | Set
	    | Prop
	    | Type of int
	    | Const of (int * (array term))
            | Var of int ] >>,loc);

(<:str_item< value array_iter2 f v1 v2 =
  let n = Array.length v1 in
  if Array.length v2 <> n then invalid_arg "array_iter2"
  else for i = 0 to n - 1 do { f v1.(i) v2.(i) } >>,loc);


(<:str_item< value rec string_of_term n = fun [
    Con c -> "Con " ^ c
  | Var x -> "Var " ^ (string_of_int x)
  | Lam1 f -> try
      ("Lam " ^ (string_of_int n) ^ ". (" ^ string_of_term (n + 1) (f (Var n)) ^ ")")
      with [ Bug _ -> 
         ("Lam " ^ (string_of_int n) ^ ". (...)") ]
  | Prod (ty, f) -> "Prod " ^ string_of_term n ty ^ " <" ^ string_of_term (n+1) (f (Var n))  ^ ">"
  | App xs -> "(" ^ List.fold_left (fun xs x -> xs ^ ", " ^ string_of_term n x) "" xs ^ ")"
  | Match xs -> "(Match" ^ Array.fold_left (fun xs x -> xs ^ ", " ^ string_of_term n x) "" xs ^ ")"
  | Set -> "Set"
  | Prop -> "Prop"
  | Type i -> "Type " ^ string_of_int i
  | Const (i, args) -> "Const " ^ string_of_int i ^ " [" ^ Array.fold_right (fun x xs -> string_of_term n x ^ ", " ^ xs) args "" ^ "]"
  | _ -> "nopp" ] >>,loc);

(<:str_item< value bug x = raise (Bug (string_of_term 0 x)) >>,loc);

(<:str_item< value app1 t1 t2 = match t1 with
  [ Lam1 f -> f t2
  | Lam2 f -> Lam1 (f t2)
  | Lam3 f -> Lam2 (f t2)
  | Lam4 f -> Lam3 (f t2)
  | Lam5 f -> Lam4 (f t2)
  | Lam6 f -> Lam5 (f t2)
  | Con x ->  App [Con x :: [t2]]
  | Var x ->  App [Var x :: [t2]]
  | App xs -> App (xs @ [t2])
  | Match _ -> App [t1 :: [t2]]
  | _ -> do {print_endline "impossible happened in app."; bug t1} ] >>,loc);
(<:str_item< value app2 t1 t2 t3 = match t1 with
  [ Lam1 f -> app1 (f t2) t3
  | Lam2 f -> f t2 t3
  | Lam3 f -> Lam1 (f t2 t3)
  | Lam4 f -> Lam2 (f t2 t3)
  | Lam5 f -> Lam3 (f t2 t3)
  | Lam6 f -> Lam4 (f t2 t3)
  | Con x ->  App [Con x :: [t2; t3]]
  | Var x ->  App [Var x :: [t2; t3]]
  | App xs -> App (xs @ [t2; t3])
  | Match _ -> App [t1 :: [t2; t3]]
  | _ -> do {print_endline "impossible happened in app."; bug t1} ] >>,loc);
(<:str_item< value app3 t1 t2 t3 t4 = match t1 with
  [ Lam1 f -> app2 (f t2) t3 t4
  | Lam2 f -> app1 (f t2 t3) t4
  | Lam3 f -> f t2 t3 t4
  | Lam4 f -> Lam1 (f t2 t3 t4)
  | Lam5 f -> Lam2 (f t2 t3 t4)
  | Lam6 f -> Lam3 (f t2 t3 t4)
  | Con x ->  App [Con x :: [t2; t3; t4]]
  | Var x ->  App [Var x :: [t2; t3; t4]]
  | App xs -> App (xs @ [t2; t3; t4])
  | Match _ -> App [t1 :: [t2; t3; t4]]
  | _ -> do {print_endline "impossible happened in app."; bug t1} ] >>,loc);
(<:str_item< value app4 t1 t2 t3 t4 t5 = match t1 with
  [ Lam1 f -> app3 (f t2) t3 t4 t5
  | Lam2 f -> app2 (f t2 t3) t4 t5
  | Lam3 f -> app1 (f t2 t3 t4) t5
  | Lam4 f -> f t2 t3 t4 t5
  | Lam5 f -> Lam1 (f t2 t3 t4 t5)
  | Lam6 f -> Lam2 (f t2 t3 t4 t5)
  | Con x ->  App [Con x :: [t2; t3; t4; t5]]
  | Var x ->  App [Var x :: [t2; t3; t4; t5]]
  | App xs -> App (xs @ [t2; t3; t4; t5])
  | Match _ -> App [t1 :: [t2; t3; t4; t5]]
  | _ -> do {print_endline "impossible happened in app."; bug t1} ] >>,loc);
(<:str_item< value app5 t1 t2 t3 t4 t5 t6 = match t1 with
  [ Lam1 f -> app4 (f t2) t3 t4 t5 t6
  | Lam2 f -> app3 (f t2 t3) t4 t5 t6
  | Lam3 f -> app2 (f t2 t3 t4) t5 t6
  | Lam4 f -> app1 (f t2 t3 t4 t5) t6
  | Lam5 f -> f t2 t3 t4 t5 t6
  | Lam6 f -> Lam1 (f t2 t3 t4 t5 t6)
  | Con x ->  App [Con x :: [t2; t3; t4; t5; t6]]
  | Var x ->  App [Var x :: [t2; t3; t4; t5; t6]]
  | App xs -> App (xs @ [t2; t3; t4; t5; t6])
  | Match _ -> App [t1 :: [t2; t3; t4; t5; t6]]
  | _ -> do {print_endline "impossible happened in app."; bug t1} ] >>,loc);
(<:str_item< value app6 t1 t2 t3 t4 t5 t6 t7 = match t1 with
  [ Lam1 f -> app5 (f t2) t3 t4 t5 t6 t7
  | Lam2 f -> app4 (f t2 t3) t4 t5 t6 t7
  | Lam3 f -> app3 (f t2 t3 t4) t5 t6 t7
  | Lam4 f -> app2 (f t2 t3 t4 t5) t6 t7
  | Lam5 f -> app1 (f t2 t3 t4 t5 t6) t7
  | Lam6 f -> f t2 t3 t4 t5 t6 t7
  | Con x ->  App [Con x :: [t2; t3; t4; t5; t6; t7]]
  | Var x ->  App [Var x :: [t2; t3; t4; t5; t6; t7]]
  | App xs -> App (xs @ [t2; t3; t4; t5; t6; t7])
  | Match _ -> App [t1 :: [t2; t3; t4; t5; t6; t7]]
  | _ -> do {print_endline "impossible happened in app."; bug t1} ] >>,loc);
(<:str_item< value app = app1 >>,loc);

(<:str_item< value rec compare n t1 t2 = match (t1,t2) with
  [ (Con c, Con c') when c = c' -> ()
  | (Var c, Var c') when c = c' -> ()
  | (Prod (t, f), Prod (t', f')) ->
      do {compare n t t';
      compare (n + 1) (f (Var n)) (f' (Var n))}
  | (App xs, App xs') -> List.iter2 (compare n) xs xs'
  | (Match xs, Match xs') -> array_iter2 (compare n) xs xs' 
  | (Set, Set) -> ()
  | (Prop, Prop) -> ()
  | (Type i, Type i') when i = i' -> ()
  | (Const (i, args), Const (i', args')) when i = i' ->
      Array.iteri (fun i _ -> compare n args.(i) args'.(i)) args
  | (Lam1 f, Lam1 g) -> compare (n+1) (f (Var n))
                                    (g (Var n))
  | (Lam2 f, Lam2 g) -> compare (n+2) (f (Var n) (Var (n+1)))
                                    (g (Var n) (Var (n+1)))
  | (Lam3 f, Lam3 g) -> compare (n+3) (f (Var n) (Var (n+1)) (Var (n+2)))
                                    (g (Var n) (Var (n+1)) (Var (n+2)))
  | (Lam4 f, Lam4 g) -> compare (n+4) (f (Var n) (Var (n+1)) (Var (n+2)) (Var (n+3)))
                                    (g (Var n) (Var (n+1)) (Var (n+2)) (Var (n+3)))
  | (Lam5 f, Lam5 g) -> compare (n+5) (f (Var n) (Var (n+1)) (Var (n+2)) (Var (n+3)) (Var (n+4)))
                                    (g (Var n) (Var (n+1)) (Var (n+2)) (Var (n+3)) (Var (n+4)))
  | (Lam6 f, Lam6 g) -> compare (n+6) (f (Var n) (Var (n+1)) (Var (n+2)) (Var (n+3)) (Var (n+4)) (Var (n+5)))
                                    (g (Var n) (Var (n+1)) (Var (n+2)) (Var (n+3)) (Var (n+4)) (Var (n+5)))

  | _ -> do {print_endline (string_of_term n t1); print_endline (string_of_term n t2); exit 1} ] >>,loc)]
