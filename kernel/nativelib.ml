open Names

exception Bug of string

type term =
  | Rel of int
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
  | Const of (int * term array)
  | Var of identifier
  | Lambda of term
  | Product of (term * term)

let array_iter2 f v1 v2 =
  let n = Array.length v1 in
  if Array.length v2 <> n then invalid_arg "array_iter2"
  else for i = 0 to n - 1 do f v1.(i) v2.(i) done

let rec string_of_term n =
  function
  | Con c -> "Con " ^ c
  | Var x -> "Var " ^ string_of_id x
  | Rel i -> "Rel " ^ string_of_int i
  | Lam1 f ->
      (try
        "Lam " ^ string_of_int n ^ ". (" ^
        string_of_term (n + 1) (f (Rel n)) ^ ")"
      with
      Bug _ -> "Lam " ^ string_of_int n ^ ". (...)")
  | Prod (ty, f) ->
      "Prod " ^ string_of_term n ty ^ " <" ^
      string_of_term (n + 1) (f (Rel n)) ^ ">"
  | App xs ->
      "(" ^
      List.fold_left (fun xs x -> xs ^ ", " ^ string_of_term n x) "" xs ^ ")"
  | Match xs ->
      "(Match" ^
      Array.fold_left (fun xs x -> xs ^ ", " ^ string_of_term n x) "" xs ^ ")"
  | Set -> "Set"
  | Prop -> "Prop"
  | Type i -> "Type " ^ string_of_int i
  | Const (i, args) ->
      "Const " ^ string_of_int i ^ " [" ^
      Array.fold_right (fun x xs -> string_of_term n x ^ ", " ^ xs) args "" ^
      "]"
  | _ -> "nopp"

let bug x = raise (Bug (string_of_term 0 x))

let app1 t1 t2 =
  match t1 with
  | Lam1 f -> f t2
  | Lam2 f -> Lam1 (f t2)
  | Lam3 f -> Lam2 (f t2)
  | Lam4 f -> Lam3 (f t2)
  | Lam5 f -> Lam4 (f t2)
  | Lam6 f -> Lam5 (f t2)
  | Con x -> App [Con x; t2]
  | Var x -> App [Var x; t2]
  | App xs -> App (xs @ [t2])
  | Match _ -> App [t1; t2]
  | _ -> 
    begin
      print_endline "impossible happened in app.";
      bug t1
    end

let app2 t1 t2 t3 =
  match t1 with
  | Lam1 f -> app1 (f t2) t3
  | Lam2 f -> f t2 t3
  | Lam3 f -> Lam1 (f t2 t3)
  | Lam4 f -> Lam2 (f t2 t3)
  | Lam5 f -> Lam3 (f t2 t3)
  | Lam6 f -> Lam4 (f t2 t3)
  | Con x -> App [Con x; t2; t3]
  | Var x -> App [Var x; t2; t3]
  | App xs -> App (xs @ [t2; t3])
  | Match _ -> App [t1; t2; t3]
  | _ ->
    begin
      print_endline "impossible happened in app.";
      bug t1
    end

let app3 t1 t2 t3 t4 =
  match t1 with
  | Lam1 f -> app2 (f t2) t3 t4
  | Lam2 f -> app1 (f t2 t3) t4
  | Lam3 f -> f t2 t3 t4
  | Lam4 f -> Lam1 (f t2 t3 t4)
  | Lam5 f -> Lam2 (f t2 t3 t4)
  | Lam6 f -> Lam3 (f t2 t3 t4)
  | Con x -> App [Con x; t2; t3; t4]
  | Var x -> App [Var x; t2; t3; t4]
  | App xs -> App (xs @ [t2; t3; t4])
  | Match _ -> App [t1; t2; t3; t4]
  | _ ->
    begin
      print_endline "impossible happened in app.";
      bug t1
    end

let app4 t1 t2 t3 t4 t5 =
  match t1 with
  | Lam1 f -> app3 (f t2) t3 t4 t5
  | Lam2 f -> app2 (f t2 t3) t4 t5
  | Lam3 f -> app1 (f t2 t3 t4) t5
  | Lam4 f -> f t2 t3 t4 t5
  | Lam5 f -> Lam1 (f t2 t3 t4 t5)
  | Lam6 f -> Lam2 (f t2 t3 t4 t5)
  | Con x -> App [Con x; t2; t3; t4; t5]
  | Var x -> App [Var x; t2; t3; t4; t5]
  | App xs -> App (xs @ [t2; t3; t4; t5])
  | Match _ -> App [t1; t2; t3; t4; t5]
  | _ ->
    begin
      print_endline "impossible happened in app.";
      bug t1
    end

let app5 t1 t2 t3 t4 t5 t6 =
  match t1 with
  | Lam1 f -> app4 (f t2) t3 t4 t5 t6
  | Lam2 f -> app3 (f t2 t3) t4 t5 t6
  | Lam3 f -> app2 (f t2 t3 t4) t5 t6
  | Lam4 f -> app1 (f t2 t3 t4 t5) t6
  | Lam5 f -> f t2 t3 t4 t5 t6
  | Lam6 f -> Lam1 (f t2 t3 t4 t5 t6)
  | Con x -> App [Con x; t2; t3; t4; t5; t6]
  | Var x -> App [Var x; t2; t3; t4; t5; t6]
  | App xs -> App (xs @ [t2; t3; t4; t5; t6])
  | Match _ -> App [t1; t2; t3; t4; t5; t6]
  | _ ->
    begin
      print_endline "impossible happened in app.";
      bug t1
    end

let app6 t1 t2 t3 t4 t5 t6 t7 =
  match t1 with
  | Lam1 f -> app5 (f t2) t3 t4 t5 t6 t7
  | Lam2 f -> app4 (f t2 t3) t4 t5 t6 t7
  | Lam3 f -> app3 (f t2 t3 t4) t5 t6 t7
  | Lam4 f -> app2 (f t2 t3 t4 t5) t6 t7
  | Lam5 f -> app1 (f t2 t3 t4 t5 t6) t7
  | Lam6 f -> f t2 t3 t4 t5 t6 t7
  | Con x -> App [Con x; t2; t3; t4; t5; t6; t7]
  | Var x -> App [Var x; t2; t3; t4; t5; t6; t7]
  | App xs -> App (xs @ [t2; t3; t4; t5; t6; t7])
  | Match _ -> App [t1; t2; t3; t4; t5; t6; t7]
  | _ ->
    begin
      print_endline "impossible happened in app.";
      bug t1
    end

let app = app1

let rec compare n t1 t2 =
  match (t1, t2) with
  | (Con c, Con c') when c = c' -> ()
  | (Rel i, Rel j) when i = j -> ()
  | (Var c, Var c') when c = c' -> ()
  | (Prod (t, f), Prod (t', f')) ->
    begin 
      compare n t t';
      compare (n + 1) (f (Rel n)) (f' (Rel n))
    end
  | (App xs, App xs') -> List.iter2 (compare n) xs xs'
  | (Match xs, Match xs') -> array_iter2 (compare n) xs xs'
  | (Set, Set) -> ()
  | (Prop, Prop) -> ()
  | (Type i, Type i') when i = i' -> ()
  | (Const (i, args), Const (i', args')) when i = i' ->
      Array.iteri (fun i _ -> compare n args.(i) args'.(i)) args
  | (Lam1 f, Lam1 g) -> compare (n + 1) (f (Rel n)) (g (Rel n))
  | (Lam2 f, Lam2 g) ->
      compare (n + 2) (f (Rel n) (Rel (n + 1))) (g (Rel n) (Rel (n + 1)))
  | (Lam3 f, Lam3 g) ->
      compare (n + 3) (f (Rel n) (Rel (n + 1)) (Rel (n + 2)))
        (g (Rel n) (Rel (n + 1)) (Rel (n + 2)))
  | (Lam4 f, Lam4 g) ->
      compare (n + 4) (f (Rel n) (Rel (n + 1)) (Rel (n + 2)) (Rel (n + 3)))
        (g (Rel n) (Rel (n + 1)) (Rel (n + 2)) (Rel (n + 3)))
  | (Lam5 f, Lam5 g) ->
      compare (n + 5)
        (f (Rel n) (Rel (n + 1)) (Rel (n + 2)) (Rel (n + 3)) (Rel (n + 4)))
        (g (Rel n) (Rel (n + 1)) (Rel (n + 2)) (Rel (n + 3)) (Rel (n + 4)))
  | (Lam6 f, Lam6 g) ->
      compare (n + 6)
        (f (Rel n) (Rel (n + 1)) (Rel (n + 2)) (Rel (n + 3)) (Rel (n + 4))
           (Rel (n + 5)))
        (g (Rel n) (Rel (n + 1)) (Rel (n + 2)) (Rel (n + 3)) (Rel (n + 4))
           (Rel (n + 5)))
  | _ ->
    begin 
      print_endline (string_of_term n t1);
      print_endline (string_of_term n t2);
      exit 1
    end

let rec normalize n c =
  match c with
  | Lam1 f -> Lambda (normalize (n + 1) (f (Rel n)))
  | Lam2 f -> Lambda (Lambda (normalize (n + 2) (f (Rel n) (Rel (n + 1)))))
  | Lam3 f ->
      Lambda
        (Lambda
           (Lambda
              (normalize (n + 3) (f (Rel n) (Rel (n + 1)) (Rel (n + 2))))))
  | Lam4 f ->
      Lambda
        (Lambda
           (Lambda
              (Lambda
                 (normalize (n + 4)
                    (f (Rel n) (Rel (n + 1)) (Rel (n + 2)) (Rel (n + 3)))))))
  | Lam5 f ->
      Lambda
        (Lambda
           (Lambda
              (Lambda
                 (Lambda
                    (normalize (n + 5)
                       (f (Rel n) (Rel (n + 1)) (Rel (n + 2)) (Rel (n + 3))
                          (Rel (n + 4))))))))
  | Lam6 f ->
      Lambda
        (Lambda
           (Lambda
              (Lambda
                 (Lambda
                    (Lambda
                       (normalize (n + 6)
                          (f (Rel n) (Rel (n + 1)) (Rel (n + 2)) (Rel (n + 3))
                             (Rel (n + 4)) (Rel (n + 5)))))))))
  | Prod (t, f) -> Product (normalize n t, normalize (n + 1) (f (Rel n)))
  | App l -> App (List.map (normalize n) l)
  | Match xs -> Match (Array.map (normalize n) xs)
  | Const (i, xs) -> Const (i, Array.map (normalize n) xs)
  | _ -> c

let print_nf c = Marshal.to_channel stdout (normalize 0 c) [];
