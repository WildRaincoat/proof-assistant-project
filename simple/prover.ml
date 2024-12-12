open Expr

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)

let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

let () = Printexc.record_backtrace true

(** Type variables. *)
(* type tvar = string *)

(** Term variables. *)
(* type var = string *)

(** Types. *)
(* type ty =
  | TVar of tvar
  | Imp of ty * ty
  | And of ty * ty   
  | Or of ty * ty     
  | True              
  | False             *)


(*1.2*)
(* type tm =
  | Var of var
  | Abs of var * ty * tm
  | App of tm * tm
  | Pair of tm * tm        
  | Fst of tm                 
  | Snd of tm               
  | Inl of tm * ty        
  | Inr of tm * ty              
  | Case of tm * (var * tm) * (var * tm)  
  | Tru                      
  | Fls                       
  | Absurd of tm * ty          *)
 

(* 1.3 字符串表示函数 *)
let rec string_of_ty t =
  match t with
  | TVar a -> a
  | Imp (t1, t2) -> "(" ^ string_of_ty t1 ^ " => " ^ string_of_ty t2 ^ ")"
  | And (t1, t2) -> "(" ^ string_of_ty t1 ^ " ∧ " ^ string_of_ty t2 ^ ")"
  | Or (t1, t2) -> "(" ^ string_of_ty t1 ^ " ∨ " ^ string_of_ty t2 ^ ")"
  | True -> "⊤"
  | False -> "⊥"


let rec string_of_tm t =
  match t with
  | Var x -> x
  | Abs (x, ty, tm) ->
      "(fun (" ^ x ^ " : " ^ string_of_ty ty ^ ") -> " ^ string_of_tm tm ^ ")"
  | App (tm1, tm2) -> "(" ^ string_of_tm tm1 ^ " " ^ string_of_tm tm2 ^ ")"
  | Pair (tm1, tm2) -> "(" ^ string_of_tm tm1 ^ ", " ^ string_of_tm tm2 ^ ")"
  | Fst tm -> "(fst " ^ string_of_tm tm ^ ")"
  | Snd tm -> "(snd " ^ string_of_tm tm ^ ")"
  | Inl (tm, ty) -> "(inl " ^ string_of_tm tm ^ " : " ^ string_of_ty ty ^ ")"
  | Inr (tm, ty) -> "(inr " ^ string_of_tm tm ^ " : " ^ string_of_ty ty ^ ")"
  | Case (tm, (x, tm1), (y, tm2)) ->
      "(case " ^ string_of_tm tm ^ " of inl " ^ x ^ " => " ^ string_of_tm tm1 ^
      " | inr " ^ y ^ " => " ^ string_of_tm tm2 ^ ")"
  | Tru -> "true"
  | Fls -> "false"
  | Absurd (tm, ty) -> "(absurd " ^ string_of_tm tm ^ " : " ^ string_of_ty ty ^ ")"

let () =
  let ty_example = Imp(Imp(TVar "A", TVar "B"), Imp(TVar "A", TVar "C")) in
  print_endline (string_of_ty ty_example);
  
  let tm_example =
    Abs("f", Imp(TVar "A", TVar "B"),
        Abs("x", TVar "A",
            App(Var "f", Var "x")))
  in
  print_endline (string_of_tm tm_example)


(** Typing contexts are lists of variable-type pairs. *)
type context = (var * ty) list

(** Exception raised when type inference fails. *)
exception Type_error

(*1.4*)
(* Type inference function. *)
(* let rec infer_type (ctx: context) (t: tm) : ty =
  match t with
  | Var x -> (
      try
        List.assoc x ctx (* 查找变量 x 的类型 *)
      with Not_found -> raise Type_error
    )
  | Abs (x, ty_x, t_body) ->
      let ctx' = (x, ty_x) :: ctx in (* 扩展上下文 *)
      let ty_body = infer_type ctx' t_body in
      Imp (ty_x, ty_body) (* 函数类型 *)
  | App (t1, t2) ->
      let ty_t1 = infer_type ctx t1 in
      let ty_t2 = infer_type ctx t2 in
      (match ty_t1 with
      | Imp (ty_arg, ty_res) ->
          if ty_arg = ty_t2 then ty_res
          else raise Type_error
      | _ -> raise Type_error) *)
(*1.6*)
(* Type inference and checking function. *)
(* let rec infer_type (ctx: context) (t: tm) : ty =
  match t with
  | Var x -> (
      try
        List.assoc x ctx (* 查找变量 x 的类型 *)
      with Not_found -> raise Type_error
    )
  | Abs (x, ty_x, t_body) ->
      let ctx' = (x, ty_x) :: ctx in (* 扩展上下文 *)
      let ty_body = infer_type ctx' t_body in
      Imp (ty_x, ty_body) (* 函数类型 *)
  | App (t1, t2) ->
      let ty_t1 = infer_type ctx t1 in
      let ty_t2 = infer_type ctx t2 in
      (match ty_t1 with
      | Imp (ty_arg, ty_res) ->
          if ty_arg = ty_t2 then ty_res
          else raise Type_error
      | _ -> raise Type_error) *)
    
(*1.7*)
let rec infer_type (ctx: context) (t: tm) : ty =
  match t with
  | Var x -> (
      try List.assoc x ctx
      with Not_found -> raise Type_error
    )
  | Abs (x, ty_x, t_body) ->
      let ctx' = (x, ty_x) :: ctx in
      let ty_body = infer_type ctx' t_body in
      Imp (ty_x, ty_body)
  | App (t1, t2) ->
      let ty_t1 = infer_type ctx t1 in
      let ty_t2 = infer_type ctx t2 in
      (match ty_t1 with
      | Imp (ty_arg, ty_res) ->
          if ty_arg = ty_t2 then ty_res
          else raise Type_error
      | _ -> raise Type_error)
  | Pair (t1, t2) ->
      let ty_t1 = infer_type ctx t1 in
      let ty_t2 = infer_type ctx t2 in
      And (ty_t1, ty_t2)
  | Fst t ->
      (match infer_type ctx t with
      | And (ty1, _) -> ty1
      | _ -> raise Type_error)
  | Snd t ->
      (match infer_type ctx t with
      | And (_, ty2) -> ty2
      | _ -> raise Type_error)
  | Inl (t, ty) ->
    let ty_t = infer_type ctx t in
    (match ty with
    | Or (ty_l, _) ->
        if ty_t = ty_l then ty
        else raise Type_error
    | _ -> raise Type_error)
  | Inr (t, ty) ->
    let ty_t = infer_type ctx t in
    (match ty with
    | Or (_, ty_r) ->
        if ty_t = ty_r then ty
        else raise Type_error
    | _ -> raise Type_error)

  | Case (t, (x, t1), (y, t2)) ->
    (match infer_type ctx t with
    | Or (ty_l, ty_r) ->
        let ctx1 = (x, ty_l) :: ctx in
        let ctx2 = (y, ty_r) :: ctx in
        let ty_t1 = infer_type ctx1 t1 in
        let ty_t2 = infer_type ctx2 t2 in
        if ty_t1 = ty_t2 then ty_t1
        else raise Type_error
    | _ -> raise Type_error)
  | Tru -> True
  | Fls -> False
  | Absurd (t, ty) ->
      (match infer_type ctx t with
      | False -> ty
      | _ -> raise Type_error)



let () =
  let ctx = [] in
  let term =
    Abs ("f", Imp (TVar "A", TVar "B"),
         Abs ("g", Imp (TVar "B", TVar "C"),
              Abs ("x", TVar "A",
                   App (Var "g", App (Var "f", Var "x")))))
  in
  let inferred_ty = infer_type ctx term in
  print_endline (string_of_ty inferred_ty)

(* 1.5 Type checking function *)
let rec check_type (ctx: context) (t: tm) (expected_ty: ty) : unit =
  match t with
  | Var x -> (
      try
        let inferred_ty = List.assoc x ctx in
        if inferred_ty <> expected_ty then raise Type_error
      with Not_found -> raise Type_error
    )
  | Abs (x, ty_x, t_body) ->
      (match expected_ty with
      | Imp (ty_arg, ty_res) ->
          if ty_arg = ty_x then
            let ctx' = (x, ty_x) :: ctx in
            check_type ctx' t_body ty_res
          else raise Type_error
      | _ -> raise Type_error)
  | App (t1, t2) ->
      let inferred_t2_ty = infer_type ctx t2 in
      (match expected_ty with
      | Imp (ty_arg, ty_res) ->
          check_type ctx t1 (Imp (inferred_t2_ty, ty_res));
          if ty_arg <> inferred_t2_ty then raise Type_error
      | _ -> raise Type_error)
  | Pair (t1, t2) ->
      (match expected_ty with
      | And (ty1, ty2) ->
          check_type ctx t1 ty1;
          check_type ctx t2 ty2
      | _ -> raise Type_error)
  | Fst t ->
      let inferred_ty = infer_type ctx t in
      (match inferred_ty with
      | And (ty1, _) ->
          if ty1 <> expected_ty then raise Type_error
      | _ -> raise Type_error)
  | Snd t ->
      let inferred_ty = infer_type ctx t in
      (match inferred_ty with
      | And (_, ty2) ->
          if ty2 <> expected_ty then raise Type_error
      | _ -> raise Type_error)
  | Inl (t, _ty) ->
      let inferred_ty = infer_type ctx t in
      (match expected_ty with
      | Or (ty_l, _) ->
          if inferred_ty <> ty_l then raise Type_error
      | _ -> raise Type_error)
  | Inr (t, _ty) ->
      let inferred_ty = infer_type ctx t in
      (match expected_ty with
      | Or (_, ty_r) ->
          if inferred_ty <> ty_r then raise Type_error
      | _ -> raise Type_error)
  | Case (t, (x, tm1), (y, tm2)) ->
      (match infer_type ctx t with
      | Or (ty_l, ty_r) ->
          let ctx1 = (x, ty_l) :: ctx in
          let ctx2 = (y, ty_r) :: ctx in
          check_type ctx1 tm1 expected_ty;
          check_type ctx2 tm2 expected_ty
      | _ -> raise Type_error)
  | Tru ->
      if expected_ty <> True then raise Type_error
  | Fls ->
      if expected_ty <> False then raise Type_error
  | Absurd (t, _ty) ->
      let inferred_ty = infer_type ctx t in
      (match inferred_ty with
      | False -> ()
      | _ -> raise Type_error)


let () =
  let ctx = [] in
  (* Test case 1: λ(x: A). x has type A → A *)
  let t1 = Abs ("x", TVar "A", Var "x") in
  (try
     check_type ctx t1 (Imp (TVar "A", TVar "A"));
     print_endline "Test case 1 passed"
   with Type_error ->
     print_endline "Test case 1 failed");

  (* Test case 2: λ(x: A). x does not have type B → B *)
  (try
     check_type ctx t1 (Imp (TVar "B", TVar "B"));
     print_endline "Test case 2 failed"
   with Type_error ->
     print_endline "Test case 2 passed");

  (* Test case 3: x does not have type A *)
  let t2 = Var "x" in
  (try
     check_type ctx t2 (TVar "A");
     print_endline "Test case 3 failed"
   with Type_error ->
     print_endline "Test case 3 passed")

(*1.8*)
let and_comm =
  Abs ("p", And (TVar "A", TVar "B"), 
       Pair (Snd (Var "p"), Fst (Var "p"))) 

let () =
  print_endline (string_of_ty (infer_type [] and_comm))

(*1.9*)
(*  (⊤ ⇒ A) ⇒ A  *)
let truth_implies_a =
  Abs ("f", Imp (True, TVar "A"), 
       App (Var "f", Tru))         

(*  (⊤ ⇒ A) ⇒ A *)
let () =
  print_endline (string_of_ty (infer_type [] truth_implies_a))

(*1.10*)
let or_comm =
  Abs ("p", Or (TVar "A", TVar "B"),         
       Case (Var "p",                         
             ("x", Inr (Var "x", Or (TVar "B", TVar "A"))),  
             ("y", Inl (Var "y", Or (TVar "B", TVar "A"))))) 

(*  (A ∨ B) ⇒ (B ∨ A) *)
let () =
  print_endline (string_of_ty (infer_type [] or_comm))

(*1.11*)
let falsity_implies_b =
  Abs ("p", And (TVar "A", Imp (TVar "A", False)),  
       Absurd (
         App (Snd (Var "p"), Fst (Var "p")),         
         TVar "B"))                                

(* test (A ∧ (A ⇒ ⊥)) ⇒ B *)
let () =
  print_endline (string_of_ty (infer_type [] falsity_implies_b))


let () =
  let l = [
    "A => B";
    "A ⇒ B";      
    "A /\\ B";
    "A ∧ B";      
    "T";
    "A \\/ B";
    "A ∨ B";       
    "_";
    "not A";
    "¬ A";
  ] in
  List.iter (fun s ->
    try
      let parsed_ty = ty_of_string s in
      Printf.printf "the parsing of %S is %s\n%!" s (string_of_ty parsed_ty)
    with _ ->
      Printf.printf "the parsing of %S failed\n%!" s
  ) l


let () =
  let l = [
    "t u v";
    "fun (x : A) -> t";
    "λ (x : A) → t";  
    "(t , u)";
    "fst(t)";
    "snd(t)";
    "()";
    "case t of x -> u | y -> v";
    "left(t,B)";
    "right(A,t)";
    "absurd(t,A)";
  ] in
  List.iter (fun s ->
    try
      let parsed_tm = tm_of_string s in
      Printf.printf "the parsing of %S is %s\n%!" s (string_of_tm parsed_tm)
    with _ ->
      Printf.printf "the parsing of %S failed\n%!" s
  ) l

(* 2.1 *)
let string_of_ctx (ctx : context) : string =
  let ctx_strings = List.map (fun (v, t) -> v ^ " : " ^ string_of_ty t) ctx in
  String.concat ", " ctx_strings

(* 2.2 *)
type sequent = context * ty

let string_of_sequent ((ctx, ty) : sequent) : string =
  let ctx_str = string_of_ctx ctx in
  let ty_str = string_of_ty ty in
  ctx_str ^ " ⊢ " ^ ty_str

(* 2.3, 2.6 with fixed "cut" command *)
let rec prove env a =
  print_endline (string_of_sequent (env, a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env a in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  match cmd with
  | "intro" ->
     (
       match a with
       | Imp (a, b) ->
          if arg = "" then error "Please provide an argument for intro." else
            let x = arg in
            let t = prove ((x, a) :: env) b in
            Abs (x, a, t)
       | _ -> error "Don't know how to introduce this."
     )
  | "exact" ->
     let t = tm_of_string arg in
     if infer_type env t <> a then error "Not the right type."
     else t
  | "elim" ->
     let t = tm_of_string arg in
     (match infer_type env t with
      | Imp (ty1, ty2) when ty2 = a ->
         let u = prove env ty1 in
         App (t, u)
      | _ -> error "Cannot eliminate: not an implication of the right form")
  | "cut" ->
   let a' = ty_of_string arg in
   let q = prove env (Imp(a', a)) in
   let p = prove env a' in
   App(q, p)
  | cmd -> error ("Unknown command: " ^ cmd)

let () =
  (* Interactive Prover *)
  (* print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string  "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok."; *)

  (* Context and Sequent Test *)
  let ctx = [("x", Imp (TVar "A", TVar "B")); ("y", And (TVar "A", TVar "B")); ("Z", True)] in
  print_endline ("Context string: " ^ string_of_ctx ctx);
  let seq = (ctx, TVar "A") in
  print_endline ("Sequent string: " ^ string_of_sequent seq)


  (* 2.5 *)
  let () =
  (* open files that to be proved *)
  let infile = open_in "s.proof" in
  print_endline "Reading formula from file...";
  let a = input_line infile in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  
  let rec prove_with_file env a =
    print_endline (string_of_sequent (env, a));
    print_string "? "; flush_all ();
    try
      let cmd = input_line infile in
      let cmd, arg =
        let n = try String.index cmd ' ' with Not_found -> String.length cmd in
        let c = String.sub cmd 0 n in
        let a = String.sub cmd n (String.length cmd - n) in
        let a = String.trim a in
        c, a
      in
      match cmd with
      | "intro" ->
         (match a with
          | Imp (a, b) ->
             if arg = "" then failwith "Please provide an argument for intro." else
               let x = arg in
               let t = prove_with_file ((x, a) :: env) b in
               Abs (x, a, t)
          | _ -> failwith "Don't know how to introduce this.")
      | "exact" ->
         let t = tm_of_string arg in
         if infer_type env t <> a then failwith "Not the right type."
         else t
      | "elim" ->
         let t = tm_of_string arg in
         (match infer_type env t with
          | Imp (ty1, ty2) when ty2 = a ->
             let u = prove_with_file env ty1 in
             App (t, u)
          | _ -> failwith "Cannot eliminate: not an implication of the right form")
      | "cut" ->
        let a' = ty_of_string arg in
        let q = prove_with_file env (Imp(a', a)) in
        let p = prove_with_file env a' in
        App(q, p)

      | cmd -> failwith ("Unknown command: " ^ cmd)
    with End_of_file -> failwith "Unexpected end of file"
  in
  let t = prove_with_file [] a in
  close_in infile;

  (* 打印证明结果 *)
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok.";
