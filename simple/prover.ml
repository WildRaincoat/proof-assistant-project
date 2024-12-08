let () = Printexc.record_backtrace true

(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  | TVar of tvar
  | Arrow of ty * ty
  | And of ty * ty   
  | Or of ty * ty     
  | True              
  | False            


(*1.2*)
type tm =
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
  | Absurd of tm * ty         
 

(* 1.3 字符串表示函数 *)
(* string_of_ty: 将类型转换为字符串表示 *)
let rec string_of_ty t =
  match t with
  | TVar a -> a
  | Arrow (t1, t2) -> "(" ^ string_of_ty t1 ^ " => " ^ string_of_ty t2 ^ ")"
  | And (t1, t2) -> "(" ^ string_of_ty t1 ^ " ∧ " ^ string_of_ty t2 ^ ")"
  | Or (t1, t2) -> "(" ^ string_of_ty t1 ^ " ∨ " ^ string_of_ty t2 ^ ")"
  | True -> "⊤"
  | False -> "⊥"


(* string_of_tm: 将λ项转换为字符串表示 *)
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


(* 测试示例 *)
let () =
  let ty_example = Arrow(Arrow(TVar "A", TVar "B"), Arrow(TVar "A", TVar "C")) in
  print_endline (string_of_ty ty_example);
  
  let tm_example =
    Abs("f", Arrow(TVar "A", TVar "B"),
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
      Arrow (ty_x, ty_body) (* 函数类型 *)
  | App (t1, t2) ->
      let ty_t1 = infer_type ctx t1 in
      let ty_t2 = infer_type ctx t2 in
      (match ty_t1 with
      | Arrow (ty_arg, ty_res) ->
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
      Arrow (ty_x, ty_body) (* 函数类型 *)
  | App (t1, t2) ->
      let ty_t1 = infer_type ctx t1 in
      let ty_t2 = infer_type ctx t2 in
      (match ty_t1 with
      | Arrow (ty_arg, ty_res) ->
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
      Arrow (ty_x, ty_body)
  | App (t1, t2) ->
      let ty_t1 = infer_type ctx t1 in
      let ty_t2 = infer_type ctx t2 in
      (match ty_t1 with
      | Arrow (ty_arg, ty_res) ->
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
    Abs ("f", Arrow (TVar "A", TVar "B"),
         Abs ("g", Arrow (TVar "B", TVar "C"),
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
      | Arrow (ty_arg, ty_res) ->
          if ty_arg = ty_x then
            let ctx' = (x, ty_x) :: ctx in
            check_type ctx' t_body ty_res
          else raise Type_error
      | _ -> raise Type_error)
  | App (t1, t2) ->
      let inferred_t2_ty = infer_type ctx t2 in
      (match expected_ty with
      | Arrow (ty_arg, ty_res) ->
          check_type ctx t1 (Arrow (inferred_t2_ty, ty_res));
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
     check_type ctx t1 (Arrow (TVar "A", TVar "A"));
     print_endline "Test case 1 passed"
   with Type_error ->
     print_endline "Test case 1 failed");

  (* Test case 2: λ(x: A). x does not have type B → B *)
  (try
     check_type ctx t1 (Arrow (TVar "B", TVar "B"));
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
  Abs ("p", And (TVar "A", TVar "B"),  (* 输入类型是 A ∧ B *)
       Pair (Snd (Var "p"), Fst (Var "p")))  (* 返回 B ∧ A *)

let () =
  print_endline (string_of_ty (infer_type [] and_comm))

(*1.9*)
(* 定义 (⊤ ⇒ A) ⇒ A 的项 *)
let truth_implies_a =
  Abs ("f", Arrow (True, TVar "A"),  (* 输入类型为 ⊤ ⇒ A *)
       App (Var "f", Tru))           (* 应用 f 到常量 Tru *)

(* 测试 (⊤ ⇒ A) ⇒ A *)
let () =
  print_endline (string_of_ty (infer_type [] truth_implies_a))

(*1.10*)
(* 定义 (A ∨ B) ⇒ (B ∨ A) 的项 *)
let or_comm =
  Abs ("p", Or (TVar "A", TVar "B"),            (* 输入类型 A ∨ B *)
       Case (Var "p",                          (* 模式匹配 p *)
             ("x", Inr (Var "x", Or (TVar "B", TVar "A"))),  (* 左注入转右注入 *)
             ("y", Inl (Var "y", Or (TVar "B", TVar "A"))))) (* 右注入转左注入 *)

(* 测试 (A ∨ B) ⇒ (B ∨ A) *)
let () =
  print_endline (string_of_ty (infer_type [] or_comm))

(*1.11*)
(* 定义 (A ∧ (A ⇒ ⊥)) ⇒ B 的项 *)
let falsity_implies_b =
  Abs ("p", And (TVar "A", Arrow (TVar "A", False)),  (* 输入类型 A ∧ (A ⇒ ⊥) *)
       Absurd (
         App (Snd (Var "p"), Fst (Var "p")),         (* 应用 A ⇒ ⊥ 到 A 得到 ⊥ *)
         TVar "B"))                                 (* 从 ⊥ 推导出 B *)

(* 测试 (A ∧ (A ⇒ ⊥)) ⇒ B *)
let () =
  print_endline (string_of_ty (infer_type [] falsity_implies_b))

