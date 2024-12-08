let () = Printexc.record_backtrace true

(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  | TVar of tvar
  | Arrow of ty * ty

(*1.2*)
type tm =
  | Var of var
  | Abs of var * ty * tm  
  | App of tm * tm        

(* 1.3 字符串表示函数 *)
(* string_of_ty: 将类型转换为字符串表示 *)
let rec string_of_ty t =
  match t with
  | TVar a -> a
  | Arrow (t1, t2) ->
      "(" ^ string_of_ty t1 ^ " => " ^ string_of_ty t2 ^ ")"

(* string_of_tm: 将λ项转换为字符串表示 *)
let rec string_of_tm t =
  match t with
  | Var x -> x
  | Abs(x, ty, tm) ->
      "(fun (" ^ x ^ " : " ^ string_of_ty ty ^ ") -> " ^ string_of_tm tm ^ ")"
  | App(tm1, tm2) ->
      "(" ^ string_of_tm tm1 ^ " " ^ string_of_tm tm2 ^ ")"

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
let rec infer_type (ctx: context) (t: tm) : ty =
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