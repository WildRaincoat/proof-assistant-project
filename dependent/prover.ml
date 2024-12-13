let () = Printexc.record_backtrace true

(** Variables. *)
type var = string

(** Expressions. *)
type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr 
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr

(*5.5*)
type context = (var * (expr * expr option)) list
(*5.9*)
exception Type_error of string


(* Fill me in! *)
(* 5.1 *)
let rec string_of_expr e =
  match e with
  | Type -> "Type"
  | Var v -> v
  | App (e1, e2) -> "(" ^ string_of_expr e1 ^ " " ^ string_of_expr e2 ^ ")"
  | Abs (v, t, e) -> "(λ (" ^ v ^ " : " ^ string_of_expr t ^ ") -> " ^ string_of_expr e ^ ")"
  | Pi (v, t, e) -> "(Π (" ^ v ^ " : " ^ string_of_expr t ^ ") -> " ^ string_of_expr e ^ ")"
  | Nat -> "Nat"
  | Z -> "Z"
  | S e -> "(S " ^ string_of_expr e ^ ")"
  | Ind (p, z, s, n) ->
      "(Ind " ^ string_of_expr p ^ " " ^ string_of_expr z ^ " " ^ string_of_expr s ^ " " ^ string_of_expr n ^ ")"
  | Eq (e1, e2) -> "(Eq " ^ string_of_expr e1 ^ " " ^ string_of_expr e2 ^ ")"
  | Refl e -> "(Refl " ^ string_of_expr e ^ ")"
  | J (p, r, x, y, eq) ->
      "(J " ^ string_of_expr p ^ " " ^ string_of_expr r ^ " " ^ string_of_expr x ^ " " ^ string_of_expr y ^ " " ^ string_of_expr eq ^ ")"
(*5.2*)
let rec to_string expr =
  match expr with
  | Type -> "Type"
  | Var x -> x
  | App (e1, e2) -> "(" ^ to_string e1 ^ " " ^ to_string e2 ^ ")"
  | Abs (x, t, e) -> "(λ (" ^ x ^ " : " ^ to_string t ^ ") -> " ^ to_string e ^ ")"
  | Pi (x, t1, t2) -> "(Π (" ^ x ^ " : " ^ to_string t1 ^ ") -> " ^ to_string t2 ^ ")"
  | Nat -> "Nat"
  | Z -> "Z"
  | S e -> "(S " ^ to_string e ^ ")"
  | Ind (e1, e2, e3, e4) -> 
      "(Ind " ^ to_string e1 ^ " " ^ to_string e2 ^ " " ^ to_string e3 ^ " " ^ to_string e4 ^ ")"
  | Eq (e1, e2) -> "(Eq " ^ to_string e1 ^ " " ^ to_string e2 ^ ")"
  | Refl e -> "(Refl " ^ to_string e ^ ")"
  | J (e1, e2, e3, e4, e5) -> 
      "(J " ^ to_string e1 ^ " " ^ to_string e2 ^ " " ^ to_string e3 ^ " " ^ to_string e4 ^ " " ^ to_string e5 ^ ")"

(* 5.3 *)
let id_counter = ref 0

let fresh_var () =
  let new_var = "x" ^ string_of_int !id_counter ^ "'" in
  id_counter := !id_counter + 1; (* 增加计数器 *)
  new_var

(* 5.4 *)
let rec subst x t u =
  match u with
  | Type -> Type
  | Var y -> if y = x then t else Var y
  | App (e1, e2) -> App (subst x t e1, subst x t e2)
  | Abs (y, ty, body) ->
      if y = x then Abs (y, subst x t ty, body) (* Skip substitution inside shadowed variable *)
      else
        let fresh = fresh_var () in
        let renamed_body = subst y (Var fresh) body in
        Abs (fresh, subst x t ty, subst x t renamed_body)
  | Pi (y, ty, body) ->
      if y = x then Pi (y, subst x t ty, body)
      else
        let fresh = fresh_var () in
        let renamed_body = subst y (Var fresh) body in
        Pi (fresh, subst x t ty, subst x t renamed_body)
  | Nat -> Nat
  | Z -> Z
  | S e -> S (subst x t e)
  | Ind (p, z, s, n) ->
      Ind (subst x t p, subst x t z, subst x t s, subst x t n)
  | Eq (e1, e2) -> Eq (subst x t e1, subst x t e2)
  | Refl e -> Refl (subst x t e)
  | J (p, r, x_eq, y, eq) ->
      J (subst x t p, subst x t r, subst x t x_eq, subst x t y, subst x t eq)


(* 5.5*)
let string_of_context (ctx : context) : string =
  let string_of_binding (x, (ty, value_opt)) =
    match value_opt with
    | None -> x ^ " : " ^ to_string ty
    | Some value -> x ^ " : " ^ to_string ty ^ " = " ^ to_string value
  in
  String.concat "\n" (List.map string_of_binding ctx)

(* 5.6 *)
let rec normalize (ctx : context) (e : expr) : expr =
  match e with
  | Var x -> (
      match List.assoc_opt x ctx with
      | Some (_, Some value) -> normalize ctx value
      | _ -> Var x
    )
  | App (e1, e2) ->
      let n1 = normalize ctx e1 in
      let n2 = normalize ctx e2 in
      (match n1 with
       | Abs (x, _, body) -> normalize ((x, (Type, Some n2)) :: ctx) body
       | _ -> App (n1, n2))
  | Abs (x, ty, body) ->
      let n_ty = normalize ctx ty in
      let n_body = normalize ctx body in
      Abs (x, n_ty, n_body)
  | Pi (x, ty, body) ->
      let n_ty = normalize ctx ty in
      let n_body = normalize ctx body in
      Pi (x, n_ty, n_body)
  | Ind (p, z, s, n) ->
      let n_p = normalize ctx p in
      let n_z = normalize ctx z in
      let n_s = normalize ctx s in
      let n_n = normalize ctx n in
      (match n_n with
       | Z -> n_z
       | S pred -> normalize ctx (App (App (n_s, pred), normalize ctx (Ind (n_p, n_z, n_s, pred))))
       | _ -> Ind (n_p, n_z, n_s, n_n))
  | Eq (e1, e2) ->
      let n1 = normalize ctx e1 in
      let n2 = normalize ctx e2 in
      Eq (n1, n2)
  | Refl e ->
      let n = normalize ctx e in
      Refl n
  | J (p, r, x, y, eq) ->
      let n_p = normalize ctx p in
      let n_r = normalize ctx r in
      let n_x = normalize ctx x in
      let n_y = normalize ctx y in
      let n_eq = normalize ctx eq in
      (match n_eq with
       | Refl v when n_x = v && n_y = v -> n_r
       | _ -> J (n_p, n_r, n_x, n_y, n_eq))
  | _ -> e 

(* 5.7 *)
let rec alpha (expr1 : expr) (expr2 : expr) : bool =
  match (expr1, expr2) with
  | (Type, Type) -> true
  | (Var x, Var y) -> x = y
  | (App (e1, e2), App (e3, e4)) ->
      alpha e1 e3 && alpha e2 e4
  | (Abs (x, t1, e1), Abs (y, t2, e2))
  | (Pi (x, t1, e1), Pi (y, t2, e2)) ->
      let new_var = fresh_var () in
      alpha t1 t2
      && alpha (subst x (Var new_var) e1) (subst y (Var new_var) e2)
  | (Nat, Nat) -> true
  | (Z, Z) -> true
  | (S e1, S e2) -> alpha e1 e2
  | (Ind (p1, z1, s1, n1), Ind (p2, z2, s2, n2)) ->
      alpha p1 p2 && alpha z1 z2 && alpha s1 s2 && alpha n1 n2
  | (Eq (e1, e2), Eq (e3, e4)) -> alpha e1 e3 && alpha e2 e4
  | (Refl e1, Refl e2) -> alpha e1 e2
  | (J (p1, r1, x1, y1, eq1), J (p2, r2, x2, y2, eq2)) ->
      alpha p1 p2 && alpha r1 r2 && alpha x1 x2 && alpha y1 y2 && alpha eq1 eq2
  | _ -> false

(*5.8*)
let conv (ctx : context) (e1 : expr) (e2 : expr) : bool =
  alpha (normalize ctx e1) (normalize ctx e2)

(*5.9*)
let rec infer (ctx : context) (e : expr) : expr =
  match e with
  (* 基础类型 *)
  | Type -> Type
  | Var x -> (
      match List.assoc_opt x ctx with
      | Some (ty, _) -> ty
      | None -> raise (Type_error ("Unbound variable: " ^ x))
    )
  (* 应用规则 *)
  | App (e1, e2) -> (
      match infer ctx e1 with
      | Pi (x, ty1, ty2) ->
          let ty_e2 = infer ctx e2 in
          if conv ctx ty1 ty_e2 then subst x e2 ty2
          else raise (Type_error "Function argument type mismatch")
      | _ -> raise (Type_error "Trying to apply a non-function")
    )
  (* 抽象规则 *)
  | Abs (x, ty, body) ->
      let ctx' = (x, (ty, None)) :: ctx in
      let ty_body = infer ctx' body in
      Pi (x, ty, ty_body)
  (* 依赖类型规则 *)
  | Pi (x, ty1, ty2) ->
      let ty1' = infer ctx ty1 in
      let ctx' = (x, (ty1, None)) :: ctx in
      let ty2' = infer ctx' ty2 in
      if conv ctx ty1' Type && conv ctx ty2' Type then Type
      else raise (Type_error "Ill-formed Pi type")
  (* 自然数规则 *)
  | Nat -> Type
  | Z -> Nat
  | S n -> 
      let ty_n = infer ctx n in
      if conv ctx ty_n Nat then Nat
      else raise (Type_error "S applied to non-Nat")
  | Ind (p, z, s, n) -> (
      match infer ctx p with
      | Pi ("x", Nat, Type) -> (
          let ty_z = infer ctx z in
          if not (conv ctx ty_z (App (p, Z))) then
            raise (Type_error "Zero case mismatch in Ind");

          let ty_s = infer ctx s in
          if not (conv ctx ty_s (Pi ("x", Nat, Pi ("y", App (p, Var "x"), App (p, S (Var "x")))))) then
            raise (Type_error "Successor case mismatch in Ind");

          let ty_n = infer ctx n in
          if not (conv ctx ty_n Nat) then
            raise (Type_error "Ind applied to non-Nat");

          App (p, n)
        )
      | _ -> raise (Type_error "P is not a dependent type in Ind")
    )
  (* 相等类型规则 *)
  | Eq (a, b) ->
      let ty_a = infer ctx a in
      let ty_b = infer ctx b in
      if conv ctx ty_a ty_b then Type
      else raise (Type_error "Equality type mismatch")
  | Refl a ->
      let ty_a = infer ctx a in
      ty_a
  | J (p, r, x, y, eq) -> (
      let ty_p = infer ctx p in
      let ty_r = infer ctx r in
      let ty_x = infer ctx x in
      let ty_y = infer ctx y in
      let ty_eq = infer ctx eq in

      if not (conv ctx ty_p Type) then
        raise (Type_error "J: P is not a type");

      if not (conv ctx ty_eq (Eq (ty_x, ty_y))) then
        raise (Type_error "J: Equality type mismatch");

      ty_r
    )


(* 5.10: Type checking *)
let check (ctx : context) (e : expr) (expected_ty : expr) : unit =
  let inferred_ty = infer ctx e in
  if not (conv ctx inferred_ty expected_ty) then
    raise (Type_error
      ("Type mismatch: inferred type " ^ to_string inferred_ty ^
       " does not match expected type " ^ to_string expected_ty))


(* 测试代码 *)
let () =
  let expr_example = 
    Pi ("x", Type, Pi ("y", Var "x", Var "y"))
  in
  print_endline (to_string expr_example);  (* expect： (Π (x : Type) -> (Π (y : x) -> y)) *)

  let example_expr = Pi ("x", Type, Pi ("y", Var "x", Var "y")) in
  print_endline (string_of_expr example_expr)

let () =
  let var1 = fresh_var () in
  let var2 = fresh_var () in
  let var3 = fresh_var () in
  Printf.printf "Generated variables: %s, %s, %s\n" var1 var2 var3;

  let example = Abs ("x", Type, App (Var "x", Var "y")) in
  let result = subst "y" (Var "z") example in
  print_endline (to_string result);
  (* 期望输出：λ (x : Type) -> (x z) *)
  
  let pi_example = Pi ("x", Type, Var "x") in
  let pi_result = subst "x" (Var "z") pi_example in
  print_endline (to_string pi_result);
  (* 期望输出：Π (x0' : Type) -> x0' *)

  let test_context = [
    ("x", (Type, None));  (* x : Type *)
    ("y", (Var "x", Some (App (Var "x", Z))));  (* y : x = (x Z) *)
    ("z", (Pi ("x", Type, Var "x"), None))  (* z : Π (x : Type) -> x *)
  ] in
  print_endline (string_of_context test_context);

  let ctx : context = [
    ("x", (Type, None));
    ("y", (Var "x", Some (App (Var "x", Z))));
    ("z", (Pi ("x", Type, Var "x"), None))
  ] in

  let expr = App (Abs ("x", Type, Var "x"), Z) in
  let normalized_expr = normalize ctx expr in
  print_endline ("Normalized: " ^ to_string normalized_expr);
  (*5.7*)
  let expr1 = Abs ("x", Type, Var "x") in
  let expr2 = Abs ("y", Type, Var "y") in
  let result = alpha expr1 expr2 in
  Printf.printf "Are the expressions α-convertible? %b\n" result;

  let expr3 = Pi ("x", Type, Var "x") in
  let expr4 = Pi ("y", Type, Var "y") in
  let result2 = alpha expr3 expr4 in
  Printf.printf "Are the expressions α-convertible? %b\n" result2;

(* 测试 conv 函数 *)

  (* 首先定义 conv 函数： *)
  let conv (ctx : context) (e1 : expr) (e2 : expr) : bool =
    alpha (normalize ctx e1) (normalize ctx e2)
  in

  let ctx = [] in

  (* 5.8 *)
  let e1 = Abs("x", Type, Var "x") in
  let e2 = Abs("y", Type, Var "y") in
  Printf.printf "Test 1: %b (it's indeed true)\n" (conv ctx e1 e2);

  let e3 = App(Abs("x", Type, Var "x"), Z) in
  let e4 = Z in
  Printf.printf "Test 2: %b (also true)\n" (conv ctx e3 e4);

  let e5 = Abs("x", Type, Var "x") in
  let e6 = Abs("x", Type, S(Var "x")) in
  Printf.printf "Test 3: %b (not true)\n" (conv ctx e5 e6);
  (*5.9*)
  let ctx = [
    ("x", (Type, None));
    ("y", (Var "x", None));
  ] in

  let e1 = App (Abs ("x", Type, Var "x"), Type) in
  let e2 = Pi ("x", Type, Var "x") in

  try
    let ty_e1 = infer ctx e1 in
    let ty_e2 = infer ctx e2 in
    print_endline ("Type of e1: " ^ to_string ty_e1);
    print_endline ("Type of e2: " ^ to_string ty_e2);
  with Type_error msg ->
    print_endline ("Type error: " ^ msg)
let () =
  let ctx = [
    ("x", (Type, None));
    ("y", (Var "x", None));
    ("f", (Pi ("z", Type, Var "z"), None));
  ] in

  (* 5.9 *)
  let e1 = App (Abs ("x", Type, Var "x"), Type) in
  let expected_ty1 = Type in
  (try
     check ctx e1 expected_ty1;
     print_endline "Test case 1 passed: e1 has the expected type."
   with Type_error msg ->
     print_endline ("Test case 1 failed: " ^ msg));

  (* not matched *)
  let e2 = App (Var "f", Var "y") in
  let expected_ty2 = Var "x" in
  (try
     check ctx e2 expected_ty2;
     print_endline "Test case 2 passed: e2 has the expected type."
   with Type_error msg ->
     print_endline ("Test case 2 failed: " ^ msg));

  let e3 = Var "y" in
  let expected_ty3 = Var "x" in
  (try
     check ctx e3 expected_ty3;
     print_endline "Test case 3 passed: e3 has the expected type."
   with Type_error msg ->
     print_endline ("Test case 3 failed: " ^ msg));

