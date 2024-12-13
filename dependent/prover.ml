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