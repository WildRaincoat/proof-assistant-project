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

(* 测试代码 *)
let () =
  let expr_example = 
    Pi ("x", Type, Pi ("y", Var "x", Var "y"))
  in
  print_endline (to_string expr_example);  (* expect： (Π (x : Type) -> (Π (y : x) -> y)) *)

  let example_expr = Pi ("x", Type, Pi ("y", Var "x", Var "y")) in
  print_endline (string_of_expr example_expr)
