(* expr.mli *)
type tvar = string
type var = string

type ty =
  | TVar of tvar
  | Imp of ty * ty
  | And of ty * ty
  | Or of ty * ty
  | True
  | False
  | Nat

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
  | Zero               (* 新增：表示0 *)
  | Succ of tm         (* 新增：表示后继 *)
  | Rec of tm * tm * tm (* 新增：递归。通常为 Rec(n, base, step) *)