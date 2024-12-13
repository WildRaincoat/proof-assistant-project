
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
  (*33.1*)  
  | Zero             
  | Succ of tm       
  | Rec of tm * tm * tm 