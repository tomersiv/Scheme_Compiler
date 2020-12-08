#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 = 
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let rec find_var_in_paramlist x lst =
  match lst with
  | [] -> raise (Failure "Not Found")
  | h :: t -> if x = h then 0 else 1 + find x t;;

let rec calculate_lexical_addresses paramList boundList expr  =  
                                    match expr with 
                                    | Const(x) -> Const'(x)
                                    (* | Def(var,value) -> Def'(var, calculate_lexical_addresses paramList boundList value)
                                    | Set(var,value) -> Set'(var, calculate_lexical_addresses paramList boundList value)   *)
                                    | Or(expr) -> Or'(List.map (fun(y) -> calculate_lexical_addresses paramList boundList y) expr) 
                                    | Seq(expr) -> Seq'(List.map (fun(y) -> calculate_lexical_addresses paramList boundList y) expr)
                                    | Applic(expr, exprList) -> Applic' (calculate_lexical_addresses paramList boundList expr, List.map (fun(y) -> calculate_lexical_addresses paramList boundList y) exprList)
                                    | Var(x) -> If (List.mem x paramList) == true then Var'(x, find_var_in_paramlist x paramList) 
                                    | LambdaSimple(args, body) -> LambdaSimple'(args, calculate_lexical_addresses params (List.append paramList boundList) body )
                                    | LambdaOpt(args, optArgs, body) -> LambdaOpt'(args, optArgs, (calculate_lexical_addresses (List.append args [optArgs]) (List.append paramList boundList)))

let annotate_lexical_addresses e = calculate_lexical_addresses [] [] e;;
                                
 

let annotate_tail_calls e = raise X_not_yet_implemented;;

let box_set e = raise X_not_yet_implemented;;

let run_semantics expr =
  (* box_set
    (annotate_tail_calls *)
       (annotate_lexical_addresses expr);;
  
end;; (* struct Semantics *)

open Semantics;;


