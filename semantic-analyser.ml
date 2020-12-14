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
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
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

let read_depth = ref 0 ;;
let write_depth = ref 0 ;; 

let rec find_var_in_paramlist x paramlst index =
  match paramlst with
  | [] -> -1
  | h :: t -> if x = h then index else find_var_in_paramlist x t (index + 1);;

let rec find_var_in_boundlist x boundlst index = 
  match boundlst with
  | [] -> -1
  | lst1 :: lst2 -> if (List.mem x lst1) == true then index else find_var_in_boundlist x lst2 (index + 1)

let extract_var expr = 
                    match expr with
                    | Var'(x) -> x  
                    | _ -> raise X_syntax_error                             

let rec calculate_lexical_addresses paramList boundList expr  =  
                                    match expr with 
                                    | Const(x) -> Const'(x)
                                    | If(test, dit, dif) ->  If' ((calculate_lexical_addresses paramList boundList test) , 
                                                                 (calculate_lexical_addresses paramList boundList dit) , 
                                                                 (calculate_lexical_addresses paramList boundList dif))
                                    | Def(var, value) -> Def'(extract_var(calculate_lexical_addresses paramList boundList var) , calculate_lexical_addresses paramList boundList value)
                                    | Set(var, value) -> Set'(extract_var(calculate_lexical_addresses paramList boundList var), calculate_lexical_addresses paramList boundList value)  
                                    | Or(expr) -> Or'(List.map (fun(y) -> calculate_lexical_addresses paramList boundList y) expr) 
                                    | Seq(expr) -> Seq'(List.map (fun(y) -> calculate_lexical_addresses paramList boundList y) expr)
                                    | Applic(rator, rands) -> Applic' (calculate_lexical_addresses paramList boundList rator, List.map (fun(y) -> calculate_lexical_addresses paramList boundList y) rands)
                                    | Var(x) -> if (List.mem x paramList) == true then Var'(VarParam(x, find_var_in_paramlist x paramList 0))
                                     else 
                                     let major_index = find_var_in_boundlist x boundList 0 in
                                     if(major_index == -1) then Var'(VarFree(x)) else
                                     let minor_list = List.nth boundList major_index in
                                     let minor_index = find_var_in_paramlist x minor_list 0 in
                                     Var'(VarBound(x,major_index,minor_index))

                                    | LambdaSimple(args, body) -> LambdaSimple'(args, (calculate_lexical_addresses args (paramList :: boundList) body))
                                    | LambdaOpt(args, optArgs, body) -> LambdaOpt'(args, optArgs, (calculate_lexical_addresses (List.append args [optArgs]) (paramList :: boundList) body))

let annotate_lexical_addresses e = calculate_lexical_addresses [] [] e;;
                                


let rec calculate_tail_calls tp expr = 
                                match expr with      
                                | Const'(x) -> Const'(x)
                                | Var'(x) -> Var'(x)
                                | Or'(exprs) -> Or'(calculate_last_tail tp exprs)
                                | If'(test, dit, dif) -> If'(calculate_tail_calls false test, calculate_tail_calls tp dit, calculate_tail_calls tp dif)
                                | Def'(var, value) -> Def'(var, calculate_tail_calls false value)
                                | Set'(var, value) -> Set'(var, calculate_tail_calls false value)
                                | Seq'(exprs) -> Seq'(calculate_last_tail tp exprs)
                                | LambdaSimple'(args, body) -> LambdaSimple'(args, calculate_tail_calls true body)
                                | LambdaOpt'(args, optArgs, body) -> LambdaOpt'(args, optArgs, calculate_tail_calls true body)
                                | Applic'(rator, rands) -> match tp with  
                                                           | true -> ApplicTP'(calculate_tail_calls false rator, List.map (fun x -> calculate_tail_calls false x) rands)
                                                           | _ -> Applic'(calculate_tail_calls false rator, List.map (fun x -> calculate_tail_calls false x) rands)


and calculate_last_tail tp exprs = 
                              match exprs with  
                              | last :: [] -> [calculate_tail_calls tp last]
                              | curr :: rest ->  [(calculate_tail_calls false curr)] @ (calculate_last_tail tp rest)
                              | _ -> raise X_syntax_error



let annotate_tail_calls e = let tp = false in
                            calculate_tail_calls tp e;;

(*TODO: check if removing box_list will succeed*)
let rec calculate_boxing box_list expr = 
                                  match expr with 
                                  | Const'(x) -> Const'(x)
                                  | Var'(var) -> box_get_var var box_list
                                  | If'(test, dit, dif) -> If' (calculate_boxing box_list test, calculate_boxing box_list dit,calculate_boxing box_list dif)
                                  | Def'(var, value) -> Def'(var, calculate_boxing box_list value)
                                  | Or'(exprs) -> Or'(List.map (fun x -> calculate_boxing box_list x) exprs)
                                  | Set'(var, value) -> box_set_var var value box_list
                                  | Seq'(exprs) -> Seq'(List.map (fun x -> calculate_boxing box_list x) exprs) (*TODO change seq to match 3.4.1*)
                                  | LambdaSimple'(args, body) -> calculate_box_lambda args body box_list expr 
                                  | LambdaOpt'(args, optArgs, body) -> calculate_box_lambda (List.append args [optArgs]) body box_list expr 
                                  | Applic'(rator, rands) -> Applic'(calculate_boxing box_list rator, List.map(fun x -> calculate_boxing box_list x) rands)
                                  | ApplicTP'(rator, rands) -> ApplicTP'(calculate_boxing box_list rator, List.map(fun x -> calculate_boxing box_list x) rands)
                                  | rest -> rest


and box_get_var var box_list = 
                  match var with  
                  | VarFree(varname) -> Var'(var)
                  | _ ->  if ((List.mem (Var'(var)) box_list)) then BoxGet'(var) else Var'(var)

and box_set_var var value box_list = 
                           match var with
                           | VarFree(varname) -> Set'(var, calculate_boxing box_list value)
                           | _ -> if (List.mem (Var'(var)) box_list) then BoxSet'(var, calculate_boxing box_list value) else Set'(var, calculate_boxing box_list value)                 
                   
and calculate_box_lambda args body box_list lambda_type = 
                                                       let updated_box_list = List.map (fun x -> 
                                                                                            match x with 
                                                                                            | Var'(VarParam(varname, index)) -> Var'(VarBound(varname, 0, index))
                                                                                            | Var'(VarBound(varname, minor_index, major_index)) ->  Var'(VarBound(varname, minor_index + 1, major_index))
                                                                                            | _-> raise X_syntax_error) 
                                                                                            box_list in
                                                       let should_be_boxed = List.filter (fun(arg) -> shouldBeBoxed arg body) args in
                                                       let wrapped_boxed_vars = List.map (fun var -> Var'(VarParam(var, find_var_in_paramlist var args 0))) should_be_boxed in
                                                       let final_box_list = List.map (fun var -> Set'(Var'(VarParam(var, find_var_in_paramlist var args 0 )),
                                                                                                      Box'(VarParam(var, find_var_in_paramlist var args 0))))
                                                                                                      should_be_boxed in
                                                       let boxed_body = (calculate_boxing body (List.append newParamsToWraplist updatedWrapList)) in
                                                       let boss = 
                                                              match final_box_list with
                                                              | [] ->
                                                                    (match lambda_type with
                                                                    | LambdaSimple'(args, body) -> LambdaSimple' (args, boxed_body)
                                                                    | LambdaOpt'(params, optParams, body) -> LambdaOpt'(params, optParams, boxed_body)
                                                                    | _ -> raise X_syntax_error 
                                                                    )
                                                              | _ -> 
                                                                    (match lambda_type with
                                                                    | LambdaSimple'(args, body) -> LambdaSimple'(args, Seq'(List.append (final_box_list [boxed_body])))
                                                                    | LambdaOpt'(params, optParams, body) -> LambdaOpt'(params, optParams, Seq'(List.append (final_box_list [boxed_body])))
                                                                    | _ -> raise X_syntax_error
                                                                    )
                                                              in
                                                              boss                                               

                                                       



and shouldBeBoxed arg body =
                    let read_occurrences = calculate_read_occurrences arg body in
                    let write_occurrences = calculate_write_occurrences arg body in 
                    if(List.length read_occurrences == 0 || List.length read_occurrences == 0) then false 
                    else 
                    let res1 = List.map (fun x -> compare_read_write x read_occurrences) write_occurrences in
                    let res2 = List.map (fun x -> compare_read_write x write_occurrences) read_occurrences in 
                    if(List.mem true res1 || List.mem true res2) then true else false
                          
                     
and calculate_read_occurrences arg body = 
                                      match body with 
                                      | Const'(x) -> [] 
                                      | Var'(var) -> calculate_read_var var arg
                                      | If'(test, dit, dif) -> List.append((calculate_read_occurrences arg test) 
                                                              (List.append ((calculate_read_occurrences arg dit) (calculate_read_occurrences arg dif))))
                                      | Def'(var, value) -> raise X_syntax_error 
                                      | Or'(exprs) -> List.flatten(List.map(fun x -> calculate_read_occurrences arg x) exprs)
                                      | Seq'(exprs) -> List.flatten(List.map(fun x -> calculate_read_occurrences arg x) exprs) (*TODO change seq to match 3.4.1*)
                                      | Set'(var, value) -> calculate_read_occurrences arg value
                                      | Applic'(rator, rands) -> (calculate_read_occurrences arg rator) @
                                                                 List.flatten(List.map (fun x -> calculate_read_occurrences arg x) rands)
                                      | ApplicTP'(rator, rands) -> (calculate_read_occurrences arg rator) @
                                                                 List.flatten(List.map (fun x -> calculate_read_occurrences arg x) rands)
                                      | LambdaSimple'(args, innerbody) -> calculate_read_innerLambda arg args innerbody
                                      | LambdaOpt'(args, optArgs, innerbody) -> calculate_read_innerLambda arg (List.append args [optArgs]) innerbody    
                                      | _ -> []                                                   


and calculate_read_innerLambda arg args innerbody = 
                                                if ((List.mem arg args) == true) then [] else 
                                                begin 
                                                read_depth := !read_depth + 1  (*TODO  change to func parameter*)                                    
                                                if (List.length (calculate_read_occurrences arg innerbody) == 0) then []
                                                else [!read_depth] 
                                                end
and calculate_read_var var arg = 
                              match var with 
                              | VarFree(varname) -> []
                              | VarParam(varname, minor_index) -> if (varname != arg) then [] else [0] 
                              | VarBound(varname, minor_index, major_index) -> if (varname != arg) then [] else [0]

and compare_read_write arg occurrences = 
                                      match occurrences with
                                      | [] -> false 
                                      | curr :: rest -> if (compare arg curr != 0) then true else compare_read_write arg rest

and calculate_write_occurrences arg body = 
                                        match body with
                                        | Const'(x) -> []
                                        | If'(test, dit, dif) -> List.append((calculate_write_occurrences arg test) 
                                                                 (List.append ((calculate_write_occurrences arg dit) (calculate_write_occurrences arg dif))))
                                        | Def'(var, value) -> raise X_syntax_error
                                        | Or'(exprs) -> List.flatten(List.map(fun x -> calculate_write_occurrences arg x) exprs)                       
                                        | Seq'(exprs) -> List.flatten(List.map(fun x -> calculate_write_occurrences arg x) exprs) (*TODO change seq to match 3.4.1*)
                                        | Set'(Var'(var), value) -> calculate_write_var var value arg
                                        | Applic'(rator, rands) -> (calculate_write_occurrences arg rator) @
                                                                   List.flatten(List.map (fun x -> calculate_write_occurrences arg x) rands)
                                        | ApplicTP'(rator, rands) -> (calculate_write_occurrences arg rator) @
                                                                     List.flatten(List.map (fun x -> calculate_write_occurrences arg x) rands)
                                        | LambdaSimple'(args, innerbody) -> calculate_write_innerLambda arg args innerbody
                                        | LambdaOpt'(args, optArgs, innerbody) -> calculate_write_innerLambda arg (List.append args [optArgs]) innerbody
                                        | _ -> []

and calculate_write_var var value arg = 
                                match var with
                                | VarFree(varname) -> if (varname != arg) then (calculate_write_occurrences arg value) 
                                                                          else (List.append [0] (calculate_write_occurrences arg value))
                                | VarParam(varname, minor_index) -> if (varname != arg) then (calculate_write_occurrences arg value) 
                                                                    else (List.append [0] (calculate_write_occurrences arg value)) 
                                | VarBound(varname, minor_index, major_index) -> if (varname != arg) then (calculate_write_occurrences arg value) 
                                                                                 else (List.append [0] (calculate_write_occurrences arg value))                                                                                                                        

and calculate_write_innerLambda arg args innerbody = 
                                                if ((List.mem arg args) == true) then [] else 
                                                begin 
                                                write_depth := !write_depth + 1  (*TODO  change to func parameter*)                                    
                                                if (List.length (calculate_write_occurrences arg innerbody) == 0) then []
                                                else [!write_depth] 
                                                end 

let box_set e = calculate_boxing [] e;;

let run_semantics expr =
  box_set
    annotate_tail_calls
       (annotate_lexical_addresses expr);;
  
end;; (* struct Semantics *)



