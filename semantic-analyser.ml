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

let rec remove_duplicates lst = match lst with
                              | [] -> lst
                              | curr :: rest -> if(List.mem curr rest) then (remove_duplicates rest) else curr :: (remove_duplicates rest) ;;                                               

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
                                    | Var(x) -> begin 
                                      if (List.mem x paramList) == false then
                                      let major_index = find_var_in_boundlist x boundList 0 in
                                      if(major_index == -1) then Var'(VarFree(x)) else
                                        let minor_list = List.nth boundList major_index in
                                        let minor_index = find_var_in_paramlist x minor_list 0 in
                                        Var'(VarBound(x,major_index,minor_index))
                                      else 
                                      Var'(VarParam(x, find_var_in_paramlist x paramList 0))
                                    end 

                                    | LambdaSimple(args, body) -> LambdaSimple'(args, (calculate_lexical_addresses args (paramList :: boundList) body))
                                    | LambdaOpt(args, optArgs, body) -> LambdaOpt'(args, optArgs, (calculate_lexical_addresses (List.append args [optArgs]) (paramList :: boundList) body))

let annotate_lexical_addresses e = calculate_lexical_addresses [] [] e;;
                                

let rec calculate_tail_calls tp expr = 
                                match expr with      
                                | Or'(exprs) -> Or'(calculate_last_tail tp exprs)
                                | If'(test, dit, dif) -> If'(calculate_tail_calls false test, calculate_tail_calls tp dit, calculate_tail_calls tp dif)
                                | Def'(var, value) -> Def'(var, calculate_tail_calls false value)
                                | Set'(var, value) -> Set'(var, calculate_tail_calls false value)
                                | Seq'(exprs) -> Seq'(calculate_last_tail tp exprs)
                                | LambdaSimple'(args, body) -> LambdaSimple'(args, calculate_tail_calls true body)
                                | LambdaOpt'(args, optArgs, body) -> LambdaOpt'(args, optArgs, calculate_tail_calls true body)
                                | Applic'(rator, rands) -> begin 
                                                            match tp with  
                                                           | true -> ApplicTP'(calculate_tail_calls false rator, List.map (fun x -> calculate_tail_calls false x) rands)
                                                           | false -> Applic'(calculate_tail_calls false rator, List.map (fun x -> calculate_tail_calls false x) rands)
                                                            end 
                                | BoxSet'(var, value) -> BoxSet'(var, calculate_tail_calls false value)
                                | rest -> rest  
                

and calculate_last_tail tp exprs = 
                              match exprs with  
                              | last :: [] -> [calculate_tail_calls tp last]
                              | curr :: rest ->  [(calculate_tail_calls false curr)] @ (calculate_last_tail tp rest)
                              | _ -> raise X_this_should_not_happen


let annotate_tail_calls e = 
                let tp = false in
                calculate_tail_calls tp e;;

let rec calculate_boxing box_list expr = 
                                  match expr with 
                                  | Var'(var) -> box_get_var var box_list
                                  | If'(test, dit, dif) -> If' (calculate_boxing box_list test, calculate_boxing box_list dit,calculate_boxing box_list dif)
                                  | Def'(var, value) -> Def'(var, calculate_boxing box_list value)
                                  | Or'(exprs) -> Or'(List.map (fun x -> calculate_boxing box_list x) exprs)
                                  | Set'(var, value) -> box_set_var var value box_list
                                  | Seq'(exprs) -> Seq'(List.map (fun x -> calculate_boxing box_list x) exprs)
                                  | LambdaSimple'(args, body) -> calculate_box_lambda args body box_list expr 
                                  | LambdaOpt'(args, optArgs, body) -> calculate_box_lambda (List.append args [optArgs]) body box_list expr 
                                  | Applic'(rator, rands) -> Applic'(calculate_boxing box_list rator, List.map(fun x -> calculate_boxing box_list x) rands)
                                  | ApplicTP'(rator, rands) -> ApplicTP'(calculate_boxing box_list rator, List.map(fun x -> calculate_boxing box_list x) rands)
                                  | rest -> rest 


and box_get_var var box_list = 
                  match var with  
                  | VarFree(varname) -> Var'(var)
                  | _ ->  if ((List.mem (Var'(var)) box_list) == false) then
                              Var'(var) 
                              else BoxGet'(var)

and box_set_var var value box_list = 
                           match var with
                           | VarFree(varname) -> Set'(var, calculate_boxing box_list value)
                           | _ -> if ( (List.mem (Var'(var)) box_list) == false) then 
                                Set'(var, calculate_boxing box_list value)  
                               else 
                                BoxSet'(var, calculate_boxing box_list value)              
                   
and calculate_box_lambda args body box_list lambda_type = 
                                                       let updated_box_list = 
                                                        let f = fun x -> 
                                                          match x with 
                                                          | Var'(VarBound(varname, minor_index, major_index)) ->  Var'(VarBound(varname, minor_index + 1, major_index))
                                                          | Var'(VarParam(varname, index)) -> Var'(VarBound(varname, 0, index))  
                                                          | _-> raise X_syntax_error in 
                                                        List.map f box_list in  

                                                       let should_be_boxed = List.filter (fun(arg) -> needs_boxing arg body) args in
                                                       let wrapped_boxed_vars = List.map (fun var -> Var'(VarParam(var, find_var_in_paramlist var args 0))) should_be_boxed in

                                                       let final_box_list = List.map (fun var -> Set'(VarParam(var, find_var_in_paramlist var args 0 ),
                                                                                                      Box'(VarParam(var, find_var_in_paramlist var args 0))))
                                                                                                      should_be_boxed in
                                                       let boxed_body = (calculate_boxing (List.append wrapped_boxed_vars updated_box_list) body ) in
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
                                                                    | LambdaSimple'(args, body) -> LambdaSimple'(args, Seq'(List.flatten(flatten_sequence (List.append (final_box_list) ([boxed_body])))))
                                                                    | LambdaOpt'(params, optParams, body) -> LambdaOpt'(params, optParams, Seq'(List.flatten(flatten_sequence (List.append (final_box_list) ([boxed_body])))))
                                                                    | _ -> raise X_syntax_error
                                                                    )
                                                              in
                                                              boss                                               

and flatten_sequence lst = List.map (fun lst -> match lst with
                                            |Seq'(lst) -> lst
                                            |x -> [x]
                                            )lst                                                       
  and read_write_additional_criteria vars expr = match expr with
    | Var'(varname) -> read_write_var vars varname
    | If'(test, dit, dif) -> merge_reads_writes_list [read_write_additional_criteria vars test;
                                                      read_write_additional_criteria vars dit;
                                                      read_write_additional_criteria vars test]
    | Or'(exprs) -> merge_reads_writes_list (List.map (read_write_additional_criteria vars) exprs)
    | Set'(var, value) -> read_write_set vars var value
    | Seq'(exprs) -> merge_reads_writes_list (List.map (read_write_additional_criteria vars) exprs)
    | LambdaSimple'(args, body) -> read_write_lambda vars args body
    | LambdaOpt'(args, optArg, body) -> read_write_lambda vars (List.append args [optArg]) body
    | Applic'(rator, rands) -> merge_two_reads_writes (read_write_additional_criteria vars rator)
                                                       (merge_reads_writes_list (List.map (read_write_additional_criteria vars) rands))
    | ApplicTP'(rator, rands) -> merge_two_reads_writes (read_write_additional_criteria vars rator)
                                                       (merge_reads_writes_list (List.map (read_write_additional_criteria vars) rands))
    | _ -> ([], [])

  and read_write_var vars var = match var with
    | VarParam(varname, major_index) -> (match (List.mem varname vars) with
                                        | true -> ([VarParam(varname, major_index)], [])
                                        | false -> ([], [])
      )
    | VarBound(varname, major_index, minor_index) -> (match (List.mem varname vars) with
                                        | true -> ([VarBound(varname, major_index, minor_index)], [])
                                        | false -> ([], [])
      )
    | VarFree(_) -> ([], [])

  and read_write_set vars var value = match var with
    | VarParam(varname, major_index) -> (match (List.mem varname vars) with
                                        | true -> merge_two_reads_writes ([], [VarParam(varname, major_index)]) (read_write_additional_criteria vars value)
                                        | false -> merge_two_reads_writes ([], []) (read_write_additional_criteria vars value)
      )
    | VarBound(varname, major_index, minor_index) -> (match (List.mem varname vars) with
                                        | true -> merge_two_reads_writes ([], [VarBound(varname, major_index, minor_index)]) (read_write_additional_criteria vars value)
                                        | false -> merge_two_reads_writes ([], []) (read_write_additional_criteria vars value)
      )
    | VarFree(_) -> merge_two_reads_writes ([], []) (read_write_additional_criteria vars value)

  and read_write_lambda vars args body = 
    let updated_vars = List.rev (remove_duplicates (List.append vars args)) in
    let body_reads_writes = read_write_additional_criteria updated_vars body in
    (filter_body_reads_writes body_reads_writes args)

  and filter_body_reads_writes body_reads_writes args = match body_reads_writes with
                                                    | (VarParam (varname, major_index) :: rest_reads, rest_writes) -> (
                                                        match (List.mem varname args) with 
                                                        | true -> (filter_body_reads_writes (rest_reads, rest_writes) args)
                                                        | false -> (merge_two_reads_writes ([VarParam (varname, major_index)], rest_writes)
                                                                                           (filter_body_reads_writes (rest_reads, rest_writes) args))
                                                      )
                                                    | (VarBound (varname, major_index, minor_index) :: rest_reads, rest_writes) -> (
                                                        match (List.mem varname args) with
                                                        | true -> (filter_body_reads_writes (rest_reads, rest_writes) args)
                                                        | false -> (merge_two_reads_writes ([VarBound (varname, major_index, minor_index)], rest_writes)
                                                                                           (filter_body_reads_writes (rest_reads, rest_writes) args))
                                                      )
                                                    | ([], VarParam (varname, major_index) :: rest_reads_writes) -> (
                                                        match (List.mem varname args) with 
                                                        | true -> (filter_body_reads_writes ([], rest_reads_writes) args)
                                                        | false -> (merge_two_reads_writes ([], [VarParam(varname, major_index)])
                                                                                           (filter_body_reads_writes ([], rest_reads_writes) args ))
                                                      )
                                                    | ([], VarBound (varname, major_index, minor_index) :: rest_reads_writes) -> (
                                                        match (List.mem varname args) with
                                                        | true -> (filter_body_reads_writes ([], rest_reads_writes) args)
                                                        | false -> (merge_two_reads_writes ([], [VarBound(varname, major_index, minor_index)])
                                                                                           (filter_body_reads_writes ([], rest_reads_writes) args))
                                                      )
                                                    | ([],[]) -> ([], [])  
                                                    | _ -> raise X_syntax_error
        
        
  and merge_reads_writes_list reads_writes_list =   
    List.fold_left merge_two_reads_writes ([],[]) reads_writes_list

  and merge_two_reads_writes first_reads_writes second_reads_writes = match first_reads_writes, second_reads_writes with
    | (first_reads, first_writes), (second_reads, second_writes) -> (List.append first_reads second_reads, List.append first_writes second_writes)

  and calculate_additional_criteria read_occur write_occur expression_with_read_occur expression_with_write_occur exprs arg_name =
    let read_occur_expr expr = 
                          match expr with  
                          | Var'(VarParam(varname, minor_index)) -> if (varname = arg_name) then true else false
                          | Var'(VarBound(varname, minor_index, major_index)) -> if (varname = arg_name) then true else false
                          | _ -> false
   
    in
    let write_occur_expr expr = 
                            match expr with
                            | Set'(var, value) -> true 
                            | _ -> false 
    
    in
    let e_with_read_occur_expr reads_writes = 
      let (reads, writes) = reads_writes in
      List.exists (fun var -> match var with
                                          | VarBound(_, _, _) -> true
                                          | _ -> false
      )
      reads 

    in
    let e_with_write_occur_expr reads_writes = 
      let (reads, writes) = reads_writes in
      List.exists (fun var -> match var with
                                          | VarBound(_, _, _) -> true
                                          | _ -> false
      )
      writes

      in 
      let calculate_rest_of_expressions1 curr_expr rest =
                                                        match (write_occur_expr curr_expr) || 
                                                        (e_with_write_occur_expr (read_write_additional_criteria [arg_name] curr_expr)) with
                                                        | true -> false
                                                        | false -> calculate_additional_criteria read_occur write_occur expression_with_read_occur expression_with_write_occur rest arg_name
   
    in
    let calculate_rest_of_expressions2 curr_expr rest = 
                                                      match (read_occur_expr curr_expr) || 
                                                      (e_with_read_occur_expr (read_write_additional_criteria [arg_name] curr_expr)) with
                                                      | true -> false
                                                      | false -> calculate_additional_criteria read_occur write_occur expression_with_read_occur expression_with_write_occur rest arg_name
    
    in  
    let calculate_rest_of_expressions3 curr_expr rest =  
                                                      match (read_occur_expr curr_expr) || (write_occur_expr curr_expr) ||
                                                            (e_with_read_occur_expr (read_write_additional_criteria [arg_name] curr_expr))
                                                             || (e_with_write_occur_expr (read_write_additional_criteria [arg_name] curr_expr))
                                                      with
                                                      | true -> false      
                                                      | false -> calculate_additional_criteria read_occur write_occur expression_with_read_occur expression_with_write_occur rest arg_name
    
    in
    let calculate_rest_of_expressions4 curr_expr rest read_occur write_occur expression_with_read_occur expression_with_write_occur = 
        calculate_additional_criteria ((read_occur_expr curr_expr) || read_occur)
                                      ((write_occur_expr curr_expr) || write_occur)
                                      ((e_with_read_occur_expr (read_write_additional_criteria [arg_name] curr_expr)) || expression_with_read_occur)
                                      ((e_with_write_occur_expr (read_write_additional_criteria [arg_name] curr_expr)) || expression_with_write_occur)
                                      rest 
                                      arg_name
    
    in
    match read_occur, write_occur, expression_with_read_occur, expression_with_write_occur, exprs with
    | _, false, true, false, curr_expr :: rest -> calculate_rest_of_expressions1 curr_expr rest     
    | false, _, false, true, curr_expr :: rest -> calculate_rest_of_expressions2 curr_expr rest   
    | true, _, _, true, [] -> true 
    | _, true, true, _, [] -> true 
    | _, _, _, _, [] -> false
    | true, _, _, true, curr_expr :: rest -> calculate_rest_of_expressions3 curr_expr rest
    | _, true, true, _, curr_expr :: rest -> calculate_rest_of_expressions3 curr_expr rest
    | _, _, _, _, curr_expr :: rest -> calculate_rest_of_expressions4 curr_expr rest read_occur write_occur expression_with_read_occur expression_with_write_occur


and set_write_param_read_bound body arg = match body with
  | Seq'(exprs) -> let lst = (List.map (check_set_write_param_read_bound arg) exprs) in 
                             (List.fold_left (fun x y -> x || y) false lst)
  | _ -> check_set_write_param_read_bound arg body

  and check_set_write_param_read_bound var_name expr = match expr with
  | Set'(VarParam(varname, minor_index), value) -> is_var_bound_in_expr varname value
  | _ -> false


  and is_var_bound_in_expr var_name expr = match expr with
                                        | Var'(VarBound(varname, _,_)) -> varname = var_name
                                        | Set'(var, value) -> is_var_bound_in_expr var_name value
                                        | If'(test, dit, dif) -> (is_var_bound_in_expr var_name test) ||
                                                                 (is_var_bound_in_expr var_name dit) ||
                                                                 (is_var_bound_in_expr var_name dif)
                                        | Or'(exprs) -> let lst = (List.map (is_var_bound_in_expr var_name) exprs) in 
                                                                  (List.fold_left (fun x y -> x || y) false lst)
                                        | Seq'(exprs) -> let lst = (List.map (is_var_bound_in_expr var_name) exprs) in 
                                                                   (List.fold_left (fun x y -> x || y) false lst)  
                                        | LambdaSimple'(args, body) -> is_var_bound_in_expr var_name body 
                                        | LambdaOpt'(args, optArg, body) -> is_var_bound_in_expr var_name body 
                                        | Applic'(rator, rands) -> (is_var_bound_in_expr var_name rator) || (let lst = (List.map (is_var_bound_in_expr var_name) rands) in 
                                                                   (List.fold_left (fun x y -> x || y) false lst))
                                        | ApplicTP'(rator, rands) -> (is_var_bound_in_expr var_name rator) || (let lst = (List.map (is_var_bound_in_expr var_name) rands) in 
                                                                   (List.fold_left (fun x y -> x || y) false lst))                           
                                        | _ -> false     

and needs_boxing arg body =
                    let write_occurrences = calculate_write_occurrences arg body in 
                    let read_occurrences = calculate_read_occurrences arg body in
                    if(List.length read_occurrences == 0 || List.length read_occurrences == 0) then false 
                    else 
                    let res1 = List.map (fun x -> compare_read_write x read_occurrences) write_occurrences in
                    let res2 = List.map (fun x -> compare_read_write x write_occurrences) read_occurrences in 
                    if(List.mem true res1 || List.mem true res2)
                    then ((match body with
                    | Seq'(exprs) ->  not (calculate_additional_criteria false false false false exprs arg)
                    | _ -> true
                    )
                    || (set_write_param_read_bound body arg))
                    else false
                          
                     
and calculate_read_occurrences arg body = 
                                      match body with 
                                      | Var'(var) -> calculate_read_var var arg
                                      | If'(test, dit, dif) -> (calculate_read_occurrences arg test) @
                                                               (calculate_read_occurrences arg dit) @
                                                               (calculate_read_occurrences arg dif)
                                      | Def'(var, value) -> raise X_syntax_error 
                                      | Or'(exprs) -> 
                                        begin 
                                          let f = (fun x -> calculate_read_occurrences arg x) in
                                            List.flatten (List.map f exprs)
                                        end 
                                      | Seq'(exprs) -> 
                                        begin 
                                          let f = (fun x -> calculate_read_occurrences arg x) in 
                                            List.flatten(List.map f exprs) 
                                        end 
                                      | Set'(var, value) -> calculate_read_occurrences arg value
                                      | Applic'(rator, rands) -> (calculate_read_occurrences arg rator) @
                                                                 List.flatten(List.map (fun x -> calculate_read_occurrences arg x) rands)
                                      | ApplicTP'(rator, rands) -> (calculate_read_occurrences arg rator) @
                                                                 List.flatten(List.map (fun x -> calculate_read_occurrences arg x) rands)
                                      | LambdaSimple'(args, innerbody) -> calculate_read_innerLambda arg args innerbody 
                                      | LambdaOpt'(args, optArgs, innerbody) -> calculate_read_innerLambda arg (List.append args [optArgs]) innerbody     
                                      | _ -> []                                                    

and calculate_read_innerLambda arg args innerbody = 
                                                if ((List.mem arg args) == false) then
                                                  begin 
                                                  read_depth := !read_depth + 1;                                    
                                                  if (List.length (calculate_read_occurrences arg innerbody) == 0) then []
                                                  else [!read_depth] 
                                                  end
                                                else []
and calculate_read_var var arg = 
                              match var with 
                              | VarFree(varname) -> []
                              | VarParam(varname, minor_index) -> check_read_occur varname arg
                              | VarBound(varname, minor_index, major_index) -> check_read_occur varname arg

and check_read_occur varname arg = if (varname = arg) then [0] else []                              

and compare_read_write arg occurrences = 
                                      match occurrences with
                                      | [] -> false 
                                      | curr :: rest -> if (compare arg curr != 0) then true else compare_read_write arg rest

and calculate_write_occurrences arg body = 
                                        match body with
                                        | Const'(x) -> []
                                        | If'(test, dit, dif) -> (calculate_write_occurrences arg test) @
                                                                 (calculate_write_occurrences arg dit) @
                                                                 (calculate_write_occurrences arg dif)
                                        | Def'(var, value) -> raise X_syntax_error
                                        | Or'(exprs) -> begin 
                                          let f = (fun x -> calculate_write_occurrences arg x) in
                                            List.flatten (List.map f exprs)
                                        end                       
                                        | Seq'(exprs) -> begin 
                                          let f = (fun x -> calculate_write_occurrences arg x) in
                                            List.flatten (List.map f exprs)
                                        end
                                        | Set'(var, value) -> calculate_write_var var value arg
                                        | Applic'(rator, rands) -> (calculate_write_occurrences arg rator) @
                                                                   List.flatten(List.map (fun x -> calculate_write_occurrences arg x) rands)
                                        | ApplicTP'(rator, rands) -> (calculate_write_occurrences arg rator) @
                                                                     List.flatten(List.map (fun x -> calculate_write_occurrences arg x) rands)
                                        | LambdaSimple'(args, innerbody) -> calculate_write_innerLambda arg args innerbody
                                        | LambdaOpt'(args, optArgs, innerbody) -> calculate_write_innerLambda arg (List.append args [optArgs]) innerbody
                                        | _ -> []

and calculate_write_var var value arg = 
                                match var with
                                | VarFree(varname) -> check_write_occur varname arg value
                                | VarParam(varname, minor_index) -> check_write_occur varname arg value
                                | VarBound(varname, minor_index, major_index) -> check_write_occur varname arg value                                                                                                                       

and check_write_occur varname arg value = if (varname = arg)
                                          then let new_write_list = (List.append [0] (calculate_write_occurrences arg value)) in
                                          new_write_list 
                                          else (calculate_write_occurrences arg value)

and calculate_write_innerLambda arg args innerbody = 
                                                if ((List.mem arg args) == false) then 
                                                begin 
                                                write_depth := !write_depth + 1;                                   
                                                if (List.length (calculate_write_occurrences arg innerbody) == 0) then []
                                                else [!write_depth] 
                                                end
                                                else [] 

let box_set e = calculate_boxing [] e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)