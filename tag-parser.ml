#use "reader.ml";;
open Reader;;

type constant =
| Sexpr of sexpr
| Void

type expr =
| Const of constant
| Var of string 
| If of expr * expr * expr
| Seq of expr list
| Set of expr * expr
| Def of expr * expr
| Or of expr list
| LambdaSimple of string list * expr
| LambdaOpt of string list * string * expr
| Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
match e1, e2 with
| Const Void, Const Void -> true
| Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
| Var(v1), Var(v2) -> String.equal v1 v2
| If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                          (expr_eq th1 th2) &&
                                            (expr_eq el1 el2)
| (Seq(l1), Seq(l2)
  | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
| (Set(var1, val1), Set(var2, val2)
  | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                            (expr_eq val1 val2)
| LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
    (List.for_all2 String.equal vars1 vars2) &&
      (expr_eq body1 body2)
| LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
    (String.equal var1 var2) &&
      (List.for_all2 String.equal vars1 vars2) &&
        (expr_eq body1 body2)
| Applic(e1, args1), Applic(e2, args2) ->
    (expr_eq e1 e2) &&
      (List.for_all2 expr_eq args1 args2)
| _ -> false;;


exception X_syntax_error;;
module type TAG_PARSER = sig
val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
["and"; "begin"; "cond"; "define"; "else";
  "if"; "lambda"; "let"; "let*"; "letrec"; "or";
  "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
  "unquote-splicing"];;

(* work on the tag parser starts here *)
exception X_not_yet_implemented;;
let rec pairsToList pairs = match pairs with
| Nil -> []
| Pair(Nil,Nil) -> []
| Pair(x,Nil) -> [x]
| Pair(x,y) -> x :: pairsToList y
| _ -> raise X_syntax_error
;;

let check_reserved_word symbol = if not (List.mem symbol reserved_word_list) then Var(symbol) else raise X_syntax_error

let rec lastElementNil pairs = match pairs with
| Nil -> true
| Pair(x,Nil) -> true
| Pair(x,y) -> lastElementNil y
| _ -> false
;;
                                                        
let begin_flat beginList = List.map (fun lst -> match lst with
                                            |Seq(lst) -> lst
                                            |x -> [x]
                                            )
                                              beginList
;;

(* sexpr -> tag expr *)
let rec tag_parse sexpr =  match sexpr with
| Number(x) -> Const(Sexpr(Number(x)))
| Bool(x) -> Const(Sexpr(Bool(x)))
| Char(x) -> Const(Sexpr(Char(x)))
| String(x) ->  Const(Sexpr(String(x)))
| Symbol(x) -> check_reserved_word x
(* | Nil -> Const(Void) *) (* <- not sure*)
| Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))
| Pair(Symbol("if"), Pair(test, Pair(dit, dif))) -> (tag_if test dit dif) 
| Pair(Symbol("or"), pairs )-> orTager pairs
| Pair(Symbol "define", Pair(Pair(name, argl), expr)) -> (tag_MITdefine name argl expr)
| Pair(Symbol("define"), Pair(x ,Pair(y, Nil))) -> Def(tag_parse x, tag_parse y)
| Pair(Symbol("set!"), Pair(var,Pair(value, Nil))) -> Set(tag_parse var, tag_parse value)
| Pair(Symbol("lambda"), Pair(Symbol args,body)) -> LambdaOpt([], args ,flatten_sequence body)
| Pair(Symbol("lambda"), Pair(args,body)) -> tag_lambda_simple args body
| Pair(Symbol("begin"), pairs )-> tag_begin pairs
| Pair(Symbol "and", pairs) -> tag_and pairs
| Pair(Symbol "let", pairs) -> tag_let pairs
| Pair(Symbol "let*", pairs) -> tag_let_star pairs
| Pair(Symbol "letrec", pairs) -> tag_letrec pairs
| Pair(Symbol "quasiquote", Pair(sexpr,Nil)) -> tag_parse (tag_quasiQuote sexpr)
| Pair(Symbol "cond", pairs) -> tag_cond pairs
| Pair(Symbol "pset!", pairs) ->  tag_parse (tag_pset pairs)
| Pair (a, b) -> Applic (tag_parse a, (List.map tag_parse (pairsToList (b)))) 
| _ -> raise X_not_yet_implemented

and tag_lambda_simple vars body = if (lastElementNil vars) then LambdaSimple(vars_to_list vars, flatten_sequence body) else
                            LambdaOpt(List.rev(List.tl (List.rev (vars_to_list vars))), List.hd(List.rev(vars_to_list vars)),flatten_sequence body)

and tag_if test dit dif =
                      match dif with
                      | Nil -> If(tag_parse test, tag_parse dit, Const(Void))
                      | Pair(dif,Nil) -> If(tag_parse test, tag_parse dit, tag_parse dif)
                      | _ -> raise X_syntax_error

and tag_begin pairs = match pairs with
                         | Nil -> Const Void
                         | Pair (x, Nil) -> tag_parse x
                         | _ -> flatten_sequence pairs

and check_one_element lst = 
                        match lst with
                          | x::[] -> true
                          | x::xs -> false
                          | []  -> false

and flatten_sequence lst =
                  if check_one_element (pairsToList lst)==true then List.hd (List.map tag_parse (pairsToList lst))
                  else Seq(List.flatten(begin_flat(List.map tag_parse (pairsToList lst))))



and tag_and pairs =
                match pairs with
                  | Nil -> Const (Sexpr (Bool (true))) 
                  | Pair(a,Nil) -> tag_parse a
                  | Pair(a,b) -> (If(tag_parse a, tag_parse (Pair(Symbol("and"),b)), tag_parse(Bool(false))))
                  | _ -> raise X_syntax_error

and tag_let pairs =  
                match pairs with
                  | Pair(varsAndVals, body) -> Applic (LambdaSimple ((extract_let_vars varsAndVals) , (flatten_sequence body) ) , (extract_let_vals varsAndVals))
                  | _ -> raise X_syntax_error

and tag_let_star pairs = 
                    match pairs with
                    | Pair(Nil,x) -> tag_parse (Pair(Symbol ("let"),Pair(Nil, x)))
                    | Pair(Pair(firstBinding,Nil),body) -> tag_parse (Pair(Symbol "let",Pair(Pair(firstBinding,Nil),body)))
                    | Pair(Pair(firstBinding,restBindings),body) -> tag_parse (more_than_one_binding_let_star (Pair(Symbol "let*", pairs)))
                    | _ -> raise X_syntax_error

and more_than_one_binding_let_star pairs =
                             match pairs with
                             | Pair(Symbol "let*",Pair(Pair(allBindings,Nil),body)) ->  pairs
                             | Pair(Symbol "let*",Pair(Pair(firstBinding,restBindings),body)) -> Pair(Symbol "let",Pair(Pair(firstBinding,Nil),Pair(more_than_one_binding_let_star (Pair (Symbol "let*", Pair(restBindings,body))),Nil))) 
                             | _ -> raise X_syntax_error

and tag_letrec pairs = 
                  match pairs with 
                  | Pair(Nil, x) -> tag_parse (Pair (Symbol "let", Pair(Nil, x)))
                  | Pair(Pair(firstBinding,restBindings),body) -> tag_parse (more_than_one_binding_letrec (Pair(Symbol "letrec", pairs)))                      
                  | _ -> raise X_syntax_error

and more_than_one_binding_letrec pairs = 
                                    match pairs with
                                    | Pair(Symbol "letrec",Pair(Pair(Pair(a, b), c), body)) -> 
                                                                                             (match c with
                                                                                             | Nil -> Pair(Symbol "let", Pair(Pair(Pair(a, Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)), Nil), (body_letrec body pairs))) 
                                                                                             | _ -> Pair(Symbol "let", Pair(Pair(Pair(a, Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)), more_than_one_binding_letrec c),(body_letrec body pairs)))
                                                                                             )
                                    | Pair(Pair(a, b), c) -> (match c with
                                                              | Nil -> Pair(Pair(a, Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)), Nil)
                                                              | _ -> Pair(Pair(a, Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)), more_than_one_binding_letrec c) 
                                    )
                                    | _ -> raise X_syntax_error

and body_letrec body pairs = 
                        match pairs with
                        | Pair(Symbol "letrec",Pair(Pair(Pair(a, b), c), d)) ->
                                                                                 (match c with
                                                                                 | Nil -> Pair(Pair(Symbol "set!", Pair(a, b)), d)
                                                                                 | _ -> Pair(Pair(Symbol "set!", Pair(a, b)), (body_letrec d c))
                                                                                 )
                        | Pair(Pair(a, b), c) -> (match c with 
                                                  | Nil -> Pair(Pair(Symbol "set!", Pair(a, b)), body)
                                                  | _-> Pair(Pair(Symbol "set!", Pair(a, b)), body_letrec body c)
                        )
                        | _ -> raise X_syntax_error   

 and extract_let_vars varsAndVals =
                      match varsAndVals with
                      | Pair(Pair(Symbol a , b), c) -> a :: (extract_let_vars c)
                      | Nil -> []
                      | _ -> raise X_syntax_error

 and extract_let_vals varsAndVals =
                      match varsAndVals with
                      | Pair(Pair(a,Pair(b,c)),d) -> tag_parse b :: (extract_let_vals d)
                      | Nil -> []
                      | _ -> raise X_syntax_error                        
                                                                             
and tag_quasiQuote sexpr =  
                      match sexpr with
                      | Pair(Symbol("unquote"), Pair(sexpr , Nil)) ->  sexpr
                      | Pair(Symbol("unquote-splicing"),Pair(sexpr,Nil)) -> raise X_syntax_error
                      | Symbol(x) -> (Pair(Symbol("quote"),Pair(Symbol(x),Nil)))
                      | Nil ->  (Pair(Symbol("quote"),Pair(Nil,Nil)))
                      | Pair(a,b) ->  (case_5_quasiQuote a b)
                      | _ ->  raise X_syntax_error 

and case_5_quasiQuote a b = 
                        match a,b with
                        | Pair(Symbol("unquote-splicing"),Pair(sexpr,Nil)),b -> Pair(Symbol("append"),Pair(sexpr,Pair((tag_quasiQuote b),Nil)))
                        | a,Pair(Symbol("unquote-splicing"),Pair(sexpr,Nil)) -> Pair(Symbol("cons"),Pair((tag_quasiQuote a),Pair(sexpr,Nil)))
                        | _ -> Pair(Symbol("cons"),Pair((tag_quasiQuote a), Pair((tag_quasiQuote b),Nil)))
                        
and tag_cond pairs =    
                match pairs with
                | Nil -> Const(Void)
                | Pair(Pair(Symbol ("else"),ans ), _) -> tag_parse (case_3_cond ans)
                | Pair(Pair(condition, Pair(Symbol "=>", func)), rest) -> tag_parse (case_2_cond condition func rest)
                | Pair(Pair(condition, ans),rest) -> tag_parse (case_1_cond condition ans rest)
                | _ -> raise X_syntax_error

and case_1_cond condition ans rest = 
                                match rest with
                                | Nil -> Pair(Symbol "if",Pair(condition, Pair(Pair(Symbol("begin"),ans), Nil)))
                                | _ -> Pair(Symbol "if",Pair(condition, Pair(Pair(Symbol("begin"),ans), Pair(Pair(Symbol ("cond"),rest),Nil))))

and case_2_cond condition func rest = 
                                  match rest with
                                  | Nil -> Pair(Symbol "let",Pair(Pair(Pair(Symbol "value",
                                           Pair (condition, Nil)),Pair(Pair(Symbol "f",Pair(Pair(Symbol "lambda",Pair(Nil,func)),Nil)),Nil)),
                                           Pair(Pair(Symbol "if", Pair(Symbol "value",Pair(Pair(Pair (Symbol "f", Nil),Pair (Symbol "value", Nil)),Nil))),Nil)))
                                  | _ -> Pair(Symbol "let",Pair(Pair(Pair(Symbol "value",
                                         Pair (condition, Nil)),Pair(Pair(Symbol "f",Pair(Pair(Symbol "lambda",Pair(Nil,func)),Nil)),
                                         Pair(Pair(Symbol "rest",Pair(Pair(Symbol "lambda",Pair(Nil,Pair(Pair(Symbol "cond",rest),Nil))),Nil)),Nil))),
                                         Pair(Pair(Symbol "if",Pair(Symbol "value",Pair(Pair(Pair (Symbol "f", Nil),Pair (Symbol "value", Nil)),Pair(Pair(Symbol "rest",Nil),Nil)))),Nil)))

and case_3_cond ans = Pair(Symbol("begin"),ans)     



and tag_MITdefine name argl expr = tag_parse (Pair(Symbol "define",
                                              Pair(name,
                                              Pair(Pair(Symbol "lambda", Pair(argl, expr)), Nil))))


and tag_pset pairs = (Pair(tag_pset1 pairs, Pair(tag_pset2 pairs, Nil)))

and tag_pset2 pairs =
                  match pairs with
                  | Pair(Pair(var, Pair (value, Nil)), body) ->
                                                              (match body with
                                                              | Nil -> make_let_empty_body_pset2 value
                                                              | _ -> make_let_pset2 value body
                                                              )  
                | _ -> raise X_syntax_error

and make_let_empty_body_pset2 value = Pair(Symbol "let",
                                                Pair(Pair(Pair(Symbol "x", Pair(value, Nil)), Nil),
                                                Pair(Pair(Symbol "cons", Pair(Symbol "x", Pair (Pair(Symbol "quote", Pair(Nil, Nil)), Nil))),
                                                  Nil)))

and make_let_pset2 value body =  Pair(Symbol "let",
                                        Pair(Pair(Pair(Symbol "x", Pair(value, Nil)), Pair(Pair(Symbol "y",Pair(Pair(Symbol "lambda", Pair(Nil, Pair ((tag_pset2 body), Nil))),
                                              Nil)),Nil)), Pair(Pair(Symbol "cons", Pair(Symbol "x", Pair(Pair(Symbol "y", Nil), Nil))),
                                          Nil)))                                               
                                   

  
and tag_pset1 pairs = 
                  match pairs with
  | Pair (Pair (var, value), body) ->
                                    (match body with
                                    | Nil -> make_lambda_empty_body_pset1 var 
                                    | _ -> make_lambda_pset1 var body
                                    )
  | _ -> raise X_syntax_error

and make_lambda_empty_body_pset1 var = Pair (Symbol "lambda",
                                        Pair (Pair (Symbol "lst", Nil), Pair(Pair (Symbol "set!",
                                            Pair (var, Pair (Pair (Symbol "car", Pair (Symbol "lst", Nil)), Nil))), Nil)))  

and make_lambda_pset1 var body = Pair (Symbol "lambda",
                                            Pair (Pair (Symbol "lst", Nil), Pair(Pair (Symbol "set!", Pair (var, Pair (Pair (Symbol "car", Pair (Symbol "lst", Nil)), Nil))), Pair (Pair ((tag_pset1 body),
                                                Pair (Pair (Symbol "cdr", Pair (Symbol "lst", Nil)), Nil)), Nil))))   
and vars_to_list vars =
                  match vars with
                    | Nil -> []
                    | Pair(Nil, Nil) -> []
                    | Pair(Symbol(x), Symbol(y)) -> [x ; y]
                    | Pair(Symbol x , y ) ->  x ::  vars_to_list(y)
                    | _ -> raise X_syntax_error

and orTager alist =
let l =(pairsToList alist) in
    match l with
      | [] -> Const(Sexpr(Bool(false)))
      | [a] -> tag_parse a
      | _ -> Or(List.map tag_parse l);
 

;;

(* the main loop *)
let tag_parse_expressions sexprs = List.map tag_parse sexprs;;

end;;





































(* struct Tag_Parser *)

(* todelete/
(* | Pair(Symbol("define"), Pair(Pair(varname,varargs),expr)) -> tag_parse(Pair (Symbol "define" , Pair(varname, Pair(Pair(Symbol "lambda", Pair(varargs,expr)),Nil)))) *)
*)
(* | Pair(Symbol("define"), Pair(var ,Pair(Symbol(value), Nil))) -> Def(Var(Sexpr(Symbol(value))), tag_parse value) *)

