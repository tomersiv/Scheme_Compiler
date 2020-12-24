#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = List.map (fun ast -> create_const_list ast []) asts;;

  let rec create_const_list ast const_list = match ast with
  | If'(test, dit, dif) -> (create_const_list test const_list) @ (create_const_list dit const_list) @ (create_const_list dif const_list)  
  | Def'(var, value) -> create_const_list value const_list
  | Set'(var, value) -> create_const_list value const_list
  | Seq'(exprs) -> List.flatten(List.map (fun expr -> create_const_list expr const_list) exprs)
  | Or'(exprs) -> List.flatten(List.map (fun expr -> create_const_list expr const_list) exprs)
  | LambdaSimple'(args, body) ->  create_const_list body const_list
  | LambdaOpt'(args,optArg, body) -> create_const_list body const_list
  | Applic'(rator, rands) -> (create_const_list rator const_list) @ (List.flatten(List.map (fun rand -> create_const_list rand const_list)) rands)
  | ApplicTP'(rator, rands) -> (create_const_list rator const_list) @ (List.flatten(List.map (fun rand -> create_const_list rand const_list)) rands) 
  | BoxSet'(var, value) -> create_const_list value const_list
  | Const'(x) -> (match x with
                 | Void -> const_list
                 | Sexpr(expr) -> (match expr with
                                   | Nil -> const_list
                                   | Bool(x) -> const_list
                                   | Symbol(str) -> [Sexpr(String(str)); Sexpr(expr)] @ const_list
                                   | Pair(first, res) -> (create_const_list Const'(Sexpr(first)) const_list) @ (create_const_list Const'(Sexpr(rest)) const_list) @ [Sexpr(Pair(first, res))] 
                                   | _ -> [Sexpr(expr)] @ const_list
                 )
                 | _ -> const_list
  )
  | _ -> const_list

  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

