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
  
  (*TODO remove*)
  val func : string -> expr'
end;;

exception X_syntax_error;;

module Code_Gen : CODE_GEN = struct

(*TODO change*)
let rec find_offset const_table exp = 
      match const_table with
      | (Sexpr(expr),(offset,tag)) :: rest -> if sexpr_eq exp expr then offset else find_offset rest exp
      | (Void, (offset, tag)) :: rest -> find_offset rest exp
      | [] -> 0 ;;


let rec create_const_tbl const_list const_table offset = 
match const_list with
| curr :: rest -> (match curr with
                  | Void -> (create_const_tbl rest (const_table @ [(Void, (offset, "MAKE_VOID"))]) (offset + 1)) 
                  | Sexpr(Nil) -> (create_const_tbl rest (const_table @ [(Sexpr(Nil), (offset , "MAKE_NIL"))]) (offset + 1)) 
                  | Sexpr(Bool(false)) -> (create_const_tbl rest (const_table @ [(Sexpr(Bool(false)), (offset, "MAKE_BOOL(0)"))]) (offset + 2)) 
                  | Sexpr(Bool(true)) -> (create_const_tbl rest (const_table @ [(Sexpr(Bool(true)), (offset, "MAKE_BOOL(1)"))]) (offset + 2)) 
                  | Sexpr(Char(ch)) -> (create_const_tbl rest (const_table @ [(Sexpr(Char(ch)), (offset, "MAKE_LITERAL_CHAR("^(string_of_int (Char.code ch))^")"))]) (offset + 2))                                                         
                  | Sexpr(Number(Fraction(x, y))) -> (create_const_tbl rest (const_table @ [(Sexpr(Number(Fraction(x, y))), (offset, "MAKE_LITERAL_RATIONAL(" ^ (string_of_int x) ^ "," ^ (string_of_int y) ^ ")"))]) (offset + 17))                                           
                  | Sexpr(Number(Float(x))) -> (create_const_tbl rest (const_table @ [(Sexpr(Number(Float(x))), (offset, "MAKE_LITERAL_FLOAT(" ^ (string_of_float x) ^ ")"))]) (offset + 9))
                  | Sexpr(String(str)) -> (create_const_tbl rest (const_table @ [(Sexpr(String(str)), (offset, "MAKE_LITERAL_STRING(" ^ str ^ ")"))]) (offset + 9 + (String.length str)))
                  | Sexpr(Symbol(str)) -> (create_const_tbl rest (const_table @ [(Sexpr(Symbol(str)), (offset, "MAKE_LITERAL_SYMBOL(const_tbl+"^(string_of_int (find_offset const_table (String(str))))^")"))]) (offset + 9))
                  | Sexpr(Pair(car, cdr)) -> (create_const_tbl rest (const_table @ [(Sexpr(Pair(car, cdr)) , (offset , "MAKE_LITERAL_PAIR(const_tbl+"^(string_of_int (find_offset const_table car))^", const_tbl+"^(string_of_int (find_offset const_table car))^")"))]) (offset + 17))
)
| [] -> const_table ;; 



let rec remove_duplicates lst = match lst with
                              | [] -> lst
                              | curr :: rest -> if(List.mem curr rest) then (remove_duplicates rest) else curr :: (remove_duplicates rest) 


let rec create_const_list ast const_list = match ast with 
| If'(test, dit, dif) -> (create_const_list test const_list) @ (create_const_list dit const_list) @ (create_const_list dif const_list)  
| Def'(var, value) -> create_const_list value const_list
| Set'(var, value) -> create_const_list value const_list
| Seq'(exprs) -> List.flatten(List.map (fun expr -> create_const_list expr const_list) exprs)
| Or'(exprs) -> List.flatten(List.map (fun expr -> create_const_list expr const_list) exprs)
| LambdaSimple'(args, body) ->  create_const_list body const_list
| LambdaOpt'(args,optArg, body) -> create_const_list body const_list
| Applic'(rator, rands) -> (create_const_list rator const_list) @ (List.flatten(List.map (fun rand -> (create_const_list rand const_list))rands))
| ApplicTP'(rator, rands) -> (create_const_list rator const_list) @ (List.flatten(List.map (fun rand -> create_const_list rand const_list)rands)) 
| BoxSet'(var, value) -> create_const_list value const_list
| Const'(x) -> (match x with
                | Void -> const_list
                | Sexpr(expr) -> (match expr with
                                  | Nil -> const_list
                                  | Bool(x) -> const_list
                                  | Symbol(str) -> [Sexpr(String(str)); Sexpr(expr)] @ const_list
                                  | Pair(car, cdr) -> (create_const_list (Const'(Sexpr(car))) const_list) @ (create_const_list (Const'(Sexpr(cdr))) const_list) @ [Sexpr(Pair(car, cdr))] 
                                  | _ -> [Sexpr(expr)] @ const_list
                )
)
| _ -> const_list

let make_consts_tbl asts = let const_list = List.flatten(List.map (fun ast -> create_const_list ast []) asts) in
                           let const_list = remove_duplicates const_list in
                           let const_list = [Void; Sexpr(Nil); Sexpr(Bool(false)); Sexpr(Bool(true))] @ const_list in
                           let const_table = create_const_tbl const_list [] 0 in
                           const_table ;;  





let rec create_fvar_list ast fvar_list =
match ast with 
| If'(test, dit, dif) -> (create_fvar_list test fvar_list) @ (create_fvar_list dit fvar_list) @ (create_fvar_list dif fvar_list) 
| Def'(VarFree(varname), value) -> (create_fvar_list value (fvar_list @ [varname]))
| Set'(var, value) -> (match var with
                            | VarFree(varname) -> (create_fvar_list value (fvar_list @ [varname]))
                            | _ -> (create_fvar_list value fvar_list)
)
| Seq'(exprs) -> List.flatten(List.map (fun expr -> create_fvar_list expr fvar_list) exprs)
| Or'(exprs) -> List.flatten(List.map (fun expr -> create_fvar_list expr fvar_list) exprs)
| LambdaSimple'(args, body) ->  create_fvar_list body fvar_list
| LambdaOpt'(args,optArg, body) -> create_fvar_list body fvar_list
| Applic'(rator, rands) -> (create_fvar_list rator fvar_list) @ (List.flatten(List.map (fun rand -> create_fvar_list rand fvar_list)rands))
| ApplicTP'(rator, rands) -> (create_fvar_list rator fvar_list) @ (List.flatten(List.map (fun rand -> create_fvar_list rand fvar_list)rands)) 
| BoxSet'(var, value) -> (match var with 
                         | VarFree(varname) -> (create_fvar_list value (fvar_list @ [varname]))
                         | _ -> (create_fvar_list value fvar_list)
)
| Var'(var) -> (match var with
               | VarFree(varname) -> (fvar_list @ [varname])
               | _ -> fvar_list
)
| _ -> fvar_list
;; 


let rec create_fvar_table fvar_list fvar_table offset = 
match fvar_list with
| curr :: rest -> create_fvar_table rest ([(curr, offset)] @ fvar_table) (offset + 1)
| [] -> fvar_table
;;


let make_fvars_tbl asts = let fvar_list = List.flatten (List.map (fun ast -> create_fvar_list ast []) asts) in
                          let fvar_list = remove_duplicates fvar_list in
                          let fvar_list = ["boolean?"; "float?"; "integer?"; "pair?";
                                          "null?"; "char?"; "string?";
                                          "procedure?"; "symbol?"; "string-length";
                                          "string-ref"; "string-set!"; "make-string";
                                          "symbol->string"; 
                                          "char->integer"; "integer->char"; "eq?";
                                          "+"; "*"; "-"; "/"; "<"; "=";
                                          "cons"; "car"; "cdr"; "set-car!"; "set-cdr!"; "apply"] @ fvar_list in  
                          let fvar_table = create_fvar_table fvar_list [] 0 in
                          fvar_table ;;

let rec find_const_offset const_table expr = 
match const_table with 
| (name, (offset, tag)) :: rest -> (match name, expr with
                   | Void, Void -> offset
                   | Sexpr(exp1), Sexpr(exp2) -> if (sexpr_eq exp1 exp2) then offset else find_const_offset rest expr
                   | _ -> find_const_offset rest expr
)
| [] -> raise X_syntax_error
;; 

let rec find_fvar_offset fvar_table expr = 
match fvar_table with
| (str, offset) :: rest -> if (str = expr) then offset else find_fvar_offset rest expr
| [] -> raise X_syntax_error
                           

let label_counter_Gen label =
  let counter = ref (-1) 
  in
  fun ToIncrease ->
    if ToIncrease
    then incr counter;
    label ^ string_of_int !counter
;;

let rec generate_code consts fvars e depth = 
match e with
| Const'(x) -> "mov rax, const_tbl + " ^ (string_of_int (find_const_offset consts x)) ^ ""
| Var'(var) -> (match var with 
                | VarFree(varname) -> "mov rax, qword [fvar_tbl + WORD_SIZE * " ^ (string_of_int (find_fvar_offset fvars varname)) ^ "]"
                | VarParam(varname, minor) -> "mov rax, qword [rbp + WORD_SIZE * (4 + " ^ (string_of_int minor) ^ ")]"
                | VarBound(varname, major, minor) -> "mov rax, qword [rbp + WORD_SIZE * (4 + " ^ (string_of_int minor) ^ ")]""
                                                      mov rax, qword [rbp + WORD_SIZE * 2]
                                                      mov rax, qword [rax + WORD_SIZE * " ^ (string_of_int major) ^ "]
                                                      mov rax, qword [rax + WORD_SIZE * " ^ (string_of_int minor) ^ "]"
)
| Set'(Var'(var), value) ->(match var with
                            | VarFree(varname) -> (generate_code consts fvars value depth) ^ "mov qword [fvar_tbl + WORD_SIZE * " ^ 
                                                  (string_of_int (get_fvar fvars v)) ^ "], rax mov rax, SOB_VOID_ADDRESS"

                            | VarParam(varname, minor) -> (generate_code consts fvars value depth) ^
                                                          "mov qword [rbp + WORD_SIZE * (4 + " ^ (string_of_int minor) ^ ")], rax
                                                           mov rax, SOB_VOID_ADDRESS"
                            | VarBound(varname, major, minor) -> (generate_code consts fvars value depth) ^ 
                                                                  "mov rbx, qword [rbp + WORD_SIZE * 2]
                                                                  mov rbx, qword [rbx + WORD_SIZE * " ^ (string_of_int major) ^ "]
                                                                  mov qword[rbx + WORD_SIZE * " ^ (string_of_int minor) ^ "], rax
                                                                  mov rax, SOB_VOID_ADDRESS"
)
| Seq'(exprs) -> String.concat "\n" (List.map (fun expr -> (generate_code consts fvars expr depth)) exprs)
| Or'(exprs) -> let label = label_counter_Gen "" in
                String.concat ("\n cmp rax, SOB_FALSE_ADDRESS\n jne Lexit"^label^"\n") 
                (List.map (fun expr -> (generate_code consts fvars expr depth)) exprs)^"Lexit"^label^":"
| If'(test, dit, dif) -> let label_else = label_counter_Gen "" in
                        let lable_exit = label_counter_Gen "" in 
                        (generate_code consts fvars test depth)^"\n cmp rax, SOB_FALSE_ADDRESS\n je Lelse"^label_else^"\n"
                        ^(generate_code consts fvars dit depth)^"\n jmp Lexit"^lable_exit^"\n Lelse"^label_else^":"
                        ^(generate_code consts fvars dif depth)^ "\n Lexit"^lable_exit^":" ;;             
                                  
                          




                
(*TODO remove*)
let func str = (Semantics.run_semantics (List.hd(Tag_Parser.tag_parse_expressions (Reader.read_sexprs str))));;
  



let generate consts fvars e = raise X_syntax_error;;(*generate_code consts fvars e 0 ;;
*)
end;;

