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
                  | Sexpr(String(str)) -> (create_const_tbl rest (const_table @ [(Sexpr(String(str)), (offset, "MAKE_LITERAL_STRING \"" ^ str ^ "\"" ))]) (offset + 9 + (String.length str)))
                  | Sexpr(Symbol(str)) -> (create_const_tbl rest (const_table @ [(Sexpr(Symbol(str)), (offset, "MAKE_LITERAL_SYMBOL(const_tbl+"^(string_of_int (find_offset const_table (String(str))))^")"))]) (offset + 9))
                  | Sexpr(Pair(car, cdr)) -> (create_const_tbl rest (const_table @ [(Sexpr(Pair(car, cdr)) , (offset , "MAKE_LITERAL_PAIR(const_tbl+"^(string_of_int (find_offset const_table car))^", const_tbl+"^(string_of_int (find_offset const_table cdr))^")"))]) (offset + 17))
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
                          let fvar_list = ["boolean?"; "flonum?"; "integer?"; "pair?";
                                          "null?"; "char?"; "rational?"; "string?"; "denominator";
                                          "procedure?"; "symbol?"; "string-length"; 
                                          "string-ref"; "string-set!"; "make-string";
                                          "symbol->string"; "exact->inexact"; 
                                          "char->integer"; "integer->char"; "eq?";
                                          "+"; "*"; "/"; "<"; "=";
                                          "cons"; "car"; "cdr"; "set-car!"; "set-cdr!"; "apply"; "gcd";] @ fvar_list in  
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
                           

let label_counter_gen =
  let counter = ref (-1) 
  in
  fun toIncrease ->
    if toIncrease
    then incr counter;
    "" ^ string_of_int !counter
;;

let rec generate_code consts fvars e depth = 
match e with

| Const'(x) -> "\n mov rax, const_tbl + " ^ (string_of_int (find_const_offset consts x))

| Var'(var) -> (match var with 
                | VarFree(varname) -> "\n mov rax, qword [fvar_tbl + " ^ (string_of_int (find_fvar_offset fvars varname)) ^ "]\n"
                | VarParam(varname, minor) -> "\n mov rax, qword [rbp + WORD_SIZE * (4 + " ^ (string_of_int minor) ^ ")]\n"
                | VarBound(varname, major, minor) ->  "\n mov rax, qword [rbp + WORD_SIZE * 2] " ^
                                                      "\n mov rax, qword [rax + WORD_SIZE * " ^ (string_of_int major) ^ "]" ^
                                                      "\n mov rax, qword [rax + WORD_SIZE * " ^ (string_of_int minor) ^ "]\n"
)

| Set'(var, value) -> (match var with
                            | VarFree(varname) -> "\n" ^ (generate_code consts fvars value depth) ^ 
                                                  "\n mov qword [fvar_tbl + " ^ (string_of_int (find_fvar_offset fvars varname)) ^ "], rax" ^
                                                  "\n mov rax, SOB_VOID_ADDRESS\n"

                            | VarParam(varname, minor) -> "\n" ^ (generate_code consts fvars value depth) ^
                                                          "\n mov qword [rbp + WORD_SIZE * (4 + " ^ (string_of_int minor) ^ ")], rax"^
                                                          "\n mov rax, SOB_VOID_ADDRESS\n"
                            | VarBound(varname, major, minor) -> "\n" ^ (generate_code consts fvars value depth) ^ 
                                                                  "\n mov rbx, qword [rbp + WORD_SIZE * 2]" ^
                                                                  "\n mov rbx, qword [rbx + WORD_SIZE * " ^ (string_of_int major) ^ "]" ^
                                                                  "\n mov qword[rbx + WORD_SIZE * " ^ (string_of_int minor) ^ "], rax" ^
                                                                  "\n mov rax, SOB_VOID_ADDRESS\n"
)

| Def'(VarFree(varname), value) -> "\n" ^ (generate_code consts fvars value depth) ^ 
                                                  "\n mov qword [fvar_tbl + " ^ (string_of_int (find_fvar_offset fvars varname)) ^ "], rax" ^
                                                  "\n mov rax, SOB_VOID_ADDRESS\n"
 
| Seq'(exprs) -> "\n" ^ String.concat "\n" (List.map (fun expr -> (generate_code consts fvars expr depth)) exprs)

| Or'(exprs) -> let label = label_counter_gen  in
                let label = (label true) in 
                let str = (String.concat ("\n cmp rax, SOB_FALSE_ADDRESS \n jne Lexit" ^ label ^ "\n") 
                (List.map (fun expr -> (generate_code consts fvars expr depth)) exprs)) in
                str ^ "\n\n Lexit" ^ label ^ ":"

| If'(test, dit, dif) -> let label = label_counter_gen in
                         let label = (label true) in 
                        (generate_code consts fvars test depth) ^ "\n cmp rax, SOB_FALSE_ADDRESS \n je Lelse" ^ label ^ "\n"
                        ^ (generate_code consts fvars dit depth) ^ "\n jmp Lexit" ^ label ^ "\n\n Lelse" ^ label ^ ":"
                        ^ (generate_code consts fvars dif depth) ^ "\n\n Lexit" ^ label ^ ":"  

| BoxGet'(var) -> (generate_code consts fvars (Var'(var)) depth) ^ "\n mov rax, qword [rax]"  

| BoxSet'(var, value) -> (generate_code consts fvars value depth) ^ "\n push rax \n" ^ 
                         (generate_code consts fvars (Var'(var)) depth) ^ "\n pop qword [rax] \n mov rax, SOB_VOID_ADDRESS" 

| Box'(var) -> "\n MALLOC r11, 8" ^
              (generate_code consts fvars (Var'(var)) depth ) ^
              "\n mov qword [r11] , rax" ^
              "\n mov rax , r11"

| LambdaSimple'(args, body) -> let label = label_counter_gen in
                              let label = (label true) in
                              "\n mov r13, " ^ string_of_int (depth + 1) ^ 
                              "\n shl r13, 3" ^
                              "\n MALLOC r13, r13                                  ; ExtEnv pointer" ^
                              "\n mov r11, 0" ^                                 
                              "\n cmp r11, " ^ (string_of_int depth) ^
                              "\n jne start_env_copy" ^ label ^
                              "\n mov r13, SOB_NIL_ADDRESS"^
                              "\n jmp make_closure" ^ label ^ 
                              "\n\n start_env_copy" ^ label ^ ":"^
                              "\n mov r12, qword [rbp + WORD_SIZE * 2]             ; env pointer"^
                              "\n mov r8, 0" ^
                              "\n mov rbx, 0                                       ; i" ^
                              "\n mov rcx, 1                                       ; j" ^
                              "\n shl rcx, 3" ^
                              "\n\n env_pointer_loop" ^ label ^ ":                   ;Start copying env pointers" ^                             
                              "\n cmp r8, " ^ (string_of_int depth) ^
                              "\n je end_copy_env" ^ label ^
                              "\n mov r11, qword [r12 + rbx]" ^ 
                              "\n mov [r13 + rcx], r11" ^
                              "\n add rbx, 8" ^
                              "\n add rcx, 8" ^
                              "\n add r8, 1" ^
                              "\n jmp env_pointer_loop" ^ label ^

                              "\n\n end_copy_env" ^ label ^ ":" ^
                              "\n mov rcx, PARAM_COUNT                                ; n" ^
                              "\n add rcx, 1" ^
                              "\n shl rcx, 3" ^ 
                              "\n MALLOC rcx, rcx" ^
                              "\n mov qword [r13], rcx" ^
                              "\n mov r9, 0                                           ; ExtEnv[0][i]" ^
                              "\n mov r11, 0" ^                                        
                              "\n\n params_copy_loop" ^ label ^ ":                    ;Start copying params" ^
                              "\n cmp r9, PARAM_COUNT                                 ; loop condition" ^
                              "\n je end_param_loop" ^ label ^
                              "\n mov rdx, qword [rbp + WORD_SIZE * 4 + r11]" ^
                              "\n mov qword [rcx + r11], rdx" ^
                              "\n add r9, 1" ^
                              "\n add r11, 8" ^
                              "\n jmp params_copy_loop" ^ label ^
                              
                              "\n\n end_param_loop" ^ label ^ ":" ^ 
                              "\n mov qword [rcx + r11], SOB_NIL_ADDRESS" ^
                                  
                              "\n\n make_closure"^ label ^ ":" ^ 
                              "\n MAKE_CLOSURE(rax, r13, lcode" ^ label ^ ")" ^
                              "\n jmp lcont" ^ label ^

                              "\n\n lcode" ^ label ^ ":" ^
                              "\n push rbp" ^
                              "\n mov rbp, rsp"
                              ^ (generate_code consts fvars body (depth + 1)) ^ 
                              "\n leave \n ret" ^

                              "\n\n lcont" ^ label ^ ":"

| LambdaOpt'(args, optArg, body) -> let label = label_counter_gen in
                                    let label = (label true) in
                                    "\n mov r13, " ^ string_of_int (depth + 1) ^ 
                                    "\n shl r13, 3" ^
                                    "\n MALLOC r13, r13                      ; ExtEnv pointer" ^
                                    "\n mov r11, 0" ^                                 
                                    "\n cmp r11, " ^ (string_of_int depth) ^
                                    "\n jne start_env_copy" ^ label ^
                                    "\n mov r13, SOB_NIL_ADDRESS" ^
                                    "\n jmp make_closure" ^ label ^ 
                                    "\n\n start_env_copy" ^ label ^ ":" ^
                                    "\n mov r12, qword [rbp + WORD_SIZE * 2] ; env pointer" ^
                                    "\n mov r8, 0" ^
                                    "\n mov rbx, 0                           ; i" ^
                                    "\n mov rcx, 1                           ; j" ^
                                    "\n shl rcx, 3" ^
                                    "\n\n env_pointer_loop" ^ label ^ ":     ;Start copying env pointers" ^                             
                                    "\n cmp r8, " ^ (string_of_int depth) ^
                                    "\n je end_copy_env" ^ label ^
                                    "\n mov r11, qword [r12 + rbx]" ^
                                    "\n mov [r13 + rcx], r11" ^
                                    "\n add rbx, 8" ^
                                    "\n add rcx, 8" ^
                                    "\n add r8, 1" ^
                                    "\n jmp env_pointer_loop" ^ label ^

                                    "\n\n end_copy_env" ^ label ^ ":" ^
                                    "\n mov rcx, PARAM_COUNT                 ; n" ^
                                    "\n add rcx, 1" ^
                                    "\n shl rcx, 3" ^ 
                                    "\n MALLOC rcx, rcx" ^
                                    "\n mov qword [r13], rcx" ^
                                    "\n mov r9, 0                            ; ExtEnv[0][i]" ^
                                    "\n mov r11, 0" ^                                        
                                    "\n\n params_copy_loop" ^ label ^ ":     ;Start copying params" ^
                                    "\n cmp r9, PARAM_COUNT                  ;loop condition" ^
                                    "\n je end_param_loop" ^ label ^
                                    "\n mov rdx, qword [rbp + WORD_SIZE * 4 + r11]" ^
                                    "\n mov qword [rcx + r11], rdx" ^
                                    "\n add r9, 1" ^
                                    "\n add r11, 8" ^
                                    "\n jmp params_copy_loop" ^ label ^ 

                                    "\n\n end_param_loop" ^ label ^ ":" ^ 
                                    "\n mov qword [rcx + r11], SOB_NIL_ADDRESS" ^
                                   
                                    "\n\n make_closure" ^ label ^ ":" ^ 
                                    "\n MAKE_CLOSURE(rax, r13, lcode" ^ label ^ ")" ^
                                    "\n jmp lcont" ^ label ^

                                    "\n\n lcode" ^ label ^ ":" ^
                                    "\n push rbp" ^
                                    "\n mov rbp, rsp \n" ^
                                    "\n mov rcx, PARAM_COUNT                                ;num of total args" ^                               
                                    "\n sub rcx, " ^ (string_of_int (List.length args)) ^ " ;num of opt args" ^
                                    "\n mov r8, PARAM_COUNT" ^
                                    "\n add r8, 3" ^
                                    "\n shl r8, 3" ^
                                    "\n add r8, rbp                                         ;first opt arg" ^
                                    "\n mov r9, SOB_NIL_ADDRESS" ^
                                    "\n cmp rcx, 0" ^
                                    "\n je doneLambda" ^ label ^ 
                                    "\n\n createOptList" ^ label ^ ":" ^
                                    "\n cmp rcx, 0" ^
                                    "\n je doneOptList" ^ label ^
                                    "\n mov r11, [r8]" ^
                                    "\n MAKE_PAIR (r12, r11, r9)" ^
                                    "\n mov r9, r12                                          ;holds the opt list" ^ 
                                    "\n sub rcx, 1" ^
                                    "\n sub r8, 8" ^
                                    "\n jmp createOptList" ^ label ^
                                    "\n\n doneOptList" ^ label ^ ":" ^
                                    "\n mov r11, " ^ (string_of_int (List.length args)) ^
                                    "\n add r11, 4" ^
                                    "\n shl r11, 3" ^
                                    "\n mov [rbp + r11], r9" ^
                                    "\n mov r10, " ^ (string_of_int (List.length args)) ^
                                    "\n add r10, 1" ^

                                    "\n\n doneLambda" ^ label ^ ":" ^
                
                                    (generate_code consts fvars body (depth + 1)) ^ 
                                    "\n leave \n ret" ^

                                    "\n\n lcont"^ label ^ ":"

(*TODO maybe need to use magic here*)   
| Applic'(rator, rands) -> let label = (label_counter_gen) in
                          let label = (label true) in
                          "\n push SOB_NIL_ADDRESS" ^ 
                          (String.concat ""
                          (List.rev (List.map (fun rand -> (generate_code consts fvars rand depth) ^ "\n push rax") rands))) ^
                          "\n push qword " ^ string_of_int (List.length rands) ^ "\n" ^
                          (generate_code consts fvars rator depth) ^
                          "\n CLOSURE_ENV rbx, rax  ;env" ^
                          "\n CLOSURE_CODE rcx, rax  ;code" ^
                          "\n push rbx" ^
                          "\n call rcx" ^
                          
                          "\n add rsp, WORD_SIZE" ^
                          "\n pop rbx" ^
                          "\n shl rbx, 3" ^
                          "\n add rsp, rbx" ^
                          "\n add rsp, WORD_SIZE" ^

                          "\n\n lcont" ^ label ^ ":"
 
| ApplicTP' (rator,rands) -> let label = (label_counter_gen) in
                            let label = (label true) in
                            "\n push SOB_NIL_ADDRESS" ^ 
                            (String.concat ""
                            (List.rev (List.map (fun rand -> (generate_code consts fvars rand depth) ^ "\n push rax") rands))) ^
                            "\n push qword " ^ string_of_int (List.length rands) ^ "\n" ^
                            (generate_code consts fvars rator depth) ^

                            "\n CAR r13, rax" ^ 
                            "\n push r13 ; env" ^
                            "\n push qword [rbp + 8 * 1] ; old ret addr" ^

                            "\n mov rcx, PARAM_COUNT" ^
                            "\n mov rbx, rbp             ; old rbp" ^
                            "\n SHIFT_FRAME " ^ string_of_int (5 + List.length (rands)) ^  
                            "\n add rcx, 5" ^
                            "\n shl rcx, 3" ^  
                            "\n add rsp, rcx" ^
                            "\n mov rbp, [rbx]" ^
                            
                            "\n CDR rdx, rax" ^
                            "\n jmp rdx                 ;jmp code" ^ 
                            
                            "\n\n lcont" ^ label ^ ":"

| _ -> "" ;;                      

      
let generate consts fvars e = generate_code consts fvars e 0 ;;

end;;

