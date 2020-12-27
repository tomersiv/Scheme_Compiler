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
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  val getTagTable : string -> (string * sexpr) list

  val renameAst  : expr' list -> expr' list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  let exitCounter = ref 0;;
  let elseCounter = ref 0;;
  let startLoopVar = ref 0;;
  let endLoopVar = ref 0;;
  let lCodeVar = ref 0;;
  let lContVar = ref 0;;
  let namesCounter = ref 0;;
  let scopeCounter = ref 0;;
  let closure = ref 0;;
  let names = ref [];;
  let tagsExprs = ref [];;


  let getTagTable x = 
    !tagsExprs;;

  let plusOne x =
  begin x := !x+1 ; 
    let res = !x in
    res
  end;;

  let startNew names =
    begin names := [] ; 
      let res = !names in
      res
    end;;

  let addName name newName =
    begin names := !names @ [(name,newName)] ; 
      let res = newName in
      res
    end;;

    let addTag name exp =
      begin  tagsExprs := !tagsExprs @ [(name,exp)] ; 
      end;;
    
      let rec findStrInTags names str   = 
        match names with 
        | (oldStr,newStr) :: rest -> if(oldStr = str) then newStr
        else (findStrInTags rest str)
        | _ ->  (addName str ("x"^(string_of_int (plusOne namesCounter))));;
  
  
        let rec findStrInTagRef names str  = 
          match names with 
          | (oldStr,newStr) :: rest -> if(oldStr = str) then newStr
          (* | (oldStr,newStr) :: rest -> if(oldStr = str) then TagRef(newStr) *)
          else (findStrInTagRef rest str )
          | _ -> (addName str ("x"^(string_of_int (plusOne namesCounter))));;
  
    let rec renameExpr expr table = 
      match expr with
      | Const'(Void) -> expr
      | Const'(Sexpr(x)) -> Const'(Sexpr(renameConst x))
      | If' (test,dit,dif) -> If' (renameExpr test table,renameExpr dit table,renameExpr dif table)
      | Seq'(lst) ->  Seq' (List.map (fun(x)-> (renameExpr x table)) lst)
      | Set'(x,y) -> Set' ((renameExpr x table),(renameExpr y table))
      | Def'(x,y) -> Def' ((renameExpr x table),(renameExpr y table))
      | Or'(lst) -> Or' (List.map (fun(x)-> (renameExpr x table)) lst)
      | LambdaSimple'(x,exp)-> LambdaSimple' (x,(renameExpr exp table))
      | LambdaOpt'(x,y,exp) -> LambdaOpt'(x,y,(renameExpr exp table))
      | Applic'(exp,lst) -> Applic' ((renameExpr exp table) ,(List.map (fun(x)-> (renameExpr x table)) lst)) 
      | ApplicTP' (exp,lst) -> ApplicTP' ((renameExpr exp table) ,(List.map (fun(x)-> (renameExpr x table)) lst)) 
      | BoxSet'(var,exp) -> BoxSet'(var,(renameExpr exp table)) 
      | Var'(x) -> expr
      | Box'(x) -> expr
      | BoxGet'(x) -> expr
  
      and renameConst x  = 
      match x with
      | Pair(y,z) -> 
      let first = (renameConst y) in
      let second = (renameConst z) in
      Pair(first,second)
      | Nil -> x
      | Bool(y) -> x
      | Symbol (y) -> x
      | TaggedSexpr(str,sexp) -> (TaggedSexpr ((findStrInTags !names str),(renameConst sexp)))
         (* (findStrInTags !names str sexp) *)
      | TagRef (str) -> (TagRef(findStrInTagRef !names str ))
      | _ -> x ;;

      
    let rec renameAst ast = 
      match ast with 
      | first:: rest -> [(renameExpr first  (startNew names))] @ (renameAst rest)
      | _ -> []
      ;;

  let rec findConst expr = 
    match expr with
    | Const'(Void) -> []
    | Const'(Sexpr(x)) -> (handleConst x)
    | If' (test,dit,dif) -> (findConst test) @ (findConst dit) @ (findConst dif)
    | Seq'(lst) -> List.flatten (List.map (fun(x)-> (findConst x)) lst)
    | Set'(x,y) -> (findConst x) @ (findConst y)
    | Def'(x,y) -> (findConst x) @ (findConst y)
    | Or'(lst) -> List.flatten (List.map (fun(x)-> (findConst x)) lst)
    | LambdaSimple'(x,exp)->(findConst exp)
    | LambdaOpt'(x,y,exp) -> (findConst exp)
    | Applic'(exp,lst) -> (findConst exp) @ List.flatten (List.map (fun(x)-> (findConst x)) lst) 
    | ApplicTP' (exp,lst) -> (findConst exp) @ List.flatten (List.map (fun(x)-> (findConst x)) lst) 
    | BoxSet'(var,exp) ->(findVarName var) @ (findConst exp)
    | Var'(x) -> (findVarName x)
    | Box'(x) -> (findVarName x)
    | BoxGet'(x) -> (findVarName x)

    and handleConst x = 
    match x with
    | Pair(y,z) -> (handleConst y) @ (handleConst z) @ [Sexpr(x)]
    | Nil -> []
    | Bool(y) -> []
    | Symbol (y) -> [Sexpr (String (y));Sexpr (x)]
    | TaggedSexpr(str,sexp) ->
    begin (addTag str sexp) ;
  (handleConst sexp) end
    (* | TagRef (str) -> [Sexpr(x)] *)
    | TagRef (str) -> []
    | Number (y) -> [Sexpr(x)]
    | String (y) -> [Sexpr(x)]
    | Char(y) -> [Sexpr(x)]

    and findVarName x =
   match x with 
   | VarFree(str) -> [Sexpr(String(str))]
   | VarParam(str,index) -> [Sexpr(String(str))]
   | VarBound(str,ind1,ind2) -> [Sexpr(String(str))] ;;

   let rec makeSet lst = 
    match lst with 
    | []       -> lst
    | x::[]    -> lst
    | x::y -> if (List.mem x y) then (makeSet y) else x::(makeSet y);;
   
    let findSize element = 
      match element with 
      | Sexpr(Nil) -> 1
      | Void -> 1
      | Sexpr(Bool(x)) -> 2
      | Sexpr(Char(x)) -> 2
      | Sexpr(Number(x)) -> 9
      | Sexpr(Symbol (x)) -> 9 
      | Sexpr(Pair (x,y)) -> 17
      | Sexpr(String (x)) -> (String.length x) + 9
      | _ -> raise X_not_yet_implemented;;
      (* | Sexpr(TaggedSexpr(x,y)) -> 0
      | Sexpr(TagRef(x)) -> 8;; *)

      let rec findInTags str table =
        match table with
        | (name,const) :: rest -> if(str=name) then const else (findInTags str rest)
        | _ -> raise X_no_match ;;

      let rec addressInConstTable x table =
        match x,table with
        (* | Sexpr(x),[] -> raise X_not_yet_implemented *)
        | Sexpr(TaggedSexpr(name,expr)), ((Sexpr(e)),(address,repres)) :: rest -> 
        if(sexpr_eq e expr) then address else (addressInConstTable x rest)
        | Sexpr(TagRef(name)), ((Sexpr(e)),(address,repres)) :: rest -> 
        let address= (addressInConstTable (Sexpr((findInTags name !tagsExprs))) table) in
        address
        | Sexpr(x),((Sexpr(e)),(address,repres)) :: rest -> if(sexpr_eq x e) then address else (addressInConstTable (Sexpr(x)) rest)
        | Sexpr(x), first :: second -> (addressInConstTable (Sexpr(x)) second)

        | Void , _ -> 1
        | _ -> 496351;;

      


      let findRepres element table =
        match element with 
        | Sexpr(Nil) -> "MAKE_NIL"
        | Void -> "MAKE_VOID"
        | Sexpr(Bool(x)) -> if x=true then "MAKE_BOOL(1)" else "MAKE_BOOL(0)"
        (* | Sexpr(Char(x)) -> "MAKE_LITERAL_CHAR(\'" ^ (Char.escaped x) ^ "\')" *)
        | Sexpr(Char(x)) -> Printf.sprintf "MAKE_LITERAL_CHAR(%d)" (Char.code x)      
          | Sexpr(Number(Int (x))) -> "MAKE_LITERAL_INT(" ^ (string_of_int x) ^ ")"
        | Sexpr(Number(Float(x))) -> "MAKE_LITERAL_FLOAT(" ^ (string_of_float x) ^ ")"
        | Sexpr(Symbol (x)) -> "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (string_of_int (addressInConstTable (Sexpr(String(x))) table)) ^ ")"
        | Sexpr(Pair (x,y)) -> "MAKE_LITERAL_PAIR (const_tbl+" ^ (string_of_int (addressInConstTable (Sexpr(x)) table)) ^ ",const_tbl+" ^ (string_of_int (addressInConstTable (Sexpr(y)) table)) ^")"
        | Sexpr(String (x)) -> "MAKE_LITERAL_STRING \"" ^ x ^ "\""
        | _ -> raise X_not_yet_implemented;;

        (* | Sexpr(TagRef(name)) -> "const_tbl+"^ (string_of_int (addressInConstTable (Sexpr((findInTags name !tagsExprs))) table )) ^ "" *)
        
       
        let findMyaddress prev = 
        match prev with
        | (Void,(address,repres)) -> address + (findSize Void) 
        (*| (Sexpr(Nil),(address,repres)) -> 0 *)
        | (sexp,(address,repres)) -> (address + (findSize sexp)) ;;
        
        let rec buildConstTable lst table prev = 
        match lst with
        | [] -> table
        | first :: rest -> 
        let current = (first,((findMyaddress prev),"temp")) in 
        let current = (first,((findMyaddress prev),(findRepres first (table @ [current])))) in
        (buildConstTable rest (table @ [current]) current) ;;

        let rec buildConstTableAgain lst table prev lastTable = 
          match lst with
          | [] -> table
          | first :: rest -> 
          let current = (first,((findMyaddress prev),"temp")) in 
          let current = (first,((findMyaddress prev),(findRepres first (lastTable @ [current])))) in
          (buildConstTableAgain rest (table @ [current]) current lastTable) ;;

        let rec replaceTaggedSexpr table =  
          match table with
          | [] -> []
          | Sexpr(Pair(TaggedSexpr(name1,value1),TaggedSexpr(name2,value2))) ::rest -> Sexpr(Pair(value1,value2)) :: replaceTaggedSexpr rest
          | Sexpr(Pair(TaggedSexpr(name,value),y)) ::rest -> Sexpr(Pair(value,y)) :: replaceTaggedSexpr rest
          | Sexpr(Pair(x,TaggedSexpr(name,value))) ::rest -> Sexpr(Pair(x,value)) :: replaceTaggedSexpr rest
          | Sexpr(Pair(x,y)) :: rest -> (Sexpr (replaceInsidePair (Pair(x,y)))) ::  replaceTaggedSexpr rest
          | first :: rest -> first :: (replaceTaggedSexpr rest) 
  
          and replaceInsidePair x =
          match x with
          | (Pair(x,y)) -> (Pair( replaceInsidePair x ,replaceInsidePair y))
          | TaggedSexpr(name,value) -> value
          | e -> e ;;

    let make_consts_tbl asts = 
    let constTable=List.map (fun x -> (findConst x)) asts in
    let constTable = List.flatten constTable in
    (* let constTable = replaceTaggedSexpr constTable in *)
    let constTable = (List.rev (makeSet (List.rev constTable))) in
    let constTable1 = [Sexpr(Nil);Void;Sexpr(Bool(false));Sexpr(Bool(true))] @ constTable in
    let constTable = (buildConstTable constTable1 [] (Sexpr(Nil),(-1,"0"))) in
    let constTable = (buildConstTableAgain constTable1 [] (Sexpr(Nil),(-1,"0")) constTable) in
    (* let constTable = List.filter (fun (expr,(address,repres)) -> 
                                      match expr with
                                      | (Sexpr(TagRef(name))) -> false
                                      | _ -> true )  constTable in *)
    constTable;;
    
    let rec findFreeVar expr = 
      match expr with
      | If' (test,dit,dif) -> (findFreeVar test) @ (findFreeVar dit) @ (findFreeVar dif)
      | Seq'(lst) -> List.flatten (List.map (fun(x)-> (findFreeVar x)) lst)
      | Set'(x,y) -> (findFreeVar x) @ (findFreeVar y)
      | Def'(x,y) -> (findFreeVar x) @ (findFreeVar y)
      | Or'(lst) -> List.flatten (List.map (fun(x)-> (findFreeVar x)) lst)
      | LambdaSimple'(x,exp)-> (findFreeVar exp)
      | LambdaOpt'(x,y,exp) -> (findFreeVar exp)
      | Applic'(exp,lst) -> (findFreeVar exp) @ List.flatten (List.map (fun(x)-> (findFreeVar x)) lst) 
      | ApplicTP' (exp,lst) -> (findFreeVar exp) @ List.flatten (List.map (fun(x)-> (findFreeVar x)) lst) 
      | BoxSet'(VarFree(x),exp) -> [x] @ (findFreeVar exp)
      | BoxSet'(var,exp) ->(findFreeVar exp)
      | Var'(VarFree(x)) -> [x]
      | Box'(VarFree(x)) -> [x]
      | BoxGet'(VarFree(x)) -> [x]
      | _ -> [] ;;

  let rec buildFvarTable fvarTable count=
    match fvarTable with 
    | [] -> [] 
    | [fvar] -> [(fvar,count)]
    | fvar :: rest -> [(fvar,count)] @ (buildFvarTable rest (count+1));;

    

  let make_fvars_tbl asts = 
    let fvarTable = List.map (fun x -> (findFreeVar x)) asts in
    let fvarTable = List.flatten fvarTable in
    let fvarTable = (List.rev (makeSet (List.rev fvarTable))) in
    let fvarConst =  [("symbol->string",0);("symbol?",1);("string?",2);("string-set!",3);
    ("string-ref",4);("string-length",5);("set-cdr!",6);("set-car!",7);( "float?",8);
    ("integer->char",9);("eq?",10);("procedure?",11);("pair?",12);("null?",13);("integer?",14);    
    ("cdr",15);("car",16);("boolean?",17);("cons",18); ("char?",19);("char->integer",20);
    ("apply",21);("make-string",22);("*",23);("+",24);("-",25);("/",26);("<",27);("=",28)] in
    let fvarTable =  fvarConst @ (buildFvarTable fvarTable 30) in
    fvarTable;;

    let rec labelInFVarTable s ftable = 
        match ftable with
        | [] ->  raise X_not_yet_implemented
        | (str,index) :: rest -> 
        if (str=s) then index else  (labelInFVarTable s rest) ;; 

    
    let rec listToString lst =
      match lst with 
      | [] -> ""
      | first :: rest -> first ^ (listToString rest);;

    let rec listToStringOr lst  exitCounter =
      match lst with 
      | [] -> "Lexit"^ exitCounter ^":"
      | first :: rest -> first ^"
      cmp rax, SOB_FALSE_ADDRESS
      jne Lexit"^ exitCounter ^"
      " ^ (listToStringOr rest exitCounter);;


    let rec codeGen consts fvars e depth  =
      match e with 

      (* | Const'(Sexpr(TaggedSexpr(name,value))) -> *)
       (* (codeGen consts fvars value depth) *)
       (* (codeGen consts fvars (Const'(Sexpr(value))) depth) ^ "
      mov [const_tbl + "^(string_of_int (addressInConstTable (Sexpr(String(name))) consts))^"],rax
      mov rax,SOB_VOID_ADDRESS
      "  *)
      (* | Const'(Sexpr(TagRef(name))) -> "" *)
      (* "mov rax , const_tbl + "^(string_of_int (addressInConstTable (Sexpr(String(name))) consts))^"
      " *)
      | Const'(x) -> "\nmov rax,const_tbl+" ^ (string_of_int (addressInConstTable x consts)) 
      | Var'(VarParam(_, minor)) -> "
      mov r11 , (4 + "^(string_of_int minor)^") *8
      mov qword rax,  [rbp + r11]
      "
      | Set'(Var'(VarParam(_, minor)),x) ->
        (codeGen consts fvars x depth ) ^
        "
        mov  [rbp + (4 + "^(string_of_int minor)^") * 8], qword rax
        mov rax, SOB_VOID_ADDRESS
        "
        | Var'(VarBound (_ ,major, minor)) ->"
        mov rax, qword [rbp + 2 * 8]
        mov rax, qword [rax + "^string_of_int major^"*8]
        mov rax, qword [rax + "^string_of_int minor^"*8]
        "
      | Set'(Var'(VarBound(_,major,minor)),x) ->
      (codeGen consts fvars x depth ) ^
      "
      mov rbx, qword [rbp + 16]
      mov rbx, qword [rbx +  " ^(string_of_int major)^" * 8 ]
      mov qword [rbx + " ^(string_of_int minor) ^ " * 8 ], rax
      mov rax, SOB_VOID_ADDRESS
      "
     | Var'(VarFree(v)) -> 
      "
      mov rax, qword [fvar_tbl+8*"^ (string_of_int (labelInFVarTable v fvars)) ^ " ]
      "
      | Set'(Var'(VarFree(v)),x) -> 
      (codeGen consts fvars x depth ) ^ 
      "
      mov qword [fvar_tbl+8*"^ (string_of_int (labelInFVarTable v fvars)) ^ " ],rax
      mov rax, SOB_VOID_ADDRESS
      "
      | Seq'(lst) -> 
      let strings = List.map (fun x -> (codeGen consts fvars x depth ) ^ "\n") lst in
      (listToString strings)
      
      | Or'(lst) -> 
      let strings = List.map (fun x -> (codeGen consts fvars x depth )) lst in
      let exitCounter = (string_of_int (plusOne exitCounter)) in
      (listToStringOr strings exitCounter)
      | If'(q,t,e) ->
      let exitL = "Lexit"^(string_of_int (plusOne exitCounter)) in
      let elseL = "Lelse"^(string_of_int (plusOne elseCounter)) in
      (codeGen consts fvars q depth ) ^
      " 
      cmp rax, SOB_FALSE_ADDRESS
      je " ^ elseL ^"
      "^(codeGen consts fvars t depth ) ^"
      jmp " ^ exitL ^"
      " ^ elseL ^":
      "^(codeGen consts fvars e depth ) ^"
      " ^ exitL ^":
      "
      | BoxGet'(x) -> 
      (codeGen consts fvars (Var'(x)) depth ) ^
      "
      mov rax, qword [rax]
      "
      | BoxSet'(x,y) -> 
      (codeGen consts fvars y depth ) ^
      "
      push rax
      "
      ^ (codeGen consts fvars (Var'(x)) depth  ) ^
      "
      pop qword [rax]
      mov rax , SOB_VOID_ADDRESS\n" 
      | Box'(x) -> 
      "
      MALLOC r8, 8
      "^ (codeGen consts fvars (Var'(x)) depth ) ^
      "mov qword [r8] , rax
      mov rax , r8
      " 
      | Def'(Var'(VarFree(str)) , value)->
      let address =  labelInFVarTable str fvars in 
      (codeGen consts fvars value depth ) ^
      "
        mov qword [" ^ string_of_int address ^ " *8 + fvar_tbl ] , rax
        mov rax, SOB_VOID_ADDRESS
      "
 
      | LambdaSimple' (params , body) -> 
      let newDepth = (depth+1) in
      let noPrevEnv = "noPrevEnv"^ (string_of_int (plusOne startLoopVar)) in
      let lCode = "Lcode"^ (string_of_int(plusOne lCodeVar)) in
      let closure = "closure"^ (string_of_int(plusOne closure)) in
      let startLoop = "startLoop"^ (string_of_int (plusOne startLoopVar)) in
      let endLoop = "endLoop"^ (string_of_int(plusOne endLoopVar)) in
      let startLoop2 = "startLoop"^ (string_of_int (plusOne startLoopVar)) in
      let endLoop2 = "endLoop"^ (string_of_int(plusOne endLoopVar)) in
      let lCont = "Lcont"^ (string_of_int(plusOne lContVar)) in
      "
      mov r8, " ^string_of_int newDepth ^"     ;;;;;;;;;;;;;;;;;;;;;;;init
      shl r8 , 3
      MALLOC r8, r8
      mov r14, "^string_of_int (depth) ^"
      cmp r14, 0      
      jne "^noPrevEnv^"                          ; jump if there are no params
      mov r8 ,  SOB_NIL_ADDRESS 
      "^closure^":
        MAKE_CLOSURE(rax, r8, "^lCode^")
        jmp "^lCont^"
      "^noPrevEnv^":

        mov r15, qword[rbp+16]                ; start copy params - last end
        mov r11 ,0                            ; r11 is i
        mov rcx , 1                           ; rcx is j
       "^startLoop^":                   
        cmp r11,"^ string_of_int (depth) ^"
        je "^endLoop^"
        mov qword r12, [r15+8*r11]
        mov qword [r8+rcx*8] , r12
        add r11 ,1
        add rcx , 1
        jmp "^startLoop ^"
        "^endLoop^":
        mov qword r14 , [rbp+8*3]   ;get prev lambda args number

        add r14,1 ;;;;;;;;;;;;;;;;;;;save space for extra arg

        mov rax,8
        mul r14
        mov r14,rax
        MALLOC r14, r14      
        mov qword[r8], r14
        mov r11,0                     ; copy env (extending...)
        mov r15 , qword [rbp+8*3]   
        "^startLoop2^":                             
        cmp r11 , r15  ;compare with prev lambda args number        
        je "^endLoop2^"
        mov rbx, [rbp+32+(r11*8)] 
        mov r13, rbx
        mov [r14+(r11*8)],r13
        add r11, 1
        jmp "^startLoop2 ^"
        "^endLoop2^":
        mov qword [r14+(r11*8)],SOB_NIL_ADDRESS   ;;;;;;;;;;;;;;;;;;;add extra arg 
          jmp "^closure ^"
           
      "^lCode^":                                              ;;;;;;;;;;;;;; lcode
        push rbp
        mov rbp, rsp
        "^(codeGen consts fvars body (depth + 1))^"
        leave
        ret
      "^lCont^":
       "



       
      | LambdaOpt' (firstParams, lastParams, body) -> 
      let optStartLoop = "startLoop"^ (string_of_int (plusOne startLoopVar)) in
      let optEndLoop = "endLoop"^ (string_of_int(plusOne endLoopVar)) in
      let endLambdaOpt = "endLoop"^ (string_of_int(plusOne endLoopVar)) in
      let newDepth = (depth+1) in
      let noPrevEnv = "noPrevEnv"^ (string_of_int (plusOne startLoopVar)) in
      let lCode = "Lcode"^ (string_of_int(plusOne lCodeVar)) in
      let closure = "closure"^ (string_of_int(plusOne closure)) in
      let startLoop = "startLoop"^ (string_of_int (plusOne startLoopVar)) in
      let endLoop = "endLoop"^ (string_of_int(plusOne endLoopVar)) in
      let startLoop2 = "startLoop"^ (string_of_int (plusOne startLoopVar)) in
      let endLoop2 = "endLoop"^ (string_of_int(plusOne endLoopVar)) in
      let lCont = "Lcont"^ (string_of_int(plusOne lContVar)) in

      let beforeFix=
        "
        mov r8, " ^string_of_int newDepth ^"     ;;;;;;;;;;;;;;;;;;;;;;;init
        shl r8 , 3
        MALLOC r8, r8
        mov r14, "^string_of_int (depth) ^"
        cmp r14, 0      
        jne "^noPrevEnv^"                          ; jump if there are no params
        mov r8 ,  SOB_NIL_ADDRESS 
        "^closure^":
          MAKE_CLOSURE(rax, r8, "^lCode^")
          jmp "^lCont^"
        "^noPrevEnv^":
  
          mov r15, qword[rbp+16]                ; start copy params - last end
          mov r11 ,0                            ; r11 is i
          mov rcx , 1                           ; rcx is j
         "^startLoop^":                   
          cmp r11,"^ string_of_int (depth) ^"
          je "^endLoop^"
          mov qword r12, [r15+8*r11]
          mov qword [r8+rcx*8] , r12
          add r11 ,1
          add rcx , 1
          jmp "^startLoop ^"
          "^endLoop^":
          mov qword r14 , [rbp+8*3]   ;get prev lambda args number
          add r14,1 ;;;;;;;;;;;;;;;;;;;save space for extra arg
          mov rax,8
          mul r14
          mov r14,rax
          MALLOC r14, r14      
          mov qword[r8], r14
          mov r11,0                     ; copy env (extending...)
          mov r15 , qword [rbp+8*3]       
          "^startLoop2^":                             
          cmp r11 , r15  ;compare with prev lambda args number        
          je "^endLoop2^"
          mov rbx, [rbp+32+(r11*8)] 
          mov r13, rbx
          mov [r14+(r11*8)],r13
          add r11, 1
          jmp "^startLoop2 ^"
          "^endLoop2^":
          mov qword [r14+(r11*8)],SOB_NIL_ADDRESS   ;;;;;;;;;;;;;;;;;;;add extra arg
            jmp "^closure
        
      in

      let fix ="
           
      "^lCode^":                                              ;;;;;;;;;;;;;; lcode
      push rbp
      mov rbp, rsp
      mov r10 , [rbp+8*3] ; num of args
      mov r11 ,r10
      add r11  , -"^(string_of_int (List.length firstParams))^"   ;num of opt args
      mov r9,r10
      add r9,3
      shl r9 ,3
      mov r12, rbp  ;point to the last opt arg
      add r12 , r9
      mov r13 , SOB_NIL_ADDRESS  ; r13 hold the result
      cmp r11 ,0 
      je "^endLambdaOpt^"
      " ^ optStartLoop ^ ": 
      cmp r11 , 0
      jz   " ^ optEndLoop ^ "
      mov r14 , [r12]   ;r14 is the next var
      MAKE_PAIR (r8,r14,r13)
      mov r13,r8
      add r11 , -1
      add r12 , -8
      jmp " ^ optStartLoop ^ "
      " ^ optEndLoop ^ ": 
      mov r9 , "^(string_of_int (List.length firstParams))^"
      add r9,4
      shl r9 ,3
      mov r14 ,rbp
      add r14,r9
      mov [r14] , r13
      mov r9,1
      add r9, "^(string_of_int (List.length firstParams))^"
      ;mov [rbp+8*3] ,  r9
        ; should set the new number of args and clean the stack
     
       "^endLambdaOpt^":
       
      "^(codeGen consts fvars body (depth + 1))^" 
      leave   
      ret
      "^lCont^":
      " 

in    
      beforeFix ^ fix 
      


      | Applic' (proc, args) -> 
      let calcArgs = (listToString (List.rev (List.map (fun(x) -> (codeGen consts fvars x depth )^"\n push rax") args))) in
      let pushN = "\n push qword "^ (string_of_int (List.length args) )in
      let procString =  (codeGen consts fvars proc depth ) in
      let verifyClo = "
      mov bl,0
      mov bl, byte [rax]
      cmp bl, T_CLOSURE
      jnz illegal      ;not a closure
      CLOSURE_ENV r10, rax
      push r10
      CLOSURE_CODE r10, rax
      call r10

      add rsp, 8*1              ; pop env
      pop rbx                   ; pop arg count
      shl rbx, 3                ; rbx = rbx * 8
      add rsp, rbx              ; pop args
      add rsp,8                 ; magic
      " in
      "
      push SOB_NIL_ADDRESS
      " ^
      calcArgs ^ pushN ^ procString ^ verifyClo
      


      
      | ApplicTP' (proc,args) -> 
      let calcArgs = (listToString (List.rev (List.map (fun(x) -> (codeGen consts fvars x depth )^"\n push rax") args))) in
      let pushN = "\n push qword "^ (string_of_int (List.length args) )in
      let procString =  (codeGen consts fvars proc depth ) in
      let numOfShifts =  (string_of_int (5+ (List.length args))) in  
      let verifyClo = "
      mov bl,0
      mov bl, byte [rax]
      cmp bl, T_CLOSURE
      ;;jz illegal      ;not a closure
      CLOSURE_ENV r10, rax 
      push r10 ; push closure env
      push qword [rbp + 8 * 1] ; old ret addr
      ;fix the stack
      mov r10 , [rbp]         ;save the old rbp for later
      mov r11 , [rbp+3*8]      ;get the num of args
      SHIFT_FRAME "^ numOfShifts ^ " 
      add r11,5
      shl r11,3 
      add rsp,r11
      mov rbp , r10
      ;end fix the stack
      CLOSURE_CODE r10, rax
      jmp r10                 ;jmp rax code 
      " in


      "
      push SOB_NIL_ADDRESS
      " ^
      calcArgs ^ pushN ^ procString ^ verifyClo

      
      | _ -> ""
      
      ;;


    
  let generate consts fvars e = (codeGen consts fvars e 0)

 
end;;

