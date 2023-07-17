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
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars tab(le type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

let rec constants_finder tree =
  match tree with
  | ScmConst'(ScmPair(a,b)) -> (constants_finder (ScmConst'(a))) @ (constants_finder (ScmConst'(b))) @ [(ScmPair(a,b))]
  | ScmIf'(test,dift,diff) -> (constants_finder test) @ (constants_finder dift) @ (constants_finder diff)
  | ScmSet'(var, exp) -> (constants_finder exp)
  | ScmLambdaSimple'(args,body) -> (constants_finder body)
  | ScmLambdaOpt'(args,op,body) -> (constants_finder body)
  | ScmBoxSet'(var,exp) -> (constants_finder exp)
  | ScmDef'(var,exp) -> (constants_finder exp)
  | ScmSeq'(exps) -> (List.flatten (List.map constants_finder exps) )
  | ScmOr'(exps) -> (List.flatten (List.map constants_finder exps) )
  | ScmApplic'(exp,exps) -> (List.flatten (List.map constants_finder exps) )
  | ScmApplicTP'(exp,exps) -> (List.flatten (List.map constants_finder exps) )
  | ScmConst'(ScmSymbol(str)) -> [ScmString(str);ScmSymbol(str)]
  | ScmConst'(ScmString(str)) -> [ScmString(str)]
  | ScmConst'(ScmNumber(num)) -> [ScmNumber(num)]
  | ScmConst'(ScmChar(c)) -> [ScmChar(c)]
  | _ -> [];;

let rec get_index_a exp index const_table_arr =
  let rec getOffset exps table =
    let (a,(b,c)) = List.find (fun ( d,(e,f)) -> sexpr_eq d exps) table in b in
  match exp with
  | ScmVoid -> (index+1,(ScmVoid,(index,"db T_VOID")))
  | ScmNil -> (index+1,(ScmNil,(index,"db T_NIL")))
  | ScmBoolean(true) -> (index+2,(ScmBoolean(true),(index,"db T_BOOL, 1")))
  | ScmBoolean(false) -> (index+2,(ScmBoolean(false),(index,"db T_BOOL, 0")))
  | ScmChar(c) -> (index+2,(ScmChar(c),(index,"MAKE_LITERAL_CHAR(" ^ (string_of_int (Char.code c)) ^ ")")))
  | ScmString("") -> (index+9,(ScmString(""),(index,"MAKE_LITERAL_STRING \"\"")))
  | ScmString(str) -> (index+9+(String.length str),(ScmString(str),(index,"MAKE_LITERAL_STRING {" ^ (String.concat "," (List.map (fun v-> string_of_int (Char.code v)) (string_to_list str) )) ^ "}" )))
  | ScmNumber(ScmReal(num)) -> (index+9,(ScmNumber(ScmReal(num)),(index,"MAKE_LITERAL T_FLOAT,dq "^ (string_of_float num) ^ "\n")))
  | ScmNumber(ScmRational(num1,num2)) -> (index+17,(ScmNumber(ScmRational(num1,num2)),(index,"MAKE_LITERAL_RATIONAL(" ^ (string_of_int num1 ^ "," ^ (string_of_int num2) ^ ");" ^ (string_of_int index))))) 
  | ScmSymbol(c) -> (index+9,(ScmSymbol(c),(index, "MAKE_LITERAL_SYMBOL( const_tbl + " ^ (string_of_int (getOffset (ScmString(c)) const_table_arr)) ^ ")" )))
  | ScmPair(first,rest) -> (index+17, (ScmPair(first,rest),(index, "MAKE_LITERAL_PAIR( const_tbl + " ^ (string_of_int (getOffset first const_table_arr)) ^ " , const_tbl + " ^ (string_of_int (getOffset rest const_table_arr)) ^ ")" )))
  | ScmVector(exps) -> (index+(List.length exps), (ScmVector(exps),(index, "db T_VEC")))
  ;;

module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = 
    let rec distinct_list lst =
      match lst with
      | first::rest -> 
        if (List.mem first rest) 
          then (distinct_list rest)
          else first :: (distinct_list rest)
      | [] -> [] in
    let rec const_table exps index const_table_arr =
      match exps with
      | first::rest -> 
        let (newIndex,a) = get_index_a first index const_table_arr in
        (const_table rest newIndex (List.append const_table_arr [a]))
      | [] -> const_table_arr in
    let finalList = distinct_list (List.append [ScmBoolean(true);ScmBoolean(false);ScmNil;ScmVoid] (List.flatten (List.map constants_finder asts))) in
    (const_table finalList 0 [])


  ;;
  let make_fvars_tbl asts = 
    let rec find_all_free_vars tree =
    match tree with
    | ScmApplic'(exp,exps) -> (List.fold_left (fun (acc)->(fun (cur)-> acc @ cur)) [] (List.map find_all_free_vars ([exp] @ exps) ))
    | ScmApplicTP'(exp,exps) -> (List.fold_left (fun (acc)->(fun (cur)-> acc @ cur)) [] (List.map find_all_free_vars ([exp] @ exps) ))
    | ScmSeq'(exps) -> (List.fold_left (fun (acc)->(fun (cur)-> acc @ cur)) [] (List.map find_all_free_vars exps) )
    | ScmOr'(exps) -> (List.fold_left (fun (acc)->(fun (cur)-> acc @ cur)) [] (List.map find_all_free_vars exps) )
    | ScmIf'(test,dift,diff) -> ((find_all_free_vars test)@(find_all_free_vars dift)@(find_all_free_vars diff))
    | ScmSet'(VarFree(s),exp) -> ([s] @ (find_all_free_vars exp))
    | ScmSet'(a,b) -> (find_all_free_vars b)
    | ScmBoxSet'(VarFree(s),exp) -> ([s] @ (find_all_free_vars exp))
    | ScmBoxSet'(a,b) -> (find_all_free_vars b)
    | ScmLambdaSimple'(args,body) -> (find_all_free_vars body)
    | ScmLambdaOpt'(args,op,body) -> (find_all_free_vars body)
    | ScmVar'(VarFree(s)) -> [s]
    | ScmDef'((VarFree(s)),exp) -> ([s] @ (find_all_free_vars exp))
    | _ -> [] in
    let rec tuple_creation args i =
      match args with
      | first::rest -> [(first,i)] @ (tuple_creation rest (i+1))
      | [] -> [] in
    let rec distinct_list lst =
      match lst with
      | first::rest -> 
        if (List.mem first rest) 
          then (distinct_list rest)
          else first :: (distinct_list rest)
      | [] -> [] in
    let myFvars = ["boolean?"; "flonum?"; "rational?";"pair?"; "null?"; "char?"; "string?";"procedure?"; "symbol?";"string-length"; "string-ref"; "string-set!";"make-string"; "symbol->string";"char->integer"; "integer->char"; "exact->inexact";"eq?";"+"; "*"; "/"; "="; "<";"numerator"; "denominator"; "gcd"; "car"; "cdr"; "cons"; "set-car!"; "set-cdr!";"apply"] in
    ( tuple_creation (List.append myFvars ( distinct_list (List.flatten ( List.map find_all_free_vars asts)))) 0)
  ;;

  let cnt = ref 0;;
  let add_Cnt = (fun () -> cnt := (!cnt+1); !cnt);;

  let rec exp_2_asm consts fvars e i =
    let rec getOffset exps table =
      let (a,(b,c)) = List.find (fun ( d,(e,f)) -> sexpr_eq d exps) table in b in
    let rec getFvarOffset fvar fvars_list =
      let (a,b) = List.find (fun (exp,index)-> exp = fvar) fvars_list in b in
    match e with
    | ScmConst'(exp) -> "mov rax, const_tbl + " ^ (string_of_int (getOffset exp consts)) ^ "\n"
    | ScmBox'(v) -> 
      "" ^ (exp_2_asm consts fvars (ScmVar'(v)) i) ^ "
      MALLOC rbx, WORD_SIZE
      mov [rbx], rax
      mov rax, rbx \n"
    | ScmBoxGet'(v) ->
      "" ^ (exp_2_asm consts fvars (ScmVar'(v)) i) ^ "
      mov rax, qword[rax] \n"
    | ScmBoxSet'(v,exp) ->
      "" ^ (exp_2_asm consts fvars exp i) ^ "
      push rax
      " ^ (exp_2_asm consts fvars (ScmVar'(v)) i) ^ "
      pop qword [rax]
      mov rax, SOB_VOID_ADDRESS \n"
    | ScmVar'(VarFree (v)) -> 
      "mov rax, qword[ fvar_tbl + WORD_SIZE * " ^ (string_of_int (getFvarOffset v fvars)) ^ "]"
    | ScmVar'(VarParam(v,a)) -> 
      "mov rax, qword[ rbp + WORD_SIZE * ( 4 + " ^ (string_of_int a) ^ ")]"
    | ScmVar'(VarBound(v, a, b)) ->
      "mov rax, qword[ rbp + WORD_SIZE * 2 ]
       mov rax, qword[ rax + WORD_SIZE * " ^ (string_of_int a) ^ "]
       mov rax, qword[ rax + WORD_SIZE * " ^ (string_of_int b) ^ "]"
    | ScmSeq'(exps) ->
      List.fold_left ( fun (acc)-> (fun (cur)-> acc ^ exp_2_asm consts fvars e i)) "" exps
    | ScmDef'(VarFree(v),exp) ->
      "" ^ (exp_2_asm consts fvars exp i) ^ "
      mov qword[ fvar_tbl + WORD_SIZE * " ^ (string_of_int (getFvarOffset v fvars)) ^ "], rax
      mov rax, SOB_VOID_ADDRESS \n"
    | ScmSet'(VarParam(v,a),exp) ->
      "" ^ (exp_2_asm consts fvars exp i) ^ "
      mov qword[ rbp + WORD_SIZE * ( 4 + " ^ (string_of_int a) ^ ")], rax
      mov rax, SOB_VOID_ADDRESS \n"
    | ScmSet'(VarBound(v,a,b),exp) -> 
      "" ^ (exp_2_asm consts fvars exp i) ^ "
      mov rbx, qword[ rbp + WORD_SIZE * 2 ]
      mov rbx, qword[ rbx + WORD_SIZE * " ^ (string_of_int a) ^ "]
      mov qword[ rbx + WORD_SIZE * " ^ (string_of_int b) ^ "], rax
      mov rax, SOB_VOID_ADDRESS \n"
    | ScmSet'(VarFree(v),exp) ->
      "" ^ (exp_2_asm consts fvars exp i) ^ "
      mov qword[ fvar_tbl + WORD_SIZE * " ^ (string_of_int (getFvarOffset v fvars)) ^ "], rax
      mov rax, SOB_VOID_ADDRESS \n"
    | ScmIf'(test,dift,diff) -> 
      let curCounter = (string_of_int (add_Cnt())) in
      "" ^ (exp_2_asm consts fvars test i) ^ "
      cmp rax, SOB_FALSE_ADDRESS
      je Lelse" ^ curCounter ^ "\n
      " ^ (exp_2_asm consts fvars dift i) ^ "
      jmp Lexit" ^ curCounter ^ "\n
      Lelse" ^ curCounter ^ ":\n"
      ^ (exp_2_asm consts fvars diff i) ^ "
      Lexit" ^ curCounter ^ ":\n"
    | ScmOr'(exps) ->
      let curCounter = (string_of_int (add_Cnt())) in
      let rec orCode exp_list =
        match exp_list with
        | first::rest ->
          "" ^ (exp_2_asm consts fvars first i) ^ "\n
          cmp rax, SOB_FALSE_ADDRESS \n
          jne " ^ "Lexit" ^ curCounter ^ "\n" ^
          (orCode rest)
        | first::[] -> 
          "\n" ^ (exp_2_asm consts fvars first i) ^ "\nLexit" ^ curCounter ^ ": \n"
        | _ -> ""
        in (orCode exps)
    | ScmApplic'(operator,operands) -> 
      "" ^ (List.fold_right ( fun (cur)-> (fun (acc)-> acc ^ (exp_2_asm consts fvars cur i) ^ "\n push rax \n")) operands "") ^
      "push " ^ (string_of_int (List.length operands)) ^ "\n" ^
      ( exp_2_asm consts fvars operator i ) ^ "
      CLOSURE_NEW rbx, rax
      push rbx
      CLOSURE_CODE rbx, rax
      call rbx
      add rsp, WORD_SIZE
      pop rcx
      shl rcx,3
      add rsp, rcx \n"
    | ScmApplicTP'(operator,operands) ->
      "" ^ (List.fold_right ( fun (cur)-> (fun (acc)-> acc ^ (exp_2_asm consts fvars cur i) ^ "\n push rax \n")) operands "") ^
      "push " ^ (string_of_int (List.length operands)) ^ "\n" ^
      ( exp_2_asm consts fvars operator i ) ^ "
      CLOSURE_NEW rbx, rax
      push rbx
      push qword [ rbp + WORD_SIZE ] \n" ^
      "SHIFT_APPLICTP " ^ (string_of_int ((List.length operands) + 2)) ^ "
      CLOSURE_CODE rdx, rax
      jmp rdx \n"
    | ScmLambdaSimple'(args,body) ->
      let curCounter = (string_of_int (add_Cnt())) in
      let curCounter1 = (string_of_int (add_Cnt())) in
      let curCounter2 = (string_of_int (add_Cnt())) in
      let curCounter3 = (string_of_int (add_Cnt())) in
      "MALLOC rax, WORD_SIZE * " ^ (string_of_int (i+1)) ^ "
      mov rbx, ENV
      mov rcx, " ^ (string_of_int (i+1)) ^ "
      mov rdx, rcx
      vector_handle_" ^ curCounter1 ^ ":
      mov r9, rcx
      sub r9, 1
      shl r9, 3
      mov r8, rbx
      add r8, r9
      mov r8, [r8]
      mov [rax + WORD_SIZE * rdx], r8
      sub rdx, 1
      loop vector_handle_" ^ curCounter1 ^ "
      mov rbx, qword[ rbp + WORD_SIZE * 3 ]
      shl rbx, 3
      MALLOC r10, rbx
      mov [rax], r10
      cmp rbx, 0
      je end_label_simple_" ^ curCounter2 ^ "
      mov rcx, rbx
      args_loop_" ^ curCounter3 ^ ":
      mov rdx,rcx
      sub rdx, 1
      mov r8, PVAR(rdx)
      mov [ r10 + WORD_SIZE * rdx ], r8
      loop args_loop_" ^ curCounter3 ^ "
      end_label_simple_" ^ curCounter2 ^ ":
      mov rbx,rax 
      MAKE_CLOSURE( rax, rbx, Lcode_" ^ curCounter ^")
      jmp Lcont" ^ curCounter ^ "
      Lcode_" ^ curCounter ^ ":
      push rbp
      mov rbp, rsp \n" 
      ^ ( exp_2_asm consts fvars body (i+1) ) ^ "
      leave
      ret
      Lcont" ^ curCounter ^ ": \n"
    | ScmLambdaOpt'(args,op,body) ->
      let curCounter = (string_of_int (add_Cnt())) in
      let curCounter1 = (string_of_int (add_Cnt())) in
      let curCounter2 = (string_of_int (add_Cnt())) in
      let curCounter3 = (string_of_int (add_Cnt())) in
      let curCounter4 = (string_of_int (add_Cnt())) in
      let curCounter5 = (string_of_int (add_Cnt())) in
      let curCounter6 = (string_of_int (add_Cnt())) in
      let curCounter7 = (string_of_int (add_Cnt())) in
      let curCounter8 = (string_of_int (add_Cnt())) in
      "MALLOC rax, WORD_SIZE * " ^ (string_of_int (i+1)) ^ "
      mov rbx, ENV
      mov rcx, " ^ (string_of_int (i+1)) ^ "
      mov rdx, rcx
      vector_handle_" ^ curCounter1 ^ ":
      mov r9, rcx
      sub r9, 1
      shl r9, 3
      mov r8, rbx
      add r8, r9
      mov r8, [r8]
      mov [rax + WORD_SIZE * rdx], r8
      sub rdx, 1
      loop vector_handle_" ^ curCounter1 ^ "
      mov rbx, qword[ rbp + WORD_SIZE * 3 ]
      shl rbx, 3
      MALLOC r10, rbx
      mov [rax], r10
      cmp rbx, 0
      je end_label_simple_" ^ curCounter2 ^ "
      mov rcx, rbx
      args_loop_" ^ curCounter3 ^ ":
      mov rdx,rcx
      sub rdx, 1
      mov r8, PVAR(rdx)
      mov [ r10 + WORD_SIZE * rdx ], r8
      loop args_loop_" ^ curCounter3 ^ "
      end_label_simple_" ^ curCounter2 ^ ":
      mov rbx,rax 
      MAKE_CLOSURE( rax, rbx, Lcode_" ^ curCounter ^")
      jmp Lcont" ^ curCounter ^ "
      Lcode_" ^ curCounter ^ ":
      mov r8, " ^ (string_of_int ((List.length args)+1) ) ^ "
      mov r9, r8
      mov rdx, WORD_SIZE
      add rdx, WORD_SIZE
      mov r10, [ rsp + rdx ]
      cmp r10, r9
      jb args_" ^ curCounter4 ^ "
      mov r15, SOB_NIL_ADDRESS
      add r8, 2
      mov r14, 0
      mov r11, r10
      sub r11, r9
      mov rdx, r11
      add r11, 1
      mov rcx, r11
      list_adder_" ^ curCounter5 ^ ":
      mov r12, r8
      sub r12, r14
      mov r13, [ rsp + r12 * WORD_SIZR ]
      MAKE_PAIR( r11, r13, r15)
      mov r15, r11
      add r14, 1
      loop list_adder_" ^ curCounter5 ^ "
      mov r8, 2
      add r8, " ^ (string_of_int ((List.length args)+1) ) ^ "
      mov [ rsp + r8 * WORD_SIZE ], r15
      mov rcx, 3
      add rcx, " ^ (string_of_int ((List.length args)+1) ) ^ "
      mov r9, 0
      stack_looper_" ^ curCounter6 ^ ":
      mov r11, 2
      add r11, " ^ (string_of_int ((List.length args)+1) ) ^ "
      sub r11, r9
      mov r12, [ rsp + r11 * WORD_SIZE ]
      add r11, rdx
      mov [ rsp + r11 * WORD_SIZE ], r12
      add r9, 1
      loop stack_looper_" ^ curCounter6 ^ "
      shl rdx, 3
      add rsp, rdx
      mov r8, " ^ (string_of_int ((List.length args)+1) ) ^ "
      mov [ rsp + 2 * WORD_SIZE ], r8
      jmp last_commands_" ^ curCounter8 ^ "
      args_" ^ curCounter4 ^ ":
      push 0
      mov r8, 0
      mov rcx, 3
      add rcx, r10
      stack_looper_2_" ^ curCounter7 ^ ":
      mov r11, r8
      add r11, 1
      mov r9, [ rsp + WORD_SIZE * r11 ]
      mov [ rsp + WORD_SIZE * r8], r9
      add r8, 1
      loop stack_looper_2_" ^ curCounter7 ^ "
      mov r9, " ^ (string_of_int ((List.length args)+1) ) ^ "
      add r9, 2
      mov r8, SOB_NIL_ADDRESS
      mov [ rsp + WORD_SIZE * r9 ], r8
      mov r8, " ^ (string_of_int ((List.length args)+1) ) ^ "
      mov [ rsp + WORD_SIZE * 2 ], r8
      last_commands_" ^ curCounter8 ^ ":
      push rbp
      mov rbp, rsp \n" 
      ^ ( exp_2_asm consts fvars body (i+1) ) ^ "
      leave
      ret
      Lcont" ^ curCounter ^ ": \n"
    | _ -> ""
  ;;

  let generate consts fvars e = exp_2_asm consts fvars e 0;;
end;;

