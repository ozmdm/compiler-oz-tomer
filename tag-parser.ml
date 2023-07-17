#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;;

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with
(* Implement tag parsing here *)
| ScmNil -> ScmConst ScmNil
| ScmBoolean (sxp) -> ScmConst ( ScmBoolean sxp )
| ScmChar (sxp ) -> ScmConst ( ScmChar sxp )
| ScmNumber (sxp) -> ScmConst ( ScmNumber sxp )
| ScmString (sxp) -> ScmConst ( ScmString sxp )
| ScmPair( ScmSymbol "quote" , ScmPair(sxp, ScmNil)) -> ScmConst(sxp)
| ScmSymbol (sxp) -> tp_variable sxp
| ScmPair ( ScmSymbol("if") , ScmPair(test, ScmPair(dift, ScmPair(diff,ScmNil)))) -> tp_if_tf test dift diff
| ScmPair ( ScmSymbol("if") , ScmPair(test, ScmPair(dift, ScmNil))) -> tp_if_t test dift
| ScmPair ( ScmSymbol("or") , sxp) -> tp_or sxp
| ScmPair ( ScmSymbol("lambda"), ScmPair(args,body)) -> tp_lambda args body
| ScmPair ( ScmSymbol("define"), sxp) -> tp_define sxp
| ScmPair ( ScmSymbol("set!"), sxp) -> tp_set sxp
| ScmPair ( ScmSymbol("begin"), sxp) -> tp_begin sxp
| ScmPair( operator, operands) -> tp_application operator operands
| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))

and macro_expand sexpr =
match sexpr with
(* Handle macro expansion patterns here *)
| ScmPair(ScmSymbol("let"), ScmPair(bindings, body)) -> me_let bindings body
| ScmPair(ScmSymbol("let*"), ScmPair(bindings, body)) -> me_lets bindings body
| ScmPair(ScmSymbol("letrec"), ScmPair(bindings, body)) -> me_letrec bindings body
| ScmPair(ScmSymbol("and"), sxp) -> me_and sxp
| ScmPair(ScmSymbol("cond"), sxp) -> me_cond sxp
| ScmPair(ScmSymbol("quasiquote"), ScmPair(first,rest)) -> me_quasiquote first rest
| _ -> sexpr
and me_let bindings body = 
  let rec get_vars lst = 
    match lst with
      | ScmNil -> ScmNil
      | ScmPair (ScmPair(ScmSymbol var,value) , rest) -> ScmPair( ScmSymbol var, get_vars rest) in
  let rec get_vals lst = 
    match lst with
      | ScmNil -> ScmNil
      | ScmPair (ScmPair(var , ScmPair(value,ScmNil)), rest ) -> ScmPair(value, get_vals rest) in
  let vars = get_vars bindings in
  let vals = get_vals bindings in
  ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(vars,body)),vals)
and me_lets bindings body =
  match bindings with
    | ScmNil -> macro_expand( ScmPair(ScmSymbol "let", ScmPair(bindings,body)) )
    | ScmPair( bind,ScmNil ) -> macro_expand( ScmPair(ScmSymbol "let", ScmPair(bindings,body)) )
    | ScmPair( bind,rest ) -> macro_expand( ScmPair(ScmSymbol "let", ScmPair(ScmPair(bind,ScmNil),ScmPair(ScmPair(ScmSymbol "let*", ScmPair(rest,body)),ScmNil))) )
and me_letrec bindings body = 
  let rec get_whatever binding =
    match binding with
      | ScmNil -> ScmNil
      | ScmPair( ScmPair( ScmSymbol var, value), rest) -> ScmPair( ScmPair( ScmSymbol var, ScmPair( ScmPair( ScmSymbol "quote" , ScmPair( ScmSymbol "whatever", ScmNil)), ScmNil)), get_whatever rest)
      | _ -> raise (X_syntax_error (binding,"binding error syntax")) in
  let rec get_set binding bod =
    match binding with
      | ScmNil -> bod
      | ScmPair( ScmPair( ScmSymbol var, ScmPair( value, ScmNil)), rest ) -> ScmPair( ScmPair( ScmSymbol "set!", ScmPair( ScmSymbol var, ScmPair( value, ScmNil))), get_set rest bod)
      | _ -> raise (X_syntax_error (binding,"binding error syntax")) in
  let whatever_var = get_whatever bindings in
  let set_var = get_set bindings body in
  macro_expand( ScmPair( ScmSymbol "let", ScmPair(whatever_var,set_var)))
and me_and sxp =
  match sxp with
    | ScmNil -> ScmBoolean true
    | ScmPair( first, ScmNil ) -> first
    | ScmPair( first, rest ) -> ScmPair( ScmSymbol "if", ScmPair( first, ScmPair( macro_expand (ScmPair( ScmSymbol "and" , rest)),ScmPair( ScmBoolean false, ScmNil))))
    | _ -> raise (X_syntax_error (sxp,"and expresstion fail"))
and me_cond sxp =
  match sxp with
    | ScmNil -> raise (X_syntax_error (sxp, "cond expresstion fail"))
    | ScmPair( ScmPair( ScmSymbol "else", exp), rest) -> ScmPair( ScmSymbol "begin", exp)
    | ScmPair( ScmPair( exp, expr ), ScmNil) -> ScmPair( ScmSymbol "if" , ScmPair( exp, ScmPair( ScmPair( ScmSymbol "begin", expr),ScmNil)))
    | ScmPair( ScmPair( exp, ScmPair( ScmSymbol "=>", expr)), ScmNil) -> macro_expand ( ScmPair( ScmSymbol "let" , ScmPair( ScmPair(ScmPair( ScmSymbol "value" , ScmPair ( exp, ScmNil)),ScmPair( ScmPair( ScmSymbol "f" , ScmPair( ScmPair (ScmSymbol "lambda",ScmPair( ScmNil,expr)), ScmNil)),ScmNil)),ScmPair( ScmPair( ScmSymbol "if", ScmPair( ScmSymbol "value", ScmPair(ScmPair ( ScmPair( ScmSymbol "f", ScmNil), ScmPair( ScmSymbol "value", ScmNil)),ScmNil))),ScmNil))))
    | ScmPair( ScmPair( exp, ScmPair( ScmSymbol "=>", expr)), exprs) -> macro_expand( ScmPair( ScmSymbol "let", ScmPair( ScmPair(ScmPair (ScmSymbol "value", ScmPair( exp, ScmNil)),ScmPair( ScmPair( ScmSymbol "f", ScmPair( ScmPair( ScmSymbol "lambda", ScmPair( ScmNil,expr)),ScmNil)),ScmPair( ScmPair (ScmSymbol "rest" , ScmPair( ScmPair( ScmSymbol "lambda",ScmPair( ScmNil, ScmPair( macro_expand ( ScmPair( ScmSymbol "cond" , exprs)), ScmNil))), ScmNil)), ScmNil))),ScmPair( ScmPair( ScmSymbol "if", ScmPair( ScmSymbol "value", ScmPair( ScmPair(ScmPair ( ScmSymbol "f", ScmNil), ScmPair( ScmSymbol "value", ScmNil)),ScmPair( ScmPair( ScmSymbol "rest", ScmNil), ScmNil)))), ScmNil))))
    | ScmPair( ScmPair( exp, expr ), exprs) -> ScmPair( ScmSymbol "if" , ScmPair(exp,ScmPair(ScmPair(ScmSymbol "begin", expr),ScmPair(me_cond exprs,ScmNil))))
    | _ -> raise (X_syntax_error (sxp, "cond expresstion fail"))
and me_quasiquote first rest =
  match first with
    | ScmNil -> ScmPair( ScmSymbol "quote" , ScmPair( ScmNil,ScmNil))
    | ScmSymbol(s) -> ScmPair( ScmSymbol "quote" , ScmPair( ScmSymbol s, ScmNil))
    | ScmPair( ScmSymbol "unquote", ScmPair(s,ScmNil)) -> s
    | ScmVector( exps ) -> ScmPair( ScmSymbol "list->vector", ScmPair( macro_expand (ScmPair( ScmSymbol "quasiquote",ScmPair(list_to_proper_list exps,ScmNil))),ScmNil))
    | ScmPair( ScmSymbol "unquote-splicing", s)-> ScmPair( ScmSymbol "quote",ScmPair(ScmPair(ScmSymbol "unquote-splicing",s),ScmNil))
    | ScmPair( ScmPair( ScmSymbol "unquote-splicing" , ScmPair(exp,ScmNil)), rest) -> ScmPair( ScmSymbol "append", ScmPair( exp, ScmPair( macro_expand( ScmPair( ScmSymbol "quasiquote", ScmPair( rest ,ScmNil))), ScmNil)))
    | ScmPair( first,rest ) -> ScmPair( ScmSymbol "cons", ScmPair( macro_expand(ScmPair( ScmSymbol "quasiquote", ScmPair(first,ScmNil))), ScmPair( macro_expand (ScmPair( ScmSymbol "quasiquote", ScmPair(rest,ScmNil))), ScmNil)))
    | _ -> first
and tp_variable sxp =
  if(List.exists (fun rw -> rw = sxp) reserved_word_list)
    then raise (X_reserved_word sxp)
    else ScmVar(sxp)
and tp_if_tf test dift diff =
  ScmIf( tag_parse_expression test, tag_parse_expression dift, tag_parse_expression diff)
and tp_if_t test dift = 
  ScmIf( tag_parse_expression test, tag_parse_expression dift, ScmConst ScmVoid)
and tp_or sxp = 
  match sxp with
  | ScmNil -> tag_parse_expression (ScmBoolean false)
  | ScmPair ( sexp , ScmNil ) -> tag_parse_expression sexp
  | ScmPair ( first,rest  ) -> ScmOr (List.map (fun sexp -> tag_parse_expression sexp) (scm_list_to_list sxp))
  | _ -> raise (X_syntax_error (sxp, "or expression fail" ))
and tp_lambda args body = 
  let pred = properlistCheck args in
  match pred with
    | (firsts, ScmNil) -> ScmLambdaSimple(symbol_list firsts, tag_parse_expression (ScmPair(ScmSymbol "begin",body)))
    | (firsts, last) -> ScmLambdaOpt(symbol_list1 firsts, ( match last with | ScmSymbol(s)->s | _ -> raise (X_syntax_error (last, "or expression fail" )) ),tag_parse_expression (ScmPair(ScmSymbol "begin",body)))
and symbol_list lst =
  (List.map (fun symbol-> match symbol with | ScmSymbol(s)-> s | _ -> raise (X_syntax_error (symbol,"lamda expression error"))) lst)
and symbol_list1 lst =
  (List.map (fun symbol-> match symbol with | ScmSymbol(s)-> s | _ -> raise (X_syntax_error (symbol,"lamda1 expression error"))) lst)
and properlistCheck lst  =
  match lst with
    | ScmPair(a,b) -> let (first,rest) = properlistCheck b in
                      (a::first,rest)
    | _ -> ([],lst)
and tp_define sxp =
  match sxp with
    | ScmPair( ScmSymbol(v) , ScmPair(exp,ScmNil)) -> ScmDef ( tag_parse_expression (ScmSymbol(v)),tag_parse_expression exp)
    | ScmPair( ScmPair(v, args), exp) -> tag_parse_expression (ScmPair(ScmSymbol "define", ScmPair(v,ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(args,exp)),ScmNil))))
    | _ -> raise (X_syntax_error (sxp, "define experssion fail"))
and tp_set sxp =
  match sxp with
    | ScmPair (v, ScmPair(exp,ScmNil)) -> ScmSet(tag_parse_expression v,tag_parse_expression exp)
    | _ -> raise (X_syntax_error ( sxp, "set experssion fail" ))
and tp_begin sxp = 
  match sxp with
    | ScmNil -> ScmConst ScmVoid
    | ScmPair( first,ScmNil ) -> tag_parse_expression first
    | _ -> ScmSeq((List.map (fun sexp -> tag_parse_expression sexp) (scm_list_to_list sxp)))
and tp_application operator operands = 
  match operands with
    | ScmNil -> ScmApplic( tag_parse_expression operator,[])
    | ScmPair( first,rest ) -> ScmApplic( tag_parse_expression operator, (List.map (fun sexp -> tag_parse_expression sexp) (scm_list_to_list operands)) )
    | _ -> raise (X_syntax_error ( operands , "Application exprestion fail"))
end;; 
