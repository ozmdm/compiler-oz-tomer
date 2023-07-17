(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr                              
  | ScmVar' of var'                                 
  | ScmBox' of var'                                 
  | ScmBoxGet' of var'                              
  | ScmBoxSet' of var' * expr'                      
  | ScmIf' of expr' * expr' * expr'                 
  | ScmSeq' of expr' list                           
  | ScmSet' of var' * expr'                         
  | ScmDef' of var' * expr'                         
  | ScmOr' of expr' list                            
  | ScmLambdaSimple' of string list * expr'         
  | ScmLambdaOpt' of string list * string * expr'   
  | ScmApplic' of expr' * (expr' list)              
  | ScmApplicTP' of expr' * (expr' list);;          


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
      match pe with
      | ScmConst(c) -> ScmConst'(c)
      | ScmVar(v) -> ScmVar'(tag_lexical_address_for_var v params env)
      | ScmIf(test,dift,diff) -> ScmIf'((run test params env),(run dift params env),(run diff params env))
      | ScmSeq(e) -> ScmSeq'(List.map (fun exp -> run exp params env) e)
      | ScmSet(ScmVar(x),y) -> ScmSet'((tag_lexical_address_for_var x params env),(run y params env ))
      | ScmDef(ScmVar(var),value) -> ScmDef'((tag_lexical_address_for_var var params env),(run value params env))
      | ScmOr(e) -> ScmOr'(List.map (fun exp -> run exp params env) e)
      | ScmLambdaSimple(args,body) -> ScmLambdaSimple'(args, (run body args (params::env)))
      | ScmLambdaOpt(args,op,body) -> ScmLambdaOpt'(args,op, (run body (args @ [op]) (params::env)))
      | ScmApplic(operator,operands) -> ScmApplic'((run operator params env), (List.map (fun exp-> run exp params env) operands))
   in 
   run pe [] [];;

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail =
      match pe with
      | ScmConst'(c) -> ScmConst'(c)
      | ScmVar'(v) -> ScmVar'(v)
      | ScmIf'(test,dift,diff) -> ScmIf'((run test false),(run dift in_tail),(run diff in_tail))
      | ScmSeq'(exps)-> let (first,rest) = rdc_rac exps in
        ScmSeq'(List.append (List.map (fun exp-> run exp false) first) [(run rest in_tail)])
      | ScmSet'(v, exps) -> ScmSet'(v, (run exps false))
      | ScmDef'(v, exps) -> ScmDef'(v, (run exps false))
      | ScmOr'(exps)-> let (first,rest) = rdc_rac exps in
        ScmOr'(List.append (List.map (fun exp-> run exp false) first) [(run rest in_tail)])
      | ScmLambdaSimple'(args,body) -> ScmLambdaSimple'(args, (run body true))
      | ScmLambdaOpt'(args,op,body) -> ScmLambdaOpt'(args,op,(run body true))
      | ScmApplic'(operator,operands) ->
        if in_tail
          then ScmApplicTP'((run operator false),(List.map (fun exp-> run exp false) operands))
          else ScmApplic'((run operator false),(List.map (fun exp-> run exp false) operands))
      | _ -> raise X_this_should_not_happen
   in 
   run pe false;;

  (* boxing *)

  (*let find_reads name enclosing_lambda expr = raise X_not_yet_implemented*)


  let rec box_set expr = 
    match expr with
    | ScmVar'( VarParam(var,value) ) -> ScmBoxGet'(VarParam(var,value))
    | ScmVar'( VarBound(var,value1,value2)) -> ScmBoxGet'(VarBound(var,value1,value2))
    | ScmIf'( test,dift,diff ) -> ScmIf'((box_set test),(box_set dift),(box_set diff))
    | ScmSeq'(exps) -> ScmSeq'(List.map (fun exp-> box_set exp) exps)
    | ScmSet'(v,exps) -> ScmBoxSet'(v, (box_set exps))
    | ScmDef'(v,exps) -> ScmDef'(v, (box_set exps))
    | ScmOr'(exps) -> ScmOr'((List.map (fun exp-> box_set exp) exps))
    (*| ScmLambdaSimple'(args,body) ->
      ScmLambdaSimple'(args, ScmSeq'(List.mapi (fun i exp -> ScmSet'(VarParam(exp,i),ScmBox'(VarParam(exp,i)))) args @ [box_set body]))
    | ScmLambdaOpt'(args,"",body) ->
      ScmLambdaOpt'(args,"", ScmSeq'(List.mapi (fun i exp -> ScmSet'(VarParam(exp,i),ScmBox'(VarParam(exp,i)))) args @ [box_set body]))
    | ScmLambdaOpt'(args,op,body) ->
      ScmLambdaOpt'(args,op, ScmSeq'(List.mapi (fun i exp -> ScmSet'(VarParam(exp,i),ScmBox'(VarParam(exp,i)))) args @ [ScmSet'(VarParam(op,List.length(args) -1),ScmBox'(VarParam(op,List.length(args) -1)))] @ [box_set body]))
    *)| ScmApplic'(operator,operands) -> ScmApplic'(box_set operator,(List.map (fun exp-> box_set exp) operands))
    | ScmApplicTP'(operator,operands) -> ScmApplicTP'(box_set operator,(List.map (fun exp-> box_set exp) operands))
    | _ -> expr

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
