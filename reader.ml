(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
    val nt_boolean : sexpr PC.parser
    val nt_int : int PC.parser
    val nt_frac : scm_number PC.parser
    val nt_exponent_token : char list PC.parser
    val nt_exponent : char list PC.parser
    val nt_float_a : float PC.parser
    val nt_float_b : float PC.parser
    val nt_float_c : float PC.parser
    val nt_float : scm_number PC.parser
    val nt_line_comment : unit PC.parser
    val nt_sexpr_comment : unit PC.parser
    val nt_paired_comment : unit PC.parser
    val nt_char : sexpr PC.parser
end;; (* end of READER signature *) 

module Reader : READER = struct
open PC;;

let rec list_pl str =
    match str with
    | [] -> ScmNil
    | head::tail -> ScmPair(head, list_pl tail) ;;

let rec list_impl str =
    match str with
    | [] -> raise PC.X_no_match
    | head::tail::[] -> ScmPair(head, tail)
    | head::tail -> ScmPair (head ,list_impl tail);;

let rec list_2_plist = function
| [] -> ScmNil
| h::t -> ScmPair (h, list_2_plist t);;

let natural_num = plus(range '0' '9');; 

let unitify nt = pack nt (fun _ -> ());;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str
and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str
and nt_line_comment str = 
  let nt_end = disj (unitify (char '\n')) (unitify nt_end_of_input) in
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end in
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end) in
  let nt1 = unitify nt1 in
  nt1 str
and nt_paired_comment str =
  let nt1 = char '{' in
  let nt2 = char '}' in
  let nt3 = caten nt1 ( caten (star nt_sexpr) nt2) in
  let nt4 = unitify nt3 in
  nt4 str
and nt_sexpr_comment str = 
  let nt1 = word "#;" in
  let nt2 = caten nt1 nt_sexpr in
  let nt2 = unitify nt2 in
  nt2 str
and nt_comment str =
  disj_list
    [nt_line_comment;
     nt_paired_comment;
     nt_sexpr_comment] str
and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str
and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1
and nt_int str = 
  let p = char '+' in
  let m = char '-' in
  let p_m = disj p m in
  let p_m = maybe(p_m) in
  let sig_num = caten p_m natural_num in
  let sig_num = pack sig_num(fun (a,b) -> match a with
  | Some ('-') -> -1 * int_of_string(list_to_string b)
  | Some ('+') -> int_of_string(list_to_string b)
  | None -> int_of_string(list_to_string b)) in
    sig_num str
and nt_frac str = 
  let div = char '/' in
  let num_num = caten nt_int (caten div natural_num) in 
  let num_num = pack num_num(fun (a,(d,b)) -> 
    ScmRational(
      a,
      int_of_string(list_to_string b))
      ) in
  num_num str
and nt_integer_part str = 
  let ip = natural_num in
  ip str
and nt_mantissa str = 
  let man = natural_num in
  man str
and nt_exponent_token str =
  let e = word_ci "e" in
  let e_num = word "*10^" in
  let e_num2 = word "*10**" in
  let nt = disj_list[e; e_num; e_num2] in
  let nt = pack nt (fun a -> ['e']) in
  nt str
and nt_exponent str =  
  let et = nt_exponent_token in
  let integer = nt_int in
  let expo = caten et integer in 
  let expo = pack expo (fun (a,b) -> a@ (string_to_list(string_of_int b))) in
  expo str
and nt_float_a str = 
  let ip = natural_num in 
  let po = word "." in
  let man = pack (maybe nt_mantissa) (fun (a) -> match a with
  | Some (a) -> a
  | None -> ['0']) in
  let expo = pack (maybe nt_exponent) (fun (a) -> match a with
  | Some (a) -> a
  | None -> ['0']) in
  let expo = caten_list [ip; po; man; expo] in
  let expo = pack expo (fun [a; n; b; c] -> float_of_string(list_to_string(a@n@b@c))) in
  expo str
and nt_float_b str = 
  let po = word "." in
  let man = nt_mantissa in
  let expo = pack (maybe nt_exponent) (fun (a) -> match a with
  | Some (a) -> a
  | None -> ['0']) in
  let expo = caten_list [po; man; expo] in
  let expo = pack expo (fun [n; b; c] -> float_of_string(list_to_string(n@b@c))) in
  expo str
and nt_float_c str = 
  let ip = natural_num in 
  let expo = pack (maybe nt_exponent) (fun (a) -> match a with
  | Some (a) -> a
  | None -> []) in
  let expo = caten_list [ip; expo] in
  let expo = pack expo (fun [a; c] -> float_of_string(list_to_string(a@c))) in
  expo str
and nt_float str = 
  let p = char '+' in
  let m = char '-' in
  let p_m = disj p m in
  let p_m = maybe(p_m) in
  let fla = nt_float_a in
  let flb = nt_float_b in
  let flc = nt_float_c in
  let fl = disj_list [fla; flb; flc] in
  let nt1 = caten p_m fl in 
  let nt1 = pack nt1 (fun (sign,num) -> match sign with
    | Some ('-') -> ScmReal (num *. (-1.))
    | _ -> ScmReal num) in
  nt1 str
and nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str
and nt_boolean str = 
  let nt1 = word_ci "#f" in
  let nt1 = pack nt1 (fun _ -> false) in
  let nt2 = word_ci "#t" in
  let nt2 = pack nt2 (fun _ -> true) in
  let nt1 = disj nt1 nt2 in
  let nt1 = pack nt1 (fun b -> ScmBoolean b) in
  nt1 str
and nt_char_simple str = 
  let nt1 = const (fun c-> c > ' ') in
  nt1 str 
and make_named_char char_name ch =  
  let nt1 = word_ci char_name in
  let nt1 = pack nt1 (fun a -> ch) in
  nt1
and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] in
  nt1 str
and nt_char_hex str =  
  let nt1 = range '0' '9' in
  let nt2 = range 'a' 'f' in 
  let nt3 = range 'A' 'F' in
  let nt1 = disj_list [nt1;nt2;nt3] in 
  nt1 str
and nt_hexa_char str = 
  let nt1 = char 'x' in
  let nt1 = caten nt1 (plus nt_char_hex) in
  let nt1 = pack nt1 (fun (a,b) -> char_of_int(int_of_string("0x"^(list_to_string b)))) in
  nt1 str
and nt_char_prefix str = 
  let nt1 = word "#\\" in
  nt1 str
and nt_char str = 
  let nt1 = caten nt_char_prefix (not_followed_by (disj_list [nt_char_named; nt_char_hex; nt_char_simple]) nt_symbol_char) in 
  let nt1 = pack nt1 (fun (a,b) -> ScmChar b) in
  nt1 str
and nt_symbol_char str = 
  let nt1 = range '0' '9' in
  let nt2 = range 'a' 'z' in
  let nt3 = range 'A' 'Z' in
  let nt4 = char '!' in
  let nt5 = char '$' in
  let nt6 = char '^' in
  let nt7 = char '*' in
  let nt8 = char '-' in
  let nt9 = char '_' in
  let nt10 = char '=' in
  let nt11 = char '+' in
  let nt12 = char '<' in
  let nt13 = char '>' in
  let nt14 = char '?' in
  let nt15 = char '/' in
  let nt16 = char ':' in
  let ntAll = disj_list [nt1; nt2; nt3; nt4; nt5; nt6; nt7; nt8; nt9; nt10; nt11; nt12; nt13; nt14; nt15; nt16] in
  ntAll str
and nt_symbol str = 
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str
and nt_string_literal_char str = 
  let nt1 = nt_symbol_char in
  nt1 str
and nt_string_meta_char str = 
    let nt1 = word "\\\\" in
    let nt1 = pack nt1 (fun _-> '\\') in
    let nt2 = word "\\\"" in
    let nt2 = pack nt2 (fun _-> '"') in
    let nt3 = word_ci "\\t" in
    let nt3 = pack nt3 (fun _-> '\t') in
    let nt4 = word_ci "\\n" in
    let nt4 = pack nt4 (fun _-> '\n') in
    let nt5 = word_ci "\\r" in
    let nt5 = pack nt5 (fun _-> '\r') in
    let nt6 = word_ci "\\f" in
    let nt6 = pack nt6 (fun _-> char_of_int(12)) in
    let nt7 = word "~~" in
    let nt7 = pack nt7 (fun _-> '~') in
    let nt7 = disj_list [nt1;nt2;nt3;nt4;nt5;nt6;nt7] in
    nt7 str
and nt_string_hex_char str =
    let nt1 = word "\\x" in
    let nt2 = plus nt_hexa_char in
    let nt3 = caten nt2 (char ';') in
    let nt4 = caten nt1 nt3 in
    let nt4 = pack nt4 (fun (a,(b,c))-> char_of_int(int_of_string("0x"^(list_to_string b)))) in
    nt4 str
and nt_string_interpolated str = 
  let spaces =  (star nt_whitespace) in
  let nt1 = caten (char '~') (char '{') in
  let nt1 = caten nt1 spaces in
  let nt1 = caten nt1 nt_sexpr in
  let nt1 = caten nt1 spaces in 
  let nt1 = caten nt1 (char '}') in
  let nt1 = pack nt1 (fun ((((((a,b),c),d),e),f))-> ScmPair(ScmSymbol "format",ScmPair(ScmString "~a",ScmPair(d,ScmNil)))) in
  nt1 str
and nt_string_char str = 
  let nt1 = disj_list [nt_string_literal_char;nt_string_meta_char;nt_string_hex_char] in
  nt1 str
and nt_string str =
  let strs = char '"' in
  let strc = plus nt_string_char in
  let strc = pack strc (fun (a)-> ScmString ( list_to_string a)) in
  let nt1 = caten strs (star (disj nt_string_interpolated strc ) ) in
  let nt1 = caten nt1 strs in
  let nt1 = pack nt1 (fun (((a,b),c))-> match b with
    | [] -> ScmString ""
    | h::[] -> h
    | h::t -> list_2_plist ([ScmSymbol "string-append"]@b)
  ) in
  nt1 str
and nt_vector str = 
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str
and nt_proper_list str = 
  let spaces = star nt_whitespace in
  let nt1 = caten (char '(' ) spaces in
  let nt1 = caten nt1 (star nt_sexpr) in
  let nt1 = caten nt1 spaces in
  let nt1 = caten nt1 (char ')') in
  let nt2 = pack nt1 (fun (((((a,b),c),d),e))-> list_pl c) in
  nt2 str
and nt_improper_list str = 
  let spaces = star nt_whitespace in
  let nt1 = caten (char '(') spaces in
  let nt1 = caten nt1 (plus nt_sexpr) in
  let nt1 = caten nt1 spaces in
  let nt1 = caten nt1 (char '.') in
  let nt1 = caten nt1 spaces in
  let nt1 = caten nt1 nt_sexpr in
  let nt1 = caten nt1 spaces in
  let nt1 = caten nt1 (char ')') in
  let nt2 = pack nt1 (fun ((((((((a,b),c),d),e),f),g),h),i)-> List.append c [g]) in
  let nt2 = pack nt2 (fun (a)-> list_impl a) in
  nt2 str
and nt_list str = 
  let spaces = star nt_whitespace in
  let nt1 = disj nt_improper_list nt_proper_list in
  let nt1 = caten spaces (caten nt1 spaces) in
  let nt1 = pack nt1 (fun (a,(b,c))-> b) in
  nt1 str
and nt_quoted str = 
  let nt1 = char '\'' in
  let nt2 = pack (caten nt1 nt_sexpr) (fun (q,sexp) -> ScmPair ((ScmSymbol "quote"), ScmPair(sexp,ScmNil))) in
  nt2 str
and nt_quasi_quoted str = 
  let nt1 = char '`' in
  let nt2 = pack (caten nt1 nt_sexpr) (fun (q,sexp) -> ScmPair ((ScmSymbol "quasiquote"), ScmPair(sexp,ScmNil))) in
  nt2 str
and nt_unquoted str =
  let nt1 = char ',' in
  let nt2 = pack (caten nt1 nt_sexpr) (fun (uq,sexp) -> ScmPair ((ScmSymbol "unquote"), ScmPair(sexp,ScmNil))) in
  nt2 str 
and nt_unquoted_and_spliced str = 
  let nt1 = char ',' in
  let nt2 = char '@' in
  let nt2 = caten nt1 nt2 in
  let nt2 = caten nt2 nt_sexpr in
  let nt2 = pack nt2 (fun ((l,r),b) -> ScmPair ((ScmSymbol "unquote-splicing"), ScmPair(b,ScmNil))) in
  nt2 str
and nt_quoted_forms str = 
  let nt1 = disj_list [nt_quoted;nt_quasi_quoted;nt_unquoted;nt_unquoted_and_spliced] in
  nt1 str
and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
               nt_string; nt_vector; nt_list; nt_quoted_forms; nt_improper_list] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;

end;; (* end of struct Reader *)

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;