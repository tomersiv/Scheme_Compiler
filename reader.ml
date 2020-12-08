
  #use "pc.ml";;
  open PC;;

  exception X_not_yet_implemented;;
  exception X_this_should_not_happen;;

  type number =
    | Fraction of int * int
    | Float of float;;

  type sexpr =
    | Bool of bool
    | Nil
    | Number of number
    | Char of char
    | String of string
    | Symbol of string
    | Pair of sexpr * sexpr;;

    let rec sexpr_eq s1 s2 =
      match s1, s2 with
      | Bool(b1), Bool(b2) -> b1 = b2
      | Nil, Nil -> true
      | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
      | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
      | Char(c1), Char(c2) -> c1 = c2
      | String(s1), String(s2) -> s1 = s2
      | Symbol(s1), Symbol(s2) -> s1 = s2
      | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
      | _ -> false;;

  module Reader: sig
    val read_sexprs : string -> sexpr list
  end
  = struct
  let normalize_scheme_symbol str =
    let s = string_to_list str in
    if (andmap
    (fun ch -> (ch = (lowercase_ascii ch)))
    s) then str
    else Printf.sprintf "|%s|" str;;

  (* write your code here *)

  let make_paired nt_left nt_right nt =
    let nt = caten nt_left nt in
    let nt = pack nt (function (_, e) -> e) in
    let nt = caten nt nt_right in
    let nt = pack nt (function (e, _) -> e) in
    nt;;

  let newLineParser = pack (char '\n') (fun x ->[x]);;
  let parse_sc = (char ';');;

  (* Parse Line Comments *)
  let parse_line_comment = pack (caten (caten  parse_sc (star (diff nt_any (disj newLineParser nt_end_of_input)))) (disj newLineParser nt_end_of_input))
                                (fun x -> Nil);;
  (* Parse whitespaces *)
  let parse_whitespaces =  pack (const (fun ch -> ch <= ' '))
                                (fun x -> Nil) ;;
  (* make_spaced  *)
  let make_spaced nt =  make_paired parse_whitespaces parse_whitespaces nt;;


  let parse_t =  (char_ci 't');;
  let parse_f =  (char_ci 'f');;
  let parse_hashtag =  (char '#');;
  let parse_dot =  (char '.');;
  let parse_dot2 =  pack (char '.') (fun x -> Nil);;
  let digit = (range '0' '9');;
  let digitNum = pack digit (fun x-> Char.code(x) - 48);;
  let natural = plus digit;;
  let naturalNum = plus digitNum;;
  let parse_alphabet = pack (range_ci 'a' 'z') (fun x-> lowercase_ascii x);;
  let rec gcd a b = if b = 0 then a else gcd b (a mod b);;

  (* Parse symbols *)
  let parse_symbols =  (disj_list ([
    (char '!');
    (char '$');
    (char '^');
    (char '*');
    (char '-');
    (char '_');
    (char '=');
    (char '+');
    (char '<');
    (char '>');
    (char '?');
    (char '/');
    (char ':');
    ]));;

  (* Parse Boolean *)
  let parse_boolean =  pack (pack (caten parse_hashtag (disj parse_t parse_f)) (fun (a,b) -> b))
  (fun x -> match x with
  | 't' -> Bool(true)
  | 'f' -> Bool(false)
  | 'T' -> Bool(true)
  | 'F' -> Bool(false)
  | _ -> raise X_this_should_not_happen
  );;

  (* Parse Char Prefix *)
  let parse_charPrefix = caten parse_hashtag (char '\\');;

  (* Parse Named Char *)
  let parse_namedChar = disj_list ([
    pack (word_ci "nul") (fun a -> char_of_int 0);
    pack (word_ci "newline") (fun a -> char_of_int 10);
    pack (word_ci "return") (fun a -> char_of_int 13);
    pack (word_ci "tab") (fun a -> char_of_int 9);
    pack (word_ci "page") (fun a -> char_of_int 12);
    pack (word_ci "space") (fun a -> char_of_int 32)
  ]);;

  (* Parse String Meta Char *)
  let parse_stringMetaChar = disj_list [
    pack (word_ci "\\n") (fun (x) -> char_of_int 10);
    pack (word_ci "\\r") (fun (x) -> char_of_int 13);
    pack (word_ci "\\t") (fun (x) -> char_of_int 9);
    pack (word_ci "\\f") (fun (x) -> char_of_int 12);
    pack (word_ci "\\\\") (fun (x) -> char_of_int 92);
    pack (word_ci "\\\"") (fun (x) -> char_of_int 34);
  ];;

  (* Parse Symbol Char No Dot*)
  let parse_symbolCharNoDot = disj_list ([ digit; parse_alphabet; parse_symbols; ]);;

  (* Parse Symbol Char *)
  let parse_symbolChar = disj parse_dot parse_symbolCharNoDot ;;

  (* Parse String Literal Char *)
  let parse_StringLiteralChar = const (fun ch -> ch != char_of_int 92 && ch != char_of_int 34);;

  (* Parse VisibleSimpleChar *)
  let parse_visibleSimpleChar = const (fun ch -> ch > char_of_int 32);;

  (* Parse String Char *)
  let parse_stringChar = disj parse_StringLiteralChar parse_stringMetaChar;;

  (* Parse Char *)
  let parse_char = (pack (caten parse_charPrefix (disj parse_namedChar parse_visibleSimpleChar))
                      (fun ((a,b),c)-> Char(c)));;
  (* Parse String *)
  let parse_string = pack (caten (caten (char '"') (star parse_stringChar))(char '"'))
                          (fun ((a,b),c) -> String(list_to_string(b)));;

  (* Parse Symbol *)
  let parse_symbol = pack (disj
                              (pack ( caten parse_symbolChar (plus parse_symbolChar) ) (fun (a,b) -> a::b ))
                              (pack (parse_symbolCharNoDot) (fun x -> [x]))
                            )
                          (fun x -> Symbol(list_to_string x));;

  (* Parse sign *)
  let parse_sign = (maybe (disj (char '+') (char '-')));;

  (* Parse plusminus *)
  let parse_plusminus = (pack parse_sign (fun (x) -> match x with
  | Some('+') -> '+'
  | Some('-') -> '-'
  | None -> '+'
  | _ -> raise X_this_should_not_happen ));;

  (* Parse integerHelper *)
  let parse_integerHelper = (caten parse_plusminus natural);;

  (* Parse integer *)
  let parse_integer = (pack parse_integerHelper
      (fun (x)-> if (fst x) = '-' then Number(Fraction(-1 * int_of_string(list_to_string(snd x)),1))
                    else Number(Fraction(int_of_string(list_to_string(snd x)),1)) ));;
  (* getInt helper *)
  let getInt = (pack parse_integerHelper
  (fun (x)-> if (fst x) = '-' then (-1 * int_of_string(list_to_string(snd x)))
                              else int_of_string(list_to_string(snd x))));;

  (* get float value*)
  let calculateFloat = (fun (a, ( (b, c) , d)) ->
                                                ( a , ( float_of_int
                                                          (List.fold_left (fun a b -> b + 10 * a) 0 b ) +.
                                                          (List.fold_right (fun a b -> a +. b /. 10.0 )
                                                                            (List.map (fun x -> float_of_int x) d) 0.0 )
                                                                            /. 10.0 )));;

  (* get float sign value*)
  let calculatFloatSign = (fun (a,b)-> if a = '-' then (-1.0 *. b)
                                                  else b);;

  (* get float value with sign*)
  let getFloat = pack (pack (caten parse_plusminus (caten (caten naturalNum parse_dot) naturalNum))
                      calculateFloat) calculatFloatSign;;

  let norm_num num =
    if num < 0 then -1 * num else num;;

  (* parse fraction*)
  let parse_fraction = pack (caten (caten getInt (char '/')) natural)
              ((fun (x,y) -> Number(Fraction((fst x) / (gcd (norm_num(fst x)) (int_of_string(list_to_string(y)))),
              (int_of_string(list_to_string(y))) / (gcd (int_of_string(list_to_string(y))) (norm_num(fst x)))))
              ));;

  (* parse float*)
  let parse_float = pack getFloat (fun x -> Number(Float(x)));;

  let getFInt = (pack parse_integerHelper
      (fun (x)-> if (fst x) = '-' then (-1.0 *. float_of_int(int_of_string(list_to_string(snd x))))
                    else float_of_int(int_of_string(list_to_string(snd x)))));;

  let parse_scientific1 = pack (caten (caten (disj getFInt getFloat) (char_ci 'e')) getInt)
                            (fun (x,y) -> Number(Float( (fst x) *. (10.0 ** (float_of_int y)))));;
  let parse_scientific2 = pack (caten (caten (disj getFloat getFInt) (char_ci 'e')) getInt)
                            (fun (x,y) -> Number(Float( (fst x) *. (10.0 ** (float_of_int y)))));;

  (* parse scientific *)
  let parse_scientific = disj parse_scientific1 parse_scientific2;;

  (* Parse number *)
  let parse_number = disj_list( [
    parse_scientific;
    parse_fraction;
    parse_float;
    parse_integer;
    ]);;

  (* Parse sexpr *)
  let rec parse_sexpr str = make_paired love love (disj_list[
    parse_boolean;
    parse_char;
    not_followed_by parse_number (disj parse_symbol parse_dot2);
    parse_string;
    parse_symbol;
    parse_list;
    parse_unquoted;
    parse_unquoteAndSpliced;
    parse_quoted;
    parse_quasiQuoted;
    parse_dottedList;
    parse_ParenthesesComments;
    ]) str

 (* Parse dottedlist   *)
  and parse_dottedList str =
      let exp  = (caten (caten (plus parse_sexpr) parse_dot) parse_sexpr) in
      let expwithPair =  (make_paired (char '(') (char ')') exp) in
      pack (expwithPair)
          (fun ((a,b),c) -> (List.fold_right (fun x y -> Pair(x,y)) a c)) str

  (* Parse quasiQuoted *)
  and parse_quasiQuoted str = pack (caten (char '`') parse_sexpr)
                                  (fun (a,b) -> Pair(Symbol("quasiquote") , Pair (b,Nil))) str

  (* Parse unquoted *)
  and parse_unquoted str = pack (caten (char ',') parse_sexpr)
                                (fun (a,b) -> Pair(Symbol("unquote") , Pair (b,Nil))) str

  (* Parse quoted *)
  and parse_quoted str = pack (caten (char '\'') parse_sexpr)
                                (fun (a,b) -> Pair(Symbol("quote") , Pair (b,Nil))) str

  (* Parse list *)
  and parse_list str =  pack (caten (caten (char '(') (star parse_sexpr)) (char ')'))
                                (fun ((a,b),c) -> List.fold_right (fun x y -> Pair(x,y)) b Nil ) str

  (* Parse unquoteAndSpliced *)
  and parse_unquoteAndSpliced str = pack (caten (caten (char ',') (char '@')) parse_sexpr)
                                    (fun ((a,b),c) -> Pair(Symbol("unquote-splicing") , Pair (c,Nil))) str

  (* Parse sexprComment *)
  and parse_sexprComment str = pack (caten (pack (caten (char '#') (char ';')) (fun _ -> Nil)) parse_sexpr)
                                (fun (a,b) -> Nil ) str

  (* Parse all the white spaces, line comments and S-expression Comments *)
  and love str = (star (disj_list [parse_whitespaces; parse_line_comment; parse_sexprComment]))
                        str

  (* Parse all the white spaces, line comments and S-expression Comments that are surrounded by parentheses *)
  and parse_ParenthesesComments str = pack (caten (caten (char '(') love) (char ')'))
                                    (fun _ -> Nil) str
  ;;
  (* the main loop *)
  let read_sexprs string = (fst ((star parse_sexpr) (string_to_list string)))
  end;;
