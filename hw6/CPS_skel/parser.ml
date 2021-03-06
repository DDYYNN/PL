type token =
  | IF
  | THEN
  | ELSE
  | FN
  | RARROW
  | DOT
  | PLUS
  | MINUS
  | LP
  | RP
  | REC
  | COMMA
  | EOF
  | NUM of (int)
  | ID of (string)

open Parsing;;
let _ = parse_error;;
# 8 "parser.mly"
exception EmptyBinding
exception IncorrectSelection
let whichSel = function (e, 1) -> M0.Fst e
      | (e, 2) -> M0.Snd e
      | _ -> raise IncorrectSelection
# 27 "parser.ml"
let yytransl_const = [|
  257 (* IF *);
  258 (* THEN *);
  259 (* ELSE *);
  260 (* FN *);
  261 (* RARROW *);
  262 (* DOT *);
  263 (* PLUS *);
  264 (* MINUS *);
  265 (* LP *);
  266 (* RP *);
  267 (* REC *);
  268 (* COMMA *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  269 (* NUM *);
  270 (* ID *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\000\000"

let yylen = "\002\000\
\002\000\003\000\001\000\002\000\001\000\004\000\005\000\002\000\
\003\000\003\000\006\000\005\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\003\000\
\005\000\013\000\000\000\000\000\000\000\004\000\000\000\000\000\
\000\000\000\000\001\000\000\000\000\000\000\000\002\000\000\000\
\000\000\010\000\000\000\000\000\000\000\000\000\000\000\000\000\
\012\000\000\000\000\000"

let yydgoto = "\002\000\
\010\000\020\000"

let yysindex = "\007\000\
\024\255\000\000\024\255\252\254\009\255\024\255\010\255\000\000\
\000\000\000\000\029\000\005\255\021\255\000\000\042\255\013\255\
\023\255\024\255\000\000\026\255\024\255\024\255\000\000\024\255\
\034\255\000\000\251\254\056\255\078\255\067\255\024\255\024\255\
\000\000\078\255\086\255"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\
\000\000\000\000\015\000\000\000\047\000\000\000\000\000\000\000\
\000\000\058\000\042\000"

let yygindex = "\000\000\
\000\000\255\255"

let yytablesize = 326
let yytable = "\011\000\
\008\000\012\000\005\000\006\000\015\000\003\000\021\000\001\000\
\004\000\013\000\017\000\018\000\005\000\006\000\009\000\007\000\
\027\000\008\000\009\000\028\000\029\000\014\000\030\000\016\000\
\003\000\022\000\025\000\004\000\019\000\034\000\035\000\005\000\
\006\000\005\000\007\000\026\000\008\000\009\000\031\000\000\000\
\000\000\011\000\003\000\000\000\000\000\004\000\006\000\017\000\
\018\000\005\000\006\000\023\000\007\000\024\000\008\000\009\000\
\003\000\007\000\032\000\004\000\000\000\017\000\018\000\005\000\
\006\000\000\000\007\000\003\000\008\000\009\000\004\000\000\000\
\017\000\018\000\005\000\006\000\033\000\007\000\003\000\008\000\
\009\000\004\000\000\000\017\000\018\000\005\000\006\000\000\000\
\007\000\000\000\008\000\009\000\018\000\005\000\006\000\000\000\
\000\000\000\000\000\000\009\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\008\000\008\000\008\000\008\000\000\000\008\000\008\000\
\000\000\008\000\008\000\008\000\008\000\008\000\008\000\009\000\
\009\000\009\000\009\000\000\000\009\000\009\000\000\000\000\000\
\009\000\009\000\009\000\009\000\009\000\003\000\000\000\000\000\
\004\000\000\000\017\000\018\000\005\000\006\000\000\000\007\000\
\000\000\008\000\009\000\011\000\011\000\011\000\000\000\011\000\
\006\000\006\000\000\000\011\000\011\000\011\000\011\000\000\000\
\006\000\000\000\006\000\007\000\007\000\000\000\000\000\000\000\
\000\000\000\000\000\000\007\000\000\000\007\000"

let yycheck = "\001\000\
\000\000\003\000\008\001\009\001\006\000\001\001\002\001\001\000\
\004\001\014\001\006\001\007\001\008\001\009\001\000\000\011\001\
\018\000\013\001\014\001\021\000\022\000\013\001\024\000\014\001\
\001\001\005\001\014\001\004\001\000\000\031\000\032\000\008\001\
\009\001\008\001\011\001\013\001\013\001\014\001\005\001\255\255\
\255\255\000\000\001\001\255\255\255\255\004\001\000\000\006\001\
\007\001\008\001\009\001\010\001\011\001\012\001\013\001\014\001\
\001\001\000\000\003\001\004\001\255\255\006\001\007\001\008\001\
\009\001\255\255\011\001\001\001\013\001\014\001\004\001\255\255\
\006\001\007\001\008\001\009\001\010\001\011\001\001\001\013\001\
\014\001\004\001\255\255\006\001\007\001\008\001\009\001\255\255\
\011\001\255\255\013\001\014\001\007\001\008\001\009\001\255\255\
\255\255\255\255\255\255\014\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\001\001\002\001\003\001\004\001\255\255\006\001\007\001\
\255\255\009\001\010\001\011\001\012\001\013\001\014\001\001\001\
\002\001\003\001\004\001\255\255\006\001\007\001\255\255\255\255\
\010\001\011\001\012\001\013\001\014\001\001\001\255\255\255\255\
\004\001\255\255\006\001\007\001\008\001\009\001\255\255\011\001\
\255\255\013\001\014\001\002\001\003\001\004\001\255\255\006\001\
\002\001\003\001\255\255\010\001\011\001\012\001\013\001\255\255\
\010\001\255\255\012\001\002\001\003\001\255\255\255\255\255\255\
\255\255\255\255\255\255\010\001\255\255\012\001"

let yynames_const = "\
  IF\000\
  THEN\000\
  ELSE\000\
  FN\000\
  RARROW\000\
  DOT\000\
  PLUS\000\
  MINUS\000\
  LP\000\
  RP\000\
  REC\000\
  COMMA\000\
  EOF\000\
  "

let yynames_block = "\
  NUM\000\
  ID\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : M0.mexp) in
    Obj.repr(
# 33 "parser.mly"
                  (_1)
# 199 "parser.ml"
               : M0.mexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : M0.mexp) in
    Obj.repr(
# 36 "parser.mly"
               (_2)
# 206 "parser.ml"
               : M0.mexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 37 "parser.mly"
        (M0.Num _1)
# 213 "parser.ml"
               : M0.mexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 38 "parser.mly"
              (M0.Num (- _2))
# 220 "parser.ml"
               : M0.mexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 39 "parser.mly"
       (M0.Var (_1))
# 227 "parser.ml"
               : M0.mexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : M0.mexp) in
    Obj.repr(
# 40 "parser.mly"
                      (M0.Fn(_2,_4))
# 235 "parser.ml"
               : M0.mexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : M0.mexp) in
    Obj.repr(
# 41 "parser.mly"
                          (M0.Rec(_2, _3, _5))
# 244 "parser.ml"
               : M0.mexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : M0.mexp) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : M0.mexp) in
    Obj.repr(
# 42 "parser.mly"
                        (M0.App(_1,_2))
# 252 "parser.ml"
               : M0.mexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : M0.mexp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : M0.mexp) in
    Obj.repr(
# 43 "parser.mly"
                   (M0.Add(_1,_3))
# 260 "parser.ml"
               : M0.mexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : M0.mexp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 44 "parser.mly"
                 (whichSel (_1,_3))
# 268 "parser.ml"
               : M0.mexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : M0.mexp) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : M0.mexp) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : M0.mexp) in
    Obj.repr(
# 45 "parser.mly"
                                (M0.Ifz(_2,_4,_6))
# 277 "parser.ml"
               : M0.mexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : M0.mexp) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : M0.mexp) in
    Obj.repr(
# 46 "parser.mly"
                          (M0.Pair (_2, _4))
# 285 "parser.ml"
               : M0.mexp))
(* Entry program *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let program (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : M0.mexp)
;;
