module Lexer = 
    type token =                         // Tokens
        | TkEnd                          // Special ending token
        | TkInt of int                   // Integer literal
        | TkRParen | TkLParen            // Parentheses
        | TkAdd | TkSub | TkMul | TkDiv  // Operations

    let (|Prefix|_|) (p : string) (s : string) = // String prefix active pattern
        if s.StartsWith(p) then Some(s.Substring (p.Length))
        else None

    open System.Text.RegularExpressions
    let (|Integer|_|) s = // Parse string into integer prefix i + rest of string
        let m = Regex("([0-9]+)(.*)").Match(s)
        if m.Success
        then 
            match [ for x in m.Groups -> x.Value ] with
            | [_; istr; rest] -> 
                let mutable intvalue = 0
                if System.Int32.TryParse(istr, &intvalue) 
                then Some(intvalue, rest)
                else None
            | _ -> None
        else None


    exception LexerError of string
    let rec tokenise = function 
        | Prefix " " rest -> tokenise rest              // ignore whitespace
        | Prefix "(" rest -> TkLParen :: tokenise rest  
        | Prefix ")" rest -> TkRParen :: tokenise rest 
        | Prefix "+" rest -> TkAdd :: tokenise rest 
        | Prefix "-" rest -> TkSub :: tokenise rest 
        | Prefix "*" rest -> TkMul :: tokenise rest 
        | Prefix "/" rest -> TkDiv :: tokenise rest 
        | Integer (i, rest) -> TkInt i :: tokenise rest 
        | "" -> [TkEnd]
        | _ -> raise (LexerError "Unknown Character, or whitespace between ints")

    let rec to_string = function 
        | TkInt i :: tks -> sprintf "%d" i + to_string tks
        | TkLParen :: tks -> "(" + to_string tks 
        | TkRParen :: tks -> ")" + to_string tks 
        | TkAdd :: tks -> "+" + to_string tks 
        | TkSub :: tks -> "-" + to_string tks 
        | TkMul :: tks -> "*" + to_string tks 
        | TkDiv :: tks -> "/" + to_string tks 
        | [TkEnd] -> "$" 
        | [] -> ""  // (Note: invalid token list)

// Abstract Syntax Tree
module AST =
    type expr = 
        | Lit of lit 
        | BinOp of expr * binop * expr
        | UnaryOp of unop * expr
    and lit = Int of int | Var of string
    and binop = Add | Sub | Mul | Div | Pow | Mod
    and unop = Neg | Fac | Abs

    let rec eval map = function 
        | Lit (Int i) -> i
        | Lit (Var v) -> Map.find v map
        | BinOp (e1, Add, e2) -> eval map e1 + eval map e2 
        | BinOp (e1, Sub, e2) -> eval map e1 - eval map e2
        | BinOp (e1: expr, Mul, e2) -> eval map e1 * eval map e2
        | BinOp (e1, Div, e2) -> eval map e1 / eval map e2
        | UnaryOp (Neg, e) -> - eval map e

module Parser = 
    open Lexer 
    open AST 
    exception SyntaxError of string

    let prepend_binop e1 op = function        // Helper function
        | e2, tks -> BinOp (e1, op, e2), tks 

    let prepend_unaryop op = function        // Helper function
        | e2, tks -> UnaryOp (op, e2), tks 

    let rec parse_statement tks = 
        match parse_expression tks with 
        | e, [TkEnd] -> e
        | _ -> raise (SyntaxError "Missing End Token" )
    and parse_expression tks = 
        match parse_term tks with 
        | t, TkAdd :: rtks -> prepend_binop t Add (parse_expression rtks)
        | t, TkSub :: rtks -> prepend_binop t Sub (parse_expression rtks)
        | t, rtks -> t, rtks
    and parse_term tks = 
        match parse_factor tks with 
        | f, TkMul :: rtks -> prepend_binop f Mul (parse_term rtks)
        | f, TkDiv :: rtks -> prepend_binop f Div (parse_term rtks)
        | f, rtks -> f, rtks
    and parse_factor tks = function
        
        | TkSub :: rtks -> prepend_unaryop Neg (parse_factor rtks) 
        | tks -> parse_int tks

    and parse_exponent tks = 
        match parse_brackets tks with 
        | x, TkPow ::  rtks -> prepend_binop x Pow (parse_factor rtks)
        | x, rtks -> x, rtks
    and parse_brackets = function
        | TkLParen :: rtks -> 
            match parse_expression rtks with 
            | e, TkRParen :: rrtks -> e, rrtks 
            | e, rtks -> raise (Lexer.to_string rtks |> sprintf "Missing closing bracket. Instead got: %s" |> SyntaxError)
        | TkAbs :: rtks -> 
            match parse_expression rtks with 
            | e, TkAbs :: rrtks -> e, rrtks 
            | e, rtks -> raise (Lexer.to_string rtks |> sprintf "Missing closing abs '|'. Instead got: %s" |> SyntaxError)
        | tks -> parse_lit tks
    and parse_lit = function
        | TkInt i :: rtks -> Lit (Int i), rtks
        | TkVar v :: rtks -> Lit (Var v), rtks
        | tks -> raise (Lexer.to_string tks |> sprintf "Expected literal. Instead got: %s" |> SyntaxError)

    // e = t + e | t - e | t
    // t = u * t | u / t | u mod t | u
    // u = -f | f! | x
    // x = n ^ x | b
    // b = (e) | |e|
    // n = int 


    let parse = tokenise >> parse_statement
    let parse_and_eval = parse >> eval 