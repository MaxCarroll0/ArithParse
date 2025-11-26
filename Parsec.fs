module AST =
    type expr = 
        | Lit of lit
        | BinOp of expr * binop * expr
        | UnaryOp of unaryop * expr 
    and lit = Int of int | Var of string
    and binop = Add | Sub | Mul | Div | Mod | Pow
    and unaryop = Neg | Fac | Abs
    let of_binop op e1 e2 = BinOp(e1, op, e2)
    let of_unaryop op e = UnaryOp(op, e)

    let private factorial n = 
        let rec aux acc n = if n <= 1 then acc else aux (n * acc) (n - 1)
        aux 1 n

    let private absolute_value n = if n > 0 then n else -1 * n

    let assign assoc e = 
        let rec assign_aux = function 
        | Lit (Int i) as l -> l 
        | Lit (Var s) as l -> 
            match List.tryFind (fun (k, v) -> s = k) assoc with 
            | None -> l
            | Some (k, e) -> e
        | BinOp (a, op, b) -> BinOp (assign_aux a, op, assign_aux b) 
        | UnaryOp (op, a) -> UnaryOp (op, assign_aux a)
        assign_aux e
    
    exception MissingVariableAssignment of string
    exception DivideByZeroException
    exception FloatModuloException
    exception ZeroModuloException
    let eval_float assoc e = 
        let rec eval_aux = function 
        | Lit(Int i) -> float i
        | Lit (Var s) -> 
            match List.tryFind (fun (k, v) -> s = k) assoc with 
            | None -> raise <| MissingVariableAssignment (sprintf "Variable '%s' was not assigned." s)
            | Some (k, e) -> eval_aux e
        | BinOp (e1, Add, e2) -> eval_aux e1 + eval_aux e2
        | BinOp (e1: expr, Sub, e2) -> eval_aux e1 - eval_aux e2
        | BinOp (e1, Mul, e2) -> eval_aux e1 * eval_aux e2
        | BinOp (e1, Div, e2) -> let denom = eval_aux e2 in if denom <> 0.0 then eval_aux e1 / denom else raise DivideByZeroException
        | BinOp (e1, Mod, e2) -> 
            let modulo = eval_aux e2 
            if modulo <> 0.0 then 
                if (floor modulo) = modulo then eval_aux e1 % modulo else raise FloatModuloException
            else raise ZeroModuloException
        | BinOp (e1, Pow, e2) -> eval_aux e1 ** eval_aux e2
        | UnaryOp (Neg, e) -> - eval_aux e
        | UnaryOp (Fac, e) -> float (factorial (int (eval_aux e)))
        | UnaryOp (Abs, e) -> let x = eval_aux e in if x > 0. then x else -x
        eval_aux e


    let rec to_string = function 
        | Lit(Int i) -> sprintf "%i" i 
        | Lit(Var s) -> s
        | BinOp (e1, Add, e2) -> "(" + to_string e1 + " + " + to_string e2 + ")"
        | BinOp (e1: expr, Sub, e2) -> "(" + to_string e1 + " - " + to_string e2 + ")"
        | BinOp (e1, Mul, e2) -> "(" + to_string e1 + " * " + to_string e2 + ")"
        | BinOp (e1, Div, e2) -> "(" + to_string e1 + " / " + to_string e2 + ")"
        | BinOp (e1, Mod, e2) -> "(" + to_string e1 + " mod " + to_string e2 + ")"
        | BinOp (e1, Pow, e2) -> "(" + to_string e1 + " ^ " + to_string e2 + ")"
        | UnaryOp (Neg, e) -> "(" + "-" + to_string e + ")"
        | UnaryOp (Fac, e) -> "(" + to_string e + "!" + ")"
        | UnaryOp (Abs, e) -> "|" + to_string e + "|"

    let assignment_to_string assignment = "[" + (List.map (fun (s, e) -> s + " -> " + to_string e) assignment |> String.concat " , ") + "]" 

module Parser = 
    open AST
    open FParsec
    
    let private string_of_infix = function 
        | Add -> "+"
        | Sub -> "-"
        | Mul -> "*"
        | Div -> "/"
        | Mod -> "mod"
        | Pow -> "^"
    let reserved_keywords = ["mod"; "with"; "prev"]
        
    let private (<!>) (p: Parser<_,_>) label : Parser<_,_> = // Parsing tracer, could print to log instead
        fun stream ->
            let reply = p stream
            reply

    let private integer = pint32 .>> spaces |>> (Int >> Lit)                                                                 
                          <!> "integer"
    let private variableString = asciiLetter .>>.? many (asciiLetter <|> digit) 
                                 |>> fun (f, r) -> string f + (List.map string r |> String.concat "") 
                                 >>=? fun c -> // Disallow mod keyword from variable names
                                        if List.contains c reserved_keywords
                                        then fail (sprintf "Cannot parse reserved keywords: %O as variable names." reserved_keywords)
                                        else preturn c
                                 .>> spaces                                                                
                                 <!> "variable"
    let private variable = variableString |>> (Var >> Lit)
    let private brackets contains (l, r) = between (pstring l) (pstring r) contains .>> spaces     
                                            <!> sprintf "brackets %s %s" l r
    
    let rec private apply_n f n x = //Helper n applications of f to x
        match n with 
        | 0 -> x
        | n -> apply_n f (n-1) (f x)

    let private infix op = pstring <| string_of_infix op .>> spaces >>% of_binop op                     
                                  <!> sprintf "%s %O" "infix:" op
    let private left_assoc ops next = chainl1 next <| choice (ops |> List.map infix)
    let private right_assoc ops next = chainr1 next <| choice (ops |> List.map infix)
    let private prefix_unary next op str = many (pstring str .>> spaces <!> sprintf "%s %O" "prefix unaryop:" op) 
                                        .>>. next |>> fun (l, e) -> apply_n (of_unaryop op) (List.length l) e  
    let private postfix_unary next op str = next .>>. many (pstring str .>> spaces <!> sprintf "%s %O" "postfix unaryop:" op) 
                                        |>> fun (e, l) -> apply_n (of_unaryop op) (List.length l) e   
    let private abs_val contains = brackets contains ("|", "|") |>> of_unaryop Abs

    // Forward declare recursive parser
    let private  precedenceTop, precedenceTopImpl = createParserForwardedToRef()
    // Parse each precedence level with the corresponding operations
    let precedenceBot = integer <|> variable <|> abs_val precedenceTop
                        <|> choice (["(", ")"; "[", "]"; "{", "}"] |> List.map (brackets precedenceTop))  
                        <!> "val or parenthesised expression"
    let precedence5 = postfix_unary precedenceBot Fac "!"  <!> "precedence 5" // Omitting ! implicitly included in postfix_unary
    let precedence4 = right_assoc [Pow] precedence5  <!> "precedence 4"
    let precedence3 = prefix_unary precedence4 Neg "-" <|> precedence4  <!> "precedence 3" // Omitting - implicity included in prefix_unary
    let precedence2 = left_assoc [Mul; Div; Mod] precedence3  <!> "precedence 2"
    // Recursive grammar joined by precedenceTop
    do precedenceTopImpl := left_assoc [Add; Sub] precedence2  <!> "precedence 1" // left_assoc includes case of one occurance
    
    let private expression = spaces >>. precedenceTop  <!> "EXPRESSION"
    let parse_expression = run (expression .>> eof)  

    let private assignment = between (pchar '[') (pchar ']') 
                              (sepBy (spaces >>. variableString .>> spaces .>> pstring "->" .>>. expression .>> spaces) (pchar ','))
                              <|> (spaces >>. preturn [])   <!> "ASSIGNMENT"
    let parse_assignment = run (spaces >>. assignment .>> spaces .>> eof)


    module REPL =
        type command = 
            | Assign of expr * (string * expr) list 
            | AssignPrev of (string * expr) list 
            | Eval of expr * (string * expr) list 
            | EvalPrev of (string * expr) list 
            | View of expr
            | Exit
        let private assign = pstring "assign" >>. spaces1 
                            >>. ((pstring "prev" >>. spaces1 >>. pstring "with" >>. spaces1 
                                >>. assignment |>> AssignPrev)
                            <|> (expression .>> spaces .>> pstring "with" .>> spaces1 
                                .>>. assignment |>> Assign))
                            <!> "COMMAND: assign"
        let private with_assignment_or_empty = (spaces >>? pstring "with" >>. spaces1 >>. assignment .>> spaces)
                                                <|> (spaces >>. preturn [])
        let private eval = pstring "eval" >>. spaces1 
                            >>. ((pstring "prev" >>. with_assignment_or_empty |>> EvalPrev) 
                            <|> (expression .>>. with_assignment_or_empty |>> Eval))
                            <!> "COMMAND: eval"
        let private view = pstring "save" >>. spaces1 >>. expression |>> View <!> "COMMAND: save"
        let private exit = pstring "exit" >>. preturn Exit  <!> "COMMAND: exit"
        let command = run (spaces >>. view <|> eval <|> assign <|> exit .>> spaces .>> eof <!> "COMMAND")




// TODO: repl of commands for assign, simplify etc.
[<EntryPoint>]
let main args = 
    printfn "%s" "Integer arithmetic expression REPL Started.\n";
    printfn "%s" "Examples of commands:\n 
     To exit,                                    type:    exit\n
     To view/save an expression,                 type:    save 1 + 2 * 3\n 
     To evaluate expression,                     type:    eval 1 + 2 * 3\n 
     To evaluate previous expression output,     type:    eval prev\n
     To evaluate expressions with variables,     type:    eval 1 + varx * y with [varx -> 2, y -> 3]\n
     To assign variables in expression,          type:    assign 1 + varx * y with [varx -> 2, y -> 3]\n
     To assign variables of previous expression, type:    assign prev [varx -> 2, y -> 3]\n";
    printfn "%s" "Traces of parsing are printed to console. Each input expression is printed back with explicit brackets denoting evaluation order."


    let (|Success|Failure|) = function 
        | FParsec.CharParsers.ParserResult.Success (parsed, _, _) -> Success parsed
        | FParsec.CharParsers.ParserResult.Failure (expr, _, _) -> Failure expr

    let prev = ref None
    while true do 
        printfn "\n\nPrevious expression is:\n %s\n" (AST.to_string (Option.defaultValue (AST.Lit(AST.Var "None")) (!prev)));
        printfn "Enter Next Command.\n"
        let input = System.Console.ReadLine();   
        match Parser.REPL.command input with 
        | Success Parser.REPL.Exit -> exit 0
        | Success (Parser.REPL.View expr) -> 
            printfn "\n"
            prev := Some expr;
            printfn "RESULT:\nExpression saved as prev:\n %s" (AST.to_string expr)
        | Success (Parser.REPL.EvalPrev []) -> 
            printfn "\n";
            match !prev with 
            | Some expr -> 
                try AST.eval_float [] expr 
                    |> printfn "RESULT:\nExpression:\n %s\n Evaluates to: %f" (AST.to_string expr) 
                with
                | AST.MissingVariableAssignment s -> printfn "ERROR: Unbound Variable: %s\n While evaluating expression:\n %s" s (AST.to_string expr)
                | AST.DivideByZeroException -> printfn "ERROR: Division by 0 error\n While evaluating expression:\n %s" (AST.to_string expr)
                | AST.FloatModuloException -> printfn "ERROR: Modulo of non-integer error\n While evaluating expression:\n %s" (AST.to_string expr)
                | AST.ZeroModuloException -> printfn "ERROR: Modulo by 0 error\n While evaluating expression:\n %s" (AST.to_string expr)
            | None -> printfn "ERROR: No previous expression has been entered yet!"
        | Success (Parser.REPL.EvalPrev assignment) -> 
            printfn "\n";
            match !prev with 
            | Some expr -> 
                try AST.eval_float assignment expr 
                    |> printfn "RESULT:\nExpression:\n %s\n Substituting:\n %s\n Evaluates to: %f" (AST.to_string expr) (AST.assignment_to_string assignment)
                with
                | AST.MissingVariableAssignment s -> printfn "ERROR: Unbound Variable: %s\n While evaluating expression:\n %O\n With substitution:\n %O" s (AST.to_string expr) (AST.assignment_to_string assignment)
                | AST.DivideByZeroException -> printfn "ERROR: Division by 0 error\n While evaluating expression:\n %O\n With substitution:\n %O" (AST.to_string expr) (AST.assignment_to_string assignment)
                | AST.FloatModuloException -> printfn "ERROR: Modulo of non-integer error\n While evaluating expression:\n %s" (AST.to_string expr)
                | AST.ZeroModuloException -> printfn "ERROR: Division by 0 error\n While evaluating expression:\n %s" (AST.to_string expr)
            | None -> printfn "ERROR: No previous expression has been entered yet!"
        | Success (Parser.REPL.Eval (expr, [])) -> 
            printfn "\n";
            prev := Some expr;
            try AST.eval_float [] expr 
                    |> printfn "RESULT:\nExpression:\n %O\n Evaluates to: %f" (AST.to_string expr) 
            with
            | AST.MissingVariableAssignment s -> printfn "ERROR: Unbound Variable: %s\n While evaluating expression:\n %O" s (AST.to_string expr)
            | AST.DivideByZeroException -> printfn "ERROR: Division by 0 error\n While evaluating expression:\n %O" (AST.to_string expr)
            | AST.FloatModuloException -> printfn "ERROR: Modulo of non-integer error\n While evaluating expression:\n %s" (AST.to_string expr)
            | AST.ZeroModuloException -> printfn "ERROR: Division by 0 error\n While evaluating expression:\n %s" (AST.to_string expr)
        | Success (Parser.REPL.Eval (expr, assignment)) -> 
            printfn "\n";
            prev := Some expr;
            try AST.eval_float assignment expr 
                |> printfn "RESULT:\nExpression:\n %O\n Substituting:\n %O\n Evaluates to: %f" (AST.to_string expr) (AST.assignment_to_string assignment)
            with
            | AST.MissingVariableAssignment s -> printfn "ERROR: Unbound Variable: %s\n While evaluating expression:\n %O\n With substitution:\n %O" s (AST.to_string expr) (AST.assignment_to_string assignment)
            | AST.DivideByZeroException -> printfn "ERROR: Division by 0 error\n While evaluating expression:\n %O\n With substitution:\n %O" (AST.to_string expr) (AST.assignment_to_string assignment)
            | AST.FloatModuloException -> printfn "ERROR: Modulo of non-integer error\n While evaluating expression:\n %s" (AST.to_string expr)
            | AST.ZeroModuloException -> printfn "ERROR: Division by 0 error\n While evaluating expression:\n %s" (AST.to_string expr)
        | Success (Parser.REPL.Assign (expr, assignment)) -> 
            printfn "\n";
            prev := Some expr;
            let assigned = AST.assign assignment expr
            prev := Some assigned;
            printfn "RESULT:\nExpression:\n %O\n Substituting:\n %O\n Assigns to: %O" (AST.to_string expr) (AST.assignment_to_string assignment) (AST.to_string assigned)
        | Success (Parser.REPL.AssignPrev assignment) -> 
            printfn "\n";
            match !prev with 
            | Some expr -> 
                printfn "\n";
                let assigned = AST.assign assignment expr
                prev := Some assigned;
                printfn "RESULT:\nExpression:\n %s\n Substituting:\n %s\n Assigns to: %s" (AST.to_string expr) (AST.assignment_to_string assignment) (AST.to_string assigned)
            | None -> printfn "ERROR: No previous expression has been entered yet!"
        | Failure s -> printfn "\n"; printfn "ERROR: Failed to parse command:\n%s\n(See parse trace for more detailed info.)" s
    ; -1