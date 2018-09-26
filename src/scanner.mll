(*
	Jeffrey Monahan 	- jm4155
	Christine Pape 		- cmp2223
	Montana St. Pierre 	- mrs2296
	Shelley Zhong 		- sz2699
	Tengyu Zhou 		- tz2338
*)

{ open Parser }

rule token = parse
	(* Whitespace *)
	[' ' '\t' '\r' '\n'] { token lexbuf }

	(* Comments *)
	| "/*"     { blockComment lexbuf }			
	| "//"     { singleComment lexbuf }

	(* Delimiters *)
	| '('  { LPAREN }  
	| ')'  { RPAREN } 
	| '{'  { LBRACE } 
	| '}'  { RBRACE }
	| '['  { LBRACKET } 
	| ']'  { RBRACKET }
	| ';'  { SEMI } 
	| ','  { COMMA } 
	| ':'  { COLON } 

	(* Arithmetic Operators *)
	| '+'  { PLUS } 
	| '-'  { MINUS } 
	| '*'  { TIMES } 
	| '/'  { DIVIDE }
	| '='  { ASSIGN } 
	| "++" { INC } 
	| "--" { DEC }

	(* Relational Operators *)
	| "==" { EQ } 
	| "!=" { NEQ } 
	| '<'  { LT } 
	| ">"  { GT }
	| "<=" { LEQ } 
	| ">=" { GEQ } 

	(* Logical Operators *)
	| "&&" { AND } 
	| "||" { OR } 
	| '!'  { NOT }

	(* Control Flow *)
	| "if"     { IF } 
	| "else"   { ELSE } 
	| "while"  { WHILE }
	| "for"    { FOR } 
	| "return" { RETURN }

	(* Boolean Values *)
	| "true"  { TRUE } 
	| "false" { FALSE }

	(* Data Types *)
	| "int"    { INT } 
	| "float"  { FLOAT } 
	| "bool"   { BOOL } 
	| "void"   { VOID }
	| "String" { STRING } 
	| "matrix" { MATRIX } 

	(* Matrix-related *)
	| "rows" { ROWS } 
	| "cols" { COLS } 
	| "transpose"   { TRANSPOSE }
	| "trace" { TRACE }
	| "subMatrix" { SUBMATRIX }

	(* Literals, Identifiers, EOF *)
	| ['0'-'9']+ as lxm { NUM_LIT(Ast.IntLit(int_of_string lxm)) }
	| ['0'-'9']+ '.' ['0'-'9']+ as lxm { NUM_LIT(Ast.FloatLit(float_of_string lxm)) }
	| '"' (([^ '"'] | "\\\"")* as str) '"' { STRING_LIT(str) }
	| ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']* as lxm { ID(lxm) }
	| eof { EOF }
	| _ as char { raise (Failure("illegal character " ^ Char.escaped char)) }

and blockComment = parse
  "*/" { token lexbuf }
	| _    { blockComment lexbuf }

and singleComment = parse
  ['\n' '\r'] { token lexbuf}
	| _    { singleComment lexbuf }
