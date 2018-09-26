(*
	Jeffrey Monahan 	- jm4155
	Christine Pape 		- cmp2223
	Montana St. Pierre 	- mrs2296
	Shelley Zhong 		- sz2699
	Tengyu Zhou 		- tz2338
*)

open Ast

type snum =
		SIntLit of int
	|	SFloatLit of float

type sexpr =
	  SNumLit of snum
	| SBoolLit of bool
	| SStringLit of string
	| SMatrixLit of sexpr list list * typ
	| SId of string * typ
	| SBinop of sexpr * op * sexpr * typ
	| SUnop of uop * sexpr * typ
	| SAssign of sexpr * sexpr * typ
	| SCall of string * sexpr list * typ
	| SNoexpr
	| SMatrixAccess of string * sexpr * sexpr * typ
	| SRows of int
	| SCols of int
	| STranspose of string * typ
	| SSubMatrix of string * sexpr * sexpr * sexpr * sexpr * typ
	| STrace of string * typ

let get_sexpr_type sexpr = match sexpr with
	SNumLit(SIntLit(_))					-> Int
	| SNumLit(SFloatLit(_))				-> Float
	| SBoolLit(_)						-> Bool
	| SStringLit(_) 					-> String
	| SNoexpr 							-> Void
	| SRows(r) 							-> Int
	| SCols(c) 							-> Int
	| STranspose(_,t) 					-> t
	| SId(_, t) 						-> t
	| SBinop(_, _, _, t) 				-> t
	| SAssign(_, _, t) 					-> t
	| SCall(_, _, t)					-> t
	| SUnop(_, _, t) 					-> t
	| SMatrixAccess(_, _, _, t)			-> t
	| SMatrixLit(smlist, t)				->
		let c = List.length (List.hd smlist) in
		let r = List.length smlist in
		(match t with
			Int 		-> Matrix(Int, IntLit(r), IntLit(c))
			| Float	-> Matrix(Float, IntLit(r), IntLit(c))
			| _ 				-> raise(Failure"UnsupportedMatrixType"))
	| SSubMatrix (_,_,_,_,_,t)  		-> t 
	| STrace(_,t) 						-> t

type sstmt =
	  SBlock of sstmt list
	| SExpr of sexpr
	| SIf of sexpr * sstmt * sstmt
	| SFor of sexpr * sexpr * sexpr * sstmt
	| SWhile of sexpr * sstmt
	| SReturn of sexpr

type sfunc_decl = {
	styp 			: typ;
	sfname 			: string;
	sformals 		: bind list;
	slocals  		: bind list;
	sbody 			: sstmt list;
}

type sprogram = bind list * sfunc_decl list
