(*
	Jeffrey Monahan 	- jm4155
	Christine Pape 		- cmp2223
	Montana St. Pierre 	- mrs2296
	Shelley Zhong 		- sz2699
	Tengyu Zhou 		- tz2338
*)

open Ast
open Sast

module StringMap = Map.Make(String)


let check (globals, functions) =

	(* Checking duplicates *)
	let report_duplicate exceptf list =
		let rec helper = function
			n1 :: n2 :: _ when n1 = n2 -> raise (Failure (exceptf n1))
			| _ :: t -> helper t
			| [] -> ()
		in helper (List.sort compare list)
	in

	(* Checking void type in binding *)
	let check_not_void exceptf = function
	      (Void, n) -> raise (Failure (exceptf n))
	    | _ -> ()

	in

	(**** Checking Global Variables ****)
	List.iter (check_not_void (fun n -> "illegal void global " ^ n)) globals;
	report_duplicate (fun n -> "duplicate global " ^ n) (List.map snd globals);
	

	(**** Checking User-defined Functions. Cannot define built-in functions.  ****)
	if List.mem "printInt" (List.map (fun fd -> fd.fname) functions)
  	then raise (Failure ("function printInt may not be defined")) else ();
  	if List.mem "printFloat" (List.map (fun fd -> fd.fname) functions)
  	then raise (Failure ("function printFloat may not be defined")) else ();
  	if List.mem "printStr" (List.map (fun fd -> fd.fname) functions)
  	then raise (Failure ("function printStr may not be defined")) else ();
  	if List.mem "printBool" (List.map (fun fd -> fd.fname) functions)
  	then raise (Failure ("function printBool may not be defined")) else ();

  	(* Checking duplicate function names *)
	report_duplicate (fun n -> "duplicate function " ^ n) (List.map (fun fd -> fd.fname) functions);

	(* Add built-in print functions *)
	let built_in_decls = [{
			typ			= Void;
			fname 		= "printInt";
			formals 	= [(Int, "i")];
			locals		= [];
			body 		= [];
		};
		{
			typ			= Void;
			fname 		= "printFloat";
			formals 	= [(Float, "f")];
			locals		= [];
			body 		= [];
		};
		{
			typ			= Void;
			fname 		= "printStr";
			formals 	= [(String, "s")];
			locals		= [];
			body 		= [];
		};
		{
			typ			= Void;
			fname 		= "printBool";
			formals 	= [(Bool, "b")];
			locals		= [];
			body 		= [];
		}]
	in

	let function_decls = List.fold_left
			(fun m fd -> StringMap.add fd.fname fd m) StringMap.empty (functions @ built_in_decls)
	in

	(* Checking if s a declared function *)
	let function_decl s =
		try StringMap.find s function_decls
		with Not_found -> raise (Failure "Unrecognized function")
	in

	let _ = function_decl "main" in

	(* Several checks on a single function *)
	let check_function func =
		(* Check void/duplicate for formals and locals *)
		List.iter (check_not_void (fun n -> "illegal void formal " ^ n ^ " in " ^ func.fname)) func.formals;
    	List.iter (check_not_void (fun n -> "illegal void local " ^ n ^ " in " ^ func.fname)) func.locals;
		report_duplicate (fun n -> "duplicate formal " ^ n ^ " in " ^ func.fname) (List.map snd func.formals);
    	report_duplicate (fun n -> "duplicate local " ^ n ^ " in " ^ func.fname) (List.map snd func.locals);

		(* Check for duplicate variables *)
		ignore(report_duplicate (fun n -> "duplicate global variable " ^ n) (List.map snd globals));
		ignore(report_duplicate (fun n -> "duplicate formal variable " ^ n) (List.map snd func.formals));
		ignore(report_duplicate (fun n -> "duplicate local variable " ^ n) (List.map snd func.locals));
	in


	(* Build function symbol table *)
	let func_to_symbols func =
		List.fold_left (fun m (t, n) -> StringMap.add n t m) StringMap.empty (globals @ func.formals @ func.locals)
	in

	let rec type_of_identifier s symbols =
		try StringMap.find s symbols
		with | Not_found -> raise (Failure("Undefined ID " ^ s))

	and check_eq_type se1 se2 op = function
		(Int, Int) -> SBinop(se1, op, se2, Int)
		| (Float, Float) -> SBinop(se1, op, se2, Float)
		| (String, String) -> SBinop(se1, op, se2, String)
		| _ -> raise (Failure "Illegal type for equality operators")

	and check_log_type se1 se2 op = function
			(Bool, Bool) -> SBinop(se1, op, se2, Bool)
			| _ -> raise (Failure "Illegal type for logical operators")

	and check_arith_type se1 se2 op = function
			  (Int, Float) 
			| (Float, Int) 
			| (Float, Float) 	-> SBinop(se1, op, se2, Float)
			| (Int, Int) 		-> SBinop(se1, op, se2, Int)
			| (String, String) 	->
				(match op with
					Add -> SBinop(se1, op, se2, String)
					| _ -> raise(Failure "Invalid operation on String"))
			| (Matrix(t1, r1, c1), Matrix(t2, r2, c2)) ->
				(match op with
					Add | Sub 	->
						if t1=t2 && r1=r2 && c1=c2 then
							SBinop(se1, op, se2, Matrix(t1, r1, c2))
						else raise(Failure "Incorrect dimention/type for matrix addition/subtraction")
					| Mult 		->
						if t1=t2 && c1 = r2 then
							SBinop(se1, op, se2, Matrix(t1, r1, c2))
						else raise(Failure "Incorrect dimention/type for matrix multiplication")
					| _ -> raise(Failure("Invalid operation on matrix")))
			| (Int, Matrix(Int,r,c)) ->
				(match op with
					Mult -> SBinop(se1, op, se2, Matrix(Int, r, c))
					| _ -> raise(Failure "Invalid operation between integer and matrix"))
			| (Float, Matrix(Float,r,c)) ->
				(match op with
					Mult -> SBinop(se1, op, se2, Matrix(Float, r, c))
					| _ -> raise(Failure("Invalid operation between float and matrix")))
			| _ -> raise (Failure("Invalid type for arithmetic operators"))

	and check_is_int symbols e = match e with
		NumLit(IntLit(n)) 	-> Int
		| Id(s) 			-> type_of_identifier s symbols
		| _ 				-> raise(Failure"Integer required for matrix dimension/index")

	and lit_to_slit n = match n with
		IntLit(n)     -> SNumLit(SIntLit(n))
		| FloatLit(n) -> SNumLit(SFloatLit(n))

	and typ_of_lit n = match n with
		IntLit(n)     -> Int
		| FloatLit(n) -> Float

	and sexpr symbols = function
		  NumLit(IntLit(n))  		-> SNumLit(SIntLit(n))
		| NumLit(FloatLit(n))		-> SNumLit(SFloatLit(n))
		| BoolLit(b)       			-> SBoolLit(b)
		| StringLit(s)        		-> SStringLit(s)
		| Id(s)                		-> SId(s, type_of_identifier s symbols)
		| Binop(e1, op, e2)			-> 	let se1 = sexpr symbols e1 in
										let se2 = sexpr symbols e2 in
										let t1 = Sast.get_sexpr_type se1 in
										let t2 = Sast.get_sexpr_type se2 in
											(match op with
											Equal | Neq -> check_eq_type se1 se2 op (t1, t2)
											| And | Or -> check_log_type se1 se2 op (t1, t2)
											| Less | Leq | Greater | Geq when (t1 = Int || t1 = Float) && t1 = t2 -> SBinop(se1, op, se2, t1)
											| Add | Mult | Sub | Div -> check_arith_type se1 se2 op (t1, t2)
											| _ -> raise (Failure "Invalid binary operator"))
		| Unop(op, e)          		-> let se = sexpr symbols e in
										let t = Sast.get_sexpr_type se in
										(match op with
											Neg when t = Int -> SUnop(op, se ,t)
											| Neg when t = Float -> SUnop(op, se ,t)
											| Inc when t = Int -> SUnop(op, se ,t)
											| Inc when t = Float -> SUnop(op, se ,t)
											| Dec when t = Int -> SUnop(op, se ,t)
											| Dec when t = Float -> SUnop(op, se ,t)
											| Not when t = Bool -> SUnop(op, se, t)
											| _ -> raise(Failure "Invalid datatype for unop")
										)
		| Assign(s,e) 				-> 	let se1 = sexpr symbols s in
										let se2 = sexpr symbols e in
										let t1 = Sast.get_sexpr_type se1 in
										let t2 = Sast.get_sexpr_type se2 in
											(if t1 = t2
												then SAssign(se1, se2, t1)
											else raise(Failure "Mismatched assignment type"))
		
		| Call(fname, actuals)		-> let fd = function_decl fname in
										if List.length actuals != List.length fd.formals then
											raise (Failure "Incorrect number of arguments")
								 		else
								 			SCall(fname, List.map (sexpr symbols) actuals, fd.typ)
		| Noexpr               		-> SNoexpr
		| MatrixAccess(s, dim1, dim2)	-> 	ignore(check_is_int symbols dim1);
											ignore(check_is_int symbols dim2);
											let typ = type_of_identifier s symbols	in
												(match typ with
													Matrix(t,r,c) ->
														SMatrixAccess(s, sexpr symbols dim1, sexpr symbols dim2, t)
													| _ -> raise(Failure "Cannot operate on nonmatrix")	)
		| MatrixLit(mlist)			-> let smlist = (List.map (fun l -> (List.map lit_to_slit l)) mlist) in
										let entry = List.hd (List.hd mlist) in
										let row_size = List.length (List.hd mlist) in
											ignore(List.iter (fun nl -> if (List.length nl = row_size) then () else raise(Failure "Rows of matrix must have the same size")) mlist);
										let entry_typ = typ_of_lit entry in
											ignore(List.iter (fun nl -> List.iter (fun n ->
												(let typ = typ_of_lit n in
													if (typ = entry_typ)
														then ()
														else raise(Failure "More than one datatype in a matrix" ))) nl) mlist);
										SMatrixLit(smlist, entry_typ)
		| Rows(s)					-> (match type_of_identifier s symbols with
												Matrix(_, r, _) -> 
													(match r with IntLit(n) -> SRows(n) 
														| _ -> raise(Failure "Integer required for matrix dimension"))
												| _ -> raise(Failure"Cannot operate on nonmatrix"))
		| Cols(s)					-> (match type_of_identifier s symbols with
											Matrix(_, _, c) -> 
												(match c with IntLit(n) -> SCols(n) 
															| _ -> raise(Failure"Integer required for matrix dimension"))
											| _ -> raise(Failure"Cannot operate on nonmatrix"))
		| Transpose(s)				-> (match type_of_identifier s symbols with
											Matrix(t, r, c) -> STranspose(s, Matrix(t, c, r))
											| _ -> raise(Failure"Cannot operate on nonmatrix"))									
		| Trace(s)					-> (match type_of_identifier s symbols with 
										Matrix(t, r, c) -> (if r = c then STrace(s, Matrix(t,r,c))
																	else raise(Failure "Trace only operates on square matrices"))
											| _ -> raise(Failure"Cannot operator on nonmatrix"))
		| SubMatrix(s,e1,e2,e3,e4)  -> ignore(check_is_int symbols e1);
										ignore(check_is_int symbols e2);
										ignore(check_is_int symbols e3);
										ignore(check_is_int symbols e4);
										let se1 = sexpr symbols e1 in
										let se2 = sexpr symbols e2 in
										let se3 = sexpr symbols e3 in
										let se4 = sexpr symbols e4 in
										let typ = type_of_identifier s symbols in
											(match typ with 
											Matrix(t,r,c) -> SSubMatrix(s, se1, se2, se3, se4, Matrix(t,r,c))
											| _ -> raise(Failure"Cannot operator on nonmatrix"))
	in

	let rec sstmt symbols = function
		Block(stmt_list) 		-> SBlock(stmt_list_to_sstmt_list symbols stmt_list)
		| Expr(e) 				-> SExpr(sexpr symbols e)
		| If(e, s1, s2) 		-> SIf((sexpr symbols e), (sstmt symbols s1), (sstmt symbols s2))
		| For(e1, e2, e3, s) 	-> SFor((sexpr symbols e1), (sexpr symbols e2), (sexpr symbols e3), (sstmt symbols s))
		| While(e, s)			-> SWhile((sexpr symbols e), (sstmt symbols s))
		| Return(e)				-> SReturn(sexpr symbols e)

	and stmt_list_to_sstmt_list symbols stmt_list = List.map (sstmt symbols) stmt_list
	in

	let func_to_sfunc func =
		{
			sfname 			= func.fname;
			styp 			= func.typ;
			sformals 		= func.formals;
			slocals 		= func.locals;
			sbody 			= (stmt_list_to_sstmt_list (func_to_symbols func) func.body);
		}
	in
	
(* check functions *)
ignore(List.iter check_function functions);

(* convert func to sfunc *)
let sfuncs = List.map func_to_sfunc functions 
in	(globals, sfuncs)