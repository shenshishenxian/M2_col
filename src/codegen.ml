(*
    Jeffrey Monahan     - jm4155
    Christine Pape      - cmp2223
    Montana St. Pierre  - mrs2296
    Shelley Zhong       - sz2699
    Tengyu Zhou         - tz2338
*)

open Llvm
open Ast
open Sast
module L = Llvm
module A = Ast
module S = Sast

module StringMap = Map.Make(String)

let translate (globals, functions) =

    let context = L.global_context() in
    let the_module = L.create_module context "M2"
    and i32_t     = L.i32_type context
    and i8_t      = L.i8_type context
    and i1_t      = L.i1_type context
    and void_t    = L.void_type context
    and float_t   = L.double_type context
    and array_t   = L.array_type
    and pointer_t = L.pointer_type
    in

    let ltype_of_typ = function
          A.Int     -> i32_t
        | A.Float   -> float_t
        | A.Bool    -> i1_t
        | A.Void    -> void_t
        | A.String  -> pointer_t i8_t
        | A.Matrix(t, r, c) ->
            let rows = match r with IntLit(s) -> s 
                                    | _ -> raise(Failure"Integer required for matrix dimension") in
            let cols = match c with IntLit(s) -> s 
                                    | _ -> raise(Failure"Integer required for matrix dimension") in
            (match t with
                A.Int      -> array_t (array_t i32_t cols) rows
                | A.Float  -> array_t (array_t float_t cols) rows
                | _ -> raise(Failure"Invalid datatype for matrix"))
    in

    let global_vars =
        let global_var m (t,n) =
        let init = L.const_int (ltype_of_typ t) 0
        in  StringMap.add n (L.define_global n init the_module) m in
        List.fold_left global_var StringMap.empty globals in

    let printf_t = L.var_arg_function_type i32_t [| L.pointer_type i8_t |] 
    in

    let printf_func = L.declare_function "printf" printf_t the_module 
    in

    let function_decls =
        let function_decl m fdecl =
            let name = fdecl.S.sfname
            and formal_types = Array.of_list
                (List.map (function A.(t,s) -> ltype_of_typ t) fdecl.S.sformals) in
            let ftype =
                L.function_type (ltype_of_typ fdecl.S.styp) formal_types in
                StringMap.add name (L.define_function name ftype the_module, fdecl) m in
        List.fold_left function_decl StringMap.empty functions
    in

    let build_function_body fdecl =
        let (the_function, _) = StringMap.find fdecl.S.sfname function_decls in
        let builder = L.builder_at_end context (L.entry_block the_function) in

        let int_format_str = L.build_global_stringptr "%d\t" "fmt" builder
        and float_format_str = L.build_global_stringptr "%f\t" "fmt" builder
        and string_format_str = L.build_global_stringptr "%s\n" "fmt" builder
        in

        let local_vars =
            let add_formal m (t, n) p = L.set_value_name n p;
            let local = L.build_alloca (ltype_of_typ t) n builder in
            ignore (L.build_store p local builder);
            StringMap.add n local m
        in

        let add_local m (t, n) =
            let local_var = L.build_alloca (ltype_of_typ t) n builder
            in StringMap.add n local_var m
        in

        let formals = List.fold_left2 add_formal StringMap.empty
            (List.map (function A.(t,n) -> (t,n)) fdecl.S.sformals) (Array.to_list (L.params the_function)) in
            List.fold_left add_local formals (List.map (function A.(t,n) -> (t,n)) fdecl.S.slocals)
        in

        let lookup n = try StringMap.find n local_vars
            with Not_found -> StringMap.find n global_vars
        in

        let build_matrix_access s rowIndex colIndex builder assigned =
            let ptr = L.build_gep (lookup s) [|L.const_int i32_t 0; rowIndex; colIndex|] s builder in
            if assigned then ptr else L.build_load ptr s builder
        in

        let rec expr builder = function
            S.SNumLit(SIntLit(i))      -> L.const_int i32_t i
            | S.SNumLit(SFloatLit(f))  -> L.const_float float_t f
            | S.SBoolLit b             -> L.const_int i1_t (if b then 1 else 0)
            | S.SStringLit s           -> L.build_global_stringptr s "tmp" builder
            | S.SId (s, d)             -> L.build_load (lookup s) s builder
            | S.SBinop (se1, op, se2, d)  ->
                let type1 = Sast.get_sexpr_type se1 in
                let type2 = Sast.get_sexpr_type se2 in
                let se1' = expr builder se1
                and se2' = expr builder se2 in

                let int_binop op se1' se2' =
                    (match op with
                        A.Add     -> L.build_add 
                        | A.Sub     -> L.build_sub 
                        | A.Mult    -> L.build_mul 
                        | A.Div     -> L.build_sdiv
                        | A.Equal   -> L.build_icmp L.Icmp.Eq 
                        | A.Neq     -> L.build_icmp L.Icmp.Ne 
                        | A.Less    -> L.build_icmp L.Icmp.Slt 
                        | A.Leq     -> L.build_icmp L.Icmp.Sle 
                        | A.Greater -> L.build_icmp L.Icmp.Sgt 
                        | A.Geq     -> L.build_icmp L.Icmp.Sge 
                        | A.And     -> L.build_and 
                        | A.Or      -> L.build_or
                        | _         -> raise(Failure "Invalid binary operator for int")) se1' se2' "tmp" builder
                in

                let float_binop op se1' se2' =
                    (match op with
                        A.Add       -> L.build_fadd 
                        | A.Sub       -> L.build_fsub
                        | A.Mult      -> L.build_fmul
                        | A.Div       -> L.build_fdiv
                        | A.Equal     -> L.build_fcmp L.Fcmp.Oeq
                        | A.Neq       -> L.build_fcmp L.Fcmp.One 
                        | A.Less      -> L.build_fcmp L.Fcmp.Olt 
                        | A.Leq       -> L.build_fcmp L.Fcmp.Ole 
                        | A.Greater   -> L.build_fcmp L.Fcmp.Ogt
                        | A.Geq       -> L.build_fcmp L.Fcmp.Oge
                        | _           -> raise(Failure"Invalid binary operator for float")) se1' se2' "tmp" builder
                in

                let bool_binop op se1' se2' =
                    (match op with
                        | A.And   -> L.build_and
                        | A.Or    -> L.build_or 
                        | _       -> raise(Failure"Invalid boolean operator")) se1' se2' "tmp" builder
                in

                let matrix_binop mtype rDimension cDimension op se1 se2 =
                    let lhs_str = (match se1 with SId(s,_) -> s | _ -> "") in
                    let rhs_str = (match se2 with SId(s,_) -> s | _ -> "") in
                    let operator_type = match mtype with
                     "int" -> i32_t | "float" -> float_t | _ -> i32_t
                    in
                    let operator_type2 = match mtype with
                     "int" -> L.const_int | "float" -> L.const_int | _ -> L.const_int
                    in
                    let buildtype = match mtype with
                     "int" -> (match op with A.Add -> L.build_add | A.Sub -> L.build_sub | A.Mult -> L.build_mul |  _ -> raise(Failure "Invalid Matrix Binop"))
                    | "float" -> (match op with A.Add -> L.build_fadd | A.Sub -> L.build_fsub | A.Mult -> L.build_fmul | _ -> raise(Failure "Invalid Matrix Binop"))
                    | _ -> L.build_add
                    in
                    let buildtype2 = match mtype with
                     "int" -> L.build_add | "float" -> L.build_fadd | _ -> L.build_add
                    in
                            (match op with
                                A.Add  | A.Sub    ->
                                    let tmp_mat = L.build_alloca (array_t (array_t operator_type cDimension) rDimension) "tmpmat" builder in
                                    for i=0 to (rDimension-1) do
                                        for j=0 to (cDimension-1) do
                                            let m1 = build_matrix_access lhs_str (L.const_int i32_t i) (L.const_int i32_t j) builder false in
                                            let m2 = build_matrix_access rhs_str (L.const_int i32_t i) (L.const_int i32_t j) builder false in
                                            let result = buildtype m1 m2 "tmp" builder in
                                            let ld = L.build_gep tmp_mat [| L.const_int i32_t 0; L.const_int i32_t i; L.const_int i32_t j |] "tmpmat" builder in
                                            ignore(build_store result ld builder);
                                        done
                                    done;
                                    L.build_load (L.build_gep tmp_mat [| L.const_int i32_t 0 |] "tmpmat" builder) "tmpmat" builder
                                | A.Mult    ->
                                    let first_typ = Sast.get_sexpr_type se1 in
                                    let tmp_mat = L.build_alloca (array_t (array_t operator_type cDimension) rDimension) "tmpmat" builder in
                                    (match first_typ with
                                        Int| Float ->
                                            for i=0 to (rDimension-1) do
                                                for j=0 to (cDimension-1) do
                                                    let m2 = build_matrix_access rhs_str (L.const_int i32_t i) (L.const_int i32_t j) builder false in
                                                    let result = buildtype (build_load (lookup lhs_str) "tmp" builder) m2 "tmp" builder in
                                                    let ld = L.build_gep tmp_mat [| L.const_int i32_t 0; L.const_int i32_t i; L.const_int i32_t j |] "tmpmat" builder in
                                                    ignore(build_store result ld builder);
                                                done
                                            done;
                                            L.build_load (L.build_gep tmp_mat [| L.const_int i32_t 0 |] "tmpmat" builder) "tmpmat" builder
                                        
                                        | Matrix(Int,r,c) ->
                                            let tmp_product = L.build_alloca operator_type "tmpproduct" builder in
                                            let c_i = (match c with IntLit(n) -> n | _ -> -1) in
                                            ignore(L.build_store (operator_type2 operator_type 0) tmp_product builder);
                                            for i=0 to (rDimension-1) do
                                                for j=0 to (cDimension-1) do
                                                    ignore(L.build_store (operator_type2 operator_type 0) tmp_product builder);
                                                    for k=0 to (c_i-1) do
                                                        let m1 = build_matrix_access lhs_str (L.const_int i32_t i) (L.const_int i32_t k) builder false in
                                                        let m2 = build_matrix_access rhs_str (L.const_int i32_t k) (L.const_int i32_t j) builder false in
                                                        let result = buildtype m1 m2 "tmp" builder in
                                                        ignore(L.build_store (buildtype2 result (L.build_load tmp_product "addtmp" builder) "tmp" builder) tmp_product builder);
                                                    done;
                                                    let ld = L.build_gep tmp_mat [| L.const_int i32_t 0; L.const_int i32_t i; L.const_int i32_t j |] "tmpmat" builder in
                                                    ignore(build_store (L.build_load tmp_product "restmp" builder) ld builder);
                                                done
                                            done;
                                            L.build_load (L.build_gep tmp_mat [| L.const_int i32_t 0 |] "tmpmat" builder) "tmpmat" builder
                                        | Matrix(Float,r,c) ->
                                            let tmp_product = L.build_alloca float_t "tmpproduct" builder in
                                                let c_i = (match c with IntLit(n) -> n | _ -> -1) in
                                                ignore(L.build_store (L.const_float float_t 0.0) tmp_product builder);
                                                for i=0 to (rDimension-1) do
                                                    for j=0 to (cDimension-1) do
                                                        ignore(L.build_store (L.const_float float_t 0.0) tmp_product builder);
                                                        for k=0 to (c_i-1) do
                                                            let m1 = build_matrix_access lhs_str (L.const_int i32_t i) (L.const_int i32_t k) builder false in
                                                            let m2 = build_matrix_access rhs_str (L.const_int i32_t k) (L.const_int i32_t j) builder false in
                                                            let result = L.build_fmul m1 m2 "tmp" builder in
                                                            ignore(L.build_store (L.build_fadd result (L.build_load tmp_product "addtmp" builder) "tmp" builder) tmp_product builder);
                                                        done;
                                                        let ld = L.build_gep tmp_mat [| L.const_int i32_t 0; L.const_int i32_t i; L.const_int i32_t j |] "tmpmat" builder in
                                                        ignore(build_store (L.build_load tmp_product "restmp" builder) ld builder);
                                                    done
                                                done;
                                                L.build_load (L.build_gep tmp_mat [| L.const_int i32_t 0 |] "tmpmat" builder) "tmpmat" builder
                                        | _ -> L.const_int i32_t 0)

                                | _         -> raise(Failure "Invalid Matrix Binop"))
                in

                let build_binop operand1 operand2 type1 type2 =
                    match (type1, type2) with
                        (Int, Int)          ->  int_binop op operand1 operand2
                        | (Float, Float)    ->  float_binop op operand1 operand2
                        | (Bool, Bool)      ->  bool_binop op operand1 operand2
                        | (Int, Matrix(Int,r1,c2)) -> let rDimension = (match r1 with IntLit(n) -> n | _ -> -1)
                                and cDimension = (match c2 with IntLit(n) -> n | _ -> -1) in
                                    matrix_binop "int" rDimension cDimension op se1 se2  
                        | (Float, Matrix(Float,r1,c2)) ->
                            let rDimension = (match r1 with IntLit(n) -> n | _ -> -1)
                                and cDimension = (match c2 with IntLit(n) -> n | _ -> -1) in
                                    matrix_binop "float" rDimension cDimension op se1 se2  
                        | (Matrix(Int,r1,c1), Matrix(Int,r2,c2)) ->
                            let rDimension = (match r1 with IntLit(n) -> n | _ -> -1)
                                and cDimension = (match c2 with IntLit(n) -> n | _ -> -1) in
                                    matrix_binop "int" rDimension cDimension op se1 se2  
                        | (Matrix(Float,r1,c1), Matrix(Float,r2,c2)) ->
                            let rDimension = (match r1 with IntLit(n) -> n | _ -> -1)
                                and cDimension = (match c2 with IntLit(n) -> n | _ -> -1) in
                                    matrix_binop "float" rDimension cDimension op se1 se2  
                        | _                                 -> raise(Failure"Cannot build binop")
                in
                build_binop se1' se2' type1 type2

            | S.SUnop(op, e, t)         ->
                let e' = expr builder e in 
                (match t with
                Int -> (match op with
                        A.Neg     -> L.build_neg e' "tmp" builder
                        | A.Inc   -> L.build_store (L.build_add e' (L.const_int i32_t 1) "tmp" builder) (lookup (match e with S.SId(s, d) -> s | _->raise(Failure"IncMustBeCalledOnID"))) builder
                        | A.Dec   -> L.build_store (L.build_sub e' (L.const_int i32_t 1) "tmp" builder) (lookup (match e with S.SId(s, d) -> s | _->raise(Failure"DecMustBeCalledOnID"))) builder
                        | _       -> raise(Failure"IllegalIntUnop"))
                | Float -> (match op with
                        A.Neg   -> L.build_fneg e' "tmp" builder
                        | _     -> raise(Failure"IllegalFloatUnop"))
                | Bool -> (match op with
                        A.Not   -> L.build_not e' "tmp" builder
                        | _       -> raise(Failure"IllegalBoolUnop"))
                | _ -> (raise(Failure"InvalidUnopType")))
            | S.SAssign (se1, se2, d)  ->
                let se1' =
                    (match se1 with
                        S.SId(s,_) -> (lookup s)
                        | S.SMatrixAccess(s, i1, j1, d) ->
                            let i = expr builder i1 and j = expr builder j1 in
                                build_matrix_access s i j builder true
                        | _ -> raise(Failure"AssignLHSMustBeAssignable"))
                and se2' = expr builder se2 in
                ignore (L.build_store se2' se1' builder); se2'    
            | S.SCall ("printStr", [e], _) ->
                L.build_call printf_func [| string_format_str ; (expr builder e) |] "printf" builder
            | S.SCall ("printInt", [e], _) ->
                L.build_call printf_func [| int_format_str ; (expr builder e) |] "printf" builder
            | S.SCall ("printBool", [e], _) ->
                L.build_call printf_func [| int_format_str ; (expr builder e) |] "printf" builder    
            | S.SCall ("printFloat", [e], _) ->
                L.build_call printf_func [| float_format_str ; (expr builder e) |] "printf" builder
            | S.SCall (f, act, _) ->
                let (fdef, fdecl) = StringMap.find f function_decls in
                let actuals = List.rev (List.map (expr builder) (List.rev act)) in
                let result =
                    (match fdecl.S.styp with
                        A.Void -> ""
                        | _ -> f ^ "_result") in
                L.build_call fdef (Array.of_list actuals) result builder
            | S.SNoexpr                -> L.const_int i32_t 0
            | S.SMatrixAccess (s, se1, se2, _) ->
                let i = expr builder se1 and j = expr builder se2 in
                    (build_matrix_access s i j builder false)
            | S.SMatrixLit (smlist, t) -> let numtype = match t with A.Float -> float_t
                                                                | A.Int -> i32_t
                                                                | _ -> i32_t
                                         in
                                            let flipped     = List.map List.rev smlist in
                                            let lists       = List.map (List.map (expr builder)) flipped in
                                            let listArray   = List.map Array.of_list lists in
                                            let listArray2  = List.rev (List.map (L.const_array numtype) listArray) in
                                            let arrayArray  = Array.of_list listArray2 in
                                            L.const_array (array_t numtype (List.length (List.hd smlist))) arrayArray
            | S.SRows(r)                -> L.const_int i32_t r
            | S.SCols(c)                -> L.const_int i32_t c
            | S.STranspose(s,t)         -> 
                let alloctype = match t with
                    Matrix(Int, c, r) -> i32_t | Matrix(Float, c, r) -> float_t| _ -> i32_t in
                (match t with
                    Matrix(Int, c, r) | Matrix(Float, c, r) ->
                        let r_tr = (match c with IntLit(n) -> n | _ -> -1) in
                        let c_tr = (match r with IntLit(n) -> n | _ -> -1) in
                        let tmp_tr = L.build_alloca (array_t (array_t alloctype c_tr) r_tr) "tmpmat" builder in
                        for i=0 to (r_tr-1) do
                            for j=0 to (c_tr-1) do
                                let mtr = build_matrix_access s (L.const_int i32_t i) (L.const_int i32_t j) builder false in
                                let ld = L.build_gep tmp_tr [| L.const_int i32_t 0; L.const_int i32_t j; L.const_int i32_t i |] "tmpmat" builder in
                                ignore(build_store mtr ld builder);
                            done
                        done;
                        L.build_load (L.build_gep tmp_tr [| L.const_int i32_t 0 |] "tmpmat" builder) "tmpmat" builder
                    | _ -> const_int i32_t 0)
            | S.SSubMatrix(s, r1, r2, c1, c2, t) ->
                (let alloctype = match t with
                    Matrix(Int, c, r) -> i32_t | Matrix(Float, c, r) -> float_t| _ -> i32_t in
                    match t with Matrix(Int, c, r)| Matrix(Float, c, r) ->
                        let r1' = (match r1 with SNumLit(SIntLit(n)) -> n | _ -> -1) in
                        let r2' = (match r2 with SNumLit(SIntLit(n)) -> n | _ -> -1) in
                        let c1' = (match c1 with SNumLit(SIntLit(n)) -> n | _ -> -1) in
                        let c2' = (match c2 with SNumLit(SIntLit(n)) -> n | _ -> -1) in
                        let tmp_tr = L.build_alloca (array_t (array_t alloctype (c2' - c1' + 1)) (r2' - r1' + 1)) "tmptr" builder in
                        for i=r1' to (r2') do
                            for j=c1' to (c2') do
                                let mtr = build_matrix_access s (L.const_int i32_t i) (L.const_int i32_t j) builder false in
                                let ld = L.build_gep tmp_tr [| L.const_int i32_t 0; L.const_int i32_t (i - r1'); L.const_int i32_t (j - c1') |] "tmpmat" builder in
                                ignore(build_store mtr ld builder);
                            done
                        done;
                        L.build_load (L.build_gep tmp_tr [| L.const_int i32_t 0 |] "tmptr" builder) "tmptr" builder
                    | _ -> const_int i32_t 0)
            | S.STrace(s, t) -> 
                (let alloctype = match t with
                    Matrix(Int, c, r) -> i32_t 
                    | Matrix(Float, c, r) -> float_t
                    | _ -> i32_t 
                in
                let buildtype = match t with
                    Matrix(Int, c, r) -> L.build_add 
                    | Matrix(Float, c, r) -> L.build_fadd
                    | _ -> L.build_add 
                in
                let initial_val = match t with 
                    Matrix(Int, c, r) -> L.const_int i32_t 0
                    | Matrix(Float, c, r) -> L.const_float float_t 0.0
                    | _ -> L.const_int i32_t 0
                in
                match t with
                    Matrix(Int, c, r)
                    | Matrix(Float, c, r) ->
                        let c_tr = (match c with IntLit(n) -> n | _ -> -1) in
                        let tmp_sum = L.build_alloca alloctype "tmpsum" builder in
                        ignore(L.build_store initial_val tmp_sum builder);
                        for i=0 to (c_tr-1) do
                                let result = build_matrix_access s (L.const_int i32_t i) (L.const_int i32_t i) builder false in
                                ignore(L.build_store (buildtype result (L.build_load tmp_sum "addtmp" builder) "tmp" builder) tmp_sum builder);
                        done;
                        L.build_load tmp_sum "restmp" builder
                    | _ -> raise(Failure "Cannot calculate trace!"))
    
        in

  
        let add_terminal builder f =
            match L.block_terminator (L.insertion_block builder) with
                Some _ -> ()
                | None -> ignore (f builder)
        in

        let rec stmt builder = function
            S.SBlock sl -> List.fold_left stmt builder sl
            | S.SExpr e -> ignore (expr builder e); builder
            | S.SReturn e ->
                ignore(match fdecl.S.styp with
                    A.Void  -> L.build_ret_void builder
                    | _                 -> L.build_ret (expr builder e) builder); builder
            | S.SIf (predicate, then_stmt, else_stmt) ->
                let bool_val = expr builder predicate in
                let merge_bb = L.append_block context
                    "merge" the_function in
                let then_bb = L.append_block context
                    "then" the_function in
                add_terminal
                    (stmt (L.builder_at_end context then_bb) then_stmt)
                    (L.build_br merge_bb);
                let else_bb = L.append_block context
                    "else" the_function in
                add_terminal
                    (stmt (L.builder_at_end context else_bb) else_stmt)
                    (L.build_br merge_bb);
                ignore (L.build_cond_br bool_val then_bb else_bb builder);
                L.builder_at_end context merge_bb
            | S.SWhile (predicate, body) ->
                let pred_bb = L.append_block context
                    "while" the_function in
                ignore (L.build_br pred_bb builder);
                let body_bb = L.append_block context
                    "while_body" the_function in
                add_terminal (stmt (L.builder_at_end context body_bb) body)
                (L.build_br pred_bb);
                let pred_builder = L.builder_at_end context pred_bb in
                let bool_val = expr pred_builder predicate in
                let merge_bb = L.append_block context
                    "merge" the_function in
                ignore (L.build_cond_br bool_val body_bb merge_bb pred_builder);
                L.builder_at_end context merge_bb
            | S.SFor (op1, op2, e3, body) -> stmt builder
                (S.SBlock [S.SExpr op1 ;
                    S.SWhile (op2, S.SBlock [body ;
                        S.SExpr e3]) ])
        in

        let builder = stmt builder (S.SBlock fdecl.S.sbody) in

        add_terminal builder (match fdecl.S.styp with
            A.Void -> L.build_ret_void;
            | t -> L.build_ret (L.const_int (ltype_of_typ t) 0))
    in

    List.iter build_function_body functions;
    the_module
