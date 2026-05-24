
open Types

type Ast.Instr.t += Exit of Ast.Expr.t Ast.loc
type Ast.Instr.t += Start
type Ast.Instr.t += IRandom of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
type Ast.Instr.t += NondetPtr of Ast.Loc.t Ast.loc

type Ir.builtin += Exit_with of Dba.Expr.t
type Ir.builtin += SetRandom of Dba.Var.t * Dba.Expr.t * Dba.Expr.t
type Ir.builtin += Start_exe
type Ir.builtin += AddBasePtr of Dba.Var.t


type Ir.builtin += Check_assert of Dba.Expr.t
type Ir.builtin += Check_validity of Expr.t * int (* base address and size *)




include Cli.Make (struct
  let name = "Emulation"

  let shortname = "emul"
end)

module PermFile = Builder.String_option (struct
  let name = "perm"

  let doc = "path to the permision file"
end)

let () =
  Exec.register_plugin
    (module struct
      let name = "true-exit2"

      let grammar_extension = [
                Dyp.Add_rules [
                    (
                        (
                            "instr", 
                            [
                                Dyp.Regexp (RE_String "exit");
                                Dyp.Regexp (RE_Char '(');
                                Dyp.Non_ter ("expr", No_priority);
                                Dyp.Regexp (RE_Char ')');
                            ],
                            "default_priority",
                            [] 
                        ),
                        fun _ -> function 
                        | [ _; _; Libparser.Syntax.Expr status; _; ] -> 
                                (Libparser.Syntax.Stmt [ Exit status; ], [])
                        | _ -> assert false 
                    );

                    (
                        (
                            "instr",
                            [
                            Dyp.Regexp (RE_String "start_exe");
                            ],
                            "default_priority",
                            []
                        ),
                        fun _ -> function
                        | [ _ ] ->
                            ( Libparser.Syntax.Stmt [Start], [] )
                        | _ -> assert false
                        );
                    (
                        (
                            "instr", 
                            [
                                Dyp.Non_ter ("loc", No_priority);
                                Dyp.Regexp (RE_String ":=");
                                Dyp.Regexp (RE_String "rand");
                                Dyp.Regexp (RE_Char '(');
                                Dyp.Non_ter ("expr", No_priority);
                                Dyp.Regexp (RE_Char ',');
                                Dyp.Non_ter ("expr", No_priority);
                                Dyp.Regexp (RE_Char ')');
                            ],
                            "default_priority",
                            [] 
                        ),
                        fun _ -> function 
                            | [ Libparser.Syntax.Loc loc; _; _; _; Libparser.Syntax.Expr e1; _; Libparser.Syntax.Expr e2; _; ] -> 
                                (Libparser.Syntax.Stmt [ IRandom (loc, e1, e2); ], [])
                        | _ -> assert false 
                    );
                    (
                        (
                            "instr", 
                            [
                                Dyp.Non_ter ("loc", No_priority);
                                Dyp.Regexp (RE_String ":=");
                                Dyp.Regexp (RE_String "nondet_ptr");
                                Dyp.Non_ter ("accept_newline", No_priority);
                                Dyp.Ter "AS";
                                Dyp.Non_ter ("ident", No_priority);
                            ],
                            "default_priority",
                            [] 
                        ),
                        fun _ -> function 
                            | [ Libparser.Syntax.Loc lval; _; _; _; _; Libparser.Syntax.String name] ->
                                let var =
                                    ( Ast.Loc.var name ~size:(Ast.Size.sizeof lval),
                                        Lexing.dummy_pos )
                                in
                                (Libparser.Syntax.Stmt [ NondetPtr var; (Ast.Instr.assign lval (Ast.Expr.loc var, Lexing.dummy_pos)); ], [] )
                        | _ -> assert false 
                    );
                ];
            ]

            let instruction_printer = Some (fun ppf -> function
            | Exit (status, _) ->
                Format.fprintf ppf "exit(%a)" Ast.Expr.pp status;
                true
            | IRandom ((loc, _), (e1, _), (e2, _)) ->
                Format.fprintf ppf "%a := random(%a, %a)" Ast.Loc.pp loc Ast.Expr.pp e1 Ast.Expr.pp e2;
                true
            | _ -> false)

      let declaration_printer = None

      let extension :
          type a b.
          (module EXPLORATION_STATISTICS) ->
          (module Path.S with type t = a) ->
          (module STATE with type t = b) ->
          (module Exec.EXTENSION with type path = a and type state = b) option =
       fun stats path state ->
        if Options.is_enabled () && Options.Engine.get () = Env.Preca then
        let module S = (val state) in
        match S.Value.kind with
            | Env.Term -> (
          Some
            (module struct
              module P = (val path)

              type path = P.t

              and state = S.t

              module Stats = (val stats)
              module Eval = Eval.Make (P) (S)

              let start = ref false
              let base_pointers = Sexpr.BvTbl.create 8

              let initialization_callback =
                Some (fun _path state ->
                    start := false;
                    state
                )

              let declaration_callback = None

              let instruction_callback = Some (fun inst env ->
                match inst with
                | Exit (Int z, _) ->
                   [ Ir.Builtin (Exit_with (Dba.Expr.constant (Bitvector.create z 8))) ]
                | Exit status ->
                        [ Ir.Builtin (Exit_with (Script.eval_expr status env)) ]
                | IRandom (lval, (Int min, _), (Int max, _)) ->
                    (match Script.eval_loc lval env with
                    | Var var -> 
                        [ Ir.Builtin 
                            (SetRandom (var,
                                (Dba.Expr.constant (Bitvector.create min 8)), 
                                (Dba.Expr.constant (Bitvector.create max 8))))
                        ]
                    | _ -> failwith "Can only get a random value into a variable")
                | Start -> [ Ir.Builtin (Start_exe) ]
                | NondetPtr lval -> (
                    match Script.eval_loc lval env with
                    | Var var -> [ Symbolize var; Builtin (AddBasePtr var) ]
                    | _ -> failwith "Nondet_ptr only implemented for vars"
                )
                | _ -> [])


              let exit_with status _addr path _depth state =
                                    Options.Logger.info "@[<v 2>Exploration@,%a@]" Stats.pp ();
                                    let code = (Bitvector.to_uint (Bitvector.extract (Eval.get_value status state path) { hi=7; lo=0 })) in
                                    if code == 0 then Format.printf "Exited with code: %d@." code
                                    else Format.printf "[EMUL ERROR] Exited with code: %d@." code;
                                    Options.Logger.result "Formula \n%a" (S.pp_smt None) state;
                                    exit 0
                                    
                let check_assert cond addr path depth state=
                if !start then
                                    let value, state = Eval.safe_eval cond state path in
                                    (* evaluate current state with condition *)
                                    let res = S.test value state in
                                    match res with
                                    | True state -> Ok state
                                    | False state -> exit_with (Dba.Expr.constant (Bitvector.fill 8)) addr path depth state
                                    |Both _ -> assert false
                else
                    Ok state

                let genrandom (var, e1, e2) _addr path _depth state =
                    let imin = (Bitvector.to_uint (Bitvector.extract (Eval.get_value e1 state path) { hi=7; lo=0 })) in
                    let imax = (Bitvector.to_uint (Bitvector.extract (Eval.get_value e2 state path) { hi=7; lo=0 })) in
                    let irand = (imin + Random.int (imax - imin)) in
                    let rand = S.Value.constant (Bitvector.of_int ~size:64 irand) in
                    Ok (S.assign var rand state)

                
                let rec read state ~addr len (dir : Sexpr.Expr.endianness) (memory : Sexpr.Memory.t) =
                    (* Code adapted from sse/term/memory_manager.ml *)
                    match memory with
                    | Root | Symbol _ -> 
                        Sexpr.Expr.load len dir addr memory
                    | Layer { addr = addr'; store; over; _ } -> (
                        let offset = Sexpr.Expr.sub addr addr' in
                        let offsetvalue = S.get_a_value offset state in
                        let miss i s =
                            Sexpr.Chunk.of_term
                                (read state ~addr:(Sexpr.Expr.addz addr' i) s LittleEndian over)
                            in
                            let bytes = Sexpr.Chunk.to_term (Sexpr.Store.select miss offsetvalue len store) in
                            match dir with LittleEndian -> bytes | BigEndian -> Sexpr.bswap bytes
                        )
                
                let rec parse_expr tbl (e : S.Value.t) state = match e with
                    | Var _  when Sexpr.BvTbl.mem base_pointers e -> Sexpr.BvTbl.replace tbl e ()
                    | Var _ -> ()
                    | Cst _ -> ()
                    | Unary { x; _ } -> parse_expr tbl x state
                    | Binary { x; y; _ } -> parse_expr tbl x state; parse_expr tbl y state
                    | Ite {c; t; e; _;} -> (
                        match S.test c state with
                        | True _ -> parse_expr tbl t state
                        | False _ -> parse_expr tbl e state
                        | Both _ -> 
                            (* In the plugins, symbolic values can only have one value, 
                               so conditions are either True or False *)
                            assert false
                    )
                    | Load {label=(Root|Symbol _); _; } -> ()
                    | Load {addr; label; len; dir; _ } -> 
                        (* Works only because the plugin enforce only one value for 
                           each read/write i.e., emulate concrete execution *)
                        parse_expr tbl (read state ~addr len dir label) state

                let get_base (sexpr : S.Value.t) state : S.Value.t option = 
                    let found_bases = Sexpr.BvTbl.create 8 in
                    parse_expr found_bases sexpr state;
                    assert ((Sexpr.BvTbl.length found_bases) <= 1);
                    Sexpr.BvTbl.fold (fun e _ _ -> Some e) found_bases None (* returns None if found_bases  *)
                   

                (* evaluate if the address is = or != than 0 and add it to pp*)                
                let check_validity (accessed_addr, _size) _addr path _depth state=
                if !start then
                    (* evaluate current state with condition : address is = or diff than 0 and add it to state *)
                    let zero = S.Value.constant (Bitvector.zeros (Expr.size_of accessed_addr)) in
                    let sexpr_addr, state = Eval.safe_eval accessed_addr state path in
                    let base_addr_opt = get_base sexpr_addr state in
                    let condition = match base_addr_opt with
                    | Some base_addr -> S.Value.binary Eq base_addr zero
                    | None -> S.Value.binary Eq sexpr_addr zero
                    in
                    let res = S.test condition state in
                    match res with
                    | False state -> Ok state
                    | True state ->  exit_with (Dba.Expr.constant (Bitvector.fill 8)) _addr path _depth state
                    |Both _ -> assert false
                else
                    Ok state
                
                let start_exe _addr _path _depth state =
                    start := true;
                    Env.check_perm := true;
                    Ok state


                let add_base_ptr (var : Var.t) _addr _path _depth state = 
                    let svar = S.lookup var state in
                    Sexpr.BvTbl.add base_pointers svar ();
                    Ok state

                    let process_handler : type a. (module Ir.GRAPH with type t = a) -> a -> unit =
                        fun graph ->
                            let module G = (val graph) in
                            fun graph ->
                            G.iter_new_vertex
                                (fun vertex ->
                                match G.node graph vertex with
                                | Fallthrough { kind = Assert cond; _ } ->
                                    ignore (G.insert_before graph vertex (Builtin (Check_assert cond)))
                                | Fallthrough { kind = Load {var = { size; _ } ; base = None ; dir=_ ; addr }; _ } ->
                                    ignore (G.insert_before graph vertex (Builtin (Check_validity (addr, size / 8))))
                                | Fallthrough { kind = Store {base = None ; dir=_ ; addr ; rval}; _ } ->
                                    ignore (G.insert_before graph vertex (Builtin (Check_validity (addr, Dba.Expr.size_of rval / 8))))
                                | _ -> ())
                                graph

              let process_callback = Some process_handler

              let builtin_callback = Some (function
                                | Exit_with status -> Some (exit_with status)
                                | SetRandom (loc, e1, e2) -> Some (genrandom (loc, e1, e2))
                                | Check_assert cond -> Some (check_assert cond)
                                | Check_validity (addr, size) -> Some(check_validity (addr, size))
                                | Start_exe -> Some start_exe
                                | AddBasePtr var -> Some (add_base_ptr var)
                                | _ -> None)
              let builtin_printer = None

              let at_exit_callback = None
            end))
        | _ -> failwith "Wrong Value Type"
        else None
    end : Exec.PLUGIN)
    
    (*type Options.Engine.t += Exepath*)

