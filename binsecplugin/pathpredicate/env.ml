(**************************************************************************)
(*  This file is part of BINSEC.                                          *)
(*                                                                        *)
(*  Copyright (C) 2016-2024                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)

open Options
open Types

exception Undef = Types.Undef
exception Uninterp = Types.Uninterp
exception Unknown = Types.Unknown
exception Non_unique = Types.Non_unique
exception Non_mergeable = Types.Non_mergeable


(*-----------G-----------*)
module Bv = Term.Bv
let check_perm = ref false
(*-----------G-----------*)


type 'a test = 'a Types.test =
  | True of 'a
  | False of 'a
  | Both of { t : 'a; f : 'a }

(* utils *)

module BiMap = Basic_types.BigInt.Map
module NiTbl = Basic_types.Int.Htbl
open Sexpr
module BiItM = Imap
module S = Basic_types.String.Map
module I = Basic_types.Int.Map
module R = Basic_types.Int.Htbl
module K = Basic_types.Int.Set

type _ Types.value += Term : Sexpr.Expr.t Types.value

(*-----------G-----------*)
(*Etendre Type pour prendre en compte un bitvector (la valeur de la var)*)
type _ Types.value += Concrete : Bitvector.t Types.value

(*-----------G-----------*)
module State
    (QS : Types.QUERY_STATISTICS) =
struct
  module Uid = struct
    type t = Suid.t

    let zero = Suid.incr Suid.zero

    let succ = Suid.incr
    let compare = Suid.compare
  end
  let addr_space = Kernel_options.Machine.word_size ()

  let timeout =
    match Formula_options.Solver.Timeout.get () with
    | 0 -> None
    | n -> Some (float_of_int n)

  type t = {
    constraints : Expr.t list;
    (* reversed sequence of assertions *)
    mutable deps : BvSet.t BvMap.t;
    mutable anchors : K.t;
    vsymbols : Expr.t I.t;
    (* collection of visible symbols *)
    varrays : Memory.t S.t;
    (* collection of visible arrays *)
    vmemory : Memory.t;
    (* visible memory *)
    model : Model.t; (* a model that satisfy constraints *)
  }


  (*crée un dummy contexte pour le MMU*)
  module C : Ai.CONTEXT with type t = t and type v := Domains.Interval.t = struct
    type nonrec t = t
     let add_dependency _ ~parent:_ _ = ()
    let find_dependency _ _ = BvSet.empty
    let add _ _ _ = ()
    let find _ e = Domains.Interval.top (Expr.sizeof e)
    let _anchor _ _ = ()
    let _anchored _ _ = false
  end
  (*changed to use the dummy ver*)
  module Overapprox : Memory_manager.CONTEXT with type t = t and type v := Domains.Interval.t =
  struct
    include Ai.Make (Domains.Interval) (C)

    let anchor t (m : Memory.t) =
      match m with
      | Root | Symbol _ -> ()
      | Layer { id; _ } -> t.anchors <- K.add id t.anchors

    let anchored t (m : Memory.t) =
      match m with
      | Root | Symbol _ -> true
      | Layer { id; _ } -> K.mem id t.anchors
  end

  module MMU = Memory_manager.Make (Domains.Interval) (Overapprox)


  let pp ppf state = Model.pp ppf state.model

  let empty () =
    {
      constraints = [];
      deps = BvMap.empty;
      anchors = K.empty;
      vsymbols = I.empty;
      varrays = S.empty;
      vmemory = Memory.root;
      model = Model.empty addr_space;
    }

    let pp_smt (target : Expr.t Types.target) ppf t =
      let module P = Smt2_solver.Printer in
      let ctx = P.create ~next_id:Uid.zero () in
      (* visit assertions *)
      List.iter (P.visit_bl ctx) t.constraints;
      (* visit terms *)
      let defs =
        match target with
        | Some defs ->
            List.iter (fun (e, _) -> P.visit_bv ctx e) defs;
            defs
        | None ->
            P.visit_ax ctx t.vmemory;
            List.rev
              (I.fold
                 (fun id expr defs ->
                    match Dba.Var.from_id id with
                    | exception Not_found -> defs
                    |{ name; info = Temp; id; _ } ->
                        P.visit_bv ctx expr;
                              (expr, Format.sprintf "%s_%d" name id) :: defs
                    | { name; _ } ->
                        P.visit_bv ctx expr;
                              (expr, name) :: defs)
                 t.vsymbols [])
      in
      Format.pp_open_vbox ppf 0;
      (* print definitions *)
      P.pp_print_defs ppf ctx;
      List.iter
        (fun (bv, name) ->
          Format.fprintf ppf "@[<h>(define-fun %s () (_ BitVec %d)@ " name
            (Expr.sizeof bv);
          P.pp_print_bv ctx ppf bv;
          Format.fprintf ppf ")@]@ ")
        defs;
      if target = None then
        Format.fprintf ppf
          "@[<h>(define-fun memory () (Array (_ BitVec %d) (_ BitVec 8))@ %a)@]"
          (Kernel_options.Machine.word_size ())
          (P.pp_print_ax ctx) t.vmemory;
      (* print assertions *)
      List.iter
        (fun bl ->
          Format.pp_open_hbox ppf ();
          Format.pp_print_string ppf "(assert ";
          P.pp_print_bl ctx ppf bl;
          Format.pp_print_char ppf ')';
          Format.pp_close_box ppf ();
          Format.pp_print_space ppf ())
        t.constraints;
      Format.pp_close_box ppf ()
      
  let alloc ~array state =
    let symbol = Memory.fresh array in
    { state with varrays = S.add array symbol state.varrays }

  let assign ({ id; _ } : Types.Var.t) value state =
    { state with vsymbols = I.add id value state.vsymbols }

  let write ~addr value dir state =
    if !check_perm && (Bv.is_zeros (Model.eval state.model addr)) then begin 
      Printf.printf "[EMUL ERROR] Invalid memory write\n"; 
      Options.Logger.result "Formula \n%a" (pp_smt None) state;
      exit 0;
    end
    else
    let vmemory = MMU.write state ~addr value dir state.vmemory in
    { state with vmemory }

  let store name ~addr value dir state =
    try
      let ar = S.find name state.varrays in
      let varrays =
        S.add name (MMU.write state ~addr value dir ar) state.varrays
      in
      { state with varrays }
    with Not_found -> raise_notrace (Uninterp name)

  let lookup ({ id; _ } as var : Types.Var.t) t =
    try I.find id t.vsymbols with Not_found -> raise_notrace (Undef var)


  let read ~addr bytes dir state =
    if !check_perm && (Bv.is_zeros (Model.eval state.model addr)) then begin 
      Printf.printf "[EMUL ERROR] Invalid memory read\n";
      Options.Logger.result "Formula \n%a" (pp_smt None) state;
      exit 0; end
    else
    let bytes = MMU.read state ~addr bytes dir state.vmemory in
    (bytes, state) 
    
  let select name ~addr bytes dir state =
    try
      let array = S.find name state.varrays in
      let bytes = MMU.read state ~addr bytes dir array in
      (bytes, state)
    with Not_found -> raise_notrace (Uninterp name)

  let memcpy ~addr len orig state =
    
    let vmemory =
      MMU.source state ~addr:(Expr.constant addr) ~len orig state.vmemory
    in
    { state with  vmemory }

    
  let assume (cond : Expr.t) state =
    if Expr.is_equal cond Expr.one then (
      QS.Preprocess.incr_true ();
      Some state)
    else if Expr.is_equal cond Expr.zero then (
      QS.Preprocess.incr_false ();
      None)
    else match cond with
      | Binary { f = Eq; x = Var _ as var; y = Cst bv; _} -> 
        let _, sigma, _, _, _ = state.model in
        (match BvTbl.find sigma var with
        | exception Not_found -> BvTbl.add sigma var bv; Some state
        | bv' ->
          if Bv.equal bv bv' then Some { state with constraints = cond :: state.constraints }
          else None)
      | _ ->
        if Bitvector.zero = Model.eval state.model cond then None
        else Some { state with constraints = cond :: state.constraints }


  let test cond state =
    if Expr.is_equal cond Expr.one then (
      QS.Preprocess.incr_true ();
      True state)
    else if Expr.is_equal cond Expr.zero then (
      QS.Preprocess.incr_false ();
      False state)
    else
      if Bitvector.zero = Model.eval state.model cond then False { state with constraints = Expr.lognot cond :: state.constraints }
      else True { state with constraints = cond :: state.constraints }

     
  let enumerate =
    
    fun e ?n:_ ?(except = []) state ->
      match e with
      | Expr.Cst bv when List.mem bv except = false ->
          QS.Preprocess.incr_const ();
          [ (bv, state) ]
      | Expr.Cst _ ->
          QS.Preprocess.incr_const ();
          []
      | _ -> (
          let bv = Model.eval state.model e in
          if List.mem bv except then []
          else 
            let cond = Expr.equal e (Expr.constant bv) in
            let state =
              { state with constraints = cond :: state.constraints }
            in
            [ (bv, state) ])

  let merge ~parent:_ _ _ = raise Non_mergeable

  module Value = struct
    type t = Expr.t

    let kind = Term
    let constant = Expr.constant
    let var id name size = Expr.var (name ^ Suid.to_string id) size name
    let unary = Expr.unary
    let binary = Expr.binary
    let ite = Expr.ite
    
  end

  let assertions t = t.constraints

  let get_value (e : Expr.t) _ =
    match e with Cst bv -> bv | _ -> raise_notrace Non_unique

  let get_a_value (e : Expr.t) t = Model.eval t.model e

  

  let to_formula t =
    let module C = Smt2_solver.Cross in
    let ctx = C.create ~next_id:Uid.zero () in
    List.iter (C.assert_bl ctx) t.constraints;
    C.define_ax ctx "memory" t.vmemory;
    I.iter
      (fun id expr -> C.define_bv ctx (Dba.Var.from_id id).name expr)
      t.vsymbols;
    C.to_formula ctx

  let downcast _ = None
end

type Options.Engine.t += Preca

let () =
  Options.Engine.register "exepath" Preca (fun () -> 
    if MaxDepth.is_default () then MaxDepth.set max_int;
    (module State)
  )

  
