open Core

(*! phi module *)
(* module Phi = struct end *)

module IType = struct
  type t =
    | Arrow of { arg : int; ret : int }
    | String
    | Bool
    | Int
  [@@deriving sexp]
end

type node =
  | Alias of int
  | Leaf of IType.t option
[@@deriving sexp]

type phi = node Int.Table.t

let rec find_exn phi a =
  match Hashtbl.find phi a with
  | Some (Alias i) ->
      find_exn phi i
  | Some (Leaf t) ->
      (a, t)
  | None ->
      failwithf
        !"unable to find variable %d in typing environment %{sexp: node \
          Int.Table.t}"
        a
        phi
        ()

let rec extract_full_type ~phi a =
  let a, a_type = find_exn phi a in
  match a_type with
  | None ->
      Type.Generic a
  | Some (IType.Arrow { arg; ret }) ->
      let arg = extract_full_type ~phi arg in
      let ret = extract_full_type ~phi ret in
      Type.Arrow { arg; ret }
  | Some IType.Bool ->
      Type.Bool
  | Some IType.String ->
      Type.String
  | Some IType.Int ->
      Type.Int

let find_or_insert phi a =
  let a_val = None in
  match Hashtbl.add phi ~key:a ~data:(Leaf a_val) with
  | `Ok ->
      (a, a_val)
  | `Duplicate ->
      find_exn phi a

let new_type_var =
  let i = ref 0 in
  fun phi ->
    let type_var = !i in
    incr i ;
    Hashtbl.set phi ~key:type_var ~data:(Leaf None) ;
    type_var

let check_no_cycles phi ~alias has_value =
  let rec free_variables phi a =
    let a, a_type = find_exn phi a in
    match a_type with
    | None ->
        Int.Set.singleton a
    | Some (Arrow { arg; ret }) ->
        Set.union (free_variables phi arg) (free_variables phi ret)
    | _ ->
        Int.Set.empty
  in
  let free_variables = free_variables phi has_value in
  if Set.mem free_variables alias
  then failwithf "cannot unify: divergent type" ()
  else ()

let rec union phi a b =
  (* get the new leaf's indices as well as their values *)
  let a, a_type = find_or_insert phi a in
  let b, b_type = find_or_insert phi b in
  match (a_type, b_type) with
  | None, None ->
      Hashtbl.set phi ~key:a ~data:(Alias b)
  | Some _a_type, None ->
      check_no_cycles phi ~alias:b a ;
      Hashtbl.set phi ~key:b ~data:(Alias a)
  | None, Some _b_type ->
      check_no_cycles phi ~alias:a b ;
      Hashtbl.set phi ~key:a ~data:(Alias b)
  | Some a_type, Some b_type ->
      union_types phi ~a ~b (a_type, b_type)

and union_types phi ~a ~b = function
  | Arrow { arg = a_arg; ret = a_ret }, Arrow { arg = b_arg; ret = b_ret } ->
      (* note to self: this could be a point of parallelization,
             * although we may have to change to random indices instead
             *
             * of auto-incrementing onec. *)
      union phi a_arg b_arg ;
      union phi a_ret b_ret
  | a_type, b_type ->
      failwithf
        !"incompatible types %{sexp: (IType.t * IType.t)}, for indices %d and \
          %d in typing environment %{sexp: node Int.Table.t}"
        (a_type, b_type)
        a
        b
        phi
        ()

let union_to phi a type_ =
  let t = new_type_var phi in
  Hashtbl.set phi ~key:t ~data:(Leaf (Some type_)) ;
  union phi a t

let rec constraints ~env ~phi = function
  | Ast.Value (k, Ast.Int _i) ->
      union_to phi k Int
  | Ast.Value (k, Ast.Bool _b) ->
      union_to phi k Bool
  | Ast.Value (k, Ast.String _s) ->
      union_to phi k String
  | Ast.Value (k, Ast.Lambda (name, body)) ->
      let arg = new_type_var phi in
      let env = Map.set env ~key:name ~data:arg in
      constraints ~env ~phi body ;
      let ret = Ast.metadata body in
      union_to phi k (Arrow { arg; ret })
  | Ast.Var (k, name) ->
      let var_type = Map.find_exn env name in
      union phi k var_type
  | Ast.App (k, a_ast, b_ast) ->
      constraints ~env ~phi a_ast ;
      constraints ~env ~phi b_ast ;
      let fn, arg = (Ast.metadata a_ast, Ast.metadata b_ast) in
      union_to phi fn (Arrow { arg; ret = k })
  | Ast.Let (k, x, a_ast, b_ast) ->
      let x_type = Ast.metadata a_ast in
      constraints ~env ~phi a_ast ;
      let env = Map.set env ~key:x ~data:x_type in
      constraints ~env ~phi b_ast ;
      union phi k (Ast.metadata b_ast)

let add_type_variables ~phi =
  let type_var () = new_type_var phi in
  let rec lp = function
    | Ast.Value ((), Ast.Lambda (name, body)) ->
        Ast.Value (type_var (), Ast.Lambda (name, lp body))
    | Ast.Value ((), Ast.Int i) ->
        Ast.Value (type_var (), Ast.Int i)
    | Ast.Value ((), Ast.String s) ->
        Ast.Value (type_var (), Ast.String s)
    | Ast.Value ((), Ast.Bool b) ->
        Ast.Value (type_var (), Ast.Bool b)
    | Ast.App ((), a, b) ->
        Ast.App (type_var (), lp a, lp b)
    | Ast.Var ((), s) ->
        Ast.Var (type_var (), s)
    | Ast.Let ((), x, a, b) ->
        Ast.Let (type_var (), x, lp a, lp b)
  in
  lp

let typecheck tree =
  let phi = Int.Table.create () in
  let tree = add_type_variables ~phi tree in
  constraints ~env:String.Map.empty ~phi tree ;
  let rec lp = function
    | Ast.Value (m, Ast.Lambda (name, body)) ->
        Ast.Value (extract_full_type ~phi m, Ast.Lambda (name, lp body))
    | Ast.Value (m, Ast.Int i) ->
        Ast.Value (extract_full_type ~phi m, Ast.Int i)
    | Ast.Value (m, Ast.String s) ->
        Ast.Value (extract_full_type ~phi m, Ast.String s)
    | Ast.Value (m, Ast.Bool b) ->
        Ast.Value (extract_full_type ~phi m, Ast.Bool b)
    | Ast.Var (m, name) ->
        Ast.Var (extract_full_type ~phi m, name)
    | Ast.App (m, a, b) ->
        Ast.App (extract_full_type ~phi m, lp a, lp b)
    | Ast.Let (m, x, a, b) ->
        Ast.Let (extract_full_type ~phi m, x, lp a, lp b)
  in
  lp tree

let%test_module "type inference tests" =
  ( module struct
    open Construct

    let eval_type_and_print ast =
      let tree = typecheck ast in
      printf !"type of tree: %{Type}\n" (Ast.metadata tree) ;
      match Eval.eval ast with
      | ast ->
          printf "evaluated to: %s" (Ast.to_string ast)
      | exception Eval.Error (message, ast) ->
          eprintf "Error %s %s" message (Ast.to_string ast)
      | exception e ->
          eprintf !"Got unknown error: %{Exn}" e

    let%expect_test "one variable" =
      app (fn "x" (var "x")) (int 2) |> eval_type_and_print ;
      [%expect {|
        type of tree: int
        evaluated to: 2 |}]

    let%expect_test "printing type variables" =
      fn "x" (var "x") |> eval_type_and_print ;
      [%expect
        {|
        type of tree: ('a -> 'a)
        evaluated to: \x{ x } |}] ;
      fn "x" (fn "y" (var "x")) |> eval_type_and_print ;
      [%expect
        {|
        type of tree: ('a -> ('b -> 'a))
        evaluated to: \x{ \y{ x } } |}]

    let%expect_test "two variables" =
      lt "id" (fn "x" (var "x")) (lt "_" (app (var "id") (int 2)) (var "id"))
      |> eval_type_and_print ;
      (*! Notice that this is inferred to be monomorphic. The addition of
       * polymorphic type inference will fix that! *)
      [%expect
        {|
        type of tree: (int -> int)
        evaluated to: \x{ x } |}]
  end )
