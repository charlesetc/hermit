open Core

module Polytype = struct
  type t =
    | Monotype of int
    | Polytype of int * Int.Set.t * Kind.Intermediate.Constraint.Set.t
  [@@deriving sexp]
end

module Env = struct
  type t = Polytype.t String.Map.t [@@deriving sexp]

  let empty = String.Map.empty

  let add (t : t) x ptype = Map.set t ~key:x ~data:ptype

  let lookup (t : t) name = Map.find t name
end

let rec constraints ~env ~phi ast =
  match ast with
  | `Value (k, `Int _i) ->
      Phi.union_to phi k Int
  | `Value (k, `Bool _b) ->
      Phi.union_to phi k Bool
  | `Value (k, `String _s) ->
      Phi.union_to phi k String
  | `Value (k, `Lambda (name, body)) ->
      let arg = Phi.new_type_var phi in
      let env = Env.add env name (Polytype.Monotype arg) in
      constraints ~env ~phi body ;
      let ret = Ast.metadata body in
      Phi.union_to phi k (Arrow { arg; ret })
  | `Var (k, name) ->
    ( match Env.lookup env name with
    | Some (Polytype.Monotype var_type) ->
        Phi.union phi k var_type
    | Some
        (Polytype.Polytype (var_type, quantified_variables, quantified_kinds))
      ->
        ignore quantified_kinds ;
        let substitution = Substitution.create phi quantified_variables in
        let var_type = Substitution.apply_to_type substitution phi var_type in
        Phi.union phi k var_type
    | None ->
      ( match Builtins.lookup_type phi name with
      | Some var_type ->
          Phi.union phi k var_type
      | None ->
          failwithf "undefined variable %s" name () ) )
  | `App (k, a_ast, b_ast) ->
      constraints ~env ~phi a_ast ;
      constraints ~env ~phi b_ast ;
      let fn, arg = (Ast.metadata a_ast, Ast.metadata b_ast) in
      Phi.union_to phi fn (Arrow { arg; ret = k })
  | `Let (k, x, a_ast, b_ast) ->
      constraints ~env ~phi a_ast ;
      let ta = Ast.metadata a_ast in
      let fvs = Phi.free_variables phi ta in
      let env =
        Env.add
          env
          x
          (Polytype.Polytype
             ( ta
             , fvs
             , Kind.Intermediate.Constraint.Set.empty (* don't keep this *) ))
      in
      constraints ~env ~phi b_ast ;
      Phi.union phi k (Ast.metadata b_ast)

let add_type_variables ~phi =
  let type_var () = Phi.new_type_var phi in
  let rec lp = function
    | `Value ((), `Lambda (name, body)) ->
        `Value (type_var (), `Lambda (name, lp body))
    | `Value ((), `Int i) ->
        `Value (type_var (), `Int i)
    | `Value ((), `String s) ->
        `Value (type_var (), `String s)
    | `Value ((), `Bool b) ->
        `Value (type_var (), `Bool b)
    | `App ((), a, b) ->
        `App (type_var (), lp a, lp b)
    | `Var ((), s) ->
        `Var (type_var (), s)
    | `Let ((), x, a, b) ->
        `Let (type_var (), x, lp a, lp b)
  in
  lp

let typecheck tree =
  let phi = Int.Table.create () in
  let tree = add_type_variables ~phi tree in
  let extract_full_type = Type.extract_full_type (Phi.find_exn phi) in
  constraints ~env:Env.empty ~phi tree ;
  let rec lp = function
    | `Value (m, `Lambda (name, body)) ->
        `Value (extract_full_type m, `Lambda (name, lp body))
    | `Value (m, `Int i) ->
        `Value (extract_full_type m, `Int i)
    | `Value (m, `String s) ->
        `Value (extract_full_type m, `String s)
    | `Value (m, `Bool b) ->
        `Value (extract_full_type m, `Bool b)
    | `Var (m, name) ->
        `Var (extract_full_type m, name)
    | `App (m, a, b) ->
        `App (extract_full_type m, lp a, lp b)
    | `Let (m, x, a, b) ->
        `Let (extract_full_type m, x, lp a, lp b)
  in
  lp tree

let%test_module "type inference tests" =
  ( module struct
    open Construct

    let eval_type_and_print ast =
      let tree = typecheck ast in
      printf !"type of tree: %{Type}\n" (Ast.metadata tree) ;
      let ast = Eval.eval tree in
      printf "evaluated to: %s" (Ast.to_string ast)

    let eval_type_and_print ast =
      try eval_type_and_print ast with e -> eprintf !"Got error: %{Exn}" e

    let%expect_test "one variable" =
      app (fn "x" (var "x")) (int 2) |> eval_type_and_print ;
      [%expect {|
        type of tree: int
        evaluated to: 2 |}]

    let%expect_test "application type error" =
      app (int 2) (int 2) |> eval_type_and_print ;
      [%expect
        {|
        Got error: (Failure "incompatible types. expected (int -> 'a), but got int") |}]

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

    let%expect_test "infer id" =
      lt "id" (fn "x" (var "x")) (lt "_" (app (var "id") (int 2)) (var "id"))
      |> eval_type_and_print ;
      (*! Notice that this is inferred to be monomorphic. The addition of
       * polymorphic type inference will fix that! *)
      [%expect
        {|
        type of tree: ('a -> 'a)
        evaluated to: \x{ x } |}]

    let%expect_test "call id twice" =
      lt
        "id"
        (fn "x" (var "x"))
        (lt "_" (app (var "id") (int 2)) (app (var "id") (str "hi")))
      |> eval_type_and_print ;
      (*! Notice that this is inferred to be monomorphic. The addition of
       * polymorphic type inference will fix that! *)
      [%expect {|
        type of tree: string
        evaluated to: "hi" |}]

    let%expect_test "playing with id" =
      app (fn "x" (var "x")) (fn "x" (var "x")) |> eval_type_and_print ;
      [%expect
        {|
        type of tree: ('a -> 'a)
        evaluated to: \x{ x } |}] ;
      lt "id" (fn "x" (var "x")) (app (var "id") (var "id"))
      |> eval_type_and_print ;
      [%expect
        {|
        type of tree: ('a -> 'a)
        evaluated to: \x{ x }  |}]

    let%expect_test "playing with id" =
      app (fn "x" (var "x")) (fn "x" (var "x")) |> eval_type_and_print ;
      [%expect
        {|
        type of tree: ('a -> 'a)
        evaluated to: \x{ x } |}] ;
      lt "id" (fn "x" (var "x")) (app (var "id") (var "id"))
      |> eval_type_and_print ;
      [%expect
        {|
        type of tree: ('a -> 'a)
        evaluated to: \x{ x }  |}]

    (*! currently type checking is not being done for builtins *)
    let%expect_test "integer operations" =
      app (app (var "+") (int 2)) (int 3) |> eval_type_and_print ;
      (*! Notice that this is inferred to be monomorphic. The addition of
       * polymorphic type inference will fix that! *)
      [%expect {|
        type of tree: int
        evaluated to: 5|}] ;
      app (app (var "*") (int 2)) (int 3) |> eval_type_and_print ;
      [%expect {|
        type of tree: int
        evaluated to: 6 |}]

    let%expect_test "operation type error" =
      app (app (var "+") (str "okay")) (str "hi") |> eval_type_and_print ;
      (*! Notice that this is inferred to be monomorphic. The addition of
       * polymorphic type inference will fix that! *)
      [%expect
        {|
        Got error: (Failure "incompatible types. expected string, but got int")|}]
  end )
