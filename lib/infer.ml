open Core

module IType = struct
  type t =
    | Arrow of { arg : int; ret : int }
    | String
    | Bool
    | Int
  [@@deriving sexp]
end

module Phi = struct
  module Node = struct
    type t =
      | Alias of int
      | Leaf of IType.t option
    [@@deriving sexp]
  end

  type t = Node.t Int.Table.t [@@deriving sexp]

  let rec find_exn phi a =
    match Hashtbl.find phi a with
    | Some (Node.Alias i) ->
        find_exn phi i
    | Some (Node.Leaf t) ->
        (a, t)
    | None ->
        failwithf
          !"unable to find variable %d in typing environment %{sexp: Node.t \
            Int.Table.t}"
          a
          phi
          ()

  let find_or_insert phi a =
    let a_val = None in
    match Hashtbl.add phi ~key:a ~data:(Node.Leaf a_val) with
    | `Ok ->
        (a, a_val)
    | `Duplicate ->
        find_exn phi a

  let new_type_var =
    let i = ref 0 in
    fun phi ->
      let type_var = !i in
      incr i ;
      Hashtbl.set phi ~key:type_var ~data:(Node.Leaf None) ;
      type_var

  let rec free_variables phi a =
    let a, a_type = find_exn phi a in
    match a_type with
    | None ->
        Int.Set.singleton a
    | Some (Arrow { arg; ret }) ->
        Set.union (free_variables phi arg) (free_variables phi ret)
    | _ ->
        Int.Set.empty

  let check_no_cycles phi ~alias has_value =
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
          !"incompatible types %{sexp: (IType.t * IType.t)}, for indices %d \
            and %d in typing environment %{sexp: Node.t Int.Table.t}"
          (a_type, b_type)
          a
          b
          phi
          ()

  let union_to phi a type_ =
    let t = new_type_var phi in
    Hashtbl.set phi ~key:t ~data:(Leaf (Some type_)) ;
    union phi a t

  let copy_quantified phi ~quantified_variables ty =
    let quantified_variables =
      Set.to_list quantified_variables
      |> List.map ~f:(fun q -> (q, new_type_var phi))
      |> Int.Map.of_alist_exn
    in
    let rec lp ty =
      match find_exn phi ty with
      | ty, None ->
          (* Return `None` if the variable is not quantified over,
           * telling the caller that the variable has not changed.
           *
           * Return `Some new_type_var` if the variable has been
           * quantified over, telling the caller that the variable
           * is now new_type_var.
           * *)
          Map.find quantified_variables ty
      | _, Some String | _, Some Bool | _, Some Int ->
          None
      | _, Some (Arrow { arg = ta; ret = tb }) ->
        (* We pass in the original ta and tb so that we can handle 3 cases with
         * only one code branch *)
        ( match (lp ta, lp tb, `A ta, `B tb) with
        | None, None, _, _ ->
            None
        | Some ta, None, _, `B tb
        | None, Some tb, `A ta, _
        | Some ta, Some tb, _, _ ->
            let ty = new_type_var phi in
            union_to phi ty (Arrow { arg = ta; ret = tb }) ;
            Some ty )
    in
    match lp ty with
    | None ->
        (* no variables need to be quantified over *)
        ty
    | Some ty ->
        ty
end

let rec extract_full_type ~phi a =
  let a, a_type = Phi.find_exn phi a in
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

module Polytype = struct
  type t =
    | Monotype of int
    | Polytype of int * Int.Set.t
  [@@deriving sexp]
end

module Env = struct
  type t = Polytype.t String.Map.t [@@deriving sexp]

  let empty = String.Map.empty

  let add (t : t) x ptype = Map.set t ~key:x ~data:ptype

  let lookup (t : t) name =
    match Map.find t name with
    | Some ptype ->
        ptype
    | None ->
        failwithf "undefined variable %s" name ()
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
    | Polytype.Monotype var_type ->
        Phi.union phi k var_type
    | Polytype.Polytype (var_type, quantified_variables) ->
        let var_type =
          Phi.copy_quantified phi ~quantified_variables var_type
        in
        Phi.union phi k var_type )
  | `App (k, a_ast, b_ast) ->
      constraints ~env ~phi a_ast ;
      constraints ~env ~phi b_ast ;
      let fn, arg = (Ast.metadata a_ast, Ast.metadata b_ast) in
      Phi.union_to phi fn (Arrow { arg; ret = k })
  | `Let (k, x, a_ast, b_ast) ->
      constraints ~env ~phi a_ast ;
      let ta = Ast.metadata a_ast in
      let fvs = Phi.free_variables phi ta in
      let env = Env.add env x (Polytype.Polytype (ta, fvs)) in
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
  constraints ~env:Env.empty ~phi tree ;
  let rec lp = function
    | `Value (m, `Lambda (name, body)) ->
        `Value (extract_full_type ~phi m, `Lambda (name, lp body))
    | `Value (m, `Int i) ->
        `Value (extract_full_type ~phi m, `Int i)
    | `Value (m, `String s) ->
        `Value (extract_full_type ~phi m, `String s)
    | `Value (m, `Bool b) ->
        `Value (extract_full_type ~phi m, `Bool b)
    | `Var (m, name) ->
        `Var (extract_full_type ~phi m, name)
    | `App (m, a, b) ->
        `App (extract_full_type ~phi m, lp a, lp b)
    | `Let (m, x, a, b) ->
        `Let (extract_full_type ~phi m, x, lp a, lp b)
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
  end )
