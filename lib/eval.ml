open Core

exception Error of string * unit Ast.t

let substitute x a ~within:b =
  let open Ast in
  let rec lp = function
    | Var (m, name) ->
        if name = x then a else Var (m, name)
    | Value (m, Lambda (y, body)) ->
        if y = x
        then Value (m, Lambda (y, body))
        else Value (m, Lambda (y, lp body))
    | App (m, a, b) ->
        App (m, lp a, lp b)
    | Value (m, v) ->
        Value (m, v)
  in
  lp b

let rec step ast =
  let open Ast in
  match ast with
  | Value _ ->
      `Done ast
  | Var (_, var) ->
      failwithf "unbound variable %s" var ()
  | App (_, Value (_, Lambda (x, body)), (Value _ as b)) ->
      `Continue (substitute x b ~within:body)
  | App (_, (Value _ as a), (Value _ as b)) ->
      raise (Error ("expected a function, found", a))
  | App (m, (Value _ as a), b) ->
      `Continue (App (m, a, eval b))
  | App (m, a, b) ->
      `Continue (App (m, eval a, b))

and eval a = match step a with `Continue a -> eval a | `Done a -> a
