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
    | Let (m, y, a, b) ->
        if y = x then Let (m, y, a, b) else Let (m, y, lp a, lp b)
  in
  lp b

let rec step ast =
  (* Very useful in the too see all the steps taken: *)
  (* Core.printf !"%{sexp: unit Ast.t}\n" [%here] ast ; *)
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
  | Let (_, x, (Value _ as a), b) ->
      `Continue (substitute x a ~within:b)
  | Let (m, x, a, b) ->
      `Continue (Let (m, x, eval a, b))

and eval a = match step a with `Continue a -> eval a | `Done a -> a
