open Ast

let app a b = App ((), a, b)

let var x = Var ((), x)

let int i = Value ((), Int i)

let str s = Value ((), String s)

let fn x a = Value ((), Lambda (x, a))

let lt x a b = Let ((), x, a, b)
