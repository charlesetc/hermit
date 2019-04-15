open Core

type t =
  | Generic of int
  | Arrow of { arg : t; ret : t }
  | String
  | Bool
  | Int
[@@deriving sexp]

let rec to_string = function
  | Generic i ->
      "'"
      ^
      if i < 26
      then Char.of_int_exn (Char.to_int 'a' + i) |> Char.to_string
      else string_of_int i
  | Arrow { arg; ret } ->
      "(" ^ to_string arg ^ " -> " ^ to_string ret ^ ")"
  | Bool ->
      "bool"
  | Int ->
      "int"
  | String ->
      "string"

let relabel t =
  let state = ref 0 in
  let mapping = Int.Table.create () in
  let rec lp = function
    | Arrow { arg; ret } ->
        Arrow { arg = lp arg; ret = lp ret }
    | Generic i ->
      ( match Hashtbl.find mapping i with
      | Some i' ->
          Generic i'
      | None ->
          let i' = !state in
          incr state ;
          Hashtbl.add_exn mapping ~key:i ~data:i' ;
          Generic i' )
    | anything_else ->
        anything_else
  in
  lp t

let to_string t = relabel t |> to_string
