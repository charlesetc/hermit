open Core

module rec Full_kind : sig
  type nonrec t [@@deriving sexp, compare]
end = struct
  type t =
    { labels : Kind.Label.t list
    ; relations : T.t Kind.Label.Map.t
    }
  [@@deriving sexp, compare]
end

and Constraint : Kind.C = Kind.Make_constraint (Full_kind)

and T : sig
  type t =
    | Generic of int
    | Arrow of { arg : t; ret : t }
    | String
    | Bool
    | Int
    | Kinded of Constraint.Set.t
  [@@deriving sexp, compare]
end = struct
  type t =
    | Generic of int
    | Arrow of { arg : t; ret : t }
    | String
    | Bool
    | Int
    | Kinded of Constraint.Set.t
  [@@deriving sexp, compare]
end

include T

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
  | Kinded constraints ->
      ignore constraints ;
      "< >"

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

module Intermediate = struct
  type t =
    | Arrow of { arg : int; ret : int }
    | String
    | Bool
    | Int
    | Kinded of Kind.Intermediate.Constraint.Set.t
  [@@deriving sexp]
end

let rec extract_full_type find a =
  let a, a_type = find a in
  match a_type with
  | None ->
      Generic a
  | Some (Intermediate.Arrow { arg; ret }) ->
      let arg = extract_full_type find arg in
      let ret = extract_full_type find ret in
      Arrow { arg; ret }
  | Some Intermediate.Bool ->
      Bool
  | Some Intermediate.String ->
      String
  | Some Intermediate.Int ->
      Int
  | Some (Intermediate.Kinded _constraints) ->
      raise (Failure "unimplemented")
