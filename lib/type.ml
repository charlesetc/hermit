open Core

module rec Full_kind : (Kind.S with type a = T.t) = Kind.Make_kind (struct
  type a = T.t [@@deriving sexp, compare]
end)

and T : sig
  type t =
    | Generic of int
    | Arrow of { arg : t; ret : t }
    | String
    | Bool
    | Int
  [@@deriving sexp, compare]
end = struct
  type t =
    | Generic of int
    | Arrow of { arg : t; ret : t }
    | String
    | Bool
    | Int
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
  type index = int [@@deriving sexp, compare]

  type t =
    | Arrow of { arg : index; ret : index }
    | String
    | Bool
    | Int
  [@@deriving sexp]
end

include Comparable.Make (T)

let rec extract_full_type find a =
  let _, a_type = find a in
  match a_type with
  | `Generic a ->
      Generic a
  | `Type_leaf (Intermediate.Arrow { arg; ret }) ->
      let arg = extract_full_type find arg in
      let ret = extract_full_type find ret in
      Arrow { arg; ret }
  | `Type_leaf Intermediate.Bool ->
      Bool
  | `Type_leaf Intermediate.String ->
      String
  | `Type_leaf Intermediate.Int ->
      Int

and extract_full_kind find { Kind.Intermediate.labels; relations } =
  let relations = Kind.Label.Map.map relations ~f:(extract_full_type find) in
  { Full_kind.labels; relations }
