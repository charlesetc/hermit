open Core

type 'metadata value =
  | Int of int
  | Bool of bool
  | String of string
  | Lambda of string * 'metadata t
[@@deriving sexp]

and 'metadata t =
  | Value of 'metadata * 'metadata value
  | Var of 'metadata * string
  | App of 'metadata * 'metadata t * 'metadata t
[@@deriving sexp]

let metadata = function
  | Value (m, _) ->
      m
  | Var (m, _) ->
      m
  | App (m, _, _) ->
      m

let rec to_string ~add_metadata = function
  | Value (m, Bool b) ->
      string_of_bool b |> add_metadata m
  | Value (m, Int i) ->
      string_of_int i |> add_metadata m
  | Value (m, String s) ->
      "\"" ^ String.escaped s ^ "\"" |> add_metadata m
  | Value (m, Lambda (x, a)) ->
      "\\" ^ x ^ "{ " ^ to_string ~add_metadata a ^ " }" |> add_metadata m
  | Var (m, s) ->
      s |> add_metadata m
  | App (m, a, b) ->
      "(" ^ to_string ~add_metadata a ^ " " ^ to_string ~add_metadata b ^ ")"
      |> add_metadata m

let to_string ?(metadata_to_string = fun _ -> None) ?(sep = "::") =
  to_string ~add_metadata:(fun m s ->
      s ^ match metadata_to_string m with None -> "" | Some s -> sep ^ s )
