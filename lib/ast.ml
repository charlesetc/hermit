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
  | Let of 'metadata * string * 'metadata t * 'metadata t
[@@deriving sexp]

let metadata = function
  | Value (m, _) ->
      m
  | Var (m, _) ->
      m
  | App (m, _, _) ->
      m
  | Let (m, _, _, _) ->
      m

let map_metadata f =
  let rec lp = function
    | Value (m, Lambda (x, b)) ->
        Value (f m, Lambda (x, lp b))
    | Value (m, v) ->
        Value (f m, v)
    | Var (m, v) ->
        Var (f m, v)
    | App (m, a, b) ->
        App (f m, lp a, lp b)
    | Let (m, x, a, b) ->
        Let (f m, x, lp a, lp b)
  in
  lp

let to_string ~add_metadata =
  let rec lp = function
    | Value (m, Bool b) ->
        string_of_bool b |> add_metadata m
    | Value (m, Int i) ->
        string_of_int i |> add_metadata m
    | Value (m, String s) ->
        "\"" ^ String.escaped s ^ "\"" |> add_metadata m
    | Value (m, Lambda (x, a)) ->
        "\\" ^ x ^ "{ " ^ lp a ^ " }" |> add_metadata m
    | Var (m, s) ->
        s |> add_metadata m
    | App (m, a, b) ->
        "(" ^ lp a ^ " " ^ lp b ^ ")" |> add_metadata m
    | Let (m, x, a, b) ->
        "(let " ^ x ^ " = " ^ lp a ^ " in " ^ lp b ^ ")" |> add_metadata m
  in
  lp

let to_string ?(metadata_to_string = fun _ -> None) ?(sep = "::") =
  to_string ~add_metadata:(fun m s ->
      s ^ match metadata_to_string m with None -> "" | Some s -> sep ^ s )
