open Core

module Node = struct
  type t =
    | Alias of int
    | Leaf of Type.Intermediate.t option
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
  | Int, Int ->
      ()
  | Bool, Bool ->
      ()
  | String, String ->
      ()
  | _, _ ->
      failwithf
        !"incompatible types. expected %{Type}, but got %{Type}"
        (Type.extract_full_type (find_exn phi) a)
        (Type.extract_full_type (find_exn phi) b)
        ()

let union_to phi a type_ =
  let t = new_type_var phi in
  (* This could be a little confusing if ever "union_to"-ing arrow types *)
  Hashtbl.set phi ~key:t ~data:(Leaf (Some type_)) ;
  union phi t a

module Substitution = struct end
