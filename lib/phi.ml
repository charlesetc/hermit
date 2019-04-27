open Core
module Full = Type

module Type_t = struct
  type t =
    | Arrow of { arg : int; ret : int }
    | String
    | Bool
    | Int
  [@@deriving sexp]
end

module Node = struct
  type t =
    | Alias of int
    | Leaf of Type_t.t option
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

module Type = struct
  include Type_t

  let rec extract_full_type ~phi a =
    let a, a_type = find_exn phi a in
    match a_type with
    | None ->
        Full.Generic a
    | Some (Arrow { arg; ret }) ->
        let arg = extract_full_type ~phi arg in
        let ret = extract_full_type ~phi ret in
        Full.Arrow { arg; ret }
    | Some Bool ->
        Full.Bool
    | Some String ->
        Full.String
    | Some Int ->
        Full.Int
end

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
        !"incompatible types. expected %{Full}, but got %{Full}"
        (Type.extract_full_type ~phi a)
        (Type.extract_full_type ~phi b)
        ()

let union_to phi a type_ =
  let t = new_type_var phi in
  (* This could be a little confusing if ever "union_to"-ing arrow types *)
  Hashtbl.set phi ~key:t ~data:(Leaf (Some type_)) ;
  union phi t a

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
