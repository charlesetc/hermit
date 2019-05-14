open Core

type t = int Int.Map.t

(* get new type var and copy any existing kinds *)
let new_type_var phi q =
  let v = Phi.new_type_var phi in
  ignore (q, v) ;
  raise (Failure "unimplemented")

let create phi quantified_variables =
  Set.to_list quantified_variables
  |> List.map ~f:(fun q -> (q, new_type_var phi q))
  |> Int.Map.of_alist_exn

let apply_to_type substitution phi ty =
  let rec lp ty =
    match Phi.find_exn phi ty with
    | ty, None ->
        (* Return `None` if the variable is not quantified over,
           * telling the caller that the variable has not changed.
           *
           * Return `Some new_type_var` if the variable has been
           * quantified over, telling the caller that the variable
           * is now new_type_var.
           * *)
        Map.find substitution ty
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
          let ty = Phi.new_type_var phi in
          Phi.union_to phi ty (Arrow { arg = ta; ret = tb }) ;
          Some ty )
    | _, Some (Kinded constraints) ->
        ignore constraints ;
        raise (Failure "unimplemented")
  in
  match lp ty with
  | None ->
      (* no variables need to be quantified over *)
      ty
  | Some ty ->
      ty
