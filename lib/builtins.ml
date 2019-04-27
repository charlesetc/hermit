open Core

let create name add_type arity f =
  object
    method name = name

    method apply = f

    method add_type = add_type

    method arity = arity
  end

let int_star_int_to_int phi =
  let integer = Phi.new_type_var phi in
  let ret = Phi.new_type_var phi in
  let k = Phi.new_type_var phi in
  Phi.union_to phi integer Int ;
  Phi.union_to phi ret (Arrow { arg = integer; ret = integer }) ;
  Phi.union_to phi k (Arrow { arg = integer; ret }) ;
  k

let all () : 'a String.Map.t =
  let plus =
    create "plus" int_star_int_to_int 2 (function
        | [ `Int a; `Int b ] ->
            `Int (a + b)
        | _ ->
            failwithf "type error: plus" () )
  in
  let minus =
    create "minus" int_star_int_to_int 2 (function
        | [ `Int a; `Int b ] ->
            `Int (a - b)
        | _ ->
            failwithf "type error: minus" () )
  in
  let divide =
    create "divide" int_star_int_to_int 2 (function
        | [ `Int a; `Int b ] ->
            `Int (a / b)
        | _ ->
            failwithf "type error: divide" () )
  in
  let multiply =
    create "multiply" int_star_int_to_int 2 (function
        | [ `Int a; `Int b ] ->
            `Int (a * b)
        | _ ->
            failwithf "type error: multiply" () )
  in
  String.Map.of_alist_exn
    [ ("+", plus); ("-", minus); ("/", divide); ("*", multiply) ]

let lookup_type phi name =
  Map.find (all ()) name |> Option.map ~f:(fun b -> b#add_type phi)
