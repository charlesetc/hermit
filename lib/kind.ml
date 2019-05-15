open Core

module Label = struct
  module T = struct
    type t = string [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

module Make_kind (A : sig
  type t [@@deriving compare, sexp]
end) =
struct
  type a = A.t [@@deriving compare, sexp]

  type t =
    { labels : Label.t list
    ; relations : a Label.Map.t
    }
  [@@deriving compare, sexp]

  module Constraint = struct
    module T = struct
      type nonrec t = a * t [@@deriving compare, sexp]
    end

    include T
    include Comparable.Make (T)
  end
end

module type S = sig
  type a [@@deriving compare, sexp]

  type t =
    { labels : Label.t list
    ; relations : a Label.Map.t
    }
  [@@deriving compare, sexp]

  module Constraint : sig
    include Comparable.S with type t := a * t

    type nonrec t = a * t [@@deriving compare, sexp]
  end
end

module Intermediate : S with type a = int = Make_kind (struct
  type t = int [@@deriving sexp, compare]
end)
