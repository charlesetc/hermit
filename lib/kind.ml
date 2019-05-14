open Core

module Label = struct
  module T = struct
    type t = string [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

module Full = struct end

module Make_constraint (Inner : sig
  type nonrec t [@@deriving compare, sexp]
end) =
struct
  type inner = Inner.t

  module T = struct
    type nonrec t = int * Inner.t [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

module type C = sig
  type inner

  include Comparable.S with type t := int * inner
end

module Intermediate = struct
  module T = struct
    type t =
      { labels : Label.t list
      ; relations : int Label.Map.t
      }
    [@@deriving compare, sexp]
  end

  include T

  module Constraint : C = Make_constraint (T)
end
