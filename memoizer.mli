(********************************)

(* THIS PART OF THE ASSIGNMENT IS OPTIONAL *)
(*Many students find this problem mind-blowing and fun, but it is OPTIONAL.
 You don't need to do it if you don't want to.*)

(********************************)


module type MEMOIZER =
sig
  (* the type of the memoized function's argument *)
  type key

  (* memo f returns a memoized version of f.
   * assumes f r x makes recursive calls by calling r not f *)
  val memo : ((key -> 'a) -> (key -> 'a)) -> (key -> 'a)
end

module Memoizer : functor (D : Map.S) -> MEMOIZER with type key = D.key
