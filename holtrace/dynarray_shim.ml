(* Minimal Dynarray for OCaml < 5.2: just the operations holtrace.ml uses (version 20250714)       *)
(* (make, length, get, add_last, clear), with the OCaml 5.2 semantics for them.                      *)
module Dynarray = struct
  type 'a t = { mutable arr : 'a array; mutable len : int; dummy : 'a }
  let make n x = { arr = Array.make (max n 16) x; len = n; dummy = x }
  let length a = a.len
  let get a i =
    if i < 0 || i >= a.len then invalid_arg "Dynarray.get: index out of bounds"
    else Array.unsafe_get a.arr i
  let add_last a x =
    let cap = Array.length a.arr in
    if a.len = cap then begin
      let na = Array.make (2 * cap + 1) a.dummy in
      Array.blit a.arr 0 na 0 a.len;
      a.arr <- na
    end;
    Array.unsafe_set a.arr a.len x;
    a.len <- a.len + 1
  let clear a = a.len <- 0; a.arr <- Array.make 16 a.dummy
end;;

