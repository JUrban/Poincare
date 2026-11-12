(* ========================================================================= *)
(* OCaml library functions that src/ uses and Candle lacks.  Loaded after    *)
(* the HOL Light library and before src/.  The List and Hashtbl modules are  *)
(* Candle's (candle/ocaml.ml) with members added, so code loaded later sees  *)
(* a superset of what it saw before.                                          *)
(* ========================================================================= *)

let string_of_bool b = if b then "true" else "false";;

module List = struct
  let fold_left = List.fold_left
  let fold_right = List.fold_right
  let find = List.find
  let nth = List.nth
  let for_all = List.for_all
  let iter = List.iter
  let hd = List.hd
  let assoc = List.assoc
  let mem_assoc = List.mem_assoc
  let filter = List.filter
  let partition = List.partition
  let sort = List.sort
  let length = List.length
  let map = List.map
  let map2 = List.map2
  let mem = List.mem
  let rev = List.rev
  let concat = List.concat
  let rev_append = List.rev_append
  let exists = List.exists
  let compare = List.compare
  let rec for_all2 f l1 l2 =
    match (l1, l2) with
      ([], []) -> true
    | (a1::r1, a2::r2) -> f a1 a2 && for_all2 f r1 r2
    | _ -> raise (Invalid_argument "List.for_all2")
end;;

(* ------------------------------------------------------------------------- *)
(* Hashtbl: Candle's tables take a hash function and an order when they are  *)
(* created.  add is replace, which a cache cannot tell apart from OCaml's    *)
(* add; reset empties the table; hash_param hashes a term, by its names and  *)
(* structure up to a bounded number of nodes, as OCaml's does.  src/ uses it *)
(* on terms only.                                                             *)
(* ------------------------------------------------------------------------- *)

let candle_hash_mod = 1000000007;;

let candle_term_hash =
  (* names and structure only: types are left out, which makes the hash cheaper; the table's order tells
     apart the terms that collide *)
  let mix h x = (h * 31 + x) mod candle_hash_mod in
  fun limit tm ->
    let budget = ref limit in
    let rec hash tm =
      if !budget <= 0 then 0 else
      (budget := !budget - 1;
       if is_var tm then mix 1 (String.hash (fst(dest_var tm)) mod candle_hash_mod)
       else if is_const tm then mix 2 (String.hash (fst(dest_const tm)) mod candle_hash_mod)
       else if is_comb tm then let f, x = dest_comb tm in let hf = hash f in mix (mix 3 hf) (hash x)
       else let v, b = dest_abs tm in let hv = hash v in mix (mix 4 hv) (hash b)) in
    hash tm;;

module Hashtbl = struct
  type ('a, 'b) t = ('a, 'b) Hashtbl.t
  let create = Hashtbl.create
  let find = Hashtbl.find
  let replace = Hashtbl.replace
  let remove = Hashtbl.remove
  let fold = Hashtbl.fold
  let add tbl x y = Hashtbl.replace tbl x y
  let reset tbl = Cake.Hashtable.clear tbl
  let hash_param (meaningful:int) (total:int) tm = candle_term_hash meaningful tm
end;;

(* Orders and hashes for the keys of the caches of src/pc_rfa_h3d.ml.        *)

let candle_int_order (a:int) b = if a < b then -1 else if b < a then 1 else 0;;
let candle_int_hash (a:int) = (if a < 0 then 0 - a else a) mod candle_hash_mod;;

let candle_term_table n = Hashtbl.create n (candle_term_hash 500) Term.compare;;
let candle_int_table n = Hashtbl.create n candle_int_hash candle_int_order;;
let candle_hterm_table n =
  Hashtbl.create n (fun ((h:int),(_:term)) -> candle_int_hash h)
    (fun (h1,t1) (h2,t2) -> let c = candle_int_order h1 h2 in
                            if c <> 0 then c else Term.compare t1 t2);;
let candle_htermterm_table n =
  Hashtbl.create n (fun ((h:int),(_:term),(_:term)) -> candle_int_hash h)
    (fun (h1,s1,t1) (h2,s2,t2) ->
       let c = candle_int_order h1 h2 in
       if c <> 0 then c else
       let c = Term.compare s1 s2 in
       if c <> 0 then c else Term.compare t1 t2);;
