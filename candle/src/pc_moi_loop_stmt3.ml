(* ========================================================================= *)
(* pc_moi_loop_stmt3: the statements of the C25 cut steps.                  *)
(*   MOI_LT2_CASE1_EXCLUDED: for an orientable finite combinatorial         *)
(*   3-manifold with boundary and a normal2 disk (genuine crossings), the   *)
(*   preimage of a closed double component is not connected (Case 1 of     *)
(*   Moise p.185 cannot occur: one preimage polygon would make the          *)
(*   monodromy of the crossing along k a reflection).                       *)
(*   MOI_LT_ORIENT_SIGN: an injective PL map of a connected open set of     *)
(*   real^3 into the interior of an oriented finite combinatorial           *)
(*   3-manifold with boundary has one orientation sign relative to the      *)
(*   orientation sg (the clauses of orientable_complex written out), the    *)
(*   sign of det of the Gram form of its linear part in the frame of the    *)
(*   tetrahedron times sg (proved via MOI_S35_LOCAL_SIGN).                  *)
(*   MOI_LT3_CLEAN_CAP: the clean cap of the separate case of CUT_SWAP.     *)
(*   Statement terms of the loop files (MOI_LT3_UNIT_TARGETS):              *)
(*   MOI_LT3_INNERMOST_FROM_EXCL (lt_cuta1), MOI_LT_ORIENT_SIGN (lt_orient), *)
(*   MOI_LT3_CASE1_FROM_ORIENT (lt_case1), MOI_LT3_SWAP_FROM_CAP (lt_cuta2), *)
(*   MOI_LT3_CLEAN_CAP (lt_cap); glue MOI_LT3D_CUT_INNERMOST,                *)
(*   MOI_LT3D_CUT_SWAP and the C25 closure MOI_LT3D_C25_CLOSURE over the     *)
(*   refined list.                                                           *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt2.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_LT2_CASE1_EXCLUDED =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N) k.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ orientable_complex c /\
     moi_lt_normal2_disk c f /\ k IN components (moi_lt_double_image f) /\
     k INTER complex_boundary c = {}
     ==> ~connected {x | x IN std_triangle /\ f x IN k}`;;

let MOI_LT_ORIENT_SIGN =
 `!(c:(real^N->bool)->bool) sg (g:real^3->real^N) w.
    FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
    (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
               ==> (sg a b d e = &1 \/ sg a b d e = -- &1) /\
                   sg b a d e = --(sg a b d e) /\ sg a d b e = --(sg a b d e) /\
                   sg a b e d = --(sg a b d e)) /\
    (!a b d e e'. ~(e = e') /\
                  convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
                  convex hull {a,b,d,e'} IN c /\ aff_dim(convex hull {a,b,d,e'}) = &3
                  ==> sg a b d e' = --(sg a b d e)) /\
    open w /\ connected w /\ pl_map_on w g /\
    (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y) /\
    IMAGE g w SUBSET UNIONS c DIFF complex_boundary c
    ==> ?s. (s = &1 \/ s = -- &1) /\
            !a b d e (l:real^3->real^N) y z r.
               convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
               linear l /\ &0 < r /\ ball(z,r) SUBSET w /\
               (!x. x IN ball(z,r) ==> g x = l x + y /\ g x IN convex hull {a,b,d,e})
               ==> sg a b d e *
                   real_sgn(det((lambda i j. l(basis j) dot
                                   (if i = 1 then b - a else if i = 2 then d - a else e - a))
                                :real^3^3)) = s`;;

(* The sg clauses of MOI_LT_ORIENT_SIGN are the body of orientable_complex. *)

let MOI_LT3D_ORIENT_CLAUSES = prove
 (`!(c:(real^N->bool)->bool).
     orientable_complex c <=>
     ?sg:real^N->real^N->real^N->real^N->real.
       (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                  ==> (sg a b d e = &1 \/ sg a b d e = -- &1) /\
                      sg b a d e = --(sg a b d e) /\ sg a d b e = --(sg a b d e) /\
                      sg a b e d = --(sg a b d e)) /\
       (!a b d e e'. ~(e = e') /\
                     convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
                     convex hull {a,b,d,e'} IN c /\ aff_dim(convex hull {a,b,d,e'}) = &3
                     ==> sg a b d e' = --(sg a b d e))`,
  REWRITE_TAC[orientable_complex]);;

(* The clean cap of the separate case (Moise p.185 Case 2, DG              *)
(* exists_adaptedCleanCap): the hypotheses of CUT_SWAP_2 with the disks D1 *)
(* and D2 disjoint (the separate case) instead of j2 outside the inside of *)
(* j1; a polygon j around D2 with no double points between j and j2, and a *)
(* PL disk d bounded by f(j) meeting the image only in f(j), in the        *)
(* interior of c.  The swap then maps j UNION inside j onto d (Alexander   *)
(* trick).                                                                  *)

let MOI_LT3_CLEAN_CAP =
 `!(c:(real^N->bool)->bool) (f:real^2->real^N) k (j1:real^2->bool) j2.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lt_normal2_disk c f /\
     k IN components (moi_lt_double_image f) /\
     k INTER complex_boundary c = {} /\
     pl_sphere 1 j1 /\ pl_sphere 1 j2 /\ DISJOINT j1 j2 /\
     {x | x IN std_triangle /\ f x IN k} = j1 UNION j2 /\
     j1 UNION inside j1 SUBSET std_triangle DIFF relative_frontier std_triangle /\
     j2 UNION inside j2 SUBSET std_triangle DIFF relative_frontier std_triangle /\
     {x | x IN inside j1 /\ f x IN moi_lt_double_image f} = {} /\
     DISJOINT (j1 UNION inside j1) (j2 UNION inside j2)
     ==> ?j d. pl_sphere 1 j /\ j2 UNION inside j2 SUBSET inside j /\
               j UNION inside j SUBSET std_triangle DIFF relative_frontier std_triangle /\
               {x | x IN (j UNION inside j) DIFF (j2 UNION inside j2) /\
                    f x IN moi_lt_double_image f} = {} /\
               pl_cell_with_boundary 2 d (IMAGE f j) /\
               d INTER IMAGE f std_triangle = IMAGE f j /\
               d SUBSET UNIONS c DIFF complex_boundary c`;;

(* Statement terms of lt_cuta1, lt_case1 and lt_cuta2 (lt_orient proves      *)
(* MOI_LT_ORIENT_SIGN and lt_cap proves MOI_LT3_CLEAN_CAP).                  *)

let MOI_LT3_INNERMOST_FROM_EXCL = mk_imp(MOI_LT2_CASE1_EXCLUDED,MOI_LT2_CUT_INNERMOST);;
let MOI_LT3_CASE1_FROM_ORIENT = mk_imp(MOI_LT_ORIENT_SIGN,MOI_LT2_CASE1_EXCLUDED);;
let MOI_LT3_SWAP_FROM_CAP = mk_imp(MOI_LT3_CLEAN_CAP,MOI_LT2_CUT_SWAP);;

let MOI_LT3D_CUT_INNERMOST = prove
 (mk_imp(list_mk_conj [MOI_LT3_INNERMOST_FROM_EXCL; MOI_LT3_CASE1_FROM_ORIENT;
                       MOI_LT_ORIENT_SIGN], MOI_LT2_CUT_INNERMOST),
  DISCH_THEN(fun th ->
    let a,bc = CONJ_PAIR th in let b,c = CONJ_PAIR bc in ACCEPT_TAC(MP a (MP b c))));;

let MOI_LT3D_CUT_SWAP = prove
 (mk_imp(mk_conj(MOI_LT3_SWAP_FROM_CAP,MOI_LT3_CLEAN_CAP), MOI_LT2_CUT_SWAP),
  DISCH_THEN(fun th -> let a,b = CONJ_PAIR th in ACCEPT_TAC(MP a b)));;

(* The refined list MOI_LT3_UNIT_TARGETS and the C25 closure over it.      *)

let MOI_LT3_UNIT_TARGETS =
  flat (map (fun t -> if t = MOI_LT2_CUT_INNERMOST
                      then [MOI_LT3_INNERMOST_FROM_EXCL; MOI_LT3_CASE1_FROM_ORIENT;
                            MOI_LT_ORIENT_SIGN]
                      else if t = MOI_LT2_CUT_SWAP
                      then [MOI_LT3_SWAP_FROM_CAP; MOI_LT3_CLEAN_CAP]
                      else [t]) MOI_LT2_UNIT_TARGETS);;

let MOI_LT3D_C25_CLOSURE =
  let ity = [`:7`,`:N`; `:7`,`:M`] in
  let hs = map (inst ity) (MOI_LT3_UNIT_TARGETS @ MOI_LT_FND_TERMS) @
           [MOI_CORE_GLUE_LOOP3] in
  let hconj = list_mk_conj hs in
  let asm = CONJUNCTS (ASSUME hconj) in
  let _ = if length asm = length hs then () else failwith "conjunct count" in
  let get t = find (fun th -> aconv (concl th) (inst ity t)) asm in
  let it th = INST_TYPE ity th in
  let inn = MP (it MOI_LT3D_CUT_INNERMOST)
               (end_itlist CONJ (map get [MOI_LT3_INNERMOST_FROM_EXCL;
                                          MOI_LT3_CASE1_FROM_ORIENT; MOI_LT_ORIENT_SIGN])) in
  let swp = MP (it MOI_LT3D_CUT_SWAP)
               (end_itlist CONJ (map get [MOI_LT3_SWAP_FROM_CAP; MOI_LT3_CLEAN_CAP])) in
  let hs2 = map (inst ity) (MOI_LT2_UNIT_TARGETS @ MOI_LT_FND_TERMS) @
            [MOI_CORE_GLUE_LOOP3] in
  let get2 t = if aconv t (inst ity MOI_LT2_CUT_INNERMOST) then inn
               else if aconv t (inst ity MOI_LT2_CUT_SWAP) then swp
               else find (fun th -> aconv (concl th) t) asm in
  DISCH hconj (MP MOI_LT2D_C25_CLOSURE (end_itlist CONJ (map get2 hs2)));;

(* Checks.  The cap has exactly the hypotheses of CUT_SWAP_2 except the     *)
(* last one, which is replaced by the disjointness of the two disks; the    *)
(* refined list replaces exactly CUT_INNERMOST_2 and CUT_SWAP_2; the        *)
(* closure concludes LOOP_THEOREM_3_STATEMENT with no hypotheses.           *)

let moi_lt3_cap_ok =
  let vs1,b1 = strip_forall MOI_LT3_CLEAN_CAP and vs2,b2 = strip_forall MOI_LT2_CUT_SWAP in
  let h1 = conjuncts(lhand b1) and h2 = conjuncts(lhand b2) in
  vs1 = vs2 && length h1 = length h2 && forall2 aconv (butlast h1) (butlast h2) &&
  type_of MOI_LT3_CLEAN_CAP = bool_ty && frees MOI_LT3_CLEAN_CAP = [];;

let moi_lt3_check =
  moi_lt3_cap_ok &&
  length MOI_LT3_UNIT_TARGETS = length MOI_LT2_UNIT_TARGETS + 3 &&
  not (mem MOI_LT2_CUT_INNERMOST MOI_LT3_UNIT_TARGETS) &&
  not (mem MOI_LT2_CUT_SWAP MOI_LT3_UNIT_TARGETS) &&
  forall (fun t -> type_of t = bool_ty && frees t = [])
         [MOI_LT2_CASE1_EXCLUDED; MOI_LT_ORIENT_SIGN; MOI_LT3_INNERMOST_FROM_EXCL;
          MOI_LT3_CASE1_FROM_ORIENT; MOI_LT3_SWAP_FROM_CAP] &&
  hyp MOI_LT3D_CUT_INNERMOST = [] && hyp MOI_LT3D_CUT_SWAP = [] &&
  hyp MOI_LT3D_C25_CLOSURE = [] &&
  aconv (rand(concl MOI_LT3D_C25_CLOSURE)) `LOOP_THEOREM_3_STATEMENT`;;

print_string ("LT3 " ^
   string_of_bool (moi_lt3_check) ^
   " " ^
   string_of_int ((length MOI_LT3_UNIT_TARGETS)) ^
   "\n");;

