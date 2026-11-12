(* ========================================================================= *)
(* Unit pc_pde_base: generic space-time vocabulary of the PDE layer: index   *)
(* lists of bounded length, smoothness of curried families                   *)
(* u : real -> real^N -> real^K on sets of times and points, smoothness up   *)
(* to an initial time (extension past it, as in ricci_flow_from) and its     *)
(* classical form (all iterated partials extend continuously to the initial  *)
(* time).  Basic facts.                                                      *)
(* ========================================================================= *)

needs "src/poincare_statement.ml";;
needs "src/ns_smooth_elem.ml";;

prioritize_real();;
type_invention_error := true;;

(* Index lists of length at most s with entries in 1..dimindex u.            *)

let pde_index_lists = new_definition
 `pde_index_lists (s:num) (u:N->bool) =
    {l:(num)list | LENGTH l <= s /\ ALL (\i. 1 <= i /\ i <= dimindex u) l}`;;

let pde_st_smooth = new_definition
 `pde_st_smooth (J:real->bool) (U:real^N->bool) (u:real->real^N->real^K) <=>
    smooth_map_on {pastecart (lift t) y | t IN J /\ y IN U}
                  (\z. u (drop(fstcart z)) (sndcart z))`;;

let pde_upto = new_definition
 `pde_upto (a:real) (b:real) (U:real^N->bool) (u:real->real^N->real^K) <=>
    ?e F. &0 < e /\
          smooth_map_on (interval(lift(a - e),lift b) PCROSS U) F /\
          !t y. a <= t /\ t < b /\ y IN U ==> F(pastecart (lift t) y) = u t y`;;

let pde_upto_classical = new_definition
 `pde_upto_classical (a:real) (b:real) (U:real^N->bool) (u:real->real^N->real^K) <=>
    smooth_map_on (interval(lift a,lift b) PCROSS U) (\z. u (drop(fstcart z)) (sndcart z)) /\
    !l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
        ==> ?h. h continuous_on {pastecart (lift t) y | a <= t /\ t < b /\ y IN U} /\
                !t y. a < t /\ t < b /\ y IN U
                      ==> h(pastecart (lift t) y) =
                          iterated_partial l (\z. u (drop(fstcart z)) (sndcart z))
                                           (pastecart (lift t) y)`;;

(* ------------------------------------------------------------------------- *)
(* Index lists.  PDE_INDEX_LISTS_FINITE is NS_PF_CLASSES_MULTI_FINITE of the *)
(* Navier_Stokes development (github.com/hol-light-family/Navier_Stokes),    *)
(* restated for pde_index_lists.                                             *)
(* ------------------------------------------------------------------------- *)

let PDE_MULTI_FINITE = prove
 (`!d m. FINITE {l:num list | ALL (\i. 1 <= i /\ i <= d) l /\ LENGTH l <= m}`,
  GEN_TAC THEN INDUCT_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{[]:num list}` THEN
    REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING; LE; LENGTH_EQ_NIL] THEN
    MESON_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `([]:num list) INSERT
                IMAGE (\p:num#(num list). CONS (FST p) (SND p))
                  ((1..d) CROSS
                   {l:num list | ALL (\i. 1 <= i /\ i <= d) l /\ LENGTH l <= m})` THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; FINITE_CROSS; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS;
                IN_NUMSEG] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; LENGTH; NOT_CONS_NIL; CONS_11; LE_SUC] THEN
    MESON_TAC[]]);;

let PDE_INDEX_LISTS_FINITE = prove
 (`!s (u:N->bool). FINITE (pde_index_lists s u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_index_lists] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[PDE_MULTI_FINITE]);;

let PDE_INDEX_LISTS_NIL = prove
 (`!s (u:N->bool). [] IN pde_index_lists s u`,
  REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LENGTH; ALL; LE_0]);;

let PDE_INDEX_LISTS_MONO = prove
 (`!s s' (u:N->bool). s <= s' ==> pde_index_lists s u SUBSET pde_index_lists s' u`,
  REWRITE_TAC[pde_index_lists; SUBSET; IN_ELIM_THM] THEN MESON_TAC[LE_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness up to the initial time: restriction to the open slab and to    *)
(* subintervals.                                                             *)
(* ------------------------------------------------------------------------- *)

let PDE_UPTO_SMOOTH = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K).
        open U /\ pde_upto a b U u
        ==> smooth_map_on (interval(lift a,lift b) PCROSS U)
                          (\z. u (drop(fstcart z)) (sndcart z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^K`
      STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `FF:real^(1,N)finite_sum->real^K` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC]);;

let PDE_UPTO_SUBINTERVAL = prove
 (`!a b b' (U:real^N->bool) (u:real->real^N->real^K).
        pde_upto a b U u /\ b' <= b ==> pde_upto a b' U u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^K`
      STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `FF:real^(1,N)finite_sum->real^K`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

