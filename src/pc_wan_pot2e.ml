(* ========================================================================= *)
(* pc_wan_pot2e: the Schauder estimate for all k by induction on k through   *)
(* the derivatives d_i w, and |- WAN_SCHAUDER_2D_STATEMENT.                  *)
(*   - iterated partials of C^m functions, C^(m+1) from C^m partials;        *)
(*   - wan_ckal manipulation (subsets, constants, radius, derivatives);      *)
(*   - tests closed under the Laplacian; the very weak equation for a        *)
(*     C^2 solution and for its partial derivatives;                         *)
(*   - the mean value step wan_ckal (k+1) ==> wan_ckal k;                    *)
(*   - the theta-form predicate wanl_pt_schp, its case k = 0, constants;     *)
(*   - the induction step, the induction, WAN_SCHAUDER_2D.                   *)
(* ========================================================================= *)

needs "src/pc_wan_pot2d.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Iterated partials of C^m functions; C^(m+1) from differentiability and   *)
(* C^m partial derivatives.                                                  *)
(* ------------------------------------------------------------------------- *)

(* A copy of BEL_ITERATED_PARTIAL_LOCAL (pc_an_beltrami.ml, which this file  *)
(* does not load), with the same statement and proof.                        *)

let WANL_PT_ITP_LOCAL = prove
 (`!l U f g:real^M->real^N z.
        open U /\ (!z. z IN U ==> f z = g z) /\ z IN U
        ==> iterated_partial l f z = iterated_partial l g z`,
  SUBGOAL_THEN
   `!l U f g:real^M->real^N.
        open U /\ (!z. z IN U ==> f z = g z)
        ==> !z. z IN U ==> iterated_partial l f z = iterated_partial l g z`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
  EXISTS_TAC `U:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let WANL_PT_ITP_CD = prove
 (`!l m (s:real^N->bool) (g:real^N->real^K).
     open s /\ continuously_differentiable m s g /\ LENGTH l <= m
     ==> continuously_differentiable (m - LENGTH l) s (iterated_partial l g)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; LENGTH; SUB_0] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `s:real^N->bool`; `g:real^N->real^K`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `m - LENGTH(t:num list) = SUC(m - SUC(LENGTH t))` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[PARTIAL_DERIVATIVE_ALT] THEN
  MP_TAC(ISPECL [`m - SUC(LENGTH(t:num list))`; `s:real^N->bool`;
                 `iterated_partial t (g:real^N->real^K)`] CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `continuously_differentiable (m - LENGTH(t:num list)) s
                   (iterated_partial t (g:real^N->real^K))` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `basis h:real^N`) THEN REWRITE_TAC[]]);;

let WANL_PT_FRECHET_PARTIALS = prove
 (`!(g:real^N->real^K) x h.
     g differentiable at x
     ==> frechet_derivative g (at x) h =
         vsum(1..dimindex(:N)) (\i. h$i % partial_derivative i g x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; partial_derivative]);;

let WANL_PT_CD_SUC_PARTIALS = prove
 (`!n (s:real^N->bool) (g:real^N->real^K).
     open s /\ (!x. x IN s ==> g differentiable at x) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> continuously_differentiable n s (partial_derivative i g))
     ==> continuously_differentiable (SUC n) s g`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  EXISTS_TAC `\x. frechet_derivative (g:real^N->real^K) (at x)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  X_GEN_TAC `h:real^N` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC `\x. vsum(1..dimindex(:N)) (\i. (h:real^N)$i % partial_derivative i (g:real^N->real^K) x)` THEN
  ASM_SIMP_TAC[WANL_PT_FRECHET_PARTIALS] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_VSUM_OPEN THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN THEN ASM_SIMP_TAC[ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* wan_ckal: smaller sets, larger constants, smaller radius, derivatives,   *)
(* and the bound for f from bounds for its partial derivatives.             *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_LIST_SNOC = prove
 (`!l:(num)list. ~(l = []) ==> ?l' i. l = APPEND l' [i] /\ LENGTH l = SUC(LENGTH l')`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`BUTLAST(l:(num)list)`; `LAST(l:(num)list)`] THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP APPEND_BUTLAST_LAST) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC);;

let WANL_PT_CKAL_SUBSET = prove
 (`!(s:real^N->bool) t k al r (f:real^N->real^K) A.
     wan_ckal s k al r f A /\ t SUBSET s ==> wan_ckal t k al r f A`,
  REWRITE_TAC[wan_ckal; SUBSET] THEN MESON_TAC[]);;

let WANL_PT_CKAL_MONO = prove
 (`!(s:real^N->bool) k al r (f:real^N->real^K) A B.
     wan_ckal s k al r f A /\ A <= B ==> wan_ckal s k al r f B`,
  REWRITE_TAC[wan_ckal] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A:real` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A * norm(x - y:real^N) rpow al` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[NORM_POS_LE]]);;

let WANL_PT_CKAL_RADIUS = prove
 (`!(s:real^N->bool) k al r r' (f:real^N->real^K) A.
     wan_ckal s k al r f A /\ &0 < r' /\ r' <= r /\ &0 <= al
     ==> wan_ckal s k al r' f A`,
  REWRITE_TAC[wan_ckal] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `r pow LENGTH(l:(num)list) * norm(iterated_partial l (f:real^N->real^K) x)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `r rpow (&k + al) *
                norm(iterated_partial l (f:real^N->real^K) x - iterated_partial l f y)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[REAL_POS]]);;

let WANL_PT_CKAL_DERIV = prove
 (`!(s:real^N->bool) k al r (f:real^N->real^K) A i.
     wan_ckal s (SUC k) al r f A /\ &0 < r /\ 1 <= i /\ i <= dimindex(:N)
     ==> wan_ckal s k al r (partial_derivative i f) (A / r)`,
  REWRITE_TAC[wan_ckal] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!l. iterated_partial l (partial_derivative i (f:real^N->real^K)) =
                    iterated_partial (APPEND l [i]) f /\
                    LENGTH(APPEND l [i]) = SUC(LENGTH(l:(num)list)) /\
                    (ALL (\i. 1 <= i /\ i <= dimindex(:N)) (APPEND l [i]) <=>
                     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; LENGTH_APPEND;
                             LENGTH; ALL_APPEND; ALL] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`APPEND l [i:num]`; `x:real^N`] o check (fun th ->
      can (find_term (fun t -> t = `LENGTH:(num)list->num`)) (concl th) &&
      not(can (find_term (fun t -> t = `y:real^N`)) (concl th)) && is_forall(concl th) &&
      not(can (find_term (fun t -> t = `rpow`)) (concl th)))) THEN
    ASM_REWRITE_TAC[real_pow] THEN ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`APPEND l [i:num]`; `x:real^N`; `y:real^N`] o check (fun th ->
    can (find_term (fun t -> t = `rpow`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r rpow (&(SUC k) + al) = r rpow (&k + al) * r` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ARITH `(k + &1) + al = (k + al) + &1`] THEN
    ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `A / r * norm(x - y:real^N) rpow al = (A * norm(x - y) rpow al) / r`
  SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let WANL_PT_CKAL_LIFT = prove
 (`!(s:real^N->bool) m al r (f:real^N->real^K) B0 B.
     &0 < r /\ &0 <= B0 /\ &0 <= B /\
     (!x. x IN s ==> norm(f x) <= B0) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_ckal s m al r (partial_derivative i f) B)
     ==> wan_ckal s (SUC m) al r f (B0 + r * B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!l:(num)list. ~(l = []) /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
        ==> ?l' i. 1 <= i /\ i <= dimindex(:N) /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l' /\
                   LENGTH l = SUC(LENGTH l') /\
                   iterated_partial l (f:real^N->real^K) =
                   iterated_partial l' (partial_derivative i f)`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP WANL_PT_LIST_SNOC) THEN
    DISCH_THEN(X_CHOOSE_THEN `l':(num)list` (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`l':(num)list`; `i:num`] THEN
    UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:N)) (l:(num)list)` THEN
    ASM_REWRITE_TAC[ALL_APPEND; ALL; ITERATED_PARTIAL_APPEND; iterated_partial] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[wan_ckal] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:(num)list`; `x:real^N`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `l:(num)list = []` THENL
     [ASM_REWRITE_TAC[LENGTH; real_pow; REAL_MUL_LID; iterated_partial] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B0:real` THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:(num)list` o check (fun th ->
      can (find_term (fun t -> t = `SUC`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l':(num)list` (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[real_pow] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[wan_ckal] o SPEC `i:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_ckal")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`l':(num)list`; `x:real^N`] o CONJUNCT1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `LENGTH(l:(num)list) <= SUC m` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `r * r pow LENGTH(l':(num)list) *
                  norm(iterated_partial l' (partial_derivative i (f:real^N->real^K)) x) <= r * B`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`l:(num)list`; `x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(l:(num)list = [])` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `LENGTH(l:(num)list) = SUC m` THEN
    ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:(num)list` o check (fun th ->
    can (find_term (fun t -> t = `SUC`)) (concl th) && is_forall(concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':(num)list` (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `LENGTH(l':(num)list) = m` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`LENGTH(l:(num)list) = SUC m`;
                           `LENGTH(l:(num)list) = SUC(LENGTH(l':(num)list))`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[wan_ckal] o SPEC `i:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_ckal")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`l':(num)list`; `x:real^N`; `y:real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r rpow (&(SUC m) + al) = r * r rpow (&m + al)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ARITH `(k + &1) + al = &1 + (k + al)`] THEN
    ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC `D = norm(x - y:real^N) rpow al` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r * r rpow (&m + al) *
                norm(iterated_partial l' (partial_derivative i (f:real^N->real^K)) x -
                     iterated_partial l' (partial_derivative i f) y) <= r * (B * D)`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B0 * D` MP_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Test functions on s closed under sums, dparts and the flat Laplacian;     *)
(* the very weak equation for a classical C^2 solution and for its partial  *)
(* derivatives.                                                              *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_TEST_ADD = prove
 (`!(s:real^N->bool) phi psi.
     wan_test s phi /\ wan_test s psi ==> wan_test s (\x. phi x + psi x)`,
  REWRITE_TAC[wan_test] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k1:real^N->bool` STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k2:real^N->bool` STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    EXISTS_TAC `k1 UNION k2:real^N->bool` THEN
    ASM_SIMP_TAC[COMPACT_UNION; UNION_SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_ADD_LID]]);;

let WANL_PT_LLAP2 = prove
 (`!(phi:real^2->real).
     smooth_map_on (:real^2) (\x. lift(phi x))
     ==> llap (\y. mat 1) phi =
         \x. wan_dpart 1 (wan_dpart 1 phi) x + wan_dpart 2 (wan_dpart 2 phi) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^2` THEN
  ASM_SIMP_TAC[WANL_LLAP_DPART; DIMINDEX_2; SUM_2]);;

let WANL_PT_TEST_LLAP = prove
 (`!(s:real^2->bool) phi. wan_test s phi ==> wan_test s (llap (\y. mat 1) phi)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\x. lift(phi x))` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_test]; ALL_TAC] THEN
  ASM_SIMP_TAC[WANL_PT_LLAP2] THEN MATCH_MP_TAC WANL_PT_TEST_ADD THEN
  REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[WAN_TEST_DPART_OPEN]);;

let WANL_PT_DPART_ADD = prove
 (`!(g:real^N->real) h i x.
     (\y. lift(g y)) differentiable at x /\ (\y. lift(h y)) differentiable at x
     ==> wan_dpart i (\y. g y + h y) x = wan_dpart i g x + wan_dpart i h x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LIFT_EQ; LIFT_ADD; WAN_DPART_LIFT] THEN
  REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[]);;

let WANL_PT_DPART_LLAP = prove
 (`!(phi:real^2->real) i x.
     wan_test (:real^2) phi /\ 1 <= i /\ i <= 2
     ==> wan_dpart i (llap (\y. mat 1) phi) x = llap (\y. mat 1) (wan_dpart i phi) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. wan_test (:real^2) (wan_dpart j phi) /\
                    wan_test (:real^2) (wan_dpart j (wan_dpart j phi))` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[WAN_TEST_DPART_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `!g. wan_test (:real^2) g ==> smooth_map_on (:real^2) (\x. lift(g x))`
  ASSUME_TAC THENL [MESON_TAC[wan_test]; ALL_TAC] THEN
  ASM_SIMP_TAC[WANL_PT_LLAP2] THEN
  W(fun (asl,w) -> MP_TAC(ISPECL [`wan_dpart 1 (wan_dpart 1 (phi:real^2->real))`;
                                 `wan_dpart 2 (wan_dpart 2 (phi:real^2->real))`;
                                 `i:num`; `x:real^2`] WANL_PT_DPART_ADD)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^2)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= 2
        ==> wan_dpart i (wan_dpart j (wan_dpart j (phi:real^2->real))) x =
            wan_dpart j (wan_dpart j (wan_dpart i phi)) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`wan_dpart j (phi:real^2->real)`; `j:num`; `i:num`; `x:real^2`]
                  WAN_DPART_SYM) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^2` THEN
    MP_TAC(ISPECL [`phi:real^2->real`; `j:num`; `i:num`; `z:real^2`] WAN_DPART_SYM) THEN
    ASM_REWRITE_TAC[DIMINDEX_2];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH] THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPEC `wan_dpart i (phi:real^2->real)` WANL_PT_LLAP2) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let WANL_PT_C2_VERY_WEAK = prove
 (`!(s:real^2->bool) (w:real^2->real) (f:real^2->real).
     open s /\ continuously_differentiable 2 s (\x. lift(w x)) /\
     (!x. x IN s ==> llap (\y. mat 1) w x = f x)
     ==> !phi. wan_test s phi
               ==> integral s (\x. lift(w x * llap (\y:real^2. mat 1) phi x)) =
                   integral s (\x. lift(f x * phi x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `phi:real^2->real` THEN DISCH_TAC THEN
  ABBREV_TAC `W = \x:real^2. lift(w x)` THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\x. lift(phi x))` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_test]; ALL_TAC] THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 s (W:real^2->real^1) /\
    !i. continuously_differentiable 1 s (partial_derivative i (W:real^2->real^1)) /\
        partial_derivative i (partial_derivative i W) continuous_on s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN EXISTS_TAC `2` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    GEN_TAC THEN
    MP_TAC(ISPECL [`[i:num]`; `2`; `s:real^2->bool`; `W:real^2->real^1`] WANL_PT_ITP_CD) THEN
    MP_TAC(ISPECL [`[i:num; i]`; `2`; `s:real^2->bool`; `W:real^2->real^1`] WANL_PT_ITP_CD) THEN
    ASM_REWRITE_TAC[LENGTH; iterated_partial] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0; ETA_AX] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc s (W:real^2->real^1)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_CONTINUOUS_ON_LLOC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> wan_test s (wan_dpart i (wan_dpart i phi)) /\
            (\x. wan_dpart i (wan_dpart i phi) x % (W:real^2->real^1) x) integrable_on s /\
            (\x. phi x % partial_derivative i (partial_derivative i W) x) integrable_on s /\
            integral s (\x. wan_dpart i (wan_dpart i phi) x % W x) =
            integral s (\x. phi x % partial_derivative i (partial_derivative i W) x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `wan_test s (wan_dpart i (phi:real^2->real)) /\
                  wan_test s (wan_dpart i (wan_dpart i phi))` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[WAN_TEST_DPART_OPEN]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^2->bool`; `\x:real^2. drop((W:real^2->real^1) x)`;
                     `wan_dpart i (wan_dpart i (phi:real^2->real))`]
            WANL_PT_TEST_MUL_INTEGRABLE) THEN
      ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`s:real^2->bool`;
                     `\x:real^2. drop(partial_derivative i (partial_derivative i (W:real^2->real^1)) x)`;
                     `phi:real^2->real`] WANL_PT_TEST_MUL_INTEGRABLE) THEN
      ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN ANTS_TAC THENL
       [MATCH_MP_TAC WAN_CONTINUOUS_ON_LLOC THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `wan_wpd s i (W:real^2->real^1) (\x. partial_derivative i W x) /\
      wan_wpd s i (partial_derivative i W)
                  (\x. partial_derivative i (partial_derivative i W) x)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC WAN_WPD_C1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[wan_wpd] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (MP_TAC o SPEC `wan_dpart i (phi:real^2->real)` o CONJUNCT2 o CONJUNCT2)
      (MP_TAC o SPEC `phi:real^2->real` o CONJUNCT2 o CONJUNCT2)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[VECTOR_NEG_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s (\x. lift(w x * llap (\y:real^2. mat 1) phi x)) =
    integral s (\x. wan_dpart 1 (wan_dpart 1 phi) x % (W:real^2->real^1) x +
                    wan_dpart 2 (wan_dpart 2 phi) x % W x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[WANL_PT_LLAP2] THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM((fun th -> MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `1` th)) o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "integrable_on")) (concl th))) THEN
  REWRITE_TAC[ARITH] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[INTEGRAL_ADD] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `integral s (\x. phi x % partial_derivative 1 (partial_derivative 1 W) x +
                              phi x % partial_derivative 2 (partial_derivative 2
                                        (W:real^2->real^1)) x)` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(x:real^2) IN s`))]) o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "llap"))
                         (concl th) && is_forall(concl th))) THEN
  REWRITE_TAC[WANL_PT_LLAP_FLAT0; DIMINDEX_2; SUM_2] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM VECTOR_ADD_LDISTRIB; LIFT_ADD; LIFT_DROP] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL; LIFT_ADD; LIFT_DROP]);;

let WANL_PT_VW_DERIV = prove
 (`!(s:real^2->bool) (w:real^2->real) (f:real^2->real) i.
     open s /\ 1 <= i /\ i <= 2 /\
     continuously_differentiable 2 s (\x. lift(w x)) /\
     continuously_differentiable 1 s (\x. lift(f x)) /\
     (!x. x IN s ==> llap (\y. mat 1) w x = f x)
     ==> !phi. wan_test s phi
               ==> integral s (\x. lift(drop(partial_derivative i (\y. lift(w y)) x) *
                                      llap (\y:real^2. mat 1) phi x)) =
                   integral s (\x. lift(drop(partial_derivative i (\y. lift(f y)) x) * phi x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `phi:real^2->real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `wan_test s (llap (\y. mat 1) phi) /\ wan_test s (wan_dpart i phi) /\
                wan_test (:real^2) phi` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[WANL_PT_TEST_LLAP; WAN_TEST_DPART_OPEN] THEN
    MATCH_MP_TAC WAN_TEST_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_wpd s i (\x. lift(w x)) (\x. partial_derivative i (\y. lift((w:real^2->real) y)) x) /\
    wan_wpd s i (\x. lift(f x)) (\x. partial_derivative i (\y. lift((f:real^2->real) y)) x)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_WPD_C1 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[wan_wpd] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (MP_TAC o SPEC `llap (\y:real^2. mat 1) phi` o CONJUNCT2 o CONJUNCT2)
    (MP_TAC o SPEC `phi:real^2->real` o CONJUNCT2 o CONJUNCT2)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `w:real^2->real`; `f:real^2->real`] WANL_PT_C2_VERY_WEAK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `wan_dpart i (phi:real^2->real)`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(drop(partial_derivative i (\y. lift(w y)) x) * llap (\y:real^2. mat 1) phi x)) =
    (\x. llap (\y. mat 1) phi x % partial_derivative i (\y. lift((w:real^2->real) y)) x) /\
    (\x. lift(drop(partial_derivative i (\y. lift(f y)) x) * phi x)) =
    (\x. phi x % partial_derivative i (\y. lift((f:real^2->real) y)) x) /\
    (\x. lift(w x * llap (\y:real^2. mat 1) (wan_dpart i phi) x)) =
    (\x. wan_dpart i (llap (\y. mat 1) phi) x % lift((w:real^2->real) x)) /\
    (\x. lift(f x * wan_dpart i phi x)) = (\x. wan_dpart i phi x % lift((f:real^2->real) x))`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT CONJ_TAC THEN X_GEN_TAC `x:real^2` THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL; LIFT_DROP];
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL; LIFT_DROP];
      ASM_SIMP_TAC[WANL_PT_DPART_LLAP] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[LIFT_CMUL];
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
     not(can (find_term (fun t -> t = `(--):real^1->real^1`)) (concl th)))) THEN
  ASM_REWRITE_TAC[VECTOR_EQ_NEG2]);;

(* ------------------------------------------------------------------------- *)
(* The mean value step: wan_ckal (k+1) on a ball of radius r gives          *)
(* wan_ckal k with constant 2 N A (N = dimension).                           *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_PARTIALS_ONORM = prove
 (`!(g:real^N->real^K) x B.
     g differentiable at x /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> norm(partial_derivative j g x) <= B)
     ==> onorm(frechet_derivative g (at x)) <= &(dimindex(:N)) * B`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o MATCH_MP ONORM) THEN
  X_GEN_TAC `h:real^N` THEN ASM_SIMP_TAC[WANL_PT_FRECHET_PARTIALS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\j. norm(h:real^N) * B)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[COMPONENT_LE_NORM; REAL_ABS_POS; NORM_POS_LE];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC]);;

let WANL_PT_LIP_HOLDER = prove
 (`!d r al. &0 <= d /\ d <= &2 * r /\ &0 < al /\ al < &1 /\ &0 < r
            ==> d <= &2 * r rpow (&1 - al) * d rpow al`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `d = &0` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d = d rpow (&1 - al) * d rpow al` (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
   [ASM_SIMP_TAC[GSYM RPOW_ADD] THEN REWRITE_TAC[REAL_ARITH `(&1 - al) + al = &1`] THEN
    REWRITE_TAC[RPOW_POW; REAL_POW_1];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * r) rpow (&1 - al)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_MUL; REAL_POS; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 rpow &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL]]);;

let WANL_PT_CKAL_DOWN = prove
 (`!(a:real^N) r k al (f:real^N->real^K) A.
     &0 < r /\ &0 < al /\ al < &1 /\ &0 <= A /\
     continuously_differentiable (SUC k) (ball(a,r)) f /\
     wan_ckal (ball(a,r)) (SUC k) al r f A
     ==> wan_ckal (ball(a,r)) k al r f (&2 * &(dimindex(:N)) * A)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `A <= &2 * &(dimindex(:N)) * A` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&1 * A <= (&2 * &(dimindex(:N))) * A` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `wan_ckal (ball(a:real^N,r)) (SUC k) al r (f:real^N->real^K) A` THEN
  REWRITE_TAC[wan_ckal] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A:real` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`l:(num)list`; `x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  ABBREV_TAC `G = iterated_partial l (f:real^N->real^K)` THEN
  SUBGOAL_THEN `!z. z IN ball(a:real^N,r) ==> (G:real^N->real^K) differentiable at z`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`l:(num)list`; `SUC k`; `ball(a:real^N,r)`; `f:real^N->real^K`]
                  WANL_PT_ITP_CD) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `SUC k - k = SUC 0`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON) THEN
    SIMP_TAC[DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z j. z IN ball(a:real^N,r) /\ 1 <= j /\ j <= dimindex(:N)
          ==> norm(partial_derivative j (G:real^N->real^K) z) <= A / r pow (SUC k)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN SUBGOAL_THEN `&0 < r pow (SUC k)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[GSYM(CONJUNCT2 iterated_partial)] THEN
    SUBGOAL_THEN `SUC k = LENGTH(CONS j (l:(num)list))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[LENGTH]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      not(can (find_term (fun t -> t = `rpow`)) (concl th)) && is_forall(concl th) &&
      can (find_term (fun t -> t = `LENGTH:(num)list->num`)) (concl th))) THEN
    ASM_REWRITE_TAC[ALL; LENGTH; LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^N->real^K`; `\z. frechet_derivative (G:real^N->real^K) (at z)`;
                 `ball(a:real^N,r)`; `&(dimindex(:N)) * A / r pow (SUC k)`]
                DIFFERENTIABLE_BOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_BALL] THEN CONJ_TAC THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      MATCH_MP_TAC WANL_PT_PARTIALS_ONORM THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(x - y:real^N) <= &2 * r` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN ball(a,r)` THEN UNDISCH_TAC `(y:real^N) IN ball(a,r)` THEN
    REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(ISPECL [`x - a:real^N`; `a - y:real^N`] NORM_TRIANGLE) THEN
    REWRITE_TAC[VECTOR_ARITH `(x - a) + (a - y):real^N = x - y`] THEN
    REWRITE_TAC[NORM_SUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`norm(x - y:real^N)`; `r:real`; `al:real`] WANL_PT_LIP_HOLDER) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  ABBREV_TAC `D = norm(x - y:real^N) rpow al` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r rpow (&k + al) /\ &0 < r pow (SUC k) /\ &0 < r rpow (&1 - al)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT; REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `r rpow (&k + al) * r rpow (&1 - al) = r pow (SUC k)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM RPOW_ADD; GSYM RPOW_POW] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `N = &(dimindex(:N))` THEN
  SUBGOAL_THEN `&0 <= N` ASSUME_TAC THENL [EXPAND_TAC "N" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `r rpow (&k + al) * (N * A / r pow SUC k) * &2 * r rpow (&1 - al) * D` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(N * A / r pow SUC k) * norm(x - y:real^N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  UNDISCH_TAC `r rpow (&k + al) * r rpow (&1 - al) = r pow (SUC k)` THEN
  UNDISCH_TAC `&0 < r pow (SUC k)` THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* wan_ckal under equality on an open set and under enlarging the radius;   *)
(* the theta-form predicate, its base case k = 0, the constants and the     *)
(* hypotheses for the derivatives in the induction step.                     *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_CKAL_EQ_OPEN = prove
 (`!(s:real^N->bool) k al r (f:real^N->real^K) g A.
     open s /\ (!x. x IN s ==> f x = g x) /\ wan_ckal s k al r f A
     ==> wan_ckal s k al r g A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!l x. x IN s ==> iterated_partial l (g:real^N->real^K) x =
                                 iterated_partial l f x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WANL_PT_ITP_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `wan_ckal s k al r (f:real^N->real^K) A` THEN
  REWRITE_TAC[wan_ckal] THEN ASM_SIMP_TAC[]);;

let WANL_PT_CKAL_RADIUS_UP = prove
 (`!(s:real^N->bool) m al r1 r c (f:real^N->real^K) B.
     &0 < r1 /\ r1 <= r /\ r <= c * r1 /\ &0 <= B /\ &0 <= al /\ al < &1 /\
     wan_ckal s m al r1 f B
     ==> wan_ckal s m al r f (c pow (m + 1) * B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= c` ASSUME_TAC THENL
   [SUBGOAL_THEN `r1 * &1 <= r1 * c` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!e. &0 <= e /\ e <= &m + &1
                    ==> r rpow e <= c pow (m + 1) * r1 rpow e` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(c * r1) rpow e` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RPOW_MUL; REAL_LT_IMP_LE; REAL_ARITH `&1 <= c ==> &0 <= c`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[GSYM RPOW_POW; GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `wan_ckal s m al r1 (f:real^N->real^K) B` THEN
  REWRITE_TAC[wan_ckal] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:(num)list`; `x:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(c pow (m + 1) * r1 pow LENGTH(l:(num)list)) *
                norm(iterated_partial l (f:real^N->real^K) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      SUBGOAL_THEN `r pow LENGTH(l:(num)list) = r rpow &(LENGTH l) /\
                    r1 pow LENGTH(l:(num)list) = r1 rpow &(LENGTH l)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL [REWRITE_TAC[RPOW_POW]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[REAL_POS] THEN UNDISCH_TAC `LENGTH(l:(num)list) <= m` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_ARITH `&1 <= c ==> &0 <= c`]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`l:(num)list`; `x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(c pow (m + 1) * r1 rpow (&m + al)) *
              norm(iterated_partial l (f:real^N->real^K) x - iterated_partial l f y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_ARITH `&1 <= c ==> &0 <= c`]]);;

let wanl_pt_schp = new_definition
 `wanl_pt_schp k al th C <=>
    !(a:real^2) r (u:real^2->real) (f:real^2->real) U A.
       &0 < r /\ &0 <= U /\ &0 <= A /\
       (\x. lift(u x)) measurable_on ball(a,r) /\
       (!x. x IN ball(a,r) ==> abs(u x) <= U) /\
       continuously_differentiable k (ball(a,r)) (\x. lift(f x)) /\
       wan_ckal (ball(a,r)) k al r (\x. lift(f x)) A /\
       (!phi. wan_test (ball(a,r)) phi
              ==> integral (ball(a,r)) (\x. lift(u x * llap (\y:real^2. mat 1) phi x)) =
                  integral (ball(a,r)) (\x. lift(f x * phi x)))
       ==> ?w. continuously_differentiable (k + 2) (ball(a,th * r)) (\x. lift(w x)) /\
               negligible {x | x IN ball(a,th * r) /\ ~(u x = w x)} /\
               wan_ckal (ball(a,th * r)) (k + 2) al r (\x. lift(w x))
                        (C * (r pow 2 * A + U)) /\
               (!x. x IN ball(a,th * r) ==> llap (\y. mat 1) w x = f x)`;;

let WANL_PT_SCHK_BASE = prove
 (`!al th. &0 < al /\ al < &1 /\ &0 < th /\ th < &1
           ==> ?C. &0 < C /\ wanl_pt_schp 0 al th C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`al:real`; `th:real`] WANL_PT_SCH0) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sch"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[wanl_pt_schp; ADD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real`; `f:real^2->real`;
                       `U:real`; `A:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[wan_ckal] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_ckal")) (concl th) &&
    not(can (find_term (fun t -> t = `w:real^2->real`)) (concl th)) &&
    not(is_forall(concl th)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SPEC `[]:(num)list`)
                             (ASSUME_TAC o SPEC `[]:(num)list`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; ALL; iterated_partial; real_pow; REAL_MUL_LID;
                              NORM_LIFT; REAL_ADD_LID; GSYM LIFT_SUB; LE_REFL]) THEN
  SUBGOAL_THEN `(\x. lift((f:real^2->real) x)) measurable_on ball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
    ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_0];
    ALL_TAC] THEN
  USE_THEN "sch" MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

let WANL_PT_SCHK_CONST = prove
 (`!Ca Cb th1 k r U A.
     &0 < Ca /\ &0 < Cb /\ &0 < th1 /\ th1 < &1 /\ &0 < r /\ &0 <= U /\ &0 <= A
     ==> Ca * (r pow 2 * (&4 * A) + U) +
         r * ((&1 / th1) pow (k + 3) * Cb *
              ((th1 * r) pow 2 * (A / r) + (Ca * (r pow 2 * (&4 * A) + U)) / r))
         <= (&4 * Ca + (&1 / th1) pow (k + 3) * Cb * (&1 + &4 * Ca)) * (r pow 2 * A + U)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = (&1 / th1) pow (k + 3)` THEN
  SUBGOAL_THEN `&0 <= P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `W = r pow 2 * A + U` THEN
  SUBGOAL_THEN `&0 <= r pow 2 * A /\ &0 <= W` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Ca * (r pow 2 * (&4 * A) + U) <= &4 * Ca * W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN
    SUBGOAL_THEN `Ca * U <= Ca * (&4 * U)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(th1 * r) pow 2 * (A / r) * r <= r pow 2 * A` ASSUME_TAC THENL
   [SUBGOAL_THEN `(th1 * r) pow 2 * (A / r) * r = th1 pow 2 * (r pow 2 * A)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `r * (P * Cb * ((th1 * r) pow 2 * (A / r) + (Ca * (r pow 2 * (&4 * A) + U)) / r)) =
    P * Cb * ((th1 * r) pow 2 * (A / r) * r + Ca * (r pow 2 * (&4 * A) + U))`
  SUBST1_TAC THENL [UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `P * Cb * ((th1 * r) pow 2 * (A / r) * r + Ca * (r pow 2 * (&4 * A) + U)) <=
    P * Cb * (W + &4 * Ca * W)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&4 * Ca + P * Cb * (&1 + &4 * Ca)) * W =
                &4 * Ca * W + P * Cb * (W + &4 * Ca * W)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let WANL_PT_SCHK_DHYPS = prove
 (`!k al (a:real^2) r th1 (w:real^2->real) (f:real^2->real) A Bw i.
     &0 < r /\ &0 < th1 /\ th1 < &1 /\ &0 <= A /\ &0 < al /\ al < &1 /\
     1 <= i /\ i <= 2 /\
     continuously_differentiable (SUC k) (ball(a,r)) (\x. lift(f x)) /\
     wan_ckal (ball(a,r)) (SUC k) al r (\x. lift(f x)) A /\
     continuously_differentiable (k + 2) (ball(a,th1 * r)) (\x. lift(w x)) /\
     wan_ckal (ball(a,th1 * r)) (k + 2) al r (\x. lift(w x)) Bw /\
     (!x. x IN ball(a,th1 * r) ==> llap (\y. mat 1) w x = f x)
     ==> &0 < th1 * r /\ &0 <= Bw / r /\ &0 <= A / r /\
         partial_derivative i (\y. lift(w y)) continuous_on ball(a,th1 * r) /\
         partial_derivative i (\y. lift(w y)) measurable_on ball(a,th1 * r) /\
         (!x. x IN ball(a,th1 * r)
              ==> abs(drop(partial_derivative i (\y. lift(w y)) x)) <= Bw / r) /\
         continuously_differentiable k (ball(a,th1 * r))
           (partial_derivative i (\y. lift(f y))) /\
         wan_ckal (ball(a,th1 * r)) k al (th1 * r)
           (partial_derivative i (\y. lift(f y))) (A / r) /\
         (!phi. wan_test (ball(a,th1 * r)) phi
                ==> integral (ball(a,th1 * r))
                      (\x. lift(drop(partial_derivative i (\y. lift(w y)) x) *
                                llap (\y:real^2. mat 1) phi x)) =
                    integral (ball(a,th1 * r))
                      (\x. lift(drop(partial_derivative i (\y. lift(f y)) x) * phi x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < th1 * r /\ th1 * r <= r` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,th1 * r) SUBSET ball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Bw` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [wan_ckal] o check (fun th ->
      can (find_term (fun t -> t = `w:real^2->real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_ckal")) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPECL [`[]:(num)list`; `a:real^2`]) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; LENGTH; ALL; LE_0; real_pow; REAL_MUL_LID;
                    iterated_partial] THEN
    MP_TAC(ISPEC `lift((w:real^2->real) a)` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN
   `continuously_differentiable (k + 1) (ball(a:real^2,th1 * r))
      (partial_derivative i (\y. lift((w:real^2->real) y)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`[i:num]`; `k + 2`; `ball(a:real^2,th1 * r)`;
                   `\y. lift((w:real^2->real) y)`] WANL_PT_ITP_CD) THEN
    ASM_REWRITE_TAC[OPEN_BALL; LENGTH; iterated_partial] THEN
    REWRITE_TAC[ARITH_RULE `(k + 2) - SUC 0 = k + 1`; ARITH_RULE `SUC 0 <= k + 2`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `partial_derivative i (\y. lift((w:real^2->real) y)) continuous_on ball(a,th1 * r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    EXISTS_TAC `k + 1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [wan_ckal] o check (fun th ->
      can (find_term (fun t -> t = `w:real^2->real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_ckal")) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPECL [`[i:num]`; `x:real^2`]) THEN
    ASM_REWRITE_TAC[LENGTH; ALL; DIMINDEX_2; iterated_partial; real_pow; REAL_MUL_RID] THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NORM_1] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`[i:num]`; `SUC k`; `ball(a:real^2,r)`;
                   `\y. lift((f:real^2->real) y)`] WANL_PT_ITP_CD) THEN
    ASM_REWRITE_TAC[OPEN_BALL; LENGTH; iterated_partial] THEN
    REWRITE_TAC[ARITH_RULE `SUC k - SUC 0 = k`; ARITH_RULE `SUC 0 <= SUC k`] THEN
    DISCH_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `ball(a:real^2,r)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WANL_PT_CKAL_RADIUS THEN EXISTS_TAC `r:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC WANL_PT_CKAL_SUBSET THEN
    EXISTS_TAC `ball(a:real^2,r)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WANL_PT_CKAL_DERIV THEN ASM_REWRITE_TAC[DIMINDEX_2];
    MATCH_MP_TAC WANL_PT_VW_DERIV THEN ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN EXISTS_TAC `k + 2` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
      EXISTS_TAC `ball(a:real^2,r)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN EXISTS_TAC `SUC k` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC]]);;


(* ------------------------------------------------------------------------- *)
(* The induction step (apply the k-case to w, then to the derivatives d_i w *)
(* on the intermediate ball), the induction on k, and WAN_SCHAUDER_2D.       *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_SCHK_STEP = prove
 (`!k. (!al th. &0 < al /\ al < &1 /\ &0 < th /\ th < &1
                ==> ?C. &0 < C /\ wanl_pt_schp k al th C)
       ==> (!al th. &0 < al /\ al < &1 /\ &0 < th /\ th < &1
                    ==> ?C. &0 < C /\ wanl_pt_schp (SUC k) al th C)`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `th1 = (&1 + th) / &2` THEN
  SUBGOAL_THEN `&0 < th1 /\ th1 < &1 /\ th < th1 /\ &0 < th / th1 /\ th / th1 < &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "th1" THEN
    SUBGOAL_THEN `&0 < (&1 + th) / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPECL [`al:real`; `th1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ca:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[wanl_pt_schp] THEN DISCH_THEN(LABEL_TAC "pa") THEN
  USE_THEN "ih" (MP_TAC o SPECL [`al:real`; `th / th1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cb:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[wanl_pt_schp] THEN DISCH_THEN(LABEL_TAC "pb") THEN
  EXISTS_TAC `&4 * Ca + (&1 / th1) pow (k + 3) * Cb * (&1 + &4 * Ca)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> &0 < a + b`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[wanl_pt_schp] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real`; `f:real^2->real`;
                       `U:real`; `A:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `continuously_differentiable k (ball(a:real^2,r)) (\x. lift((f:real^2->real) x)) /\
    wan_ckal (ball(a,r)) k al r (\x. lift(f x)) (&4 * A)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN EXISTS_TAC `SUC k` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MP_TAC(ISPECL [`a:real^2`; `r:real`; `k:num`; `al:real`;
                     `\x:real^2. lift((f:real^2->real) x)`; `A:real`] WANL_PT_CKAL_DOWN) THEN
      ASM_REWRITE_TAC[DIMINDEX_2] THEN REWRITE_TAC[REAL_ARITH `&2 * &2 * A = &4 * A`]];
    ALL_TAC] THEN
  USE_THEN "pa" (MP_TAC o SPECL [`a:real^2`; `r:real`; `u:real^2->real`; `f:real^2->real`;
                                 `U:real`; `&4 * A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Bw = Ca * (r pow 2 * (&4 * A) + U)` THEN
  SUBGOAL_THEN `th / th1 * (th1 * r) = th * r` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < th1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,th * r) SUBSET ball(a,th1 * r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> ?v. continuously_differentiable (k + 2) (ball(a:real^2,th * r)) (\x. lift(v x)) /\
                (!x. x IN ball(a,th * r)
                     ==> partial_derivative i (\y. lift((w:real^2->real) y)) x = lift(v x)) /\
                wan_ckal (ball(a,th * r)) (k + 2) al (th1 * r) (\x. lift(v x))
                         (Cb * ((th1 * r) pow 2 * (A / r) + Bw / r))`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`k:num`; `al:real`; `a:real^2`; `r:real`; `th1:real`; `w:real^2->real`;
                  `f:real^2->real`; `A:real`; `Bw:real`; `i:num`] WANL_PT_SCHK_DHYPS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "pb" (MP_TAC o SPECL [`a:real^2`; `th1 * r`;
        `\x. drop(partial_derivative i (\y. lift((w:real^2->real) y)) x)`;
        `\x. drop(partial_derivative i (\y. lift((f:real^2->real) y)) x)`;
        `Bw / r`; `A / r`]) THEN
    REWRITE_TAC[LIFT_DROP; ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^2->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^2->real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_CONT_AE_EQ_OPEN THEN REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,th1 * r)` THEN
      ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
      EXISTS_TAC `k + 2` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
        is_const t && fst(dest_const t) = "negligible")) (concl th) &&
        can (find_term (fun t -> t = `v:real^2->real`)) (concl th))) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:num->real^2->real` (LABEL_TAC "V")) THEN
  ABBREV_TAC `Bv = Cb * ((th1 * r) pow 2 * (A / r) + Bw / r)` THEN
  SUBGOAL_THEN `&0 <= Bw /\ &0 <= Bv /\ &0 < th1 * r /\ th1 * r <= r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Bv"; "Bw"] THEN
    SUBGOAL_THEN `&0 <= Ca * (r pow 2 * (&4 * A) + U)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2]) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `w:real^2->real` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `SUC k + 2 = SUC(k + 2)`] THEN
    MATCH_MP_TAC WANL_PT_CD_SUC_PARTIALS THEN REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k + 1`; `ball(a:real^2,th1 * r)`; `\x. lift((w:real^2->real) x)`]
                    CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON) THEN
      ASM_REWRITE_TAC[ARITH_RULE `SUC(k + 1) = k + 2`] THEN
      SIMP_TAC[DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT; OPEN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "V" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
    EXISTS_TAC `\x. lift((V:num->real^2->real) i x)` THEN
    ASM_SIMP_TAC[OPEN_BALL];
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x | x IN ball(a:real^2,th1 * r) /\ ~((u:real^2->real) x = w x)}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC;
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[SUBSET]] THEN
  MATCH_MP_TAC WANL_PT_CKAL_MONO THEN
  EXISTS_TAC `Bw + r * ((&1 / th1) pow (k + 3) * Bv)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY EXPAND_TAC ["Bv"; "Bw"] THEN MATCH_MP_TAC WANL_PT_SCHK_CONST THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[ARITH_RULE `SUC k + 2 = SUC(k + 2)`] THEN
  MATCH_MP_TAC WANL_PT_CKAL_LIFT THEN ASM_REWRITE_TAC[DIMINDEX_2] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`[]:(num)list`; `x:real^2`] o CONJUNCT1 o
      GEN_REWRITE_RULE I [wan_ckal] o check (fun th ->
        can (find_term (fun t -> t = `Bw:real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_ckal")) (concl th))) THEN
    REWRITE_TAC[LENGTH; ALL; LE_0; real_pow; REAL_MUL_LID; iterated_partial] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "V" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC WANL_PT_CKAL_EQ_OPEN THEN
    EXISTS_TAC `\x. lift((V:num->real^2->real) i x)` THEN
    ASM_SIMP_TAC[OPEN_BALL] THEN
    REWRITE_TAC[ARITH_RULE `k + 3 = (k + 2) + 1`] THEN
    MATCH_MP_TAC WANL_PT_CKAL_RADIUS_UP THEN EXISTS_TAC `th1 * r` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < th1` THEN CONV_TAC REAL_FIELD]);;

let WANL_PT_SCHK = prove
 (`!k al th. &0 < al /\ al < &1 /\ &0 < th /\ th < &1
             ==> ?C. &0 < C /\ wanl_pt_schp k al th C`,
  INDUCT_TAC THENL
   [REWRITE_TAC[WANL_PT_SCHK_BASE];
    MATCH_MP_TAC WANL_PT_SCHK_STEP THEN FIRST_ASSUM ACCEPT_TAC]);;

let WAN_SCHAUDER_2D = prove
 (`WAN_SCHAUDER_2D_STATEMENT`,
  REWRITE_TAC[WAN_SCHAUDER_2D_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `al:real`; `&1 / &2`] WANL_PT_SCHK) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[wanl_pt_schp] THEN DISCH_THEN(LABEL_TAC "sch") THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real`; `f:real^2->real`;
                       `A:real`; `U:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= U /\ &0 <= A` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((u:real^2->real) a)` THEN
      REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL];
      FIRST_ASSUM(MP_TAC o SPECL [`[]:(num)list`; `a:real^2`] o CONJUNCT1 o
        GEN_REWRITE_RULE I [wan_ckal] o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_ckal")) (concl th))) THEN
      ASM_REWRITE_TAC[LENGTH; ALL; LE_0; real_pow; REAL_MUL_LID; iterated_partial;
                      CENTRE_IN_BALL] THEN
      MP_TAC(ISPEC `lift((f:real^2->real) a)` NORM_POS_LE) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((u:real^2->real) x)) measurable_on ball(a,r)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(a:real^2,r)`; `\x:real^2. lift(u x)`] WAN_W12_IMP_LSPACE) THEN
    ASM_REWRITE_TAC[lspace; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `u:real^2->real`; `f:real^2->real`] WANL_PT_VERY_WEAK) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_TAC THEN
  USE_THEN "sch" (MP_TAC o SPECL [`a:real^2`; `r:real`; `u:real^2->real`; `f:real^2->real`;
                                  `U:real`; `A:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 * r = r / &2` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]);;

