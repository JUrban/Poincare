(* ========================================================================= *)
(* pc_p2b_tube4: MT Thm 10.2, the bad-tube half, Part III: the generic       *)
(* assembly of a bad tube from a one-sided chain of 2 eps-necks with         *)
(* summable scales, boxes, the sign of the curvature and evolving necks (the *)
(* radial chart, the restricted view, the static clauses, the evolving necks *)
(* and their separating spheres), and the theorem P2BT_LIMIT_BAD_TUBE,       *)
(* conditional on the five limit-side statements of pc_p2b_tubelimst (proved *)
(* in pc_p2b_tubelim).  The route theorem P2BT_BAD_TUBE_ROUTE is in          *)
(* pc_p2b_tuberoute.                                                         *)
(* ========================================================================= *)

needs "src/pc_p2b_tube3.ml";;
needs "src/pc_apx_ncends.ml";;    (* APXN_CHAIN_UNION_OPEN *)
needs "src/pc_p2b_tubelimst.ml";; (* p2bt_lctx, P2BT_LIM_*_STATEMENT *)
needs "src/pc_vshi.ml";;          (* VSHI_LENGTH_RESTRICT *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* A radial diffeomorphism of annulus(1,2) onto the region r0 < |z|: the     *)
(* radius t goes to r0 + (t - 1)/(2 - t), with inverse u -> (2 (u - r0) +    *)
(* 1)/(u - r0 + 1).  The chart H of the bad tube is the chain chart E        *)
(* composed with it.                                                         *)
(* ========================================================================= *)

let p2bt_rad = new_definition
 `p2bt_rad (r0:real) (y:real^3) = ((r0 + (norm y - &1) / (&2 - norm y)) / norm y) % y`;;

let p2bt_radinv = new_definition
 `p2bt_radinv (r0:real) (z:real^3) =
    (((&2 * (norm z - r0) + &1) / (norm z - r0 + &1)) / norm z) % z`;;

let P2BT_OPEN_OUTSIDE = prove
 (`!r0. open {z:real^3 | r0 < norm z}`,
  GEN_TAC THEN
  SUBGOAL_THEN `{z:real^3 | r0 < norm z} = (:real^3) DIFF cball(vec 0,r0)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV; CLOSED_CBALL]]);;

(* The radius functions. *)

let P2BT_RAD_ALG = prove
 (`!r0 t. &1 < t /\ t < &2
          ==> &0 < (t - &1) / (&2 - t) /\
              (&2 * ((r0 + (t - &1) / (&2 - t)) - r0) + &1) /
              ((r0 + (t - &1) / (&2 - t)) - r0 + &1) = t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `(r0 + q) - r0 = q`] THEN
    UNDISCH_TAC `t < &2` THEN CONV_TAC REAL_FIELD]);;

let P2BT_RADINV_ALG = prove
 (`!r0 u. r0 < u
          ==> &1 < (&2 * (u - r0) + &1) / (u - r0 + &1) /\
              (&2 * (u - r0) + &1) / (u - r0 + &1) < &2 /\
              r0 + ((&2 * (u - r0) + &1) / (u - r0 + &1) - &1) /
                   (&2 - (&2 * (u - r0) + &1) / (u - r0 + &1)) = u`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < u - r0 + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < u - r0 + &1` THEN CONV_TAC REAL_FIELD);;

let P2BT_RAD_NORMS = prove
 (`!r0 y z:real^3.
     &0 < r0
     ==> (y IN annulus (&1) (&2)
          ==> norm(p2bt_rad r0 y) = r0 + (norm y - &1) / (&2 - norm y) /\
              r0 < norm(p2bt_rad r0 y) /\ p2bt_radinv r0 (p2bt_rad r0 y) = y) /\
         (r0 < norm z
          ==> norm(p2bt_radinv r0 z) = (&2 * (norm z - r0) + &1) / (norm z - r0 + &1) /\
              p2bt_radinv r0 z IN annulus (&1) (&2) /\ p2bt_rad r0 (p2bt_radinv r0 z) = z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`r0:real`; `norm(y:real^3)`] P2BT_RAD_ALG) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(p2bt_rad r0 (y:real^3)) = r0 + (norm y - &1) / (&2 - norm y)`
    ASSUME_TAC THENL
     [REWRITE_TAC[p2bt_rad; NORM_MUL] THEN
      SUBGOAL_THEN `&0 < (r0 + (norm(y:real^3) - &1) / (&2 - norm y)) / norm y`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
      UNDISCH_TAC `&1 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p2bt_radinv] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p2bt_rad; VECTOR_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `&0 < r0 + (norm(y:real^3) - &1) / (&2 - norm y) /\ &0 < norm y`
    MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    DISCH_TAC THEN
    MP_TAC(SPECL [`r0:real`; `norm(z:real^3)`] P2BT_RADINV_ALG) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(p2bt_radinv r0 (z:real^3)) =
                  (&2 * (norm z - r0) + &1) / (norm z - r0 + &1)`
    ASSUME_TAC THENL
     [REWRITE_TAC[p2bt_radinv; NORM_MUL] THEN
      SUBGOAL_THEN `&0 < ((&2 * (norm(z:real^3) - r0) + &1) / (norm z - r0 + &1)) / norm z`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
      SUBGOAL_THEN `&0 < norm(z:real^3)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    REWRITE_TAC[p2bt_rad] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p2bt_radinv; VECTOR_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `&0 < norm(z:real^3) /\ &0 < norm z - r0 + &1 /\
                  &0 < &2 * (norm z - r0) + &1`
    MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]);;

(* Smooth real functions (lifted) are closed under the field operations. *)

let P2BT_SM_LIFT = prove
 (`!s (f:real^N->real) g.
     open s /\ smooth_map_on s (\y. lift(f y)) /\ smooth_map_on s (\y. lift(g y))
     ==> smooth_map_on s (\y. lift(f y + g y)) /\
         smooth_map_on s (\y. lift(f y - g y)) /\
         smooth_map_on s (\y. lift(f y * g y)) /\
         ((!y. y IN s ==> ~(g y = &0)) ==> smooth_map_on s (\y. lift(f y / g y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift((f:real^N->real) y)`;
                   `\y:real^N. lift((g:real^N->real) y)`] SMOOTH_MAP_ON_LIFT_ADD);
    MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift((f:real^N->real) y)`;
                   `\y:real^N. lift((g:real^N->real) y)`] SMOOTH_MAP_ON_LIFT_SUB);
    MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift((f:real^N->real) y)`;
                   `\y:real^N. lift((g:real^N->real) y)`] SMOOTH_MAP_ON_LIFT_MUL);
    DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift((f:real^N->real) y)`;
                   `\y:real^N. lift((g:real^N->real) y)`] SMOOTH_MAP_ON_LIFT_DIV)] THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let P2BT_SM_LIFT_CONST = prove
 (`!s c. smooth_map_on (s:real^N->bool) (\y. lift c)`,
  REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let P2BT_SM_NORM = prove
 (`!s. s SUBSET {y:real^N | ~(y = vec 0)} ==> smooth_map_on s (\y. lift(norm y))`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `{y:real^N | ~(y = vec 0)}` THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_LIFT_NORM_NONZERO]);;

let P2BT_RAD_DIFFEO = prove
 (`!r0. &0 < r0
        ==> diffeomorphism_on (annulus (&1) (&2)) {z:real^3 | r0 < norm z}
                              (p2bt_rad r0) (p2bt_radinv r0)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  REWRITE_TAC[OPEN_ANNULUS; P2BT_OPEN_OUTSIDE] THEN
  SUBGOAL_THEN `annulus (&1) (&2) SUBSET {y:real^3 | ~(y = vec 0)} /\
                {z:real^3 | r0 < norm z} SUBSET {y:real^3 | ~(y = vec 0)}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMT_SUBSET_NONZERO_ANNULUS THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `r0 < norm(vec 0:real^3)` THEN REWRITE_TAC[NORM_0] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `p2bt_rad r0 =
      (\y:real^3. drop(lift((r0 + (norm y - &1) / (&2 - norm y)) / norm y)) % y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2bt_rad; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    REWRITE_TAC[OPEN_ANNULUS; SMOOTH_MAP_ON_ID] THEN
    ABBREV_TAC `s = annulus (&1) (&2):real^3->bool` THEN
    SUBGOAL_THEN `open (s:real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN REWRITE_TAC[OPEN_ANNULUS]; ALL_TAC] THEN
    SUBGOAL_THEN `!y:real^3. y IN s ==> &1 < norm y /\ norm y < &2` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN SIMP_TAC[annulus; IN_ELIM_THM]; ALL_TAC] THEN
    MP_TAC(ISPEC `s:real^3->bool` P2BT_SM_NORM) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`s:real^3->bool`; `\y:real^3. norm y`; `\y:real^3. &1`] P2BT_SM_LIFT)) THEN
    ASM_REWRITE_TAC[P2BT_SM_LIFT_CONST] THEN STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`s:real^3->bool`; `\y:real^3. &2`; `\y:real^3. norm y`] P2BT_SM_LIFT)) THEN
    ASM_REWRITE_TAC[P2BT_SM_LIFT_CONST] THEN STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`s:real^3->bool`; `\y:real^3. norm y - &1`; `\y:real^3. &2 - norm y`]
      P2BT_SM_LIFT)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL [`s:real^3->bool`; `\y:real^3. (r0:real)`;
                   `\y:real^3. (norm y - &1) / (&2 - norm y)`] P2BT_SM_LIFT)) THEN
    ASM_REWRITE_TAC[P2BT_SM_LIFT_CONST] THEN STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`s:real^3->bool`; `\y:real^3. (r0:real) + (norm y - &1) / (&2 - norm y)`;
                   `\y:real^3. norm y`] P2BT_SM_LIFT)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      REAL_ARITH_TAC;
      SIMP_TAC[]];
    SUBGOAL_THEN
     `p2bt_radinv r0 =
      (\z:real^3. drop(lift(((&2 * (norm z - r0) + &1) / (norm z - r0 + &1)) / norm z)) % z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2bt_radinv; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    REWRITE_TAC[P2BT_OPEN_OUTSIDE; SMOOTH_MAP_ON_ID] THEN
    ABBREV_TAC `s = {z:real^3 | r0 < norm z}` THEN
    SUBGOAL_THEN `open (s:real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN REWRITE_TAC[P2BT_OPEN_OUTSIDE]; ALL_TAC] THEN
    SUBGOAL_THEN `!z:real^3. z IN s ==> r0 < norm z` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    MP_TAC(ISPEC `s:real^3->bool` P2BT_SM_NORM) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`s:real^3->bool`; `\z:real^3. norm z`; `\z:real^3. (r0:real)`] P2BT_SM_LIFT)) THEN
    ASM_REWRITE_TAC[P2BT_SM_LIFT_CONST] THEN STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`s:real^3->bool`; `\z:real^3. &2`; `\z:real^3. norm z - (r0:real)`]
      P2BT_SM_LIFT)) THEN
    ASM_REWRITE_TAC[P2BT_SM_LIFT_CONST] THEN STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`s:real^3->bool`; `\z:real^3. &2 * (norm z - (r0:real))`; `\z:real^3. &1`]
      P2BT_SM_LIFT)) THEN
    ASM_REWRITE_TAC[P2BT_SM_LIFT_CONST] THEN STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`s:real^3->bool`; `\z:real^3. norm z - (r0:real)`; `\z:real^3. &1`]
      P2BT_SM_LIFT)) THEN
    ASM_REWRITE_TAC[P2BT_SM_LIFT_CONST] THEN STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`s:real^3->bool`; `\z:real^3. &2 * (norm z - (r0:real)) + &1`;
                   `\z:real^3. norm z - (r0:real) + &1`] P2BT_SM_LIFT)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL [`s:real^3->bool`; `\z:real^3. (&2 * (norm z - (r0:real)) + &1) / (norm z - r0 + &1)`;
                   `\z:real^3. norm z`] P2BT_SM_LIFT)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r0:real`; `y:real^3`; `y:real^3`] P2BT_RAD_NORMS) THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r0:real`; `z:real^3`; `z:real^3`] P2BT_RAD_NORMS) THEN
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Copies of small restriction lemmas from units outside the load closure of *)
(* this unit, renamed with the P2BT_ prefix; each block names its source.    *)
(* Used for the restricted view p2bt_rview and the curves of the tube T.     *)
(* ========================================================================= *)

(* Copy of P2CO_FD_LOCAL (pc_p2c_lrestrict.ml). *)

let P2BT_FD_LOCAL = prove
 (`!(f:real^N->real^M) g O z.
     open O /\ z IN O /\ (!w. w IN O ==> f w = g w)
     ==> frechet_derivative f (at z) = frechet_derivative g (at z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frechet_derivative] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f':real^N->real^M` THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [open_def]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THENL
   [MAP_EVERY EXISTS_TAC [`f:real^N->real^M`; `d:real`];
    MAP_EVERY EXISTS_TAC [`g:real^N->real^M`; `d:real`]] THEN
  ASM_SIMP_TAC[]);;

(* Copy of P2CE_MPULLBACK_ID (pc_p2c_cgemb.ml). *)

let P2BT_MPULLBACK_ID = prove
 (`!(G:real^N->real^N^N). mpullback (\z. z) G = G`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; mpullback] THEN X_GEN_TAC `y:real^N` THEN
  MP_TAC(ISPEC `at (y:real^N)` HAS_DERIVATIVE_ID) THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

(* Copy of P2CO_C1_CURVE_SUBTOP (pc_p2c_lrestrict.ml). *)

let P2BT_C1_CURVE_SUBTOP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (gamma:real->A) a b.
     mfd_c1_curve (top,atlas) gamma a b /\
     (!t. t IN real_interval[a,b] ==> gamma t IN W)
     ==> mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`UW:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN ASM_REWRITE_TAC[FST; SND] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `s:real^1` THEN
  ASM_CASES_TAC `(s:real^1) IN interval[lift a,lift b]` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) (drop s) IN W` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `(s:real^1) IN interval[lift a,lift b]` THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP]);;

(* Copy of P2GF_RESTRICT_METRIC_PT (pc_p2c_lcgf.ml). *)

let P2BT_RESTRICT_METRIC_PT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (g:A->real^N^N) g' x.
     smooth_manifold_atlas top atlas /\ open_in top W /\ x IN W /\ g' x = g x
     ==> restrict_metric atlas W g' x = restrict_metric atlas W g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[metric_local] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`] CHART_INV) THEN
  ASM_SIMP_TAC[]);;

(* Copy of P2GF_RESTRICT_METRIC_RESTRICT (pc_p2c_lcgf.ml). *)

let P2BT_RESTRICT_METRIC_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) Om W (G:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ open_in top Om /\ open_in top W /\
     W SUBSET Om /\ x IN W
     ==> restrict_metric (restrict_atlas atlas Om) W (restrict_metric atlas Om G) x =
         restrict_metric atlas W G x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology top Om) (W:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(ISPECL [`top:A topology`; `W:A->bool`] OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (Om:A->bool)`; `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) Om`;
                 `W:A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
  DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1")))))) THEN
  REWRITE_TAC[IN_RESTRICT_ATLAS] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:A) IN U INTER Om` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`; `Om:A->bool`; `G:A->real^N^N`; `x:A`] METRIC_LOCAL_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r2")))))) THEN
  USE_THEN "r2" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `phi2:A->real^N = phi` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `chart_at (restrict_atlas (restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) Om) W) x =
                 (U INTER Om) INTER W,(phi:A->real^N)` THEN
    REWRITE_TAC[RFS_RESTRICT_ATLAS_RESTRICT] THEN
    SUBGOAL_THEN `(Om:A->bool) INTER W = W` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`; `U2:A->bool`; `phi:A->real^N`; `G:A->real^N^N`; `x:A`]
                METRIC_LOCAL_TRANS) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `mpullback (chart_trans (U,phi) (U2,phi)) (metric_local atlas (U2,(phi:A->real^N)) (G:A->real^N^N))
              (phi x) =
    mpullback (\y. y) (metric_local atlas (U2,phi) G) (phi x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_LOCAL THEN EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                     `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
      REWRITE_TAC[chart_trans; SND] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                     `phi:A->real^N`] CHART_INV) THEN
      ASM_SIMP_TAC[]];
    REWRITE_TAC[P2BT_MPULLBACK_ID]]);;

(* Copy of P2GF_RFF_CONG (pc_p2c_lcgf.ml). *)

let P2BT_RFF_CONG = prove
 (`!top atlas a b (g:real->A->real^3^3) g'.
     ricci_flow_from (top,atlas) a b g /\
     (!t x. a <= t /\ t < b /\ x IN topspace top ==> g' t x = g t x)
     ==> ricci_flow_from (top,atlas) a b g'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_from] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "on") (CONJUNCTS_THEN2 (LABEL_TAC "ga") (LABEL_TAC "ext")))
    (LABEL_TAC "eq")) THEN
  USE_THEN "on" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CF_RFO_CONG THEN EXISTS_TAC `g:real->A->real^3^3` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REMOVE_THEN "eq" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC PDE_RIEMANNIAN_METRIC_CONG THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `(g:real->A->real^3^3) a`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    REMOVE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
    USE_THEN "ext" (fun th -> MP_TAC(MP (SPEC `c:(A->bool)#(A->real^3)` th)
                                        (ASSUME `(c:(A->bool)#(A->real^3)) IN atlas`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real`
      (X_CHOOSE_THEN `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`
        STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c:(A->bool)#(A->real^3)`; `(g:real->A->real^3^3) t`;
                   `(g':real->A->real^3^3) t`] PDE_METRIC_LOCAL_CONG) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      REMOVE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* Copy of P3H_RFS_PULLBACK_RESTRICT (pc_p3_c172c.ml). *)

let P2BT_RFS_PULLBACK_RESTRICT = prove
 (`!top atlas (h:A->real^3^3) W S (e:real^3->A) z.
     smooth_manifold_atlas top atlas /\ open_in top W /\ mfd_param top atlas S e /\
     IMAGE e S SUBSET W /\ z IN S
     ==> rfs_pullback (restrict_atlas atlas W) e (restrict_metric atlas W h) z =
         rfs_pullback atlas e h z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e:real^3->A) z IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                 `(e:real^3->A) z`] MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `h:A->real^3^3`;
                 `S:real^3->bool`; `e:real^3->A`; `U:A->bool`; `phi:A->real^3`; `z:real^3`]
                APX_RFS_PULLBACK_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[rfs_pullback] THEN ASM_REWRITE_TAC[SND] THEN
  REWRITE_TAC[mpullback; o_THM] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`; `W:A->bool`; `h:A->real^3^3`; `(e:real^3->A) z`]
                METRIC_LOCAL_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
  REFL_TAC);;

(* Copy of P2BK_PERSISTS_AT (pc_p2b_cone6.ml). *)

let P2BT_PERSISTS_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s.
     rfs_persists V W a b /\ a < s /\ s <= b
     ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
         open_in (rfs_vtop V s) W`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; rfs_vtop; rfs_vatlas] THEN MESON_TAC[]);;

(* Copy of P2BK_VIEW_PARAM_AT (pc_p2b_cone6.ml). *)

let P2BT_VIEW_PARAM_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a s (e:real^3->A) t.
     p2c_regular_view V /\ rfs_persists V W a (&0) /\ a < t /\ t <= &0 /\
     mfd_param (rfs_vtop V (&0)) (rfs_vatlas V (&0)) s e /\ IMAGE e s SUBSET W
     ==> mfd_param (rfs_vtop V t) (rfs_vatlas V t) s e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_diffeo (rfs_vtop V t) (rfs_vatlas V t) W
                           (rfs_vtop V (&0)) (rfs_vatlas V (&0)) W (\y:A. y) (\y. y)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_regular_view
                  (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3))` THEN
    REWRITE_TAC[p2c_regular_view] THEN DISCH_THEN(MP_TAC o el 3 o CONJUNCTS) THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (&0)`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t`;
                 `s:real^3->bool`; `e:real^3->A`; `W:A->bool`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`] MFD_PARAM_COMPOSE_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MFD_DIFFEO_SYM] THEN
    SUBGOAL_THEN `a < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[P2BT_PERSISTS_AT; REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]);;

(* ========================================================================= *)
(* The chain-chart data p2bt_cchart (a one-sided chain of 2 eps-necks and    *)
(* its chart E, the conclusion of P2BT_REQ_CHAIN_CHART at 2 eps), and its    *)
(* existence for small eps.                                                  *)
(* ========================================================================= *)

let p2bt_cchart = new_definition
 `p2bt_cchart (eps:real) (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
              (g:A->real^3^3) (x:int->A) (e:int->real^3->A) (E:real^3->A) <=>
    apx_chain (top,atlas) g (&2 * eps) {i:int | &0 <= i} x e /\
    mfd_param top atlas {y:real^3 | exp(--inv(&2 * eps) / sqrt(&2)) < norm y} E /\
    (!y. y IN apx_slab (--inv(&2 * eps)) (inv(&8 * (&2 * eps))) ==> E y = e (&0) y) /\
    IMAGE E {y:real^3 | exp(--inv(&2 * eps) / sqrt(&2)) < norm y} =
    apx_chain_union (&2 * eps) {i:int | &0 <= i} e /\
    (!n. ?rho. apx_chain_union (&2 * eps) {i:int | &0 <= i /\ i <= &n} e SUBSET
               IMAGE E (apx_slab (--inv(&2 * eps)) rho))`;;

(* The chart exists for small eps (P2BT_REQ_CHAIN_CHART_STATEMENT at 2 eps). *)

let P2BT_CCHART_EXISTS = prove
 (`!w:A->bool.
     P2BT_REQ_CHAIN_CHART_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !eps top atlas (g:A->real^3^3) x e.
              &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
              apx_chain (top,atlas) g (&2 * eps) {i:int | &0 <= i} x (e:int->real^3->A)
              ==> ?E. p2bt_cchart eps top atlas g x e E`,
  GEN_TAC THEN REWRITE_TAC[P2BT_REQ_CHAIN_CHART_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  EXISTS_TAC `e0 / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bt_cchart] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `&2 * eps`; `x:int->A`; `e:int->real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* ========================================================================= *)
(* Curvature along the chain.  Bounded partial sums of the scales            *)
(* R(x_i)^(-1/2) make R(x_i) tend to infinity; every point of the union lies *)
(* in a chain neck, where R is at least half the curvature of the centre.    *)
(* ========================================================================= *)

let P2BT_SUM_TO_INF = prove
 (`!(f:num->real) D.
     (!n. &0 <= f n) /\ (!n. sum(0..n) f <= D)
     ==> !d. &0 < d ==> ?N. !n. N <= n ==> f n < d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT]) THEN
  SUBGOAL_THEN `!m. ?N. &m * d <= sum(0..N) (f:num->real)` ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [EXISTS_TAC `0` THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(X_CHOOSE_TAC `N:num`) THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC o SPEC `N + 1`) THEN
      EXISTS_TAC `n:num` THEN
      SUBGOAL_THEN `sum(0..N) (f:num->real) + sum(N + 1..n) f = sum(0..n) f` (SUBST1_TAC o SYM)
      THENL [MATCH_MP_TAC SUM_COMBINE_R THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(f:num->real) n <= sum(N + 1..n) f` ASSUME_TAC THENL
       [SUBGOAL_THEN `n = SUC(n - 1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN
        SUBGOAL_THEN `N + 1 <= SUC(n - 1)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> b <= a + b`) THEN
        MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `d:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num` o SPEC `D:real`) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `N:num` o SPEC `m:num`) THEN
  UNDISCH_TAC `!n. sum(0..n) (f:num->real) <= D` THEN
  DISCH_THEN(MP_TAC o SPEC `N:num`) THEN ASM_REAL_ARITH_TAC);;

(* The chain curvature tends to infinity. *)

let P2BT_CHAIN_RINF = prove
 (`!top atlas (g:A->real^3^3) eps (x:int->A) e D.
     apx_chain (top,atlas) g eps {i:int | &0 <= i} x e /\
     (!n. sum(0..n) (\i. inv(sqrt(mfd_scalar atlas g (x(&i))))) <= D)
     ==> !B. ?N. !n. N <= n ==> B < mfd_scalar atlas g (x(&n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. &0 < mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&n))` ASSUME_TAC THENL
   [GEN_TAC THEN UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i} x e` THEN
    REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `&n:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[INT_POS] THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i. inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&i))))`; `D:real`]
    P2BT_SUM_TO_INF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[] THEN DISCH_TAC] THEN
  X_GEN_TAC `B:real` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(sqrt(max B (&1)))`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&n))` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [EXPAND_TAC "R" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(max B (&1)) < sqrt R` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `inv(sqrt(max B (&1))) <= inv(sqrt R)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= max B (&1) /\ &0 <= R` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_MONO_LT_EQ] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Distances inside a neck lying in an open set W, measured in the           *)
(* restricted manifold (the model path of APX_NECK_DIST_UPPER stays in the   *)
(* neck).                                                                    *)
(* ========================================================================= *)

let P2BT_NECK_DIST_SUB = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) W y z.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\ eps < &1 /\
     open_in top W /\ IMAGE e (rfs_neck_dom eps) SUBSET W /\
     y IN rfs_neck_dom eps /\ z IN rfs_neck_dom eps
     ==> mfd_joinable (subtopology top W,restrict_atlas atlas W) (e y) (e z) /\
         mfd_dist (subtopology top W,restrict_atlas atlas W) (restrict_metric atlas W g)
                  (e y) (e z) <=
         sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas g x)) *
         (abs(apx_sval y - apx_sval z) + sqrt(&2) * pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `y:real^3`; `z:real^3`] APX_MODEL_PATH) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[APX_NECK_DOM_OPEN] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN
    UNDISCH_TAC `(z:real^3) IN rfs_neck_dom eps` THEN
    REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                 `c:real->real^3`; `&0`; `&1`] APX_NECK_CURVE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_c1_curve (subtopology (top:A topology) W,
                  restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) W)
                 ((e:real^3->A) o (c:real->real^3)) (&0) (&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BT_C1_CURVE_SUBTOP THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      is_comb(concl th) && can (find_term ((=) `W:A->bool`)) (concl th) &&
      can (find_term ((=) `rfs_neck_dom eps`)) (concl th))) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    MP_TAC(ISPECL [`subtopology euclidean (rfs_neck_dom eps)`;
                   `open_set_atlas (rfs_neck_dom eps)`; `c:real->real^3`; `&0`; `&1`; `t:real`]
                  MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A) y = (e o c) (&0) /\ e z = (e o c) (&1)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length atlas (g:A->real^3^3) ((e:real^3->A) o c) (&0) (&1)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                   `g:A->real^3^3`; `(e:real^3->A) o (c:real->real^3)`; `&0`; `&1`] VSHI_LENGTH_RESTRICT) THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN
    ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
              mfd_length (open_set_atlas (rfs_neck_dom eps)) (cylinder_flow (&0))
                         (c:real->real^3) (&0) (&1)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The chain union T and its chart E.  T is open, each of its points lies in *)
(* a chain neck where R is within 1 per cent of the centre, R is bounded on  *)
(* E of every bounded part of the chart domain (near the inner sphere E is   *)
(* the first neck; the rest is compact) and tends to infinity at the far end *)
(* (finite unions lie in bounded parts and the curvature of the chain        *)
(* centres tends to infinity).                                               *)
(* ========================================================================= *)

let P2BT_CHART_BASICS = prove
 (`?eps0. &0 < eps0 /\
     !eps top atlas (g:A->real^3^3) x e E.
        &0 < eps /\ eps <= eps0 /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ p2bt_cchart eps top atlas g x e E
        ==> open_in top (apx_chain_union (&2 * eps) {i:int | &0 <= i} e) /\
            (!i. &0 <= i ==> rfs_neck (top,atlas) g (&2 * eps) (x i) (e i)) /\
            (!z. z IN apx_chain_union (&2 * eps) {i:int | &0 <= i} e
                 ==> ?i y. &0 <= i /\ y IN rfs_neck_dom (&2 * eps) /\ z = e i y) /\
            (!i y. &0 <= i /\ y IN rfs_neck_dom (&2 * eps)
                   ==> &99 / &100 * mfd_scalar atlas g (x i) <= mfd_scalar atlas g (e i y) /\
                       mfd_scalar atlas g (e i y) <= &101 / &100 * mfd_scalar atlas g (x i)) /\
            (!i. &0 <= i ==> &0 < mfd_scalar atlas g (x i)) /\
            (!z. z IN apx_chain_union (&2 * eps) {i:int | &0 <= i} e
                 ==> &0 < mfd_scalar atlas g z)`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_H) THEN
  EXISTS_TAC `e1 / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bt_cchart]) THEN
  SUBGOAL_THEN `!i. &0 <= i ==> rfs_neck (top,atlas) (g:A->real^3^3) (&2 * eps)
                                         ((x:int->A) i) ((e:int->real^3->A) i)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) (&2 * eps) {i:int | &0 <= i} x e` THEN
    REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i y. &0 <= i /\ y IN rfs_neck_dom (&2 * eps)
          ==> &99 / &100 * mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i) <=
              mfd_scalar atlas g ((e:int->real^3->A) i y) /\
              mfd_scalar atlas g (e i y) <= &101 / &100 * mfd_scalar atlas g (x i)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "nh" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `&2 * eps`; `(x:int->A) i`; `(e:int->real^3->A) i`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. &0 <= i ==> &0 < mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:int` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `&0 <= (i:int)`) o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN apx_chain_union (&2 * eps) {i:int | &0 <= i} (e:int->real^3->A)
        ==> ?i y. &0 <= i /\ y IN rfs_neck_dom (&2 * eps) /\ z = e i y`
  ASSUME_TAC THENL
   [REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM] THEN
    GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`i:int`; `y:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC APXN_CHAIN_UNION_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `x:int->A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
    `(z:A) IN apx_chain_union (&2 * eps) {i:int | &0 <= i} (e:int->real^3->A)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:int`; `y:real^3`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `&99 / &100`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `&0 <= (i:int)`) o check (fun th ->
    is_forall(concl th) && not (can (find_term ((=) `&99 / &100`)) (concl th)) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_scalar")) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th)))) THEN
  REAL_ARITH_TAC);;

(* Levels of the radius. *)

let P2BT_SVAL_RANGE = prove
 (`!a b y:real^3.
     exp(a / sqrt(&2)) < norm y /\ norm y < exp(b / sqrt(&2))
     ==> ~(y = vec 0) /\ a < apx_sval y /\ apx_sval y < b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [MP_TAC(SPEC `a / sqrt(&2)` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[apx_sval] THEN
  SUBGOAL_THEN `a / sqrt(&2) < log(norm(y:real^3)) /\ log(norm y) < b / sqrt(&2)` MP_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC);;

let P2BT_CHART_RBOUND = prove
 (`?eps0. &0 < eps0 /\
     !eps top atlas (g:A->real^3^3) x e E.
        &0 < eps /\ eps <= eps0 /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ p2bt_cchart eps top atlas g x e E
        ==> !rho. ?B. !y. exp(--inv(&2 * eps) / sqrt(&2)) < norm y /\ norm y <= rho
                          ==> mfd_scalar atlas g (E y) <= B`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cb"))
    (INST_TYPE [`:A`,`:A`] P2BT_CHART_BASICS) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "cb" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bt_cchart]) THEN
  X_GEN_TAC `rho:real` THEN
  ABBREV_TAC `r0 = exp(--inv(&2 * eps) / sqrt(&2))` THEN
  ABBREV_TAC `r1 = exp(inv(&8 * (&2 * eps)) / sqrt(&2))` THEN
  SUBGOAL_THEN `r0 < r1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r0"; "r1"] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b ==> --a < b`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the compact part *)
  SUBGOAL_THEN
   `?B1. !y:real^3. r1 <= norm y /\ norm y <= rho
                    ==> mfd_scalar atlas (g:A->real^3^3) ((E:real^3->A) y) <= B1`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS o check (fun th ->
      let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "mfd_param")) THEN
    DISCH_THEN(X_CHOOSE_THEN `E':A->real^3` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `K = {y:real^3 | r1 <= norm y /\ norm y <= rho}` THEN
    SUBGOAL_THEN `compact (K:real^3->bool) /\ K SUBSET {y:real^3 | r0 < norm y}`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "K" THEN CONJ_TAC THENL
       [SUBGOAL_THEN `{y:real^3 | r1 <= norm y /\ norm y <= rho} =
                      cball(vec 0,rho) DIFF ball(vec 0,r1)` SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
          REAL_ARITH_TAC;
          MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`subtopology euclidean {y:real^3 | r0 < norm y}`; `top:A topology`;
                   `E:real^3->A`; `K:real^3->bool`] IMAGE_COMPACT_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `euclideanreal`; `mfd_scalar atlas (g:A->real^3^3)`;
                   `IMAGE (E:real^3->A) K`] IMAGE_COMPACT_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC; real_bounded;
                FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:real` o CONJUNCT1) THEN EXISTS_TAC `B:real` THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
     [EXPAND_TAC "K" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `max B1 (&101 / &100 * mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&0)))` THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  ASM_CASES_TAC `r1 <= norm(y:real^3)` THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= max b c`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= c ==> a <= max b c`) THEN
  MP_TAC(SPECL [`--inv(&2 * eps)`; `inv(&8 * (&2 * eps))`; `y:real^3`] P2BT_SVAL_RANGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(E:real^3->A) y = (e:int->real^3->A) (&0) y` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[APX_SLAB_SVAL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&0:int`; `y:real^3`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `&101 / &100`)) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INT_LE_REFL; APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(&8 * (&2 * eps)) <= inv(&2 * eps)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* Points of the slab region of the chart, by radius. *)

let P2BT_SLAB_NORM = prove
 (`!a b y:real^3.
     y IN apx_slab a b ==> exp(a / sqrt(&2)) < norm y /\ norm y < exp(b / sqrt(&2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[APX_SLAB_SVAL; apx_sval] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ &0 < norm(y:real^3)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; NORM_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `a / sqrt(&2) < log(norm(y:real^3)) /\ log(norm y) < b / sqrt(&2)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[EXP_LOG] THEN
  ASM_MESON_TAC[REAL_EXP_MONO_LT; EXP_LOG]);;

let P2BT_CHART_RINF = prove
 (`?eps0. &0 < eps0 /\
     !eps top atlas (g:A->real^3^3) x e E D.
        &0 < eps /\ eps <= eps0 /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ p2bt_cchart eps top atlas g x e E /\
        (!n. sum(0..n) (\i. inv(sqrt(mfd_scalar atlas g (x(&i))))) <= D)
        ==> !B. ?rho. exp(--inv(&2 * eps) / sqrt(&2)) <= rho /\
                      !y. rho < norm y ==> B <= mfd_scalar atlas g (E y)`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cb"))
    (INST_TYPE [`:A`,`:A`] P2BT_CHART_BASICS) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "cb" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "mem") (CONJUNCTS_THEN2 (LABEL_TAC "rr")
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bt_cchart]) THEN
  X_GEN_TAC `B:real` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `&2 * eps`; `x:int->A`; `e:int->real^3->A`; `D:real`] P2BT_CHAIN_RINF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&2 * abs B + &1`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "big")) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `rN:real` o SPEC `N:num` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_slab"))
      (concl th) && can (find_term ((=) `E:real^3->A`)) (concl th) &&
      not (can (find_term ((=) `inv(&8 * (&2 * eps))`)) (concl th)))) THEN
  EXISTS_TAC `max (exp(--inv(&2 * eps) / sqrt(&2))) (exp(rN / sqrt(&2)))` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(E:real^3->A) y IN apx_chain_union (&2 * eps) {i:int | &0 <= i} e`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (lhand(concl th)))) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "mem" (MP_TAC o C MATCH_MP (ASSUME
    `(E:real^3->A) y IN apx_chain_union (&2 * eps) {i:int | &0 <= i} e`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `i <= &N:int` THENL
   [(* then E y lies in the finite union, a bounded part of the chart *)
    SUBGOAL_THEN `(E:real^3->A) y IN IMAGE E (apx_slab (--inv(&2 * eps)) rN)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      ASM_REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `IMAGE ((e:int->real^3->A) i) (rfs_neck_dom (&2 * eps))` THEN
      CONJ_TAC THENL [EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_SLAB_NORM) THEN STRIP_TAC THEN
    SUBGOAL_THEN `w:real^3 = y` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `{y:real^3 | exp(--inv(&2 * eps) / sqrt(&2)) < norm y}`;
                            `E:real^3->A`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC;
        CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* otherwise it lies in a neck far out, of large curvature *)
  SUBGOAL_THEN `?m. i:int = &m` (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `num_of_int i` THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `N <= m:num` ASSUME_TAC THENL
   [UNDISCH_TAC `~(&m <= &N:int)` THEN REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "big" (MP_TAC o C MATCH_MP (ASSUME `N <= m:num`) o SPEC `m:num`) THEN DISCH_TAC THEN
  USE_THEN "rr" (MP_TAC o SPECL [`&m:int`; `z:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The intrinsic diameter of T is finite (summable scales; consecutive      *)
(* centres are joined through a point of the overlap of their necks).        *)

let P2BT_CHART_DIAM = prove
 (`?eps0. &0 < eps0 /\
     !eps top atlas (g:A->real^3^3) x e E D.
        &0 < eps /\ eps <= eps0 /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ p2bt_cchart eps top atlas g x e E /\
        (!n. sum(0..n) (\i. inv(sqrt(mfd_scalar atlas g (x(&i))))) <= D)
        ==> ?D'. !p q. p IN apx_chain_union (&2 * eps) {i:int | &0 <= i} e /\
                       q IN apx_chain_union (&2 * eps) {i:int | &0 <= i} e
                       ==> mfd_joinable (subtopology top
                                           (apx_chain_union (&2 * eps) {i:int | &0 <= i} e),
                                         restrict_atlas atlas
                                           (apx_chain_union (&2 * eps) {i:int | &0 <= i} e))
                                        p q /\
                           mfd_dist (subtopology top
                                       (apx_chain_union (&2 * eps) {i:int | &0 <= i} e),
                                     restrict_atlas atlas
                                       (apx_chain_union (&2 * eps) {i:int | &0 <= i} e))
                                    (restrict_metric atlas
                                       (apx_chain_union (&2 * eps) {i:int | &0 <= i} e) g)
                                    p q <= D'`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cb"))
    (INST_TYPE [`:A`,`:A`] P2BT_CHART_BASICS) THEN
  EXISTS_TAC `min e1 (&1 / &4)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "cb" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "nk")
    (CONJUNCTS_THEN2 (LABEL_TAC "mem") (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (LABEL_TAC "rpos") (K ALL_TAC)))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bt_cchart]) THEN
  ABBREV_TAC `TT = apx_chain_union (&2 * eps) {i:int | &0 <= i} (e:int->real^3->A)` THEN
  ABBREV_TAC `h = \i:int. inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i)))` THEN
  ABBREV_TAC `c1 = sqrt(&1 + &2 * eps) * (inv eps + sqrt(&2) * pi)` THEN
  SUBGOAL_THEN `&0 <= c1` ASSUME_TAC THENL
   [EXPAND_TAC "c1" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology top TT)
                  (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) TT) /\
                riemannian_metric (restrict_atlas atlas TT)
                  (restrict_metric atlas TT (g:A->real^3^3))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* within one neck *)
  SUBGOAL_THEN
   `!i y z. &0 <= i /\ y IN rfs_neck_dom (&2 * eps) /\ z IN rfs_neck_dom (&2 * eps)
            ==> mfd_joinable (subtopology top TT,restrict_atlas atlas TT)
                             ((e:int->real^3->A) i y) (e i z) /\
                mfd_dist (subtopology top TT,restrict_atlas atlas TT)
                         (restrict_metric atlas TT (g:A->real^3^3)) (e i y) (e i z)
                <= c1 * h i`
  (LABEL_TAC "one") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `&2 * eps`; `(x:int->A) i`; `(e:int->real^3->A) i`; `TT:A->bool`;
                   `y:real^3`; `z:real^3`] P2BT_NECK_DIST_SUB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [USE_THEN "nk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC;
        EXPAND_TAC "TT" THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `&2 * eps`; `{i:int | &0 <= i}`; `x:int->A`;
                       `e:int->real^3->A`; `i:int`] APXN_NECK_IN_UNION) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&1 + &2 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i))) *
                (abs(apx_sval y - apx_sval z) + sqrt(&2) * pi)` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "c1" THEN EXPAND_TAC "h" THEN
    SUBGOAL_THEN `abs(apx_sval y - apx_sval z) <= inv eps` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN rfs_neck_dom (&2 * eps)` THEN
      UNDISCH_TAC `(z:real^3) IN rfs_neck_dom (&2 * eps)` THEN
      REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
      SUBGOAL_THEN `inv(&2 * eps) = inv eps / &2` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt(&1 + &2 * eps) /\
                  &0 <= inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i)))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `a * b * c <= (a * d) * b <=> &0 <= a * b * (d - c)`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the centres are points of their necks *)
  SUBGOAL_THEN
   `!i. &0 <= i ==> ?u. u IN rfs_neck_dom (&2 * eps) /\ (x:int->A) i = (e:int->real^3->A) i u`
  (LABEL_TAC "cen") THENL
   [X_GEN_TAC `i:int` THEN DISCH_TAC THEN
    USE_THEN "nk" (MP_TAC o C MATCH_MP (ASSUME `&0 <= (i:int)`)) THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE] THEN STRIP_TAC THEN
    EXISTS_TAC `x':real^3` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `&2 * eps` APX_UNIT_SPHERE_NECK_DOM) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  (* consecutive centres *)
  SUBGOAL_THEN
   `!n. mfd_joinable (subtopology top TT,restrict_atlas atlas TT)
                     ((x:int->A)(&n)) (x(&(n + 1))) /\
        mfd_dist (subtopology top TT,restrict_atlas atlas TT)
                 (restrict_metric atlas TT (g:A->real^3^3)) (x(&n)) (x(&(n + 1)))
        <= c1 * (h(&n:int) + h(&(n + 1):int))`
  (LABEL_TAC "step") THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "cen" (MP_TAC o SPEC `&n:int`) THEN REWRITE_TAC[INT_POS] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "cen" (MP_TAC o SPEC `&(n + 1):int`) THEN REWRITE_TAC[INT_POS] THEN
    DISCH_THEN(X_CHOOSE_THEN `u':real^3` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `q = exp((&3 / &4 * inv(&2 * eps)) / sqrt(&2)) % basis 1:real^3` THEN
    SUBGOAL_THEN `(q:real^3) IN apx_slab (inv(&2 * (&2 * eps))) (inv(&2 * eps))` ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN REWRITE_TAC[APX_SLAB_SVAL; apx_sval] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_EXP_POS_LT; LOG_EXP] THEN
      SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN
        SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
        MP_TAC(SPEC `(&3 / &4 * inv(&2 * eps)) / sqrt(&2)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
      SUBGOAL_THEN `&0 < inv(&2 * eps) /\ inv(&2 * (&2 * eps)) = inv(&2 * eps) / &2`
      MP_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^3) IN rfs_neck_dom (&2 * eps)` ASSUME_TAC THENL
     [UNDISCH_TAC `(q:real^3) IN apx_slab (inv(&2 * (&2 * eps))) (inv(&2 * eps))` THEN
      REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < inv(&2 * (&2 * eps))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `?v. v IN rfs_neck_dom (&2 * eps) /\
                      (e:int->real^3->A) (&n) q = e (&(n + 1)) v`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) (&2 * eps) {i:int | &0 <= i} x e` THEN
      REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `&n:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      REWRITE_TAC[INT_OF_NUM_ADD; INT_POS] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_INTER] THEN
      DISCH_THEN(MP_TAC o SPEC `(e:int->real^3->A) (&n) q`) THEN
      ANTS_TAC THENL [DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
                      ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "one" (MP_TAC o SPECL [`&n:int`; `u:real^3`; `q:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INT_POS]; STRIP_TAC] THEN
    USE_THEN "one" (MP_TAC o SPECL [`&(n + 1):int`; `v:real^3`; `u':real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INT_POS]; STRIP_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
      `(e:int->real^3->A) (&n) q = e (&(n + 1)) v`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `mfd_joinable (subtopology top TT,
                    restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) TT)
                   ((e:int->real^3->A) (&n) u) (e (&(n + 1)) u')`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN
      EXISTS_TAC `(e:int->real^3->A) (&(n + 1)) v` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`subtopology top (TT:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) TT`;
                   `restrict_metric atlas TT (g:A->real^3^3)`;
                   `(e:int->real^3->A) (&n) u`; `(e:int->real^3->A) (&(n + 1)) v`;
                   `(e:int->real^3->A) (&(n + 1)) u'`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC(MATCH_MP
      (REAL_ARITH `!x y z:real. x <= y ==> y <= z ==> x <= z`) th)) THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* distances from the first centre *)
  SUBGOAL_THEN `!n. &0 <= h(&n:int)` (LABEL_TAC "hpos") THENL
   [GEN_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "rpos" MATCH_MP_TAC THEN REWRITE_TAC[INT_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. sum(0..n) (\k. h(&k:int)) <= D` (LABEL_TAC "hsum") THENL
   [GEN_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:int->A)(&0) IN TT` ASSUME_TAC THENL
   [USE_THEN "cen" (MP_TAC o SPEC `&0:int`) THEN REWRITE_TAC[INT_LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "TT" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `&2 * eps`; `{i:int | &0 <= i}`; `x:int->A`;
                   `e:int->real^3->A`; `&0:int`] APXN_NECK_IN_UNION) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; INT_LE_REFL; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. mfd_joinable (subtopology top TT,restrict_atlas atlas TT)
                     ((x:int->A)(&0)) (x(&n)) /\
        mfd_dist (subtopology top TT,restrict_atlas atlas TT)
                 (restrict_metric atlas TT (g:A->real^3^3)) (x(&0)) (x(&n))
        <= &2 * c1 * sum(0..n) (\k. h(&k:int)) - c1 * h(&n:int)`
  (LABEL_TAC "ind") THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[SUM_SING_NUMSEG] THEN
      SUBGOAL_THEN `(x:int->A)(&0) IN topspace(subtopology top TT)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
          rand(concl th) = `TT:A->bool`)) THEN ASM SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[MFD_JOINABLE_REFL] THEN
      MP_TAC(ISPECL [`subtopology top (TT:A->bool)`;
                     `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) TT`;
                     `restrict_metric atlas TT (g:A->real^3^3)`; `(x:int->A)(&0)`]
                    MFD_DIST_REFL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "hpos" (MP_TAC o SPEC `0`) THEN
      SUBGOAL_THEN `&0 <= c1 * h(&0:int)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN USE_THEN "hpos" ACCEPT_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    POP_ASSUM STRIP_ASSUME_TAC THEN
    USE_THEN "step" (MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[ADD1] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(x:int->A)(&n)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`subtopology top (TT:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) TT`;
                   `restrict_metric atlas TT (g:A->real^3^3)`;
                   `(x:int->A)(&0)`; `(x:int->A)(&n)`; `(x:int->A)(&(n + 1))`]
                  MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; LE_0] THEN REWRITE_TAC[ADD1] THEN
    ABBREV_TAC `dA = mfd_dist (subtopology top TT,restrict_atlas atlas TT)
                       (restrict_metric atlas TT (g:A->real^3^3)) ((x:int->A)(&0)) (x(&n))` THEN
    ABBREV_TAC `dB = mfd_dist (subtopology top TT,restrict_atlas atlas TT)
                       (restrict_metric atlas TT (g:A->real^3^3)) ((x:int->A)(&n)) (x(&(n + 1)))` THEN
    ABBREV_TAC `dC = mfd_dist (subtopology top TT,restrict_atlas atlas TT)
                       (restrict_metric atlas TT (g:A->real^3^3)) ((x:int->A)(&0)) (x(&(n + 1)))` THEN
    ABBREV_TAC `S = sum(0..n) (\k. h(&k:int))` THEN
    ABBREV_TAC `h0 = h(&n:int):real` THEN ABBREV_TAC `h1 = h(&(n + 1):int):real` THEN
    UNDISCH_TAC `dA <= &2 * c1 * S - c1 * h0` THEN
    UNDISCH_TAC `dB <= c1 * (h0 + h1)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. p IN TT
        ==> mfd_joinable (subtopology top TT,restrict_atlas atlas TT) ((x:int->A)(&0)) p /\
            mfd_dist (subtopology top TT,restrict_atlas atlas TT)
                     (restrict_metric atlas TT (g:A->real^3^3)) (x(&0)) p <= &2 * c1 * D`
  (LABEL_TAC "far") THENL
   [X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    USE_THEN "mem" (MP_TAC o C MATCH_MP (ASSUME `(p:A) IN TT`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `?m. i:int = &m` (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THENL
     [EXISTS_TAC `num_of_int i` THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "cen" (MP_TAC o SPEC `&m:int`) THEN REWRITE_TAC[INT_POS] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "one" (MP_TAC o SPECL [`&m:int`; `u:real^3`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INT_POS]; STRIP_TAC] THEN
    USE_THEN "ind" (MP_TAC o SPEC `m:num`) THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(x:int->A)(&m) = (e:int->real^3->A) (&m) u`]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(e:int->real^3->A) (&m) u` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`subtopology top (TT:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) TT`;
                   `restrict_metric atlas TT (g:A->real^3^3)`;
                   `(x:int->A)(&0)`; `(e:int->real^3->A) (&m) u`; `(e:int->real^3->A) (&m) y`]
                  MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "hsum" (MP_TAC o SPEC `m:num`) THEN
    ABBREV_TAC `dA = mfd_dist (subtopology top TT,restrict_atlas atlas TT)
                       (restrict_metric atlas TT (g:A->real^3^3)) ((x:int->A)(&0))
                       ((e:int->real^3->A) (&m) u)` THEN
    ABBREV_TAC `dB = mfd_dist (subtopology top TT,restrict_atlas atlas TT)
                       (restrict_metric atlas TT (g:A->real^3^3))
                       ((e:int->real^3->A) (&m) u) (e (&m) y)` THEN
    ABBREV_TAC `dC = mfd_dist (subtopology top TT,restrict_atlas atlas TT)
                       (restrict_metric atlas TT (g:A->real^3^3)) ((x:int->A)(&0))
                       ((e:int->real^3->A) (&m) y)` THEN
    ABBREV_TAC `S = sum(0..m) (\k. h(&k:int))` THEN
    ABBREV_TAC `hm = h(&m:int):real` THEN
    UNDISCH_TAC `dA <= &2 * c1 * S - c1 * hm` THEN UNDISCH_TAC `dB <= c1 * hm` THEN
    SUBGOAL_THEN `c1 * S <= c1 * D` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN
      USE_THEN "hsum" (ACCEPT_TAC o SPEC `m:num`);
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `&4 * c1 * D` THEN MAP_EVERY X_GEN_TAC [`p:A`; `q:A`] THEN STRIP_TAC THEN
  USE_THEN "far" (MP_TAC o C MATCH_MP (ASSUME `(p:A) IN TT`) o SPEC `p:A`) THEN STRIP_TAC THEN
  USE_THEN "far" (MP_TAC o C MATCH_MP (ASSUME `(q:A) IN TT`) o SPEC `q:A`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (subtopology top TT,
                              restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) TT)
                             (p:A) ((x:int->A)(&0))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (TT:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) TT`;
                   `(x:int->A)(&0)`; `p:A`] MFD_JOINABLE_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(x:int->A)(&0)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (TT:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) TT`;
                 `restrict_metric atlas TT (g:A->real^3^3)`;
                 `p:A`; `(x:int->A)(&0)`; `q:A`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`subtopology top (TT:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) TT`;
                 `restrict_metric atlas TT (g:A->real^3^3)`;
                 `p:A`; `(x:int->A)(&0)`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC);;
(* ========================================================================= *)
(* Necks of large curvature at points of T lie in T.  The frontier of T in   *)
(* the manifold lies in the closure of the inner part E(annulus(r0,r1)) (E   *)
(* is the first chain neck there): near a frontier point R is bounded, so T  *)
(* is a bounded part of the chart there, and the rest of that part is        *)
(* compact.  On that closure R is at most 101/100 R of the first centre,     *)
(* while on a neck centred at p it is at least 99/100 R(p); a connected neck *)
(* image meeting T and its complement would meet the frontier.               *)
(* ========================================================================= *)

let P2BT_FRONTIER_CONTAIN = prove
 (`?eps0. &0 < eps0 /\
     !eps top atlas (g:A->real^3^3) x e E D.
        &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ p2bt_cchart eps top atlas g x e E /\
        (!n. sum(0..n) (\i. inv(sqrt(mfd_scalar atlas g (x(&i))))) <= D)
        ==> !p e'. p IN apx_chain_union (&2 * eps) {i:int | &0 <= i} e /\
                   &3 * mfd_scalar atlas g (x(&0)) < mfd_scalar atlas g p /\
                   rfs_neck (top,atlas) g (&2 * eps) p e'
                   ==> IMAGE e' (rfs_neck_dom (&2 * eps)) SUBSET
                       apx_chain_union (&2 * eps) {i:int | &0 <= i} e`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cb"))
    (INST_TYPE [`:A`,`:A`] P2BT_CHART_BASICS) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ri"))
    (INST_TYPE [`:A`,`:A`] P2BT_CHART_RINF) THEN
  X_CHOOSE_THEN `e5:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_H) THEN
  EXISTS_TAC `min (min e1 e3) (e5 / &2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `x:int->A`; `e:int->real^3->A`; `E:real^3->A`;
                       `D:real`] THEN
  STRIP_TAC THEN
  USE_THEN "cb" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "nk")
    (CONJUNCTS_THEN2 (LABEL_TAC "mem") (CONJUNCTS_THEN2 (LABEL_TAC "rr")
      (CONJUNCTS_THEN2 (LABEL_TAC "rpos") (LABEL_TAC "pos")))))) THEN
  USE_THEN "ri" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`; `D:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(LABEL_TAC "ri1")] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bt_cchart]) THEN
  ABBREV_TAC `TT = apx_chain_union (&2 * eps) {i:int | &0 <= i} (e:int->real^3->A)` THEN
  ABBREV_TAC `r0 = exp(--inv(&2 * eps) / sqrt(&2))` THEN
  ABBREV_TAC `r1 = exp(inv(&8 * (&2 * eps)) / sqrt(&2))` THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3)` THEN
  SUBGOAL_THEN `continuous_map (top,euclideanreal) (R:A->real)` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `r0 < r1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r0"; "r1"] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b ==> --a < b`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* R on the inner part *)
  SUBGOAL_THEN
   `!y:real^3. r0 < norm y /\ norm y < r1
               ==> (R:A->real) ((E:real^3->A) y) <= &101 / &100 * R((x:int->A)(&0))`
  (LABEL_TAC "inner") THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`--inv(&2 * eps)`; `inv(&8 * (&2 * eps))`; `y:real^3`] P2BT_SVAL_RANGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(E:real^3->A) y = (e:int->real^3->A) (&0) y` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[APX_SLAB_SVAL]; ALL_TAC] THEN
    USE_THEN "rr" (MP_TAC o SPECL [`&0:int`; `y:real^3`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INT_LE_REFL; APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `inv(&8 * (&2 * eps)) <= inv(&2 * eps)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      EXPAND_TAC "R" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:A`; `e':real^3->A`] THEN STRIP_TAC THEN
  (* R on the neck at p *)
  SUBGOAL_THEN `!z. z IN IMAGE (e':real^3->A) (rfs_neck_dom (&2 * eps))
                    ==> &99 / &100 * (R:A->real) p <= R z`
  (LABEL_TAC "nr") THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "nh" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `&2 * eps`; `p:A`; `e':real^3->A`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "R" THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `N' = IMAGE (e':real^3->A) (rfs_neck_dom (&2 * eps))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
    let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "rfs_neck" &&
    can (find_term ((=) `e':real^3->A`)) (concl th))) THEN
  SUBGOAL_THEN `connected_in top (N':A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "N'" THEN MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom (&2 * eps)`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL; rfs_neck_dom; APX_CONNECTED_ANNULUS3];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN N'` ASSUME_TAC THENL
   [EXPAND_TAC "N'" THEN
    MP_TAC(SPEC `&2 * eps` APX_UNIT_SPHERE_NECK_DOM) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((N':A->bool) INTER top frontier_of TT = {})` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_INTER_FRONTIER_OF THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
  SUBGOAL_THEN `(z:A) IN top closure_of TT /\ ~(z IN TT)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:A) IN top frontier_of TT` THEN REWRITE_TAC[frontier_of; IN_DIFF] THEN
    ASM_SIMP_TAC[INTERIOR_OF_OPEN_IN];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `TT:A->bool`] CLOSURE_OF_SUBSET_TOPSPACE) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "ri1" (X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC o SPEC `(R:A->real) z + &1`) THEN
  ABBREV_TAC `O = {w:A | w IN topspace top /\ (R:A->real) w IN {t | t < R z + &1}}` THEN
  SUBGOAL_THEN `open_in top (O:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `euclideanreal` THEN ASM_REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Ai = IMAGE (E:real^3->A) {y:real^3 | r0 < norm y /\ norm y < r1}` THEN
  ABBREV_TAC `Kc = IMAGE (E:real^3->A) {y:real^3 | r1 <= norm y /\ norm y <= max rho r1}` THEN
  SUBGOAL_THEN `(O:A->bool) INTER TT SUBSET Ai UNION Kc` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_UNION] THEN X_GEN_TAC `w:A` THEN STRIP_TAC THEN
    UNDISCH_TAC `(w:A) IN TT` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `TT:A->bool` &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (lhs(concl th)))) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `norm(y:real^3) <= rho` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `rho:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(w:A) IN O` THEN EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["Ai"; "Kc"] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    ASM_CASES_TAC `norm(y:real^3) < r1` THENL
     [DISJ1_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (Kc:A->bool) /\ Kc SUBSET TT` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS o check (fun th ->
      let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "mfd_param" &&
      can (find_term ((=) `E:real^3->A`)) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `E':A->real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `compact {y:real^3 | r1 <= norm y /\ norm y <= max rho r1} /\
                  {y:real^3 | r1 <= norm y /\ norm y <= max rho r1} SUBSET {y | r0 < norm y}`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `{y:real^3 | r1 <= norm y /\ norm y <= max rho r1} =
                      cball(vec 0,max rho r1) DIFF ball(vec 0,r1)` SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
          REAL_ARITH_TAC;
          MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "Kc" THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology euclidean {y:real^3 | r0 < norm y}` THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
      EXPAND_TAC "Kc" THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `TT:A->bool` &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (lhs(concl th)))) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN top closure_of Ai` ASSUME_TAC THENL
   [SUBGOAL_THEN `(z:A) IN top closure_of (O INTER TT)` MP_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `O:A->bool`; `TT:A->bool`]
        OPEN_IN_INTER_CLOSURE_OF_SUBSET) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPEC `top:A topology` (MATCH_MP CLOSURE_OF_MONO
      (ASSUME `(O:A->bool) INTER TT SUBSET Ai UNION Kc`))) THEN
    ASM_SIMP_TAC[CLOSURE_OF_UNION; CLOSURE_OF_CLOSED_IN] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(R:A->real) z <= &101 / &100 * R((x:int->A)(&0))` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `top closure_of Ai SUBSET
      {w:A | w IN topspace top /\ (R:A->real) w IN {t | t <= &101 / &100 * R((x:int->A)(&0))}}`
    MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
       [EXPAND_TAC "Ai" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS o check (fun th ->
            let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "mfd_param" &&
            can (find_term ((=) `E:real^3->A`)) (concl th))) THEN
          DISCH_THEN(X_CHOOSE_THEN `E':A->real^3` STRIP_ASSUME_TAC) THEN
          FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
            can (find_term ((=) `E:real^3->A`)) (concl th) &&
            let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "open_in")) THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          USE_THEN "inner" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `euclideanreal` THEN
        ASM_REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_HALFSPACE_LE]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "nr" (MP_TAC o SPEC `z:A`) THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "rpos" (MP_TAC o SPEC `&0:int`) THEN REWRITE_TAC[INT_LE_REFL] THEN
  UNDISCH_TAC `(R:A->real) z <= &101 / &100 * R((x:int->A)(&0))` THEN
  UNDISCH_TAC `&3 * (R:A->real)((x:int->A)(&0)) < R p` THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The chain-chart data and the static clauses of the bad tube (statements   *)
(* here, proofs below).  For a one-sided chain of 2 eps-necks with summable  *)
(* scales and its chart E (the conclusion of P2BT_REQ_CHAIN_CHART at 2 eps), *)
(* the union T with the restricted manifold structure and H = E o p2bt_rad   *)
(* satisfy the clauses of p2b_bad_tube that do not involve the view.         *)
(* ========================================================================= *)

(* The static clauses. *)

let P2BT_TUBE_STATIC = prove
 (`?eps0. &0 < eps0 /\
     !eps top atlas (g:A->real^3^3) x e E.
        &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
        p2bt_cchart eps top atlas g x e E /\
        (?D. !n. sum(0..n) (\i. inv(sqrt(mfd_scalar atlas g (x(&i))))) <= D)
        ==> let TT = apx_chain_union (&2 * eps) {i:int | &0 <= i} e in
            let H = E o p2bt_rad (exp(--inv(&2 * eps) / sqrt(&2))) in
            open_in top TT /\
            hausdorff_space (subtopology top TT) /\
            smooth_manifold_atlas (subtopology top TT) (restrict_atlas atlas TT) /\
            riemannian_metric (restrict_atlas atlas TT) (restrict_metric atlas TT g) /\
            connected_space (subtopology top TT) /\
            apx_sphere_sep (subtopology top TT) (restrict_atlas atlas TT) /\
            mfd_param (subtopology top TT) (restrict_atlas atlas TT) (annulus (&1) (&2)) H /\
            IMAGE H (annulus (&1) (&2)) = topspace (subtopology top TT) /\
            (?D. !p q. p IN topspace (subtopology top TT) /\ q IN topspace (subtopology top TT)
                       ==> mfd_joinable (subtopology top TT,restrict_atlas atlas TT) p q /\
                           mfd_dist (subtopology top TT,restrict_atlas atlas TT)
                                    (restrict_metric atlas TT g) p q <= D) /\
            (?B0. !y. y IN annulus (&1) (&3 / &2)
                      ==> mfd_scalar (restrict_atlas atlas TT) (restrict_metric atlas TT g) (H y)
                          <= B0) /\
            (!B0. ?r. r < &2 /\
                      !y. r < norm y /\ norm y < &2
                          ==> B0 <= mfd_scalar (restrict_atlas atlas TT)
                                               (restrict_metric atlas TT g) (H y)) /\
            (!p. p IN topspace (subtopology top TT)
                 ==> &0 < mfd_scalar (restrict_atlas atlas TT) (restrict_metric atlas TT g) p)`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cb"))
    (INST_TYPE [`:A`,`:A`] P2BT_CHART_BASICS) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rb"))
    (INST_TYPE [`:A`,`:A`] P2BT_CHART_RBOUND) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ri"))
    (INST_TYPE [`:A`,`:A`] P2BT_CHART_RINF) THEN
  X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "di"))
    (INST_TYPE [`:A`,`:A`] P2BT_CHART_DIAM) THEN
  EXISTS_TAC `min (min e1 e2) (min e3 e4)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `x:int->A`; `e:int->real^3->A`; `E:real^3->A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `D:real`)))))))) THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= e2 /\ eps <= e3 /\ eps <= e4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "cb" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pos")))))) THEN
  USE_THEN "rb" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "rb1")] THEN
  USE_THEN "ri" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`; `D:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "ri1")] THEN
  USE_THEN "di" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`; `D:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `D':real`)] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bt_cchart]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `TT = apx_chain_union (&2 * eps) {i:int | &0 <= i} (e:int->real^3->A)` THEN
  ABBREV_TAC `r0 = exp(--inv(&2 * eps) / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < r0` ASSUME_TAC THENL [EXPAND_TAC "r0" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology top TT) = (TT:A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      rand(concl th) = `TT:A->bool`)) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. p IN TT ==> mfd_scalar (restrict_atlas atlas TT) (restrict_metric atlas TT g) p =
                    mfd_scalar atlas (g:A->real^3^3) p`
  (LABEL_TAC "rs") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_SCALAR_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `r0:real` P2BT_RAD_DIFFEO) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE ((E:real^3->A) o p2bt_rad r0) (annulus (&1) (&2)) = TT` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN
    FIRST_ASSUM(SUBST1_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
        let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "diffeomorphism_on")) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN annulus (&1) (&2)
                           ==> norm(p2bt_rad r0 y) = r0 + (norm y - &1) / (&2 - norm y) /\
                               ((E:real^3->A) o p2bt_rad r0) y IN TT`
  (LABEL_TAC "hy") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r0:real`; `y:real^3`; `y:real^3`] P2BT_RAD_NORMS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (annulus (&1) (&2)) ((E:real^3->A) o p2bt_rad r0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`{z:real^3 | r0 < norm z}`; `{z:real^3 | r0 < norm z}`;
                          `p2bt_radinv r0`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* Hausdorff *)
    MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
    (* smooth *)
    MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
    (* metric *)
    MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    (* connected *)
    MATCH_MP_TAC CONNECTED_SPACE_SUBTOPOLOGY THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `TT:A->bool` &&
      can (find_term ((=) `p2bt_rad r0`)) (lhs(concl th)))) THEN
    MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclidean (annulus (&1) (&2)):(real^3)topology` THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN; SUBSET_REFL] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS o check (fun th ->
        let c,args = strip_comb(concl th) in
        is_const c && fst(dest_const c) = "mfd_param" &&
        can (find_term ((=) `p2bt_rad r0`)) (concl th))) THEN
      MESON_TAC[];
      MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `&2`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
      REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_RZERO; annulus]];
    (* sphere separation *)
    MP_TAC(ISPEC `w:A->bool` APX_SEP_OPEN) THEN REWRITE_TAC[APX_SEP_OPEN_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* the chart *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `TT:A->bool`;
                   `annulus (&1) (&2):real^3->bool`; `(E:real^3->A) o p2bt_rad r0`]
                  APX_PARAM_RESTRICT_EQ) THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    (* diameter *)
    EXISTS_TAC `D':real` THEN ASM_REWRITE_TAC[];
    (* bounded curvature near the inner end *)
    USE_THEN "rb1" (X_CHOOSE_TAC `B:real` o SPEC `r0 + &1`) THEN
    EXISTS_TAC `B:real` THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN annulus (&1) (&2) /\ norm y <= &3 / &2` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN annulus (&1) (&3 / &2)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "hy" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN annulus (&1) (&2)`)) THEN
    STRIP_TAC THEN USE_THEN "rs" (fun th -> ASM_SIMP_TAC[th]) THEN
    REWRITE_TAC[o_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN annulus (&1) (&2)` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (norm(y:real^3) - &1) / (&2 - norm y) /\
                  (norm(y:real^3) - &1) / (&2 - norm y) <= &1`
    MP_TAC THENL
     [SUBGOAL_THEN `&0 < &2 - norm(y:real^3)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    (* curvature to infinity at the outer end *)
    X_GEN_TAC `B0:real` THEN
    USE_THEN "ri1" (X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC o SPEC `B0:real`) THEN
    ABBREV_TAC `M = rho - r0 + &1` THEN
    SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `(&1 + &2 * M) / (&1 + M)` THEN
    SUBGOAL_THEN `&0 < &1 + M` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&1 < norm(y:real^3)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `norm(y:real^3) * (&1 + M) <= &1 * (&1 + M)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN annulus (&1) (&2)` ASSUME_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "hy" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN annulus (&1) (&2)`)) THEN
    STRIP_TAC THEN USE_THEN "rs" (fun th -> ASM_SIMP_TAC[th]) THEN
    REWRITE_TAC[o_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `M < (norm(y:real^3) - &1) / (&2 - norm y)` MP_TAC THENL
     [SUBGOAL_THEN `&0 < &2 - norm(y:real^3)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    (* positive curvature *)
    X_GEN_TAC `p:A` THEN DISCH_TAC THEN USE_THEN "rs" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* The restricted view (statements here, proofs below).  For a regular view  *)
(* V and sets Om s open in the slices (s <= 0), p2bt_rview V Om has the      *)
(* slices of V restricted to Om s for s <= 0 and empty slices for s > 0.     *)
(* With Om s the points of an open set T where -1/R < s, the boxes of V      *)
(* under every point of T give the box clause of the bad tube, and the sign  *)
(* of the curvature passes over.                                             *)
(* ========================================================================= *)

let p2bt_rview = new_definition
 `p2bt_rview (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
             (Om:real->A->bool) =
    (\s. if s <= &0 then subtopology (rfs_vtop V s) (Om s) else discrete_topology {}),
    (\s. if s <= &0 then restrict_atlas (rfs_vatlas V s) (Om s) else {}),
    (\s. if s <= &0 then restrict_metric (rfs_vatlas V s) (Om s) (rfs_vmetric V s)
         else (\x:A. mat 1))`;;

let P2BT_RVIEW_PARTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) Om s.
     rfs_vtop (p2bt_rview V Om) s =
       (if s <= &0 then subtopology (rfs_vtop V s) (Om s) else discrete_topology {}) /\
     rfs_vatlas (p2bt_rview V Om) s =
       (if s <= &0 then restrict_atlas (rfs_vatlas V s) (Om s) else {}) /\
     rfs_vmetric (p2bt_rview V Om) s =
       (if s <= &0 then restrict_metric (rfs_vatlas V s) (Om s) (rfs_vmetric V s)
        else (\x:A. mat 1))`,
  REWRITE_TAC[p2bt_rview; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

(* The pullback by the identity of a restricted metric between restricted *)
(* atlases (the identity a diffeomorphism near the point). *)

let P2BT_PB_RESTRICT2 = prove
 (`!top atlas top' atlas' O O' W (G:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     open_in top O /\ open_in top' O' /\
     mfd_diffeo top atlas W top' atlas' W (\y:A. y) (\y. y) /\
     x IN W /\ x IN O /\ x IN O'
     ==> mfd_pullback_metric (restrict_atlas atlas O) (restrict_atlas atlas' O') (\y:A. y)
                             (restrict_metric atlas' O' G) x =
         restrict_metric atlas O (mfd_pullback_metric atlas atlas' (\y:A. y) G) x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `O:A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U1:A->bool` (X_CHOOSE_THEN `phi1:A->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1")))))) THEN
  MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^N))->bool`;
                 `O':A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r2")))))) THEN
  USE_THEN "r1" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `top':A topology`; `atlas':((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`; `G:A->real^N^N`; `U1:A->bool`; `phi1:A->real^N`;
                 `U2:A->bool`; `phi2:A->real^N`; `x:A`] P2A_PULLBACK_METRIC_LOCAL_W) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[mfd_pullback_metric] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U1:A->bool`;
                 `phi1:A->real^N`; `O:A->bool`; `x:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mpullback ((phi2:A->real^N) o (\y:A. y) o chart_inv (U1 INTER O,phi1))
              (metric_local (restrict_atlas atlas' O') (U2 INTER O',phi2)
                            (restrict_metric atlas' O' (G:A->real^N^N)))
              ((phi1:A->real^N) x) =
    mpullback (phi2 o (\y:A. y) o chart_inv (U1 INTER O,phi1))
              (metric_local atlas' (U2,phi2) G) (phi1 x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[mpullback; o_THM] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN EXISTS_TAC `top':A topology` THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_MPULLBACK_LOCAL THEN
  EXISTS_TAC `IMAGE (phi1:A->real^N) (U1 INTER O)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN
    X_GEN_TAC `v:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U1:A->bool`;
                   `phi1:A->real^N`; `O:A->bool`; `v:A`] MFDR_CHART_INV_RESTRICT) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]]);;

let P2BT_PERSISTS_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W a b.
     rfs_persists V W a b <=>
     !s. a < s /\ s <= b
         ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\ open_in (rfs_vtop V s) W`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

(* Open sets of the restricted slices. *)

let P2BT_RVIEW_OPEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) Om s W.
     (!s. s <= &0 ==> open_in (rfs_vtop V s) (Om s)) /\
     open_in (rfs_vtop (p2bt_rview V Om) s) W /\ ~(W = {})
     ==> s <= &0 /\ W SUBSET Om s /\ open_in (rfs_vtop V s) W /\
         ~(topspace(rfs_vtop V s) = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BT_RVIEW_PARTS] THEN
  ASM_CASES_TAC `s <= &0` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `s:real`)
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) W` ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `(Om:real->A->bool) s` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `open_in (subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) ((Om:real->A->bool) s)) W` THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    UNDISCH_TAC `~(W:A->bool = {})` THEN SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN
    UNDISCH_TAC `~(W:A->bool = {})` THEN SET_TAC[]]);;

let P2BT_RVIEW_PERSISTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) Om W a b.
     (!t. ~(topspace(rfs_vtop V t) = {})
          ==> smooth_manifold_atlas (rfs_vtop V t) (rfs_vatlas V t)) /\
     (!s. s <= &0 ==> open_in (rfs_vtop V s) (Om s)) /\
     a < b /\ rfs_persists (p2bt_rview V Om) W a b /\ ~(W = {})
     ==> b <= &0 /\ rfs_persists V W a b /\ (!s. a < s /\ s <= b ==> W SUBSET Om s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2BT_PERSISTS_ALT] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. a < s /\ s <= b
        ==> s <= &0 /\ W SUBSET (Om:real->A->bool) s /\
            open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) s) W /\
            ~(topspace(rfs_vtop V s) = {})`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2BT_RVIEW_OPEN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `b:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

(* The flow families of the restricted view agree with those of V. *)

let P2BT_RVIEW_VFAM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    Om W b t x.
     t <= b /\ b <= &0 /\ x IN W /\
     smooth_manifold_atlas (rfs_vtop V t) (rfs_vatlas V t) /\
     smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
     open_in (rfs_vtop V t) (Om t) /\ open_in (rfs_vtop V b) (Om b) /\
     open_in (rfs_vtop V b) W /\ W SUBSET Om t /\ W SUBSET Om b /\
     mfd_diffeo (rfs_vtop V b) (rfs_vatlas V b) W (rfs_vtop V t) (rfs_vatlas V t) W
                (\y:A. y) (\y. y)
     ==> p2c_vfam (p2bt_rview V Om) W b t x = p2c_vfam V W b t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[p2c_vfam; P2BT_RVIEW_PARTS] THEN
  SUBGOAL_THEN `open_in (subtopology (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (Om b)) W`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      rand(concl th) = `W:A->bool`)) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN (Om:real->A->bool) b /\ x IN Om t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `t:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC P2BT_RESTRICT_METRIC_RESTRICT THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) b` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  ABBREV_TAC `PB = mfd_pullback_metric (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b)
                     (rfs_vatlas V t) (\y:A. y) (rfs_vmetric V t)` THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `restrict_metric (restrict_atlas (rfs_vatlas (V:(real->A topology)#
                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (Om b)) W
                (restrict_metric (rfs_vatlas V b) (Om b) PB) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BT_RESTRICT_METRIC_PT THEN
    EXISTS_TAC `subtopology (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (Om b)` THEN
    ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
    EXPAND_TAC "PB" THEN MATCH_MP_TAC P2BT_PB_RESTRICT2 THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b`;
      `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) t`;
      `W:A->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BT_RESTRICT_METRIC_RESTRICT THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) b` THEN
    ASM_REWRITE_TAC[]]);;

let P2BT_RVIEW_REGULAR = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) Om.
     p2c_regular_view V /\ (!s. s <= &0 ==> open_in (rfs_vtop V s) (Om s))
     ==> p2c_regular_view (p2bt_rview V Om)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "om")) THEN
  REWRITE_TAC[p2c_regular_view] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "r1") (CONJUNCTS_THEN2 (LABEL_TAC "r2")
    (CONJUNCTS_THEN2 (LABEL_TAC "r3") (CONJUNCTS_THEN2 (LABEL_TAC "r4") (LABEL_TAC "r5"))))) THEN
  SUBGOAL_THEN
   `!t. ~(topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t) = {})
        ==> smooth_manifold_atlas (rfs_vtop V t) (rfs_vatlas V t)`
  (LABEL_TAC "sm") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "r1" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the flow clause, used twice *)
  SUBGOAL_THEN
   `!W a b. a < b /\ rfs_persists (p2bt_rview V Om) W a b
            ==> p2c_vflow (p2bt_rview (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) Om) W a b`
  (LABEL_TAC "fl") THENL
   [MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    REWRITE_TAC[p2c_vflow] THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `W:A->bool = {}` THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CF_RFU_EMPTY THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_persists (p2bt_rview (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) Om) W a b` THEN
      REWRITE_TAC[P2BT_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
      ASM_SIMP_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `Om:real->A->bool`; `W:A->bool`; `a:real`; `b:real`]
                  P2BT_RVIEW_PERSISTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ws"))) THEN
    USE_THEN "r2" (MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[p2c_vflow] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC[P2BT_RVIEW_PARTS; SUBTOPOLOGY_SUBTOPOLOGY; RFS_RESTRICT_ATLAS_RESTRICT] THEN
    SUBGOAL_THEN `(Om:real->A->bool) b INTER W = W` SUBST1_TAC THENL
     [USE_THEN "ws" (MP_TAC o SPEC `b:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC P2CF_RFU_CONG THEN
    EXISTS_TAC `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) W b` THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W a b` THEN
    REWRITE_TAC[P2BT_PERSISTS_ALT] THEN DISCH_THEN(LABEL_TAC "pv") THEN
    SUBGOAL_THEN `t <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "pv" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "pv" (MP_TAC o SPEC `b:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) ((Om:real->A->bool) t) /\
                  open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) ((Om:real->A->bool) b)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "om" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `W SUBSET (Om:real->A->bool) t /\ W SUBSET Om b` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "ws" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_diffeo (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W
                             (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) W (\y:A. y) (\y. y)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_DIFFEO_SYM THEN USE_THEN "r4" MATCH_MP_TAC THEN
      EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[P2BT_PERSISTS_ALT];
      ALL_TAC] THEN
    MATCH_MP_TAC P2BT_RVIEW_VFAM THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* the slices *)
    X_GEN_TAC `t:real` THEN REWRITE_TAC[P2BT_RVIEW_PARTS] THEN
    ASM_CASES_TAC `t <= &0` THEN ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "r1" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) ((Om:real->A->bool) t)` ASSUME_TAC THENL
     [USE_THEN "om" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t` THEN ASM_REWRITE_TAC[];
    (* flows *)
    USE_THEN "fl" ACCEPT_TAC;
    (* flows from the left end *)
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    REWRITE_TAC[p2c_vflow_from] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [USE_THEN "fl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `W:A->bool = {}` THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CF_RFF_EMPTY THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_persists (p2bt_rview (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) Om) W a b` THEN
      REWRITE_TAC[P2BT_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
      ASM_SIMP_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `Om:real->A->bool`; `a:real`; `W:A->bool`] P2BT_RVIEW_OPEN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `Om:real->A->bool`; `W:A->bool`; `a:real`; `b:real`]
                  P2BT_RVIEW_PERSISTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ws"))) THEN
    USE_THEN "r3" (MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[p2c_vflow_from] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC[P2BT_RVIEW_PARTS; SUBTOPOLOGY_SUBTOPOLOGY; RFS_RESTRICT_ATLAS_RESTRICT] THEN
    SUBGOAL_THEN `(Om:real->A->bool) b INTER W = W` SUBST1_TAC THENL
     [USE_THEN "ws" (MP_TAC o SPEC `b:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC P2BT_RFF_CONG THEN
    EXISTS_TAC `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b` THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W a b` THEN
    REWRITE_TAC[P2BT_PERSISTS_ALT] THEN DISCH_THEN(LABEL_TAC "pv") THEN
    SUBGOAL_THEN `t <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "pv" (MP_TAC o SPEC `b:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) ((Om:real->A->bool) t) /\
                  open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) ((Om:real->A->bool) b)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "om" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `W SUBSET (Om:real->A->bool) b` ASSUME_TAC THENL
     [USE_THEN "ws" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `t:real = a` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a) (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a)` ASSUME_TAC THENL
       [USE_THEN "sm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `mfd_diffeo (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W
                               (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a) (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a) W (\y:A. y) (\y. y)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MFD_DIFFEO_SYM THEN USE_THEN "r5" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[P2BT_PERSISTS_ALT];
        ALL_TAC] THEN
      MATCH_MP_TAC P2BT_RVIEW_VFAM THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "pv" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `W SUBSET (Om:real->A->bool) t` ASSUME_TAC THENL
     [USE_THEN "ws" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `mfd_diffeo (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W
                             (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) W (\y:A. y) (\y. y)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_DIFFEO_SYM THEN USE_THEN "r4" MATCH_MP_TAC THEN
      EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[P2BT_PERSISTS_ALT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC P2BT_RVIEW_VFAM THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    (* the identity between slices *)
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`; `s:real`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `W:A->bool = {}` THENL [ASM_REWRITE_TAC[P2CF_DIFFEO_EMPTY]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `Om:real->A->bool`; `W:A->bool`; `a:real`; `b:real`]
                  P2BT_RVIEW_PERSISTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ws"))) THEN
    SUBGOAL_THEN `s <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W a b` THEN
    REWRITE_TAC[P2BT_PERSISTS_ALT] THEN DISCH_THEN(LABEL_TAC "pv") THEN
    USE_THEN "pv" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "pv" (MP_TAC o SPEC `b:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) ((Om:real->A->bool) s) /\
                  open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) ((Om:real->A->bool) b)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "om" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `W SUBSET (Om:real->A->bool) s /\ W SUBSET Om b` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "ws" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[P2BT_RVIEW_PARTS] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`; `(Om:real->A->bool) s`;
                   `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`; `(Om:real->A->bool) b`;
                   `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`] APX_MFD_DIFFEO_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "r4" MATCH_MP_TAC THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[P2BT_PERSISTS_ALT];
    (* the identity from the left end *)
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `W:A->bool = {}` THENL [ASM_REWRITE_TAC[P2CF_DIFFEO_EMPTY]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `Om:real->A->bool`; `a:real`; `W:A->bool`] P2BT_RVIEW_OPEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `Om:real->A->bool`; `W:A->bool`; `a:real`; `b:real`]
                  P2BT_RVIEW_PERSISTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ws"))) THEN
    UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W a b` THEN
    REWRITE_TAC[P2BT_PERSISTS_ALT] THEN DISCH_THEN(LABEL_TAC "pv") THEN
    USE_THEN "pv" (MP_TAC o SPEC `b:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a) (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a)` ASSUME_TAC THENL
     [USE_THEN "sm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a) ((Om:real->A->bool) a) /\
                  open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) ((Om:real->A->bool) b)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "om" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `W SUBSET (Om:real->A->bool) b` ASSUME_TAC THENL
     [USE_THEN "ws" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[P2BT_RVIEW_PARTS] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a`; `(Om:real->A->bool) a`;
                   `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`; `(Om:real->A->bool) b`;
                   `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`] APX_MFD_DIFFEO_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "r5" MATCH_MP_TAC THEN ASM_REWRITE_TAC[P2BT_PERSISTS_ALT]]);;

(* Open sets of slice 0 under boxes of the flow are open in the earlier slices. *)

let P2BT_ID_OPEN_TRANSFER = prove
 (`!top1 top2 X (U:A->bool).
     open_in top1 X /\ open_in top2 U /\
     homeomorphic_maps (subtopology top1 X,subtopology top2 X) ((\y. y),(\y. y))
     ==> open_in top1 (X INTER U)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `X:A->bool` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  DISCH_THEN(MP_TAC o SPEC `X INTER U:A->bool` o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] OPEN_IN_CONTINUOUS_MAP_PREIMAGE)) THEN
  ANTS_TAC THENL [MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
    rator(concl th) = `open_in (top1:A topology)`)) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]);;

let P2BT_BOXES_OPEN = prove
 (`!(Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) S s.
     p2c_regular_view Vl /\ open_in (rfs_vtop Vl (&0)) S /\ s < &0 /\
     (!y. y IN S ==> ?X a. open_in (rfs_vtop Vl (&0)) X /\ y IN X /\ a < s /\
                           p2c_vflow Vl X a (&0))
     ==> open_in (rfs_vtop Vl s) S`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:A) IN S`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `X:A->bool` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `X INTER S:A->bool` THEN ASM_REWRITE_TAC[IN_INTER; INTER_SUBSET] THEN
  MATCH_MP_TAC P2BT_ID_OPEN_TRANSFER THEN
  EXISTS_TAC `rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ASSUME `p2c_vflow (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) X a (&0)`) THEN REWRITE_TAC[p2c_vflow; P2BT_PERSISTS_ALT] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`X:A->bool`; `a:real`; `&0`; `s:real`] o CONJUNCT1 o
    CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [p2c_regular_view]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `p2c_vflow (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) X a (&0)` THEN SIMP_TAC[p2c_vflow];
    SIMP_TAC[mfd_diffeo]]);;

(* Smooth structure of the empty restriction. *)

let P2BT_HOMEO_EMPTY = prove
 (`!(top:A topology) (top':B topology) (f:A->B).
     topspace top = {} /\ topspace top' = {} ==> homeomorphic_map (top,top') f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
  EXISTS_TAC `\y:B. (ARB:A)` THEN
  ASM_SIMP_TAC[homeomorphic_maps; CONTINUOUS_MAP_ON_EMPTY; NOT_IN_EMPTY]);;

let P2BT_SMOOTH_EMPTY = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool).
     smooth_manifold_atlas (subtopology top {}) (restrict_atlas atlas {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smooth_manifold_atlas; IN_RESTRICT_ATLAS] THEN
  REWRITE_TAC[INTER_EMPTY; TOPSPACE_SUBTOPOLOGY; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `U0:A->bool` (CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC)) THEN
    REWRITE_TAC[OPEN_IN_EMPTY; IMAGE_CLAUSES; OPEN_EMPTY] THEN
    MATCH_MP_TAC P2BT_HOMEO_EMPTY THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; INTER_EMPTY];
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `U0:A->bool` (CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC))
      (X_CHOOSE_THEN `V0:A->bool` (CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC))) THEN
    REWRITE_TAC[INTER_EMPTY; IMAGE_CLAUSES; NOT_IN_EMPTY] THEN
    MESON_TAC[P2CF_SMOOTH_MAP_ON_EMPTY]]);;

let P2BT_TUBE_VIEW = prove
 (`!top atlas (g:A->real^3^3) Vl Tb.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2c_regular_view Vl /\ rfs_vtop Vl (&0) = top /\ rfs_vatlas Vl (&0) = atlas /\
     rfs_vmetric Vl (&0) = g /\
     open_in top Tb /\ (!y. y IN Tb ==> &0 < mfd_scalar atlas g y) /\
     (!y s1. y IN topspace top /\ --inv(mfd_scalar atlas g y) < s1 /\ s1 < &0
             ==> ?X a. open_in top X /\ y IN X /\ a < s1 /\
                       (!z. z IN X ==> --inv(mfd_scalar atlas g z) < a) /\
                       p2c_vflow Vl X a (&0)) /\
     (!s y w1 w2. s <= &0 /\ y IN topspace top /\
                  --inv(mfd_scalar atlas g y) < s /\ ~collinear {vec 0,w1,w2}
                  ==> &0 <= mfd_sectional (rfs_vatlas Vl s) (rfs_vmetric Vl s) y w1 w2)
     ==> let Vb = p2bt_rview Vl (\s. {y | y IN Tb /\ --inv(mfd_scalar atlas g y) < s}) in
         p2c_regular_view Vb /\
         rfs_vtop Vb (&0) = subtopology top Tb /\
         rfs_vatlas Vb (&0) = restrict_atlas atlas Tb /\
         rfs_vmetric Vb (&0) = restrict_metric atlas Tb g /\
         (!X a. open_in (subtopology top Tb) X /\
                compact_in (subtopology top Tb) (subtopology top Tb closure_of X) /\
                (!x. x IN X
                     ==> --inv(mfd_scalar (restrict_atlas atlas Tb) (restrict_metric atlas Tb g) x)
                         < a) /\
                a < &0
                ==> p2c_vflow Vb X a (&0)) /\
         (!t x u v. t <= &0 /\ x IN topspace(rfs_vtop Vb t) /\ ~collinear {vec 0,u,v}
                    ==> &0 <= mfd_sectional (rfs_vatlas Vb t) (rfs_vmetric Vb t) x u v) /\
         (!s. s <= &0
              ==> open_in (rfs_vtop Vl s) {y | y IN Tb /\ --inv(mfd_scalar atlas g y) < s})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pos") (CONJUNCTS_THEN2 (LABEL_TAC "box")
       (LABEL_TAC "sec"))))))))))) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `Om = \s. {y:A | y IN Tb /\ --inv(mfd_scalar atlas (g:A->real^3^3) y) < s}` THEN
  SUBGOAL_THEN `(Tb:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s y. y IN (Om:real->A->bool) s <=>
                      y IN Tb /\ --inv(mfd_scalar atlas (g:A->real^3^3) y) < s`
  (LABEL_TAC "omd") THENL [EXPAND_TAC "Om" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(Om:real->A->bool) (&0) = Tb` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `y:A` THEN USE_THEN "omd" (fun th -> REWRITE_TAC[th]) THEN
    EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_NEG_LT0; REAL_LT_INV_EQ] THEN USE_THEN "pos" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the boxes, for points of Tb *)
  SUBGOAL_THEN
   `!y s1. y IN Tb /\ --inv(mfd_scalar atlas (g:A->real^3^3) y) < s1 /\ s1 < &0
           ==> ?X a. open_in top X /\ y IN X /\ a < s1 /\
                     (!z. z IN X ==> --inv(mfd_scalar atlas g z) < a) /\
                     p2c_vflow (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) X a (&0)`
  (LABEL_TAC "bx") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "box" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the sets Om s are open in the slices *)
  SUBGOAL_THEN `!s. s < &0 ==> open_in top ((Om:real->A->bool) s)` (LABEL_TAC "om0") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `y:A` THEN USE_THEN "omd" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    USE_THEN "bx" (MP_TAC o SPECL [`y:A`; `s:real`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
    DISCH_THEN(X_CHOOSE_THEN `X:A->bool` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `X INTER Tb:A->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    USE_THEN "omd" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `a:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s <= &0 ==> open_in (rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) ((Om:real->A->bool) s)`
  (LABEL_TAC "om") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN ASM_CASES_TAC `s = &0` THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `s < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2BT_BOXES_OPEN THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `y:A` THEN USE_THEN "omd" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    USE_THEN "bx" (MP_TAC o SPECL [`y:A`; `s:real`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (p2bt_rview (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) Om)` (LABEL_TAC "reg") THENL
   [MATCH_MP_TAC P2BT_RVIEW_REGULAR THEN ASM_REWRITE_TAC[] THEN USE_THEN "om" ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[P2BT_RVIEW_PARTS; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [(* the box clause *)
    MAP_EVERY X_GEN_TAC [`X:A->bool`; `a:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `open_in top (X:A->bool) /\ X SUBSET Tb` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `Tb:A->bool` THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
          rand(concl th) = `X:A->bool`)) THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x. x IN X ==> --inv(mfd_scalar atlas (g:A->real^3^3) x) < a`
    (LABEL_TAC "xa") THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Tb:A->bool`;
                     `g:A->real^3^3`; `x:A`] MFD_SCALAR_RESTRICT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "reg" (MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[p2c_regular_view]) THEN
    ASM_REWRITE_TAC[P2BT_PERSISTS_ALT; P2BT_RVIEW_PARTS] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `X SUBSET (Om:real->A->bool) s` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      USE_THEN "omd" (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `a:real` THEN ASM_SIMP_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `open_in (rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (X:A->bool)` ASSUME_TAC THENL
     [ASM_CASES_TAC `s = &0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC P2BT_BOXES_OPEN THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      USE_THEN "bx" (MP_TAC o SPECL [`x:A`; `s:real`]) THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `a:real` THEN ASM_SIMP_TAC[];
        MESON_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `(Om:real->A->bool) s = {}` THENL
       [ASM_REWRITE_TAC[P2BT_SMOOTH_EMPTY]; ALL_TAC] THEN
      USE_THEN "reg" (MP_TAC o SPEC `s:real` o CONJUNCT1 o REWRITE_RULE[p2c_regular_view]) THEN
      ASM_REWRITE_TAC[P2BT_RVIEW_PARTS; TOPSPACE_SUBTOPOLOGY] THEN
      ANTS_TAC THENL
       [SUBGOAL_THEN `open_in (rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) ((Om:real->A->bool) s)` MP_TAC THENL
         [USE_THEN "om" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
        UNDISCH_TAC `~((Om:real->A->bool) s = {})` THEN SET_TAC[];
        SIMP_TAC[]];
      MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[]];
    (* the sectional curvature *)
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `u:real^3`; `v:real^3`] THEN
    REWRITE_TAC[P2BT_RVIEW_PARTS] THEN
    ASM_CASES_TAC `t <= &0` THEN ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(topspace(rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:real` o CONJUNCT1 o GEN_REWRITE_RULE I [p2c_regular_view] o
      check (fun th -> concl th = `p2c_regular_view (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(x:A) IN (Om:real->A->bool) t` ASSUME_TAC THENL
     [USE_THEN "omd" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `open_in (rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) ((Om:real->A->bool) t)` ASSUME_TAC THENL
     [USE_THEN "om" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`; `rfs_vatlas (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`; `(Om:real->A->bool) t`;
                   `rfs_vmetric (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`; `x:A`] MFDR_SECTIONAL_SET_RESTRICT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC
      `mfd_sectional (restrict_atlas (rfs_vatlas (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) ((Om:real->A->bool) t))
                     (restrict_metric (rfs_vatlas (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) (Om t) (rfs_vmetric (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)) x u v`) THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    (* the sets Om s are open in the slices of Vl *)
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `{y:A | y IN Tb /\ --inv(mfd_scalar atlas (g:A->real^3^3) y) < s} =
                  (Om:real->A->bool) s` SUBST1_TAC THENL
     [EXPAND_TAC "Om" THEN REWRITE_TAC[];
      USE_THEN "om" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;


(* ========================================================================= *)
(* Evolving necks of a regular view V are evolving necks of the restricted   *)
(* view p2bt_rview V Om when the neck image lies in Om s for all times s of  *)
(* the neck (the restricted slices are open subsets, and pullbacks, scalar   *)
(* curvature and the closeness are local).                                   *)
(* ========================================================================= *)

(* Closeness only depends on the metrics on the open domain. *)

let P2BT_CLOSE_ON_CONG = prove
 (`!k eps s (G0:real^N->real^N^N) G G'.
     open s /\ (!y. y IN s ==> G y = G' y)
     ==> (rfs_close_on k eps s G0 G <=> rfs_close_on k eps s G0 G')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_close_on] THEN
  SUBGOAL_THEN `!y. y IN s ==> lck_dist2 k (G0:real^N->real^N^N) G y = lck_dist2 k G0 G' y`
    (fun th -> MESON_TAC[th]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LCK_DIST2_LOCAL THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[]);;

let P2BT_CLOSE_FAM_CONG = prove
 (`!k eps J s (G0:real->real^N->real^N^N) G G'.
     open s /\ (!t y. t IN J /\ y IN s ==> G t y = G' t y)
     ==> (rfs_close_fam k eps J s G0 G <=> rfs_close_fam k eps J s G0 G')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_close_fam] THEN
  SUBGOAL_THEN `!t y. t IN J /\ y IN s
                      ==> lck_dist2 k ((G0:real->real^N->real^N^N) t) (G t) y =
                          lck_dist2 k (G0 t) (G' t) y`
    (fun th -> MESON_TAC[th]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LCK_DIST2_LOCAL THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[]);;

(* The transfer of an evolving neck at time 0. *)

let P2BT_ENECK_RVIEW = prove
 (`!(Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    Om eps p len (e:real^3->A).
     p2c_regular_view Vl /\ (!s. s <= &0 ==> open_in (rfs_vtop Vl s) (Om s)) /\
     rfs_evolving_neck Vl eps p (&0) len e /\
     (!s. &0 - len / mfd_scalar (rfs_vatlas Vl (&0)) (rfs_vmetric Vl (&0)) p < s /\ s <= &0
          ==> IMAGE e (rfs_neck_dom eps) SUBSET Om s)
     ==> rfs_evolving_neck (p2bt_rview Vl Om) eps p (&0) len e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "reg") (CONJUNCTS_THEN2 (LABEL_TAC "om")
    (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "in")))) THEN
  REWRITE_TAC[P2BN_EVOLVING_NECK_ALT; P2BN_RFS_VSCALAR] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ps") (LABEL_TAC "cf")))) THEN
  USE_THEN "nk" (STRIP_ASSUME_TAC o REWRITE_RULE[rfs_neck]) THEN
  ABBREV_TAC `R = mfd_scalar (rfs_vatlas (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) (rfs_vmetric Vl (&0)) (p:A)` THEN
  SUBGOAL_THEN `(p:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(p:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 - len / R < &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 - x < &0`) THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET (Om:real->A->bool) (&0)`
  ASSUME_TAC THENL
   [USE_THEN "in" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) ((Om:real->A->bool) (&0))`
  ASSUME_TAC THENL
   [USE_THEN "om" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace(rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0))`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) ((Om:real->A->bool) (&0))`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (rfs_vatlas (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) (rfs_vmetric Vl (&0))`
  ASSUME_TAC THENL
   [USE_THEN "reg" (MP_TAC o SPEC `&0` o CONJUNCT1 o REWRITE_RULE[p2c_regular_view]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar (restrict_atlas (rfs_vatlas (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) ((Om:real->A->bool) (&0)))
               (restrict_metric (rfs_vatlas Vl (&0)) (Om (&0)) (rfs_vmetric Vl (&0))) (p:A) = R`
  ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC MFD_SCALAR_RESTRICT THEN
    EXISTS_TAC `rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. --len < t /\ t <= &0 ==> &0 - len / R < &0 + t / R /\ &0 + t / R <= &0`
  (LABEL_TAC "tr") THENL
   [GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[REAL_ADD_LID] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN
    REWRITE_TAC[REAL_ARITH `&0 - x = --x`; real_div; GSYM REAL_MUL_LNEG] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ];
    ALL_TAC] THEN
  (* the neck at time 0 in the restricted slice *)
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology (rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) ((Om:real->A->bool) (&0)))
                          (restrict_atlas (rfs_vatlas Vl (&0)) (Om (&0)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_param (subtopology (rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) ((Om:real->A->bool) (&0)))
              (restrict_atlas (rfs_vatlas Vl (&0)) (Om (&0))) (rfs_neck_dom eps) (e:real^3->A)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[APX_PARAM_RESTRICT_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_close_on (rfs_kreg eps) eps (rfs_neck_dom eps) (cylinder_flow (&0))
      (\y. R %% rfs_pullback (restrict_atlas (rfs_vatlas (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) ((Om:real->A->bool) (&0)))
                             (e:real^3->A)
                             (restrict_metric (rfs_vatlas Vl (&0)) (Om (&0)) (rfs_vmetric Vl (&0))) y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_kreg eps`; `eps:real`; `rfs_neck_dom eps`; `cylinder_flow (&0)`;
      `\y. R %% rfs_pullback (restrict_atlas (rfs_vatlas (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) ((Om:real->A->bool) (&0)))
                             (e:real^3->A)
                             (restrict_metric (rfs_vatlas Vl (&0)) (Om (&0)) (rfs_vmetric Vl (&0))) y`;
      `\y. R %% rfs_pullback (rfs_vatlas (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) (e:real^3->A) (rfs_vmetric Vl (&0)) y`]
      P2BT_CLOSE_ON_CONG) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[APX_NECK_DOM_OPEN] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      BETA_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC P2BT_RFS_PULLBACK_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
                            `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[P2BT_RVIEW_PARTS; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* the neck *)
    REWRITE_TAC[rfs_neck] THEN ASM_REWRITE_TAC[];
    (* persistence *)
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ps" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_SIMP_TAC[]];
    (* the family closeness *)
    USE_THEN "cf" MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC P2BT_CLOSE_FAM_CONG THEN REWRITE_TAC[APX_NECK_DOM_OPEN; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "tr" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P2BT_RFS_PULLBACK_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`rfs_vtop (Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0 + t / R)`;
                          `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "ps" (MP_TAC o SPEC `&0 + t / R`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "om" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BT_VIEW_PARAM_AT THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (e:real^3->A) (rfs_neck_dom eps)`; `&0 - len / R`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL; P2BT_PERSISTS_ALT];
      USE_THEN "in" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* The central sphere of a 2 eps-neck inside T separates the two ends of T   *)
(* (MT Def 9.81 for the bad tube).  The neck lies in a finite union U_n of   *)
(* chain necks, the later chain necks miss it (curvature), and the A13 tube  *)
(* of the chain e_0 ... e_n has the sphere-separation property (apx_tube):   *)
(* the inner end of H is the inner end of that tube, and the outer end of H  *)
(* is joined to the outer end of the tube through the later chain necks,     *)
(* which avoid the sphere.                                                   *)
(* ========================================================================= *)

(* Separation passes to a subspace containing both points. *)

let P2BT_SEP_SUBTOP = prove
 (`!top S T (p:A) q.
     apx_separates top S p q /\ p IN T /\ q IN T
     ==> apx_separates (subtopology top T) S p q`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[apx_separates; connected_component_of; TOPSPACE_SUBTOPOLOGY;
              CONNECTED_IN_SUBTOPOLOGY; IN_DIFF; IN_INTER] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_exists(rand(concl th)))) THEN
  REWRITE_TAC[] THEN EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Finite segments of a one-sided chain are connected. *)

let P2BT_CHAIN_SEG_CONNECTED = prove
 (`!top atlas (g:A->real^3^3) eps x (e:int->real^3->A) n d.
     apx_chain (top,atlas) g eps {i:int | &0 <= i} x e
     ==> connected_in top
           (UNIONS (IMAGE (\k. IMAGE (e(&k)) (rfs_neck_dom eps)) (n..n + d)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k. rfs_neck (top,atlas) g eps ((x:int->A)(&k)) ((e:int->real^3->A)(&k))`
  (LABEL_TAC "nk") THENL
   [GEN_TAC THEN
    UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i} x e` THEN
    REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `&k:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[INT_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. connected_in top (IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps))`
  (LABEL_TAC "cn") THENL
   [GEN_TAC THEN MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
     [USE_THEN "nk" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[rfs_neck];
      REWRITE_TAC[rfs_neck_dom; APX_CONNECTED_ANNULUS3]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
   [USE_THEN "nk" (MP_TAC o SPEC `0`) THEN SIMP_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. ~(IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps) INTER
                      IMAGE (e(&(k + 1))) (rfs_neck_dom eps) = {})`
  (LABEL_TAC "ov") THENL
   [GEN_TAC THEN
    MP_TAC(SPECL [`inv(&2 * eps)`; `inv eps`] APX_SLAB_NONEMPTY) THEN
    ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^3`) THEN
    UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i} x e` THEN
    REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `&k:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[INT_POS; INT_OF_NUM_ADD] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[UNION_SUBSET] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; SUBSET] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:int->real^3->A)(&k) y`) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
                    MESON_TAC[]];
    ALL_TAC] THEN
  SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; NUMSEG_SING; IMAGE_CLAUSES; UNIONS_1] THEN BETA_TAC THEN
    USE_THEN "cn" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; NUMSEG_CLAUSES; ARITH_RULE `n <= SUC(n + d)`;
              IMAGE_CLAUSES; UNIONS_INSERT] THEN BETA_TAC THEN
  MATCH_MP_TAC CONNECTED_IN_UNION THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ov" (MP_TAC o SPEC `n + d:num`) THEN REWRITE_TAC[GSYM ADD1] THEN
  MATCH_MP_TAC(SET_RULE `(t:A->bool) SUBSET u ==> ~(t INTER s = {}) ==> ~(s INTER u = {})`) THEN
  MP_TAC(ISPECL [`\k. IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps)`; `n..n + d`;
                 `n + d:num`]
    (SET_RULE `!(f:num->A->bool) s k. k IN s ==> f k SUBSET UNIONS (IMAGE f s)`)) THEN
  REWRITE_TAC[IN_NUMSEG; LE_REFL; LE_ADD] THEN BETA_TAC THEN SIMP_TAC[]);;

(* A point of the outer collar of an A13 tube in its last neck. *)

let P2BT_TUBE_OUTER_POINT = prove
 (`!eps n (e:int->real^3->A) (En:real^3->A) L (f:real^3->real^3) f' rho2.
     &0 < eps /\ &0 <= L /\ sphere_diffeo f f' /\
     (!y. y IN apx_slab (L - inv(&8 * eps)) (L + inv eps)
          ==> En y = e (&n) (radial_ext f (exp(--L / sqrt(&2)) % y))) /\
     rho2 < exp((L + inv eps) / sqrt(&2))
     ==> ?q. q IN IMAGE (En:real^3->A) (annulus rho2 (exp((L + inv eps) / sqrt(&2)))) /\
             q IN IMAGE (e(&n)) (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `r2n = exp((L + inv eps) / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps /\ &0 < inv(&8 * eps) /\ inv(&8 * eps) < inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp((L - inv(&8 * eps)) / sqrt(&2)) < r2n` ASSUME_TAC THENL
   [EXPAND_TAC "r2n" THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `lo = max rho2 (exp((L - inv(&8 * eps)) / sqrt(&2)))` THEN
  SUBGOAL_THEN `rho2 <= lo /\ exp((L - inv(&8 * eps)) / sqrt(&2)) <= lo /\ lo < r2n /\ &0 < lo`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lo" THEN MP_TAC(SPEC `(L - inv(&8 * eps)) / sqrt(&2)` REAL_EXP_POS_LT) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `z0:real^3 = ((lo + r2n) / &2) % basis 1` THEN
  SUBGOAL_THEN `norm(z0:real^3) = (lo + r2n) / &2` ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z0:real^3) IN annulus rho2 r2n` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z0:real^3) IN apx_slab (L - inv(&8 * eps)) (L + inv eps)` ASSUME_TAC THENL
   [REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(En:real^3->A) z0` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z0:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `(z0:real^3) IN apx_slab (L - inv(&8 * eps)) (L + inv eps)`)]) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `radial_ext f (exp(--L / sqrt(&2)) % z0:real^3)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(z0:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(radial_ext f (exp(--L / sqrt(&2)) % z0:real^3)) =
                norm(exp(--L / sqrt(&2)) % z0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN
    UNDISCH_TAC `sphere_diffeo (f:real^3->real^3) f'` THEN
    REWRITE_TAC[sphere_diffeo] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval(radial_ext f (exp(--L / sqrt(&2)) % z0:real^3)) = --L + apx_sval z0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `apx_sval(exp(--L / sqrt(&2)) % z0:real^3)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[apx_sval] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_SIMP_TAC[APX_SVAL_EXP_SCALE]];
    ALL_TAC] THEN
  MP_TAC(ASSUME `(z0:real^3) IN apx_slab (L - inv(&8 * eps)) (L + inv eps)`) THEN
  REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
  REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_EXP] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* Radii of the inner end of H: p2bt_rad r0 maps a thin inner annulus into *)
(* a given thin annulus above r0.                                          *)

let P2BT_INNER_RADIUS = prove
 (`!r0 h. &0 < r0 /\ r0 < h
          ==> ?r2. &1 < r2 /\ r2 < &2 /\
                   !w:real^3. &1 < norm w /\ norm w < r2
                              ==> r0 < norm(p2bt_rad r0 w) /\ norm(p2bt_rad r0 w) < h`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = h - r0` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r2 = (&1 + &2 * d) / (&1 + d)` THEN
  SUBGOAL_THEN `&1 < r2 /\ r2 < &2 /\ r2 * (&1 + d) = &1 + &2 * d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r2" THEN
    SUBGOAL_THEN `&0 < &1 + d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `r2:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r0:real`; `w:real^3`; `w:real^3`] P2BT_RAD_NORMS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(norm(w:real^3) - &1) / (&2 - norm w) < d` MP_TAC THENL
   [SUBGOAL_THEN `&0 < &2 - norm(w:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `norm(w:real^3) * (&1 + d) < r2 * (&1 + d)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* The later chain necks miss a neck of R about R(p) inside T, which lies   *)
(* in a finite part of the chain.                                          *)

let P2BT_NECK_TAIL = prove
 (`?eps0. &0 < eps0 /\
     !eps top atlas (g:A->real^3^3) x e E D p e'.
        &0 < eps /\ eps <= eps0 /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ p2bt_cchart eps top atlas g x e E /\
        (!n. sum(0..n) (\i. inv(sqrt(mfd_scalar atlas g (x(&i))))) <= D) /\
        rfs_neck (top,atlas) g (&2 * eps) p e' /\
        IMAGE e' (rfs_neck_dom (&2 * eps)) SUBSET
        apx_chain_union (&2 * eps) {i:int | &0 <= i} e
        ==> ?n. (!k. n <= k ==> DISJOINT (IMAGE (e(&k)) (rfs_neck_dom (&2 * eps)))
                                          (IMAGE e' (rfs_neck_dom (&2 * eps)))) /\
                IMAGE e' (rfs_neck_dom (&2 * eps)) SUBSET
                apx_chain_union (&2 * eps) {i:int | &0 <= i /\ i <= &n} e`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cb"))
    (INST_TYPE [`:A`,`:A`] P2BT_CHART_BASICS) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_H) THEN
  EXISTS_TAC `min e1 (e2 / &2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `x:int->A`; `e:int->real^3->A`; `E:real^3->A`; `D:real`; `p:A`;
    `e':real^3->A`] THEN
  STRIP_TAC THEN
  USE_THEN "cb" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "mem") (CONJUNCTS_THEN2 (LABEL_TAC "rc")
    (CONJUNCTS_THEN2 (K ALL_TAC) (K ALL_TAC)))))) THEN
  SUBGOAL_THEN
   `!y. y IN rfs_neck_dom (&2 * eps)
        ==> mfd_scalar atlas (g:A->real^3^3) ((e':real^3->A) y) <=
            &101 / &100 * mfd_scalar atlas g p`
  (LABEL_TAC "rp") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "nh" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `&2 * eps`; `p:A`; `e':real^3->A`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) p` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) (&2 * eps) p e'` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_chain (top,atlas) (g:A->real^3^3) (&2 * eps) {i:int | &0 <= i} x e`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_cchart eps top atlas (g:A->real^3^3) x e E` THEN
    SIMP_TAC[p2bt_cchart];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `&2 * eps`; `x:int->A`; `e:int->real^3->A`; `D:real`] P2BT_CHAIN_RINF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num` o SPEC `&2 * mfd_scalar atlas (g:A->real^3^3) p`) THEN
  EXISTS_TAC `n:num` THEN
  SUBGOAL_THEN
   `!k. n <= k ==> DISJOINT (IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom (&2 * eps)))
                            (IMAGE (e':real^3->A) (rfs_neck_dom (&2 * eps)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `z:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(e:int->real^3->A)(&k) y1 = (e':real^3->A) y2` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "rc" (MP_TAC o SPECL [`&k:int`; `y1:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INT_POS]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "rp" (MP_TAC o SPEC `y2:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&2 * mfd_scalar atlas (g:A->real^3^3) p`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:A) IN apx_chain_union (&2 * eps) {i:int | &0 <= i} e` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> USE_THEN "mem" (MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC `i:int` INT_OF_NUM_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `(z:A) IN IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom (&2 * eps))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[apx_chain_union; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom (&2 * eps))` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]] THEN
  EXISTS_TAC `&k:int` THEN REWRITE_TAC[INT_POS; INT_OF_NUM_LE] THEN
  ASM_CASES_TAC `n:num <= k` THENL [ALL_TAC; UNDISCH_TAC `~(n:num <= k)` THEN ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Separation from a point of a later chain neck passes to the points of    *)
(* all later chain necks (they avoid the sphere and their union is          *)
(* connected).                                                              *)

let P2BT_SEP_FAR = prove
 (`!top atlas (g:A->real^3^3) eps x (e:int->real^3->A) S n j p1 q0 q.
     apx_chain (top,atlas) g eps {i:int | &0 <= i} x e /\
     (!k. n <= k ==> DISJOINT (IMAGE (e(&k)) (rfs_neck_dom eps)) S) /\
     apx_separates top S p1 q0 /\ q0 IN IMAGE (e(&n)) (rfs_neck_dom eps) /\
     n <= j /\ q IN IMAGE (e(&j)) (rfs_neck_dom eps)
     ==> apx_separates top S p1 q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `C = UNIONS (IMAGE (\k. IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps))
                                (n..n + (j - n)))` THEN
  SUBGOAL_THEN `connected_in top (C:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC P2BT_CHAIN_SEG_CONNECTED THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `x:int->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. n <= k /\ k <= j
                    ==> IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps) SUBSET C`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "C" THEN
    MP_TAC(ISPECL [`\k. IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps)`;
                   `n..n + (j - n)`; `k:num`]
      (SET_RULE `!(f:num->A->bool) s k. k IN s ==> f k SUBSET UNIONS (IMAGE f s)`)) THEN
    REWRITE_TAC[IN_NUMSEG] THEN BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. rfs_neck (top,atlas) g eps ((x:int->A)(&k)) ((e:int->real^3->A)(&k))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i} x e` THEN
    REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `&k:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[INT_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C:A->bool) SUBSET topspace top DIFF S` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps) SUBSET topspace top`
    MP_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      REWRITE_TAC[SUBSET_REFL] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
      SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q0:A) IN C /\ (q:A) IN C` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `C:A->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[LE_REFL] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `C:A->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[LE_REFL] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p1:A) IN topspace top /\ ~(p1 IN S)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apx_separates top S (p1:A) q0` THEN SIMP_TAC[apx_separates; IN_DIFF];
    ALL_TAC] THEN
  MATCH_MP_TAC APX_SEP_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`{p1:A}`; `C:A->bool`; `{p1:A}`; `C:A->bool`; `p1:A`; `q0:A`] THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SING; SING_SUBSET; IN_SING; IN_UNION; INTER_IDEMPOT;
                  IN_DIFF; NOT_INSERT_EMPTY] THEN
  ASM SET_TAC[]);;

(* The separation clause of the bad tube for one neck. *)

let P2BT_NECK_SEP = prove
 (`?eps0. &0 < eps0 /\
     !eps top atlas (g:A->real^3^3) x e E p e'.
        &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
        p2bt_cchart eps top atlas g x e E /\
        (?D. !n. sum(0..n) (\i. inv(sqrt(mfd_scalar atlas g (x(&i))))) <= D) /\
        rfs_neck (top,atlas) g (&2 * eps) p e' /\
        IMAGE e' (rfs_neck_dom (&2 * eps)) SUBSET
        apx_chain_union (&2 * eps) {i:int | &0 <= i} e
        ==> ?r2 r3. &1 < r2 /\ r2 < r3 /\ r3 < &2 /\
                    !w1 w2. &1 < norm w1 /\ norm w1 < r2 /\ r3 < norm w2 /\ norm w2 < &2
                            ==> apx_separates
                                  (subtopology top
                                     (apx_chain_union (&2 * eps) {i:int | &0 <= i} e))
                                  (IMAGE e' (sphere(vec 0,&1)))
                                  ((E o p2bt_rad (exp(--inv(&2 * eps) / sqrt(&2)))) w1)
                                  ((E o p2bt_rad (exp(--inv(&2 * eps) / sqrt(&2)))) w2)`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))
    (INST_TYPE [`:A`,`:A`] P2BT_TUBE_STATIC) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cb"))
    (INST_TYPE [`:A`,`:A`] P2BT_CHART_BASICS) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tl"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_TAIL) THEN
  X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a13"))
    (ISPEC `UNIV:A->bool` APX_A13_UNCOND) THEN
  EXISTS_TAC `min (min e1 e2) (min e3 (e4 / &2))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `x:int->A`; `e:int->real^3->A`; `E:real^3->A`; `p:A`;
    `e':real^3->A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `D:real`)
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= e2 /\ eps <= e3 /\ &2 * eps <= e4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the static clauses: curvature tends to infinity at the outer end *)
  USE_THEN "st" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(fun th -> LABEL_TAC "rinf" (CONJUNCT1(funpow 10 CONJUNCT2 th))) THEN
  (* chain facts *)
  USE_THEN "cb" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "mem") (CONJUNCTS_THEN2 (LABEL_TAC "rc")
    (CONJUNCTS_THEN2 (K ALL_TAC) (K ALL_TAC)))))) THEN
  (* the neck lies in a finite part; later necks miss it *)
  USE_THEN "tl" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`; `D:real`; `p:A`; `e':real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 (LABEL_TAC "dj") ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bt_cchart] o check (fun th ->
    let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "p2bt_cchart")) THEN
  (* the A13 tube of the chain e_0 ... e_n *)
  USE_THEN "a13" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `&2 * eps`; `n:num`; `x:int->A`; `e:int->real^3->A`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[APXC_SUBCHAIN_UPTO] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `En:real^3->A` (X_CHOOSE_THEN `L:real`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  ABBREV_TAC `TT = apx_chain_union (&2 * eps) {i:int | &0 <= i} (e:int->real^3->A)` THEN
  ABBREV_TAC `r0 = exp(--inv(&2 * eps) / sqrt(&2))` THEN
  ABBREV_TAC `r2n = exp((L + inv(&2 * eps)) / sqrt(&2))` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [apx_tube] o check (fun th ->
    let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "apx_tube")) THEN
  SUBGOAL_THEN `IMAGE (En:real^3->A) (annulus r0 r2n) =
                apx_chain_union (&2 * eps) {i:int | &0 <= i /\ i <= &n} e`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r0"; "r2n"] THEN ASM_REWRITE_TAC[GSYM apx_slab]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE (En:real^3->A) (annulus r0 r2n)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e':real^3->A) (rfs_neck_dom (&2 * eps))` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:A`; `e':real^3->A`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ends_sep")) (concl th))) THEN
  ASM_REWRITE_TAC[apx_ends_sep] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho1:real` (X_CHOOSE_THEN `rho2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sepn"))))))) THEN
  (* a point of the outer collar in the last neck *)
  MP_TAC(ISPECL [`&2 * eps`; `n:num`; `e:int->real^3->A`; `En:real^3->A`; `L:real`;
                 `f:real^3->real^3`; `f':real^3->real^3`; `rho2:real`]
                P2BT_TUBE_OUTER_POINT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q0:A` STRIP_ASSUME_TAC) THEN
  (* the inner radius *)
  MP_TAC(SPECL [`r0:real`; `min rho1 (exp(inv(&8 * &2 * eps) / sqrt(&2)))`]
               P2BT_INNER_RADIUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN EXPAND_TAC "r0" THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b ==> --a < b`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ir"))))] THEN
  (* a bound for the curvature of the centres up to n *)
  SUBGOAL_THEN `?M. &0 <= M /\
                    !k. k <= n ==> mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&k)) <= M`
  (X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mb"))) THENL
   [MP_TAC(ISPECL [`\k. mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&k))`; `0..n`]
                  UPPER_BOUND_FINITE_SET_REAL) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN
    DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN EXISTS_TAC `max (&0) M` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the outer radius *)
  USE_THEN "rinf" (MP_TAC o SPEC `&2 * M + &1`) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rr"))) THEN
  SUBGOAL_THEN `!w:real^3. &1 < norm w /\ norm w < &2 ==> ((E:real^3->A) o p2bt_rad r0) w IN TT`
  (LABEL_TAC "hT") THENL
   [X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `TT:A->bool` &&
      (let c,args = strip_comb(lhs(concl th)) in is_const c && fst(dest_const c) = "IMAGE" && length args = 2))) THEN
    REWRITE_TAC[o_THM; IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `p2bt_rad r0 (w:real^3)` THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`r0:real`; `w:real^3`; `w:real^3`] P2BT_RAD_NORMS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ANTS_TAC THENL [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r2:real`; `max r ((r2 + &2) / &2)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w1:real^3`; `w2:real^3`] THEN STRIP_TAC THEN
  (* the inner point lies in the inner collar of the tube *)
  SUBGOAL_THEN `((E:real^3->A) o p2bt_rad r0) w1 IN IMAGE (En:real^3->A) (annulus r0 rho1)` ASSUME_TAC THENL
   [USE_THEN "ir" (MP_TAC o SPEC `w1:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM; IN_IMAGE] THEN EXISTS_TAC `p2bt_rad r0 (w1:real^3)` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `p2bt_rad r0 (w1:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&8 * &2 * eps))`
      ASSUME_TAC THENL
       [REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_separates top (IMAGE (e':real^3->A) (sphere(vec 0,&1)))
                  (((E:real^3->A) o p2bt_rad r0) w1) q0` ASSUME_TAC THENL
   [USE_THEN "sepn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the outer point lies in a later chain neck *)
  SUBGOAL_THEN `((E:real^3->A) o p2bt_rad r0) w2 IN TT` ASSUME_TAC THENL
   [USE_THEN "hT" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * M + &1 <= mfd_scalar atlas (g:A->real^3^3)
                                 (((E:real^3->A) o p2bt_rad r0) w2)` ASSUME_TAC THENL
   [USE_THEN "rr" (MP_TAC o SPEC `w2:real^3`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MFD_SCALAR_RESTRICT THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "mem" (MP_TAC o C MATCH_MP (ASSUME `((E:real^3->A) o p2bt_rad r0) w2 IN TT`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC `i:int` INT_OF_NUM_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `n:num <= j` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "rc" (MP_TAC o SPECL [`&j:int`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INT_POS]; STRIP_TAC] THEN
    USE_THEN "mb" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `j:num < n` THEN ARITH_TAC; DISCH_TAC] THEN
    UNDISCH_TAC `&2 * M + &1 <= mfd_scalar atlas (g:A->real^3^3)
                                  (((E:real^3->A) o p2bt_rad r0) w2)` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* separation in the manifold, then in T *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `&2 * eps`; `x:int->A`; `e:int->real^3->A`;
                 `IMAGE (e':real^3->A) (sphere(vec 0,&1))`; `n:num`; `j:num`;
                 `((E:real^3->A) o p2bt_rad r0) w1`; `q0:A`;
                 `((E:real^3->A) o p2bt_rad r0) w2`] P2BT_SEP_FAR) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE `!s t (u:A->bool). t SUBSET u /\ DISJOINT s u ==> DISJOINT s t`) THEN
      EXISTS_TAC `IMAGE (e':real^3->A) (rfs_neck_dom (&2 * eps))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN
        ASM_REAL_ARITH_TAC;
        USE_THEN "dj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
      lhs(concl th) = `((E:real^3->A) o p2bt_rad r0) w2` then SUBST1_TAC(SYM th) else NO_TAC) THEN
  MATCH_MP_TAC P2BT_SEP_SUBTOP THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "hT" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]);;

(* ========================================================================= *)
(* The evolving necks of the bad tube.  Far out in the chain (R large) the   *)
(* evolving 2 eps-necks of Vl at the points of T lie in T                    *)
(* (P2BT_FRONTIER_CONTAIN), stay inside the sets Om s of the restricted view *)
(* over their time range (R varies by 1 per cent on a neck), so they are     *)
(* evolving necks of the restricted view (P2BT_ENECK_RVIEW), and their       *)
(* central spheres separate the two ends of T (P2BT_NECK_SEP).               *)
(* ========================================================================= *)

let P2BT_TUBE_NECKS = prove
 (`?eps0. &0 < eps0 /\
     !eps top atlas (g:A->real^3^3) Vl x e E.
        &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
        p2c_regular_view Vl /\ rfs_vtop Vl (&0) = top /\ rfs_vatlas Vl (&0) = atlas /\
        rfs_vmetric Vl (&0) = g /\
        p2bt_cchart eps top atlas g x e E /\
        (?D. !n. sum(0..n) (\i. inv(sqrt(mfd_scalar atlas g (x(&i))))) <= D) /\
        (?K. !y. y IN topspace top /\ K <= mfd_scalar atlas g y
                 ==> ?e'. rfs_evolving_neck Vl (&2 * eps) y (&0) (&1 / &2) e') /\
        (!s. s <= &0
             ==> open_in (rfs_vtop Vl s)
                   {y | y IN apx_chain_union (&2 * eps) {i:int | &0 <= i} e /\
                        --inv(mfd_scalar atlas g y) < s})
        ==> let TT = apx_chain_union (&2 * eps) {i:int | &0 <= i} e in
            let H = E o p2bt_rad (exp(--inv(&2 * eps) / sqrt(&2))) in
            let Vb = p2bt_rview Vl (\s. {y | y IN TT /\ --inv(mfd_scalar atlas g y) < s}) in
            ?r1. &1 < r1 /\ r1 < &2 /\
                 !y. r1 < norm y /\ norm y < &2
                     ==> ?e'. rfs_evolving_neck Vb (&2 * eps) (H y) (&0) (&1 / &2) e' /\
                              ?r2 r3. &1 < r2 /\ r2 < r3 /\ r3 < &2 /\
                                      !w1 w2. &1 < norm w1 /\ norm w1 < r2 /\
                                              r3 < norm w2 /\ norm w2 < &2
                                              ==> apx_separates (subtopology top TT)
                                                    (IMAGE e' (sphere(vec 0,&1)))
                                                    (H w1) (H w2)`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))
    (INST_TYPE [`:A`,`:A`] P2BT_TUBE_STATIC) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fc"))
    (INST_TYPE [`:A`,`:A`] P2BT_FRONTIER_CONTAIN) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sp"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_SEP) THEN
  X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_H) THEN
  X_CHOOSE_THEN `e5:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cb"))
    (INST_TYPE [`:A`,`:A`] P2BT_CHART_BASICS) THEN
  EXISTS_TAC `min (min e1 e2) (min e3 (min (e4 / &2) e5))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`;
    `Vl:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:int->A`; `e:int->real^3->A`; `E:real^3->A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `D:real`)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `K:real` (LABEL_TAC "kn")) (LABEL_TAC "om")))))))))))))) THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= e2 /\ eps <= e3 /\ &2 * eps <= e4 /\ eps <= e5`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  (* curvature tends to infinity at the outer end *)
  USE_THEN "st" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(fun th -> LABEL_TAC "rinf" (CONJUNCT1(funpow 10 CONJUNCT2 th))) THEN
  USE_THEN "cb" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  USE_THEN "fc" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
    `e:int->real^3->A`; `E:real^3->A`; `D:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "fc1")] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bt_cchart] o check (fun th ->
    let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "p2bt_cchart")) THEN
  ABBREV_TAC `TT = apx_chain_union (&2 * eps) {i:int | &0 <= i} (e:int->real^3->A)` THEN
  ABBREV_TAC `r0 = exp(--inv(&2 * eps) / sqrt(&2))` THEN
  ABBREV_TAC `R0 = mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&0))` THEN
  SUBGOAL_THEN `&0 < r0` ASSUME_TAC THENL
   [EXPAND_TAC "r0" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  USE_THEN "rinf" (MP_TAC o SPEC `max K (&3 * R0 + &1)`) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rr"))) THEN
  EXISTS_TAC `max r (&3 / &2)` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `((E:real^3->A) o p2bt_rad r0) w IN TT` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `TT:A->bool` &&
      (let c,args = strip_comb(lhs(concl th)) in is_const c && fst(dest_const c) = "IMAGE" && length args = 2))) THEN
    REWRITE_TAC[o_THM; IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `p2bt_rad r0 (w:real^3)` THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`r0:real`; `w:real^3`; `w:real^3`] P2BT_RAD_NORMS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ANTS_TAC THENL [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `max K (&3 * R0 + &1) <=
                mfd_scalar atlas (g:A->real^3^3) (((E:real^3->A) o p2bt_rad r0) w)`
  ASSUME_TAC THENL
   [USE_THEN "rr" (MP_TAC o SPEC `w:real^3`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MFD_SCALAR_RESTRICT THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `P = ((E:real^3->A) o p2bt_rad r0) w` THEN
  (* the evolving neck of Vl at P *)
  USE_THEN "kn" (MP_TAC o SPEC `P:A`) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (TT:A->bool)`)) THEN ASM SET_TAC[];
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `e':real^3->A` (LABEL_TAC "en"))] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) (&2 * eps) P e'` ASSUME_TAC THENL
   [USE_THEN "en" (MP_TAC o CONJUNCT1 o REWRITE_RULE[P2BN_EVOLVING_NECK_ALT]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (rfs_neck_dom (&2 * eps)) SUBSET TT` ASSUME_TAC THENL
   [USE_THEN "fc1" (MP_TAC o SPECL [`P:A`; `e':real^3->A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `e':real^3->A` THEN CONJ_TAC THENL
   [(* the evolving neck of the restricted view *)
    MATCH_MP_TAC P2BT_ENECK_RVIEW THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "nh" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `&2 * eps`; `P:A`; `e':real^3->A`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) P` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) (&2 * eps) P e'` THEN
      SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&2 * mfd_scalar atlas (g:A->real^3^3) P) <=
                  inv(mfd_scalar atlas g ((e':real^3->A) v))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 / &2) / mfd_scalar atlas (g:A->real^3^3) P =
                  inv(&2 * mfd_scalar atlas g P)` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < mfd_scalar atlas (g:A->real^3^3) P` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    (* the separation of the ends *)
    USE_THEN "sp" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:int->A`;
      `e:int->real^3->A`; `E:real^3->A`; `P:A`; `e':real^3->A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The generic assembly (statement here; the proof is decomposed below).  A  *)
(* sphere-separating manifold with a regular view Vl of slice 0, a one-sided *)
(* chain of 2 eps-necks with summable scales, boxes of the flow under every  *)
(* point, sectional curvature >= 0 on the boxes and evolving 2 eps-necks of  *)
(* length 1/2 at the points of large curvature carry a bad tube: the chain   *)
(* union T (chart E of P2BT_REQ_CHAIN_CHART composed with a radial           *)
(* diffeomorphism from annulus(1,2)), with the view Vl restricted to the     *)
(* sets of T where -1/R < s.                                                 *)
(* ========================================================================= *)

let P2BT_TUBE_ASSEMBLY = prove
 (`!w:B->bool.
     P2BT_REQ_CHAIN_CHART_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !eps (top:B topology) atlas g Vl x e.
              &0 < eps /\ eps <= eps0 /\
              hausdorff_space top /\ smooth_manifold_atlas top atlas /\
              riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
              p2c_regular_view Vl /\ rfs_vtop Vl (&0) = top /\ rfs_vatlas Vl (&0) = atlas /\
              rfs_vmetric Vl (&0) = g /\
              apx_chain (top,atlas) g (&2 * eps) {i:int | &0 <= i} x (e:int->real^3->B) /\
              (?D. !n. sum(0..n) (\i. inv(sqrt(mfd_scalar atlas g (x(&i))))) <= D) /\
              (!y s1. y IN topspace top /\ --inv(mfd_scalar atlas g y) < s1 /\ s1 < &0
                      ==> ?X a. open_in top X /\ y IN X /\ a < s1 /\
                                (!z. z IN X ==> --inv(mfd_scalar atlas g z) < a) /\
                                p2c_vflow Vl X a (&0)) /\
              (!s y w1 w2. s <= &0 /\ y IN topspace top /\
                           --inv(mfd_scalar atlas g y) < s /\ ~collinear {vec 0,w1,w2}
                           ==> &0 <= mfd_sectional (rfs_vatlas Vl s) (rfs_vmetric Vl s)
                                                   y w1 w2) /\
              (?K. !y. y IN topspace top /\ K <= mfd_scalar atlas g y
                       ==> ?e'. rfs_evolving_neck Vl (&2 * eps) y (&0) (&1 / &2) e')
              ==> ?top' atlas' g' Vb H. p2b_bad_tube eps (top':B topology,atlas') g' Vb H`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (INST_TYPE [`:B`,`:A`] P2BT_CCHART_EXISTS)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cc"))) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))
    (INST_TYPE [`:B`,`:A`] P2BT_TUBE_STATIC) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nk"))
    (INST_TYPE [`:B`,`:A`] P2BT_TUBE_NECKS) THEN
  EXISTS_TAC `min e1 (min e2 e3)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
    `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
    `x:int->B`; `e:int->real^3->B`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= e2 /\ eps <= e3` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "cc" (MP_TAC o SPECL
    [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
     `x:int->B`; `e:int->real^3->B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `E:real^3->B`)] THEN
  USE_THEN "st" (MP_TAC o SPECL
    [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
     `x:int->B`; `e:int->real^3->B`; `E:real^3->B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `!y. y IN apx_chain_union (&2 * eps) {i:int | &0 <= i} e
        ==> &0 < mfd_scalar atlas (g:B->real^3^3) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `apx_chain_union (&2 * eps) {i:int | &0 <= i} (e:int->real^3->B)`;
                   `g:B->real^3^3`; `y:B`] MFD_SCALAR_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
     `apx_chain_union (&2 * eps) {i:int | &0 <= i} (e:int->real^3->B)`] P2BT_TUBE_VIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC th) THEN
  USE_THEN "nk" (MP_TAC o SPECL
    [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
     `x:int->B`; `e:int->real^3->B`; `E:real^3->B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC th) THEN
  MAP_EVERY EXISTS_TAC
   [`subtopology top (apx_chain_union (&2 * eps) {i:int | &0 <= i} (e:int->real^3->B))`;
    `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool)
                    (apx_chain_union (&2 * eps) {i:int | &0 <= i} (e:int->real^3->B))`;
    `restrict_metric (atlas:((B->bool)#(B->real^3))->bool)
                     (apx_chain_union (&2 * eps) {i:int | &0 <= i} (e:int->real^3->B))
                     (g:B->real^3^3)`;
    `p2bt_rview (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                    (real->B->real^3^3))
       (\s. {y | y IN apx_chain_union (&2 * eps) {i:int | &0 <= i} (e:int->real^3->B) /\
                 --inv(mfd_scalar atlas (g:B->real^3^3) y) < s})`;
    `(E:real^3->B) o p2bt_rad (exp(--inv(&2 * eps) / sqrt(&2)))`] THEN
  REWRITE_TAC[p2b_bad_tube] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The limit contains a bad tube (MT Sec 10.3 after Claim 10.6: Claims       *)
(* 10.7-10.11, Prop 10.7), from the five limit-side statements of            *)
(* pc_p2b_tubelimst (hypotheses here; proved in pc_p2b_tubelim) and the      *)
(* generic assembly above.                                                   *)
(* ========================================================================= *)

let p2bt_lvars =
  [`eps:real`; `C:real`; `A:real`;
   `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
   `t:num->real`; `Q:num->real`;
   `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
   `gamma:num->real->A`; `s0:num->real`; `s1:num->real`; `EN:num->real->real^3->A`;
   `A1:real`; `sub:num->num`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
   `g:B->real^3^3`; `zl:B`; `W:num->B->bool`; `phi:num->B->A`;
   `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`];;

let P2BT_LIMIT_BAD_TUBE = prove
 (`!(u:A->bool) (w:B->bool).
     APX_A1_STATEMENT u /\ P2B_APX_A6_CS_STATEMENT u /\ APX_A8_CS_STATEMENT u /\
     P2BT_REQ_A21_CH_STATEMENT u /\ P2BT_REQ_CHAIN_CHART_STATEMENT w /\
     P2BT_LIM_CHAIN_STATEMENT u w /\ P2BT_LIM_SUMMABLE_STATEMENT u w /\
     P2BT_LIM_BOXES_STATEMENT u w /\ P2BT_LIM_SEC_STATEMENT u w /\
     P2BT_LIM_ENECK_STATEMENT u w
     ==> ?eps0. &0 < eps0 /\
           !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
            sub (top:B topology) atlas g zl W phi Vl.
              &0 < eps /\ eps <= eps0 /\ &1 < C /\ &0 < A /\
              p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\
              p2bt_cut eps C A V gamma s0 s1 A1 /\
              p2bt_lim V (\n. p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1)
                      (p2bt_zbase eps C V gamma s0) sub top atlas g zl W phi Vl
              ==> ?top' atlas' g' Vb H. p2b_bad_tube eps (top':B topology,atlas') g' Vb H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `P2BT_LIM_CHAIN_STATEMENT (u:A->bool) (w:B->bool)` THEN
  REWRITE_TAC[P2BT_LIM_CHAIN_STATEMENT] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ch"))) THEN
  UNDISCH_TAC `P2BT_LIM_SUMMABLE_STATEMENT (u:A->bool) (w:B->bool)` THEN
  REWRITE_TAC[P2BT_LIM_SUMMABLE_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sm"))) THEN
  UNDISCH_TAC `P2BT_LIM_BOXES_STATEMENT (u:A->bool) (w:B->bool)` THEN
  REWRITE_TAC[P2BT_LIM_BOXES_STATEMENT] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bx"))) THEN
  UNDISCH_TAC `P2BT_LIM_SEC_STATEMENT (u:A->bool) (w:B->bool)` THEN
  REWRITE_TAC[P2BT_LIM_SEC_STATEMENT] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sc"))) THEN
  UNDISCH_TAC `P2BT_LIM_ENECK_STATEMENT (u:A->bool) (w:B->bool)` THEN
  REWRITE_TAC[P2BT_LIM_ENECK_STATEMENT] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e5:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nk"))) THEN
  MP_TAC(SPEC `w:B->bool` P2BT_TUBE_ASSEMBLY) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e6:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "as"))) THEN
  EXISTS_TAC `min (min (min e1 e2) (min e3 e4)) (min e5 e6)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC p2bt_lvars THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= e2 /\ eps <= e3 /\ eps <= e4 /\ eps <= e5 /\ eps <= e6`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bt_lctx eps C A (V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
              t Q V gamma s0 s1 EN A1 sub (top:B topology) atlas g zl W phi Vl`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[p2bt_lctx]; ALL_TAC] THEN
  USE_THEN "ch" (MP_TAC o SPECL p2bt_lvars) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:int->B` (X_CHOOSE_TAC `e:int->real^3->B`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bt_lim] o check (fun th ->
    let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "p2bt_lim")) THEN
  SUBGOAL_THEN `apx_sphere_sep (top:B topology) atlas` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BT_LIM_SEP) THEN
    MAP_EVERY EXISTS_TAC
     [`eps:real`; `C:real`; `A:real`;
      `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `t:num->real`; `Q:num->real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `gamma:num->real->A`; `s0:num->real`; `s1:num->real`; `EN:num->real->real^3->A`;
      `\n. p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) n)
                       ((gamma:num->real->A) n) ((EN:num->real->real^3->A) n)
                       ((s0:num->real) n) ((s1:num->real) n) A1`;
      `p2bt_zbase eps C (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) gamma s0`;
      `sub:num->num`; `g:B->real^3^3`; `zl:B`; `W:num->B->bool`; `phi:num->B->A`;
      `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "as" (MP_TAC o SPECL
    [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
     `Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
     `x:int->B`; `e:int->real^3->B`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* summability *)
    USE_THEN "sm" (MP_TAC o SPECL (p2bt_lvars @ [`x:int->B`; `e:int->real^3->B`])) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    (* boxes *)
    MAP_EVERY X_GEN_TAC [`y:B`; `s1':real`] THEN STRIP_TAC THEN
    USE_THEN "bx" (MP_TAC o SPECL p2bt_lvars) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`y:B`; `s1':real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `X:B->bool` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`X:B->bool`; `a:real`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`X:B->bool`; `a:real`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2c_vflow")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC;
        MAP_EVERY EXISTS_TAC [`Kb:real`; `N:num`] THEN ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    (* sectional curvature *)
    USE_THEN "sc" (MP_TAC o SPECL p2bt_lvars) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    (* evolving necks *)
    USE_THEN "nk" (MP_TAC o SPECL p2bt_lvars) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]);;

