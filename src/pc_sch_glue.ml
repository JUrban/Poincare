(* ========================================================================= *)
(* pc_sch_glue: the gluing half of the surgery step of the smooth            *)
(* Schoenflies theorem in R^3,                                               *)
(*   SCH6_GLUE_FROM_COLLAR3 |- SCH_COLLAR3_STATEMENT ==>                     *)
(*                             SCH_SLAB_GLUE_STATEMENT,                      *)
(* and with SCH_COLLAR3 (pc_sch_collar.ml)                                   *)
(*   SCH6_SLAB_GLUE |- SCH_SLAB_GLUE_STATEMENT.                              *)
(* Route: balls for the surgered spheres give a global diffeomorphism Phi of *)
(* R^3 carrying S onto one of them (Hatcher, 3-manifold notes, Lemma 1.3    *)
(* made explicit), and SCH_BOUNDS_BALL_DIFFEO.  Phi is the time-one flow of *)
(* an explicit vertical field in a model chart glued from Theta and the ball *)
(* chart of the other surgered sphere, read through a ball chart of the      *)
(* symmetric capsule (pc_sch_glue1).  The nested case is the mirror image    *)
(* (SCH6_SLAB_FLIP).                                                         *)
(* ========================================================================= *)

needs "src/pc_sch_glue1.ml";;
needs "src/pc_sch_collar.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Compactness helpers; the model surfaces and the flipped                   *)
(* capsule Q2 in model coordinates; the capsule chart read in the c2 frame.  *)
(* ------------------------------------------------------------------------- *)

(* A continuous map avoiding a closed set on the part of a compact set in    *)
(* cball(0,1) avoids it on a slightly bigger ball.                           *)

let SCH6_RADIAL_AVOID = prove
 (`!(c:real^3->real^3) X D.
        compact X /\ c continuous_on X /\ closed D /\
        (!z. z IN X /\ norm z <= &1 ==> ~(c z IN D))
        ==> ?R. &1 < R /\ !z. z IN X /\ norm z <= R ==> ~(c z IN D)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Z = {z:real^3 | z IN X /\ (c:real^3->real^3) z IN D}` THEN
  SUBGOAL_THEN `compact(Z:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `X:real^3->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN EXPAND_TAC "Z" THEN SET_TAC[];
      EXPAND_TAC "Z" THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  ASM_CASES_TAC `Z:real^3->bool = {}` THENL
   [EXISTS_TAC `&2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    UNDISCH_TAC `Z:real^3->bool = {}` THEN EXPAND_TAC "Z" THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (norm:real^3->real) Z` COMPACT_ATTAINS_INF) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; GSYM IMAGE_o] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 < norm(z0:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `(z0:real^3) IN Z` THEN EXPAND_TAC "Z" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(&1 + norm(z0:real^3)) / &2` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN Z` MP_TAC THENL
   [EXPAND_TAC "Z" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN ASM_REAL_ARITH_TAC);;

let SCH6_COMPACT_NBHD = prove
 (`!K U:real^N->bool.
        compact K /\ open U /\ K SUBSET U
        ==> ?r. &0 < r /\ !x y. x IN K /\ dist(x,y) < r ==> y IN U`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `(:real^N) DIFF U`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(y:real^N) IN U` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM_REAL_ARITH_TAC);;

(* The model surfaces: S near the slab and the top of the flipped capsule    *)
(* (sch6_u = 0), and S1 near its dome (cylinder below -7/8, then sch_cap1).  *)

let sch6_u = new_definition
 `sch6_u (y:real^3) = y$1 pow 2 + y$2 pow 2 - sch_cap_profile(&2 - y$3)`;;

(* The flipped capsule Q2 = flip(gamma(cball 1)) by inequalities. *)

let SCH6_FLIP_GAMMA_NORM = prove
 (`!y:real^3. norm(sch6_gammai(sch_flip3 y)) pow 2 * sch6_capq(&2 * (&1 - y$3)) =
              (y$1 pow 2 + y$2 pow 2) +
              (&2 * (&1 - y$3)) pow 2 * sch6_capq(&2 * (&1 - y$3))`,
  GEN_TAC THEN REWRITE_TAC[NORM_POW_2; DOT_3; sch6_gammai; VECTOR_3; SCH6_FLIP3_COMPONENTS] THEN
  REWRITE_TAC[REAL_ARITH `&2 * (--y + &1) = &2 * (&1 - y)`] THEN
  MP_TAC(SPEC `&2 * (&1 - (y:real^3)$3)` SCH6_SQRTQ_POS) THEN
  MP_TAC(SPEC `&2 * (&1 - (y:real^3)$3)` SCH6_CAPQ_POS) THEN
  ABBREV_TAC `q = sch6_capq(&2 * (&1 - (y:real^3)$3))` THEN
  ABBREV_TAC `t = &2 * (&1 - (y:real^3)$3)` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt q pow 2 = q` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(sqrt q = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `sqrt q pow 2 = q` THEN CONV_TAC REAL_FIELD);;

let SCH6_Q2_CBALL = prove
 (`!y:real^3. y IN IMAGE sch_flip3 (IMAGE sch6_gamma (cball(vec 0,&1))) <=>
              y$1 pow 2 + y$2 pow 2 <=
              sch6_capq(&2 * (&1 - y$3)) * (&1 - (&2 * (&1 - y$3)) pow 2)`,
  GEN_TAC THEN REWRITE_TAC[SCH6_IN_FLIP3] THEN
  SUBGOAL_THEN `!w:real^3. w IN IMAGE sch6_gamma (cball(vec 0,&1)) <=>
                           sch6_gammai w IN cball(vec 0,&1)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[SCH6_GAMMA_INVERSES]; ALL_TAC] THEN
  REWRITE_TAC[IN_CBALL_0] THEN
  MP_TAC(SPEC `y:real^3` SCH6_FLIP_GAMMA_NORM) THEN
  MP_TAC(SPEC `&2 * (&1 - (y:real^3)$3)` SCH6_CAPQ_POS) THEN
  ABBREV_TAC `q = sch6_capq(&2 * (&1 - (y:real^3)$3))` THEN
  ABBREV_TAC `t = &2 * (&1 - (y:real^3)$3)` THEN
  ABBREV_TAC `n = norm(sch6_gammai(sch_flip3 y))` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= n` ASSUME_TAC THENL [EXPAND_TAC "n" THEN REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `n pow 2 * q <= &1 * q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    SUBGOAL_THEN `n pow 2 <= &1 pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `q:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC]]);;

let sch6_qq = new_definition
 `sch6_qq (y:real^3) = sch6_capq(&2 * (&1 - y$3)) * (&1 - (&2 * (&1 - y$3)) pow 2)`;;

let SCH6_IN_FLIP_GAMMA = prove
 (`!y:real^3 s. y IN IMAGE sch_flip3 (IMAGE sch6_gamma s) <=> sch6_gammai(sch_flip3 y) IN s`,
  REWRITE_TAC[SCH6_IN_FLIP3; IN_IMAGE] THEN MESON_TAC[SCH6_GAMMA_INVERSES]);;

let SCH6_GAMMAI_NORM_CMP = prove
 (`!y:real^3.
        (norm(sch6_gammai(sch_flip3 y)) < &1 <=> y$1 pow 2 + y$2 pow 2 < sch6_qq y) /\
        (norm(sch6_gammai(sch_flip3 y)) = &1 <=> y$1 pow 2 + y$2 pow 2 = sch6_qq y) /\
        (norm(sch6_gammai(sch_flip3 y)) <= &1 <=> y$1 pow 2 + y$2 pow 2 <= sch6_qq y)`,
  GEN_TAC THEN REWRITE_TAC[sch6_qq] THEN
  MP_TAC(SPEC `y:real^3` SCH6_FLIP_GAMMA_NORM) THEN
  MP_TAC(SPEC `&2 * (&1 - (y:real^3)$3)` SCH6_CAPQ_POS) THEN
  ABBREV_TAC `q = sch6_capq(&2 * (&1 - (y:real^3)$3))` THEN
  ABBREV_TAC `t = &2 * (&1 - (y:real^3)$3)` THEN
  ABBREV_TAC `n = norm(sch6_gammai(sch_flip3 y))` THEN
  ABBREV_TAC `r = (y:real^3)$1 pow 2 + y$2 pow 2` THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= n` ASSUME_TAC THENL [EXPAND_TAC "n" THEN REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `r = q * (n pow 2 - t pow 2)` SUBST1_TAC THENL
   [UNDISCH_TAC `n pow 2 * q = r + t pow 2 * q` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `!a b. q * (a - t pow 2) < q * (b - t pow 2) <=> a < b` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ARITH `q * (a - c) < q * (b - c) <=> q * a < q * b`] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. q * (a - t pow 2) = q * (b - t pow 2) <=> a = b` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ARITH `q * (a - c) = q * (b - c) <=> q * a = q * b`] THEN
    ASM_SIMP_TAC[REAL_EQ_MUL_LCANCEL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. q * (a - t pow 2) <= q * (b - t pow 2) <=> a <= b` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ARITH `q * (a - c) <= q * (b - c) <=> q * a <= q * b`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `q * (&1 - t pow 2) = q * (&1 pow 2 - t pow 2)`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS; GSYM REAL_LE_SQUARE_ABS; GSYM REAL_EQ_SQUARE_ABS] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= n ==> abs n = n`; REAL_ABS_NUM]);;

(* The squared radius sch6_qq of Q2 at each height. *)

let SCH6_QQ_TOP = prove
 (`!y:real^3. &7 / &8 <= y$3 /\ y$3 < &3 / &2 ==> sch6_qq y = sch_cap_profile(&2 - y$3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch6_qq] THEN
  MP_TAC(SPEC `&2 * (&1 - (y:real^3)$3)` SCH6_CAPQ_PROFILE_BOT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 + (&2 * (&1 - y)) / &2 = &2 - y`] THEN SIMP_TAC[]);;

let SCH6_QQ_BOT = prove
 (`!y:real^3. &1 / &2 < y$3 /\ y$3 <= &9 / &8 ==> sch6_qq y = sch_cap_profile(y$3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch6_qq] THEN
  MP_TAC(SPEC `&2 * (&1 - (y:real^3)$3)` SCH6_CAPQ_PROFILE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 - (&2 * (&1 - y)) / &2 = y`] THEN SIMP_TAC[]);;

let SCH6_QQ_OUT = prove
 (`!y:real^3. y$3 < &1 / &2 \/ &3 / &2 < y$3 ==> sch6_qq y < &0`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[sch6_qq] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < q /\ &0 < q * (t - &1) ==> q * (&1 - t) < &0`) THEN
  REWRITE_TAC[SCH6_CAPQ_POS] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  REWRITE_TAC[SCH6_CAPQ_POS; REAL_SUB_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 < a ==> &1 < a`) THEN
  SUBGOAL_THEN `&1 < abs(&2 * (&1 - (y:real^3)$3))` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&1 pow 2 < abs(&2 * (&1 - (y:real^3)$3)) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let SCH6_QQ_LE1 = prove
 (`!y:real^3. sch6_qq y <= &1`,
  GEN_TAC THEN
  ASM_CASES_TAC `(y:real^3)$3 < &1 / &2 \/ &3 / &2 < y$3` THENL
   [MATCH_MP_TAC(REAL_ARITH `x < &0 ==> x <= &1`) THEN ASM_SIMP_TAC[SCH6_QQ_OUT];
    ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^3)$3 = &3 / &2` THENL
   [ASM_REWRITE_TAC[sch6_qq] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&7 / &8 <= (y:real^3)$3` THENL
   [ASM_SIMP_TAC[SCH6_QQ_TOP; REAL_ARITH `~(a < &1 / &2 \/ &3 / &2 < a) /\ ~(a = &3 / &2)
                                           ==> a < &3 / &2`] THEN
    MP_TAC(SPEC `&2 - (y:real^3)$3` SCH_CAP_PROFILE_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^3)$3 = &1 / &2` THENL
   [ASM_REWRITE_TAC[sch6_qq] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `y:real^3` SCH6_QQ_BOT) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPEC `(y:real^3)$3` SCH_CAP_PROFILE_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Strict profile bound; the capsule chart read in the frame of              *)
(* the second surgered sphere (nu = flip o c o flip); layers and heights of  *)
(* the flipped model collar F z = flip(cap collar(flip z)).                  *)
(* ------------------------------------------------------------------------- *)

let SCH6_SS_LT1 = prove
 (`!t. t < &1 ==> smooth_step t < &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_step] THEN
  MP_TAC(SPEC `t:real` CUTOFF_FLAT_POS_LE) THEN
  MP_TAC(SPEC `&1 - t` CUTOFF_FLAT_POS_LT) THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`] THEN
  ASM_REAL_ARITH_TAC);;

let SCH6_PROFILE_LT1 = prove
 (`!t. t < &7 / &8 ==> sch_cap_profile t < &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch_cap_profile] THEN
  MP_TAC(SPEC `&4 * t - &5 / &2` SCH6_SS_LT1) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `b = smooth_step(&4 * t - &5 / &2)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (&1 - b) * (&3 / &2 - t)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* The capsule chart in the c2 frame. *)

let SCH6_NU_FCONE = prove
 (`!(c:real^3->real^3) e0 z.
        (!x. x IN annulus (&3 / &4) (&2) ==> c x = sch6_capsule e0 x) /\
        z IN sch6_fcone /\ &3 / &4 < norm z
        ==> sch_flip3(c(sch_flip3 z)) = sch_flip3(sch_cap_collar e0 (sch_flip3 z))`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `sch_flip3 z IN annulus (&3 / &4) (&2) /\ sch_flip3 z IN sch_capcone`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SCH6_FCONE_FLIP] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN sch6_fcone` THEN
    REWRITE_TAC[annulus; sch6_fcone; IN_ELIM_THM; SCH6_NORM_FLIP3] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[SCH6_CAPSULE_CONE]]);;

let SCH6_NU_CONE = prove
 (`!(c:real^3->real^3) e0 z.
        (!x. x IN annulus (&3 / &4) (&2) ==> c x = sch6_capsule e0 x) /\
        z IN sch_capcone /\ &3 / &4 < norm z
        ==> sch_flip3(c(sch_flip3 z)) = sch_cap_collar e0 z + &2 % basis 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sch_flip3 z IN annulus (&3 / &4) (&2) /\ sch_flip3 z IN sch6_fcone`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SCH6_FCONE_FLIP; SCH_FLIP3_INVOLUTION] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN sch_capcone` THEN
    REWRITE_TAC[annulus; sch_capcone; IN_ELIM_THM; SCH6_NORM_FLIP3] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SCH6_CAPSULE_FCONE_IN; SCH_FLIP3_INVOLUTION] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; SCH6_FLIP3_COMPONENTS; SCH6_MIR_COMPONENTS;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

let SCH6_NU_SPHERE = prove
 (`!(c:real^3->real^3) e0 z.
        (!x. x IN annulus (&3 / &4) (&2) ==> c x = sch6_capsule e0 x) /\ norm z = &1
        ==> sch_flip3(c(sch_flip3 z)) = sch_flip3(sch6_gamma(sch_flip3 z))`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `sch_flip3 z IN annulus (&3 / &4) (&2) /\ norm(sch_flip3 z) = &1`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[annulus; IN_ELIM_THM; SCH6_NORM_FLIP3] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[SCH6_CAPSULE_SPHERE]]);;

(* Layers and heights of the flipped model collar. *)

let SCH6_CAPCOLLAR_ABOVE = prove
 (`!e0 x:real^3. &0 < e0 /\ e0 <= &1 / &16 /\ x IN sch_capcone
                 ==> --(&9 / &8) < (sch_cap_collar e0 x)$3`,
  REWRITE_TAC[sch_capcone; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[sch_cap_collar; VECTOR_3] THEN
  SUBGOAL_THEN `--(&1 / &4) < (x:real^3)$3 / norm x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&1 / &2 < n ==> &0 < n`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&8 * ((x:real^3)$3 / norm x) - &6` SMOOTH_STEP_BOUNDS) THEN
  ABBREV_TAC `b = smooth_step(&8 * ((x:real^3)$3 / norm x) - &6)` THEN
  ABBREV_TAC `c = (x:real^3)$3 / norm x` THEN
  ABBREV_TAC `n = norm(x:real^3)` THEN STRIP_TAC THEN
  ASM_CASES_TAC `c < &5 / &8` THENL
   [SUBGOAL_THEN `b = &0` SUBST1_TAC THENL
     [EXPAND_TAC "b" THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&1 / &32) <= e0 * (n - &1) * b` MP_TAC THENL
   [ASM_CASES_TAC `&0 <= n - &1` THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --(&1 / &32) <= x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 <= e0 * (&1 - n) * b /\ e0 * (&1 - n) * b <= e0 * (&1 - n) * &1 /\
                    e0 * (&1 - n) <= (&1 / &16) * (&1 / &2)` MP_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[REAL_MUL_RID] THEN REAL_ARITH_TAC]];
    ASM_REAL_ARITH_TAC]);;

let SCH6_F_LAYER = prove
 (`!e0 z:real^3. &0 < e0 /\ e0 <= &1 / &16 /\ z IN sch6_fcone
       ==> (sch_flip3(sch_cap_collar e0 (sch_flip3 z)))$1 pow 2 +
           (sch_flip3(sch_cap_collar e0 (sch_flip3 z)))$2 pow 2 =
           sch_cap_profile((sch_flip3(sch_cap_collar e0 (sch_flip3 z)))$3) +
           e0 * (norm z - &1) /\
           (sch_flip3(sch_cap_collar e0 (sch_flip3 z)))$3 < &9 / &8 /\
           sch_flip3(sch_cap_collar e0 (sch_flip3 z)) IN sch_slab_nbhd`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SCH6_FCONE_FLIP] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e0:real`; `sch_flip3 z`] SCH_CAP_COLLAR_LAYER) THEN
  MP_TAC(SPECL [`e0:real`; `sch_flip3 z`] SCH6_CAPCOLLAR_ABOVE) THEN
  ASM_REWRITE_TAC[SCH6_FLIP3_COMPONENTS; SCH6_NORM_FLIP3; REAL_NEG_NEG] THEN
  REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM SCH6_IN_FLIP3; SCH6_FLIP3_MODEL_SETS] THEN
    ASM_REWRITE_TAC[SCH6_IN_FLIP3; SCH_FLIP3_INVOLUTION]]);;

let SCH6_CAPCOLLAR_AXIS_GEN = prove
 (`!e0 a. &0 < a ==> sch_cap_collar e0 (vector[&0; &0; a]) =
                     vector[&0; &0; --(&1 / &2) + e0 * (a - &1)]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sch_cap_collar; VECTOR_3] THEN
  ASM_SIMP_TAC[SCH6_NORM_E3; REAL_LT_IMP_LE; REAL_DIV_REFL; REAL_LT_IMP_NZ] THEN
  SUBGOAL_THEN `smooth_step(&8 * &1 - &6) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The data of the push (a slab configuration, the second                    *)
(* surgered sphere S2 with its collar g2 and a ball chart c2 that follows    *)
(* g2 near S2) and the sides: in the chart, Theta^-1 of the closed ball      *)
(* bounded by S2 is the cup above sch_cap2; S misses the inside of S2 and S1 *)
(* misses the closed ball.                                                   *)
(* ------------------------------------------------------------------------- *)

(* A connected set missing a sphere and meeting one side lies in that side. *)

let SCH6_SIDE = prove
 (`!s t:real^3->bool p.
        s homeomorphic sphere(vec 0:real^3,&1) /\ connected t /\ t INTER s = {} /\
        p IN t
        ==> (p IN inside s ==> t SUBSET inside s) /\
            (p IN outside s ==> t SUBSET outside s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `inside s:real^3->bool`; `outside s:real^3->bool`]
    SCH1_CONNECTED_SIDE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM SET_TAC[]);;

(* The slab data: a slab configuration with its chart data unpacked (the    *)
(* set equations reversed so that rewriting with assumptions is safe) and   *)
(* the three spheres.                                                        *)

let sch6_slab_data = new_definition
 `sch6_slab_data (S:real^3->bool) S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 <=>
    open N /\ sch_slab_nbhd SUBSET N /\ diffeomorphism_on N (IMAGE Theta N) Theta Theta' /\
    (!y. y IN N ==> (Theta y IN S <=> y$1 pow 2 + y$2 pow 2 = &1)) /\
    E1 UNION IMAGE Theta sch_lat UNION E2 = S /\ DISJOINT E1 E2 /\
    (!y. y IN N
         ==> (Theta y IN E1 <=> y$1 pow 2 + y$2 pow 2 = &1 /\ y$3 < -- &1) /\
             (Theta y IN E2 <=> y$1 pow 2 + y$2 pow 2 = &1 /\ &1 < y$3)) /\
    E1 UNION IMAGE Theta sch_cap1 = S1 /\ E2 UNION IMAGE Theta sch_cap2 = S2 /\
    ((!y. y IN N ==> (Theta y IN inside S <=> y$1 pow 2 + y$2 pow 2 < &1)) \/
     (!y. y IN N ==> (Theta y IN outside S <=> y$1 pow 2 + y$2 pow 2 < &1))) /\
    S homeomorphic sphere(vec 0:real^3,&1) /\ S1 homeomorphic sphere(vec 0:real^3,&1) /\
    S2 homeomorphic sphere(vec 0:real^3,&1)`;;

(* The data of the push: slab data, the collar g2 of S2 (the model collar  *)
(* near sch_cap2) and a ball chart c2 of S2 equal to g2 near S2.            *)

let sch6_push_data = new_definition
 `sch6_push_data (S:real^3->bool) S1 S2 (Theta:real^3->real^3) Theta' N E1 E2
                (g2:real^3->real^3) g2' (c2:real^3->real^3) c2' e0 <=>
    sch6_slab_data S S1 S2 Theta Theta' N E1 E2 /\
    sch_neck g2 g2' /\ IMAGE g2 (sphere(vec 0,&1)) = S2 /\
    &0 < e0 /\ e0 <= &1 / &16 /\
    (!x. x IN sch_capcone ==> g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e0 x))) /\
    sch_ball c2 c2' /\ IMAGE c2 (cball(vec 0,&1)) = S2 UNION inside S2 /\
    (!x. x IN annulus (&3 / &4) (&2) ==> c2 x = g2 x)`;;

let SCH6_PD_SLAB = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0
        ==> sch6_slab_data S S1 S2 Theta Theta' N E1 E2`,
  SIMP_TAC[sch6_push_data]);;

(* Basic consequences of the slab data: the chart is injective, the three  *)
(* spheres are compact.                                                      *)

let SCH6_SD_BASIC = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2.
        sch6_slab_data S S1 S2 Theta Theta' N E1 E2
        ==> (!y. y IN N ==> Theta' (Theta y) = y) /\
            (!y z. y IN N /\ z IN N /\ Theta y = Theta z ==> y = z) /\
            (!y. y IN sch_slab_nbhd ==> y IN N) /\
            compact S /\ compact S1 /\ compact S2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch6_slab_data] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on N (IMAGE (Theta:real^3->real^3) N) Theta Theta'` THEN
    SIMP_TAC[diffeomorphism_on];
    UNDISCH_TAC `diffeomorphism_on N (IMAGE (Theta:real^3->real^3) N) Theta Theta'` THEN
    REWRITE_TAC[diffeomorphism_on] THEN MESON_TAC[];
    UNDISCH_TAC `sch_slab_nbhd SUBSET (N:real^3->bool)` THEN SIMP_TAC[SUBSET];
    MP_TAC(ISPECL [`S:real^3->bool`; `sphere(vec 0:real^3,&1)`] HOMEOMORPHIC_COMPACTNESS) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE];
    MP_TAC(ISPECL [`S1:real^3->bool`; `sphere(vec 0:real^3,&1)`] HOMEOMORPHIC_COMPACTNESS) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE];
    MP_TAC(ISPECL [`S2:real^3->bool`; `sphere(vec 0:real^3,&1)`] HOMEOMORPHIC_COMPACTNESS) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE]]);;

(* Unpacking the slab data (with the consequences of SCH6_SD_BASIC). *)

let SCH6_SD_TAC =
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP SCH6_SD_BASIC th) THEN MP_TAC th) THEN
  REWRITE_TAC[sch6_slab_data] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th));;

(* Basic consequences of the push data: Jordan facts for S2, the chart, c2. *)

let SCH6_PD_BASIC = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0
        ==> S2 homeomorphic sphere(vec 0:real^3,&1) /\
            (!y. y IN N ==> Theta' (Theta y) = y) /\
            (!y z. y IN N /\ z IN N /\ Theta y = Theta z ==> y = z) /\
            (!z w. z IN ball(vec 0,&2) /\ w IN ball(vec 0,&2) /\ c2 z = c2 w ==> z = w) /\
            IMAGE c2 (ball(vec 0,&1)) = inside S2 /\
            IMAGE c2 (sphere(vec 0,&1)) = S2 /\
            (!z. z IN annulus (&1) (&2) ==> c2 z IN outside S2) /\
            (!z. z IN sch6_fcone ==> sch_flip3(sch_cap_collar e0 (sch_flip3 z)) IN N /\
                                     g2 z = Theta(sch_flip3(sch_cap_collar e0 (sch_flip3 z))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH6_SD_BASIC o MATCH_MP SCH6_PD_SLAB) THEN
  UNDISCH_TAC `sch6_push_data S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0` THEN
  REWRITE_TAC[sch6_push_data; sch6_slab_data] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `!z w. z IN ball(vec 0,&2) /\ w IN ball(vec 0,&2) /\
                      (c2:real^3->real^3) z = c2 w ==> z = w` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_ball (c2:real^3->real^3) c2'` THEN
    REWRITE_TAC[sch_ball; diffeomorphism_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c2:real^3->real^3`; `c2':real^3->real^3`; `S2:real^3->bool`]
    SCH1_BALL_INSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `S2:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((c2:real^3->real^3) z IN S2 UNION inside S2)` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `cball(vec 0:real^3,&1)`)) (concl th))) THEN
      REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `z:real^3 = w` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `(z:real^3) IN annulus (&1) (&2)` THEN
        ASM_REWRITE_TAC[annulus; IN_ELIM_THM; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(z:real^3) IN annulus (&1) (&2)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
        ASM_REAL_ARITH_TAC];
      ASM SET_TAC[]];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`e0:real`; `z:real^3`] SCH6_F_LAYER) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sch_flip3 z` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sch_capcone`)) (concl th))) THEN
    REWRITE_TAC[SCH_FLIP3_INVOLUTION; GSYM SCH6_FCONE_FLIP] THEN ASM_REWRITE_TAC[]]);;

(* Unpacking the push data (with the consequences of SCH6_PD_BASIC). *)

let SCH6_PD_TAC =
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP SCH6_PD_BASIC th) THEN MP_TAC th) THEN
  REWRITE_TAC[sch6_push_data; sch6_slab_data] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th));;

(* S2 in the chart: sch_cap2 and the cylinder above height 1. *)

let SCH6_SD_S2_CHART = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2.
        sch6_slab_data S S1 S2 Theta Theta' N E1 E2
        ==> !y. y IN sch_slab_nbhd
                ==> (Theta y IN S2 <=>
                     y$1 pow 2 + y$2 pow 2 = sch_cap_profile(y$3) /\ &1 / &2 <= y$3)`,
  REPEAT GEN_TAC THEN SCH6_SD_TAC THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN N` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_slab_nbhd SUBSET (N:real^3->bool)` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_cap2 SUBSET (N:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `sch_slab_nbhd` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; sch_cap2; sch_slab_nbhd; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
    STRIP_TAC THEN MP_TAC(SPEC `(w:real^3)$3` SCH_CAP_PROFILE_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `S2:real^3->bool` && can (find_term ((=) `sch_cap2`)) (lhs(concl th)))) THEN
  REWRITE_TAC[IN_UNION] THEN
  SUBGOAL_THEN `(Theta:real^3->real^3) y IN IMAGE Theta sch_cap2 <=> y IN sch_cap2`
  SUBST1_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `y:real^3 = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
      UNDISCH_TAC `!y z. y IN N /\ z IN N /\ (Theta:real^3->real^3) y = Theta z ==> y = z` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `sch_cap2 SUBSET (N:real^3->bool)` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[sch_cap2; IN_ELIM_THM] THEN
  ASM_CASES_TAC `&1 < (y:real^3)$3` THENL
   [SUBGOAL_THEN `sch_cap_profile((y:real^3)$3) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN UNDISCH_TAC `&1 < (y:real^3)$3` THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `&1 < (y:real^3)$3` THEN REAL_ARITH_TAC];
    UNDISCH_TAC `~(&1 < (y:real^3)$3)` THEN REAL_ARITH_TAC]);;

let SCH6_PD_S2_CHART = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0
        ==> !y. y IN sch_slab_nbhd
                ==> (Theta y IN S2 <=>
                     y$1 pow 2 + y$2 pow 2 = sch_cap_profile(y$3) /\ &1 / &2 <= y$3)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP SCH6_SD_S2_CHART o MATCH_MP SCH6_PD_SLAB));;

(* The open cup above sch_cap2 is starlike (from (0,0,1)); so is the slab    *)
(* below height 1/2 (from the origin).                                       *)

let SCH6_UIN_STARLIKE = prove
 (`starlike {y:real^3 | y IN sch_slab_nbhd /\
                        y$1 pow 2 + y$2 pow 2 < sch_cap_profile(y$3) /\ &1 / &2 < y$3}`,
  REWRITE_TAC[starlike] THEN EXISTS_TAC `vector[&0; &0; &1]:real^3` THEN
  REWRITE_TAC[IN_ELIM_THM; sch_slab_nbhd; VECTOR_3] THEN
  SUBGOAL_THEN `sch_cap_profile(&1) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_SEGMENT; IN_ELIM_THM] THEN X_GEN_TAC `p:real^3` THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_MUL_RID] THEN
  SUBGOAL_THEN `(u * (x:real^3)$1) pow 2 + (u * x$2) pow 2 <= x$1 pow 2 + x$2 pow 2`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `u pow 2 <= &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `(x:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(x:real^3)$2` REAL_LE_POW_2) THEN
    ABBREV_TAC `a = (x:real^3)$1 pow 2` THEN ABBREV_TAC `b = (x:real^3)$2 pow 2` THEN
    ABBREV_TAC `v = u pow 2` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `v * a <= &1 * a /\ v * b <= &1 * b` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_cap_profile((x:real^3)$3) <= sch_cap_profile(&1 - u + u * x$3)`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `(x:real^3)$3 <= &1` THENL
     [MATCH_MP_TAC SCH6_PROFILE_MONO THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - u) * (&1 - x) ==> x <= &1 - u + u * x`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 <= u * (&1 - x) ==> &1 - u + u * x <= &3 / &2`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `sch_cap_profile((x:real^3)$3) = &1 /\
                    sch_cap_profile(&1 - u + u * x$3) = &1`
      (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
      CONJ_TAC THEN MATCH_MP_TAC SCH_CAP_PROFILE_TOP THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 <= u * (x - &1) ==> &7 / &8 <= &1 - u + u * x`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 < &1 - u + u * (x:real^3)$3 /\
                abs(&1 - u + u * x$3) < &5 / &4` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(x:real^3)$3 <= &1` THENL
     [SUBGOAL_THEN `&0 <= u * (&1 - (x:real^3)$3) /\ u * (&1 - x$3) <= &1 * (&1 - x$3)`
      MP_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_RMUL] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC];
      SUBGOAL_THEN `&0 <= u * ((x:real^3)$3 - &1) /\ u * (x$3 - &1) <= &1 * (x$3 - &1)`
      MP_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_RMUL] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC]] THEN
    UNDISCH_TAC `abs((x:real^3)$3) < &5 / &4` THEN UNDISCH_TAC `&1 / &2 < (x:real^3)$3` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(x:real^3)$1 pow 2 + x$2 pow 2 < &4` THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `(x:real^3)$1 pow 2 + x$2 pow 2 < sch_cap_profile(x$3)` THEN
    ASM_REAL_ARITH_TAC]);;

let SCH6_LOW_STARLIKE = prove
 (`starlike {y:real^3 | y IN sch_slab_nbhd /\ y$3 < &1 / &2}`,
  REWRITE_TAC[starlike] THEN EXISTS_TAC `vec 0:real^3` THEN
  REWRITE_TAC[IN_ELIM_THM; sch_slab_nbhd; VEC_COMPONENT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_SEGMENT; IN_ELIM_THM] THEN X_GEN_TAC `p:real^3` THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
  SUBGOAL_THEN `(u * (x:real^3)$1) pow 2 + (u * x$2) pow 2 <= x$1 pow 2 + x$2 pow 2`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `u pow 2 <= &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `(x:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(x:real^3)$2` REAL_LE_POW_2) THEN
    ABBREV_TAC `a = (x:real^3)$1 pow 2` THEN ABBREV_TAC `b = (x:real^3)$2 pow 2` THEN
    ABBREV_TAC `v = u pow 2` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `v * a <= &1 * a /\ v * b <= &1 * b` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(u * (x:real^3)$3) <= abs(x$3) /\ u * x$3 < &1 / &2` MP_TAC THENL
   [ASM_CASES_TAC `&0 <= (x:real^3)$3` THENL
     [SUBGOAL_THEN `&0 <= u * (x:real^3)$3 /\ u * x$3 <= &1 * x$3` MP_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_RMUL] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC];
      SUBGOAL_THEN `u * (x:real^3)$3 <= &0 /\ &1 * x$3 <= u * x$3` MP_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[REAL_ARITH `u * x <= &0 <=> &0 <= u * --x`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_ARITH `&1 * x <= u * x <=> &0 <= (&1 - u) * --x`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC]] THEN
    UNDISCH_TAC `(x:real^3)$3 < &1 / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(x:real^3)$1 pow 2 + x$2 pow 2 < &4` THEN
    UNDISCH_TAC `(u * (x:real^3)$1) pow 2 + (u * x$2) pow 2 <= x$1 pow 2 + x$2 pow 2` THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `abs((x:real^3)$3) < &5 / &4` THEN
    UNDISCH_TAC `abs(u * (x:real^3)$3) <= abs(x$3)` THEN REAL_ARITH_TAC]);;

(* Two model points on the axis: an inner and an outer layer point of g2. *)

let SCH6_AXIS_F = prove
 (`!e0 a. &1 / &2 < a /\ a < &2
          ==> vector[&0; &0; --a]:real^3 IN sch6_fcone /\
              norm(vector[&0; &0; --a]:real^3) = a /\
              sch_flip3(sch_cap_collar e0 (sch_flip3(vector[&0; &0; --a]))) =
              vector[&0; &0; &1 / &2 - e0 * (a - &1)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(vector[&0; &0; --a]:real^3) = a` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_EQ_SQUARE; DOT_3; VECTOR_3] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[sch6_fcone; IN_ELIM_THM; VECTOR_3] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[sch_flip3; VECTOR_3; REAL_NEG_NEG; REAL_NEG_0] THEN
  ASM_SIMP_TAC[SCH6_CAPCOLLAR_AXIS_GEN; REAL_ARITH `&1 / &2 < a ==> &0 < a`] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN REAL_ARITH_TAC);;

let SCH6_PD_AXIS_POINTS = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0
        ==> Theta(vector[&0; &0; &1 / &2 + e0 / &8]) IN inside S2 /\
            Theta(vector[&0; &0; &1 / &2 - e0 / &8]) IN outside S2`,
  REPEAT GEN_TAC THEN SCH6_PD_TAC THEN
  SUBGOAL_THEN `!a. &3 / &4 < a /\ a < &2
                    ==> (c2:real^3->real^3)(vector[&0; &0; --a]) =
                        (Theta:real^3->real^3)(vector[&0; &0; &1 / &2 - e0 * (a - &1)])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`e0:real`; `a:real`] SCH6_AXIS_F) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(c2:real^3->real^3)(vector[&0; &0; --a]) = (g2:real^3->real^3)(vector[&0; &0; --a])`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vector[&0; &0; --a]:real^3` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `sch6_fcone`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `vector[&0; &0; &1 / &2 + e0 / &8]:real^3 =
                  vector[&0; &0; &1 / &2 - e0 * (&7 / &8 - &1)]` SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&7 / &8`) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `inside S2:real^3->bool`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_BALL_0] THEN
    MP_TAC(SPECL [`e0:real`; `&7 / &8`] SCH6_AXIS_F) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[] THEN REAL_ARITH_TAC];
    SUBGOAL_THEN `vector[&0; &0; &1 / &2 - e0 / &8]:real^3 =
                  vector[&0; &0; &1 / &2 - e0 * (&9 / &8 - &1)]` SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&9 / &8`) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    MP_TAC(SPECL [`e0:real`; `&9 / &8`] SCH6_AXIS_F) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[] THEN REAL_ARITH_TAC]]);;

(* In the chart, the closed ball bounded by S2 is the cup over sch_cap2. *)

let SCH6_PD_CUP = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0
        ==> !y. y IN sch_slab_nbhd
                ==> (Theta y IN S2 UNION inside S2 <=>
                     y$1 pow 2 + y$2 pow 2 <= sch_cap_profile(y$3))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "CH" o MATCH_MP SCH6_PD_S2_CHART) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH6_PD_AXIS_POINTS) THEN
  UNDISCH_TAC `sch6_push_data S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0` THEN
  SCH6_PD_TAC THEN
  MP_TAC(ISPEC `S2:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. y IN sch_slab_nbhd ==> y IN N` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_slab_nbhd SUBSET (N:real^3->bool)` THEN SIMP_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!X. X SUBSET sch_slab_nbhd ==> (Theta:real^3->real^3) continuous_on X`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `N:real^3->bool` THEN CONJ_TAC THENL
     [UNDISCH_TAC `diffeomorphism_on N (IMAGE (Theta:real^3->real^3) N) Theta Theta'` THEN
      SIMP_TAC[diffeomorphism_on; SMOOTH_MAP_ON_CONTINUOUS_ON];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN sch_slab_nbhd /\ y$3 < &1 / &2 ==> (Theta:real^3->real^3) y IN outside S2`
  (LABEL_TAC "LOW") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S2:real^3->bool`;
                   `IMAGE (Theta:real^3->real^3) {y | y IN sch_slab_nbhd /\ y$3 < &1 / &2}`;
                   `(Theta:real^3->real^3)(vector[&0; &0; &1 / &2 - e0 / &8])`] SCH6_SIDE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        SIMP_TAC[STARLIKE_IMP_CONNECTED; SCH6_LOW_STARLIKE] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC[];
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM] THEN
        X_GEN_TAC `p:real^3` THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
        ASM_REWRITE_TAC[] THEN REMOVE_THEN "CH" (MP_TAC o SPEC `w:real^3`) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[IN_ELIM_THM; sch_slab_nbhd; VECTOR_3] THEN ASM_REAL_ARITH_TAC];
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN sch_slab_nbhd /\
                           y$1 pow 2 + y$2 pow 2 < sch_cap_profile(y$3) /\ &1 / &2 < y$3
                           ==> (Theta:real^3->real^3) y IN inside S2` (LABEL_TAC "IN") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S2:real^3->bool`;
                   `IMAGE (Theta:real^3->real^3)
                      {y | y IN sch_slab_nbhd /\
                           y$1 pow 2 + y$2 pow 2 < sch_cap_profile(y$3) /\ &1 / &2 < y$3}`;
                   `(Theta:real^3->real^3)(vector[&0; &0; &1 / &2 + e0 / &8])`] SCH6_SIDE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        SIMP_TAC[STARLIKE_IMP_CONNECTED; SCH6_UIN_STARLIKE] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC[];
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM] THEN
        X_GEN_TAC `p:real^3` THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
        ASM_REWRITE_TAC[] THEN REMOVE_THEN "CH" (MP_TAC o SPEC `w:real^3`) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[IN_ELIM_THM; sch_slab_nbhd; VECTOR_3] THEN
        SUBGOAL_THEN `sch_cap_profile(&1 / &2 + e0 / &8) = e0 / &8` SUBST1_TAC THENL
         [SIMP_TAC[SCH_CAP_PROFILE_TIP; ASSUME `e0 <= &1 / &16`;
                   REAL_ARITH `e0 <= &1 / &16 ==> &1 / &2 + e0 / &8 <= &5 / &8`] THEN
          REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]];
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s. s <= &1 / &2 ==> sch_cap_profile s = s - &1 / &2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH_CAP_PROFILE_TIP THEN
    UNDISCH_TAC `s <= &1 / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Theta:real^3->real^3) y IN outside S2` MP_TAC THENL
     [ASM_CASES_TAC `(y:real^3)$3 < &1 / &2` THENL
       [USE_THEN "LOW" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`S2:real^3->bool`;
                     `IMAGE (Theta:real^3->real^3)
                        (segment[vector[(y:real^3)$1; y$2; &1 / &4], y])`;
                     `(Theta:real^3->real^3)(vector[(y:real^3)$1; y$2; &1 / &4])`] SCH6_SIDE) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `!p. p IN segment[vector[(y:real^3)$1; y$2; &1 / &4], y]
                        ==> p IN sch_slab_nbhd /\
                            sch_cap_profile(p$3) < p$1 pow 2 + p$2 pow 2` ASSUME_TAC THENL
       [X_GEN_TAC `p:real^3` THEN REWRITE_TAC[IN_SEGMENT] THEN
        DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                        VECTOR_3] THEN
        REWRITE_TAC[REAL_ARITH `(&1 - u) * a + u * a = a`] THEN
        UNDISCH_TAC `(y:real^3) IN sch_slab_nbhd` THEN REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `&0 <= u * ((y:real^3)$3 - &1 / &4) /\
                      u * (y$3 - &1 / &4) <= &1 * (y$3 - &1 / &4)` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_RMUL] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sch_cap_profile((y:real^3)$3)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH6_PROFILE_MONO THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_SEGMENT] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[SUBSET];
          REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN X_GEN_TAC `q:real^3` THEN
          DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
          REMOVE_THEN "CH" (MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT]];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL
       [USE_THEN "LOW" MATCH_MP_TAC THEN REWRITE_TAC[VECTOR_3] THEN
        UNDISCH_TAC `(y:real^3) IN sch_slab_nbhd` THEN
        REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM; VECTOR_3] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[ENDS_IN_SEGMENT];
      MP_TAC(ISPEC `S2:real^3->bool` OUTSIDE_NO_OVERLAP) THEN
      MP_TAC(ISPEC `S2:real^3->bool` INSIDE_INTER_OUTSIDE) THEN SET_TAC[]];
    DISCH_TAC THEN REWRITE_TAC[IN_UNION] THEN
    ASM_CASES_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 = sch_cap_profile(y$3)` THENL
     [DISJ1_TAC THEN REMOVE_THEN "CH" (MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `&1 / &2 <= (y:real^3)$3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(&1 / &2 <= (y:real^3)$3)` THEN
      UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 = sch_cap_profile(y$3)` THEN
      UNDISCH_TAC `!s. s <= &1 / &2 ==> sch_cap_profile s = s - &1 / &2` THEN
      DISCH_THEN(MP_TAC o SPEC `(y:real^3)$3`) THEN
      MP_TAC(SPEC `(y:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC;
      DISJ2_TAC THEN USE_THEN "IN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((y:real^3)$1 pow 2 + y$2 pow 2 = sch_cap_profile(y$3))` THEN
      UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 <= sch_cap_profile(y$3)` THEN
      UNDISCH_TAC `!s. s <= &1 / &2 ==> sch_cap_profile s = s - &1 / &2` THEN
      DISCH_THEN(MP_TAC o SPEC `(y:real^3)$3`) THEN
      MP_TAC(SPEC `(y:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC]]);;

(* The side of S containing Theta(r^2 > 1). *)

let SCH6_SIDES_OF = prove
 (`!s (x:real^3). (~(x IN s) /\ ~(x IN inside s) ==> x IN outside s) /\
                  (~(x IN s) /\ ~(x IN outside s) ==> x IN inside s) /\
                  (x IN inside s ==> ~(x IN outside s)) /\
                  (x IN outside s ==> ~(x IN inside s))`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `s:real^3->bool` INSIDE_INTER_OUTSIDE) THEN
  MP_TAC(ISPEC `s:real^3->bool` INSIDE_UNION_OUTSIDE) THEN SET_TAC[]);;

let SCH6_SD_SIDE_A = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2.
        sch6_slab_data S S1 S2 Theta Theta' N E1 E2
        ==> ?A:real^3->bool.
              connected A /\ A INTER S = {} /\ frontier A = S /\
              (!y. y IN N /\ &1 < y$1 pow 2 + y$2 pow 2 ==> Theta y IN A) /\
              (!y. y IN N /\ y$1 pow 2 + y$2 pow 2 < &1 ==> ~(Theta y IN A))`,
  REPEAT GEN_TAC THEN SCH6_SD_TAC THEN
  MP_TAC(ISPEC `S:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. y IN N /\ ~(y$1 pow 2 + y$2 pow 2 = &1) ==> ~((Theta:real^3->real^3) y IN S)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [EXISTS_TAC `outside S:real^3->bool` THEN
    ASM_REWRITE_TAC[OUTSIDE_NO_OVERLAP] THEN CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1(SPEC_ALL SCH6_SIDES_OF)) THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(el 2 (CONJUNCTS(SPEC_ALL SCH6_SIDES_OF))) THEN ASM_SIMP_TAC[]];
    EXISTS_TAC `inside S:real^3->bool` THEN
    ASM_REWRITE_TAC[INSIDE_NO_OVERLAP] THEN CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC(el 1 (CONJUNCTS(SPEC_ALL SCH6_SIDES_OF))) THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(el 3 (CONJUNCTS(SPEC_ALL SCH6_SIDES_OF))) THEN ASM_SIMP_TAC[]]]);;

let SCH6_PD_SIDE_A = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0
        ==> ?A:real^3->bool.
              connected A /\ A INTER S = {} /\ frontier A = S /\
              (!y. y IN N /\ &1 < y$1 pow 2 + y$2 pow 2 ==> Theta y IN A) /\
              (!y. y IN N /\ y$1 pow 2 + y$2 pow 2 < &1 ==> ~(Theta y IN A))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP SCH6_SD_SIDE_A o MATCH_MP SCH6_PD_SLAB));;

let SCH6_F_EQUATOR = prove
 (`!e0 a. &1 / &2 < a /\ a < &2 /\ &0 < e0 /\ e0 <= &1 / &16
          ==> vector[a; &0; &0]:real^3 IN sch6_fcone /\
              norm(vector[a; &0; &0]:real^3) = a /\
              sch_flip3(sch_cap_collar e0 (sch_flip3(vector[a; &0; &0]))) =
              vector[sqrt(&1 + e0 * (a - &1)); &0; &1]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(vector[a; &0; &0]:real^3) = a` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_EQ_SQUARE; DOT_3; VECTOR_3] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[sch6_fcone; IN_ELIM_THM; VECTOR_3] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[sch_flip3; VECTOR_3; REAL_NEG_0] THEN
  REWRITE_TAC[sch_cap_collar; sch_capq; VECTOR_3] THEN
  SUBGOAL_THEN `norm(vector[a; &0; &0]:real^3) = a` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `smooth_step(--(&6)) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_0 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ADD_RID] THEN
  SUBGOAL_THEN `sch_cap_profile(&1) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `a * inv a = &1` (fun th -> REWRITE_TAC[th; REAL_MUL_RID]) THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Selecting the set equation of the push data with a given right side. *)

let sch6_eq_with r t th =
  is_eq(concl th) && rhs(concl th) = r && can (find_term ((=) t)) (lhs(concl th));;

(* S misses the inside of S2, and S1 misses the closed ball bounded by S2:  *)
(* the side A of S containing Theta(r^2 > 1) misses S2 and contains an     *)
(* outer layer point of g2, so it lies outside S2.                         *)

let SCH6_PD_SIDES = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0
        ==> S INTER inside S2 = {} /\ S1 INTER (S2 UNION inside S2) = {}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `A:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "AOUT") (LABEL_TAC "AIN"))))) o
    MATCH_MP SCH6_PD_SIDE_A) THEN
  FIRST_ASSUM(LABEL_TAC "CUP" o MATCH_MP SCH6_PD_CUP) THEN
  UNDISCH_TAC `sch6_push_data S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0` THEN
  SCH6_PD_TAC THEN
  MP_TAC(ISPEC `S2:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. y IN sch_slab_nbhd ==> y IN N` (LABEL_TAC "SN") THENL
   [UNDISCH_TAC `sch_slab_nbhd SUBSET (N:real^3->bool)` THEN SIMP_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(E2:real^3->bool) SUBSET S /\ (E1:real^3->bool) SUBSET S` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S:real^3->bool` `sch_lat`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `A INTER (S2:real^3->bool) = {}` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S2:real^3->bool` `sch_cap2`)) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `p:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THENL
     [ASM SET_TAC[];
      FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(y:real^3) IN N /\ y$1 pow 2 + y$2 pow 2 <= &1` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN sch_cap2` THEN
        REWRITE_TAC[sch_cap2; IN_ELIM_THM] THEN STRIP_TAC THEN
        MP_TAC(SPEC `(y:real^3)$3` SCH_CAP_PROFILE_BOUNDS) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN CONJ_TAC THENL
         [USE_THEN "SN" MATCH_MP_TAC THEN REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM] THEN
          ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_CASES_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 = &1` THENL
       [SUBGOAL_THEN `(Theta:real^3->real^3) y IN S` MP_TAC THENL
         [ASM_SIMP_TAC[]; ASM SET_TAC[]];
        SUBGOAL_THEN `~((Theta:real^3->real^3) y IN A)` MP_TAC THENL
         [USE_THEN "AIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c2:real^3->real^3)(vector[&9 / &8; &0; &0]) IN A /\
                c2(vector[&9 / &8; &0; &0]) IN outside S2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`e0:real`; `&9 / &8`] SCH6_F_EQUATOR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `vector[&9 / &8; &0; &0]:real^3 IN annulus (&3 / &4) (&2) /\
                  vector[&9 / &8; &0; &0]:real^3 IN annulus (&1) (&2)` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o C MATCH_MP
        (ASSUME `vector[&9 / &8; &0; &0]:real^3 IN annulus (&3 / &4) (&2)`)) THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `vector[&9 / &8; &0; &0]:real^3 IN sch6_fcone`)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "AOUT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[VECTOR_3] THEN
      SUBGOAL_THEN `sqrt(&1 + e0 * (&9 / &8 - &1)) pow 2 = &1 + e0 * (&9 / &8 - &1)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `A SUBSET outside(S2:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S2:real^3->bool`; `A:real^3->bool`;
                   `(c2:real^3->real^3)(vector[&9 / &8; &0; &0])`] SCH6_SIDE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^3->bool) SUBSET S2 UNION outside S2` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(outside S2:real^3->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(A:real^3->bool)` THEN CONJ_TAC THENL
       [UNDISCH_TAC `frontier A = (S:real^3->bool)` THEN REWRITE_TAC[frontier] THEN SET_TAC[];
        MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC CLOSURE_OUTSIDE_SUBSET THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MP_TAC(ISPECL [`S2:real^3->bool`; `sphere(vec 0:real^3,&1)`] HOMEOMORPHIC_COMPACTNESS) THEN
      ASM_REWRITE_TAC[COMPACT_SPHERE]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `S2:real^3->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S1:real^3->bool` `sch_cap1`)) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `p:real^3` THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THENL
   [SUBGOAL_THEN `~((p:real^3) IN S2)` ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S2:real^3->bool` `sch_cap2`)) THEN
      REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
      DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THENL
       [UNDISCH_TAC `DISJOINT (E1:real^3->bool) E2` THEN UNDISCH_TAC `(p:real^3) IN E1` THEN
        UNDISCH_TAC `(p:real^3) IN E2` THEN SET_TAC[];
        UNDISCH_TAC `(p:real^3) IN E1` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y:real^3) IN sch_cap2` THEN REWRITE_TAC[sch_cap2; IN_ELIM_THM] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `(y:real^3) IN N` (fun th -> FIRST_ASSUM(MP_TAC o CONJUNCT1 o C MATCH_MP th))
        THENL
         [USE_THEN "SN" MATCH_MP_TAC THEN REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM] THEN
          MP_TAC(SPEC `(y:real^3)$3` SCH_CAP_PROFILE_BOUNDS) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
          DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3) IN outside S2` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `inside S2 INTER outside S2 = {}:real^3->bool` THEN ASM SET_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^3) IN sch_slab_nbhd /\ y$3 <= --(&1 / &2)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN sch_cap1` THEN
      REWRITE_TAC[sch_cap1; sch_slab_nbhd; IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(SPEC `--((y:real^3)$3)` SCH_CAP_PROFILE_BOUNDS) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REMOVE_THEN "CUP" (MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[IN_UNION] THEN
    MP_TAC(SPEC `(y:real^3)$3` SCH_CAP_PROFILE_TIP) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(SPEC `(y:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The second model surface sch6_u1 (S1 near its dome); the                  *)
(* flipped model collar F is onto the bowl of the flipped capsule; ball      *)
(* charts reflected; the capsule chart read in the frame of S2 (sch6_nu c =  *)
(* flip o c o flip) and its images; the S1 chart; north model values.       *)
(* ------------------------------------------------------------------------- *)

let sch6_u1 = new_definition
 `sch6_u1 (y:real^3) = y$1 pow 2 + y$2 pow 2 - sch_cap_profile(--(y$3))`;;

let SCH6_PROFILE_LE1 = prove
 (`!t. sch_cap_profile t <= &1`,
  GEN_TAC THEN ASM_CASES_TAC `t < &1 / &2` THENL
   [ASM_SIMP_TAC[SCH_CAP_PROFILE_TIP; REAL_ARITH `t < &1 / &2 ==> t <= &5 / &8`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&3 / &2 < t` THENL
   [ASM_SIMP_TAC[SCH_CAP_PROFILE_TOP; REAL_ARITH `&3 / &2 < t ==> &7 / &8 <= t`; REAL_LE_REFL];
    MP_TAC(SPEC `t:real` SCH_CAP_PROFILE_BOUNDS) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

let SCH6_U_LOW = prove
 (`!y:real^3. y$3 <= &9 / &8 ==> (sch6_u y = &0 <=> y$1 pow 2 + y$2 pow 2 = &1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch6_u] THEN
  SUBGOAL_THEN `sch_cap_profile(&2 - (y:real^3)$3) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* The flipped capsule lies at heights in [1/2, 3/2]; inside it sch6_u < 0, *)
(* on it sch6_u1 > 0.                                                        *)

let SCH6_QQ_HEIGHT = prove
 (`!y:real^3. y$1 pow 2 + y$2 pow 2 <= sch6_qq y ==> &1 / &2 <= y$3 /\ y$3 <= &3 / &2`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `(y:real^3)$3 < &1 / &2 \/ &3 / &2 < y$3` THENL
   [MP_TAC(SPEC `y:real^3` SCH6_QQ_OUT) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `(y:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SCH6_QQ_U = prove
 (`!y:real^3. y$1 pow 2 + y$2 pow 2 < sch6_qq y ==> sch6_u y < &0`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `y:real^3` SCH6_QQ_HEIGHT) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[sch6_u] THEN
  ASM_CASES_TAC `(y:real^3)$3 = &1 / &2 \/ y$3 = &3 / &2` THENL
   [SUBGOAL_THEN `sch6_qq y = &0` ASSUME_TAC THENL
     [REWRITE_TAC[sch6_qq] THEN FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_RZERO];
      MP_TAC(SPEC `(y:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&7 / &8 <= (y:real^3)$3` THENL
   [MP_TAC(SPEC `y:real^3` SCH6_QQ_TOP) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 < sch6_qq y` THEN
      REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    MP_TAC(SPEC `y:real^3` SCH6_QQ_BOT) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 < sch6_qq y` THEN
      REWRITE_TAC[th]) THEN
    MP_TAC(SPEC `(y:real^3)$3` SCH6_PROFILE_LT1) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sch_cap_profile(&2 - (y:real^3)$3) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let SCH6_QQ_U1 = prove
 (`!y:real^3. y$1 pow 2 + y$2 pow 2 <= sch6_qq y ==> &0 < sch6_u1 y`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SCH6_QQ_HEIGHT) THEN STRIP_TAC THEN
  REWRITE_TAC[sch6_u1] THEN
  MP_TAC(SPEC `--((y:real^3)$3)` SCH_CAP_PROFILE_TIP) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPEC `(y:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
  ASM_REAL_ARITH_TAC);;

(* The flipped model collar maps the unit sphere onto the bowl of the       *)
(* flipped capsule below height 9/8 (explicit preimage through gamma).      *)

let SCH6_F_ONTO = prove
 (`!e0 y:real^3.
        y$1 pow 2 + y$2 pow 2 = sch_cap_profile(y$3) /\ &1 / &2 <= y$3 /\ y$3 < &9 / &8
        ==> ?z. norm z = &1 /\ z IN sch6_fcone /\ z$3 = &2 * y$3 - &2 /\
                sch_flip3(sch_cap_collar e0 (sch_flip3 z)) = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `x = sch6_gammai(sch_flip3 y)` THEN
  EXISTS_TAC `sch_flip3 x` THEN
  SUBGOAL_THEN `norm(x:real^3) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN REWRITE_TAC[SCH6_GAMMAI_NORM_CMP] THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(y:real^3)$3 = &1 / &2` THENL
     [ASM_REWRITE_TAC[sch6_qq] THEN
      SUBGOAL_THEN `sch_cap_profile(&1 / &2) = &0` SUBST1_TAC THENL
       [SIMP_TAC[SCH_CAP_PROFILE_TIP; REAL_ARITH `&1 / &2 <= &5 / &8`] THEN REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_RZERO]];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCH6_QQ_BOT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3)$3 = &2 * (&1 - (y:real^3)$3)` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN REWRITE_TAC[sch6_gammai; VECTOR_3; SCH6_FLIP3_COMPONENTS] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN sch_capcone` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[sch_capcone; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[SCH6_NORM_FLIP3; SCH6_FCONE_FLIP; SCH_FLIP3_INVOLUTION;
                  SCH6_FLIP3_COMPONENTS] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM SCH6_CAPSULE_CONE; SCH6_CAPSULE_SPHERE] THEN
  EXPAND_TAC "x" THEN REWRITE_TAC[SCH6_GAMMA_INVERSES; SCH_FLIP3_INVOLUTION]);;

(* Ball charts reflected. *)

let SCH6_BALL_FLIP = prove
 (`!c c':real^3->real^3.
        sch_ball c c'
        ==> sch_ball (sch_flip3 o c o sch_flip3) (sch_flip3 o c' o sch_flip3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_ball] THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE sch_flip3 (ball(vec 0:real^3,&2)) = ball(vec 0,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; SCH6_IN_FLIP3; IN_BALL_0; SCH6_NORM_FLIP3]; ALL_TAC] THEN
  REWRITE_TAC[SCH6_IMAGE_FLIP3_CONJ] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `diffeomorphism_on (ball(vec 0:real^3,&2)) (ball(vec 0,&2)) sch_flip3 sch_flip3`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sch_flip3`; `sch_flip3`; `ball(vec 0:real^3,&2)`]
      SCH_DIFFEO_RESTRICT_UNIV) THEN
    ASM_REWRITE_TAC[SCH6_FLIP3_DIFFEO; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (IMAGE (c:real^3->real^3) (ball(vec 0,&2)))
                  (IMAGE sch_flip3 (IMAGE c (ball(vec 0,&2)))) sch_flip3 sch_flip3`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCH_DIFFEO_RESTRICT_UNIV THEN REWRITE_TAC[SCH6_FLIP3_DIFFEO] THEN
    UNDISCH_TAC `diffeomorphism_on (ball(vec 0:real^3,&2))
                   (IMAGE (c:real^3->real^3) (ball(vec 0,&2))) c c'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (ball(vec 0:real^3,&2))
                  (IMAGE (c:real^3->real^3) (ball(vec 0,&2)))
                  (c o sch_flip3) (sch_flip3 o c')` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `ball(vec 0:real^3,&2)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^3,&2)`; `IMAGE (c:real^3->real^3) (ball(vec 0,&2))`;
                 `IMAGE sch_flip3 (IMAGE (c:real^3->real^3) (ball(vec 0,&2)))`;
                 `(c:real^3->real^3) o sch_flip3`; `sch_flip3 o (c':real^3->real^3)`;
                 `sch_flip3`; `sch_flip3`] DIFFEOMORPHISM_ON_COMPOSE) THEN
  ASM_REWRITE_TAC[o_ASSOC]);;

(* The capsule chart (from SCH6_CAPSULE_CHART) read in the frame of S2. *)

let sch6_capchart = new_definition
 `sch6_capchart (c:real^3->real^3) c' e0 <=>
    sch_ball c c' /\ IMAGE c (cball(vec 0,&1)) = IMAGE sch6_gamma (cball(vec 0,&1)) /\
    (!x. x IN annulus (&3 / &4) (&2) ==> c x = sch6_capsule e0 x)`;;

let sch6_nu = new_definition
 `sch6_nu (c:real^3->real^3) (z:real^3) = sch_flip3(c(sch_flip3 z))`;;

let SCH6_NU_FACTS = prove
 (`!c c' e0.
        sch6_capchart c c' e0
        ==> diffeomorphism_on (ball(vec 0,&2)) (IMAGE (sch6_nu c) (ball(vec 0,&2)))
                              (sch6_nu c) (sch6_nu c') /\
            (!y. y IN IMAGE (sch6_nu c) (ball(vec 0,&1)) <=>
                 y$1 pow 2 + y$2 pow 2 < sch6_qq y) /\
            (!y. y IN IMAGE (sch6_nu c) (sphere(vec 0,&1)) <=>
                 y$1 pow 2 + y$2 pow 2 = sch6_qq y) /\
            (!y. y IN IMAGE (sch6_nu c) (cball(vec 0,&1)) <=>
                 y$1 pow 2 + y$2 pow 2 <= sch6_qq y) /\
            (!z. z IN sch6_fcone /\ &3 / &4 < norm z
                 ==> sch6_nu c z = sch_flip3(sch_cap_collar e0 (sch_flip3 z))) /\
            (!z. z IN sch_capcone /\ &3 / &4 < norm z
                 ==> sch6_nu c z = sch_cap_collar e0 z + &2 % basis 3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch6_capchart] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. sch6_nu c z = sch_flip3((c:real^3->real^3)(sch_flip3 z))` ASSUME_TAC THENL
   [REWRITE_TAC[sch6_nu]; ALL_TAC] THEN
  SUBGOAL_THEN `!z w. z IN ball(vec 0,&2) /\ w IN ball(vec 0,&2) /\
                      (c:real^3->real^3) z = c w ==> z = w` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_ball (c:real^3->real^3) c'` THEN
    REWRITE_TAC[sch_ball; diffeomorphism_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^3->real^3) (sphere(vec 0,&1)) = IMAGE sch6_gamma (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(SPEC `e0:real` SCH6_CAPSULE_SPHERE_IMAGE)] THEN
    MATCH_MP_TAC(SET_RULE `!f g:real^3->real^3 s.
                            (!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `sch6_capsule e0`))
      (concl th))) THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET cball(vec 0,&1) /\
                cball(vec 0:real^3,&1) SUBSET ball(vec 0,&2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^3->real^3) (ball(vec 0,&1)) = IMAGE sch6_gamma (ball(vec 0,&1))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `ball(vec 0:real^3,&1) = cball(vec 0,&1) DIFF sphere(vec 0,&1)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_DIFF; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:real^3->real^3`; `cball(vec 0:real^3,&1)`; `sphere(vec 0:real^3,&1)`;
                   `ball(vec 0:real^3,&2)`]
      (SET_RULE `!f:real^3->real^3 s t u.
                    (!z w. z IN u /\ w IN u /\ f z = f w ==> z = w) /\
                    t SUBSET s /\ s SUBSET u
                    ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t`)) THEN
    MP_TAC(ISPECL [`sch6_gamma`; `cball(vec 0:real^3,&1)`; `sphere(vec 0:real^3,&1)`]
      (SET_RULE `!f:real^3->real^3 s t. (!z w. f z = f w ==> z = w) /\ t SUBSET s
                                        ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t`)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MESON_TAC[SCH6_GAMMA_INVERSES]; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. IMAGE (sch6_nu c) s =
                    IMAGE sch_flip3 (IMAGE (c:real^3->real^3) (IMAGE sch_flip3 s))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM SCH6_IMAGE_FLIP3_CONJ] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; sch6_nu];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE sch_flip3 (ball(vec 0:real^3,&1)) = ball(vec 0,&1) /\
                IMAGE sch_flip3 (sphere(vec 0:real^3,&1)) = sphere(vec 0,&1) /\
                IMAGE sch_flip3 (cball(vec 0:real^3,&1)) = cball(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; SCH6_IN_FLIP3; IN_BALL_0; IN_SPHERE_0; IN_CBALL_0;
                SCH6_NORM_FLIP3];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `sch6_nu c = sch_flip3 o c o sch_flip3 /\
                  sch6_nu c' = sch_flip3 o c' o sch_flip3` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; sch6_nu]; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real^3->real^3`; `c':real^3->real^3`] SCH6_BALL_FLIP) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[sch_ball];
    ASM_REWRITE_TAC[SCH6_IN_FLIP_GAMMA; IN_BALL_0; SCH6_GAMMAI_NORM_CMP];
    ASM_REWRITE_TAC[SCH6_IN_FLIP_GAMMA; IN_SPHERE_0; SCH6_GAMMAI_NORM_CMP];
    ASM_REWRITE_TAC[SCH6_IN_FLIP_GAMMA; IN_CBALL_0; SCH6_GAMMAI_NORM_CMP];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH6_NU_FCONE THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH6_NU_CONE THEN
    ASM_REWRITE_TAC[]]);;

(* The S1 chart: S1 is the level sch6_u1 = 0 in the chart Theta. *)

let SCH6_SD_S1_CHART = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2.
        sch6_slab_data S S1 S2 Theta Theta' N E1 E2
        ==> !y. y IN N ==> (Theta y IN S1 <=> sch6_u1 y = &0)`,
  REPEAT GEN_TAC THEN SCH6_SD_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `sch_cap1 SUBSET (N:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; sch_cap1] THEN X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(SPEC `--((w:real^3)$3)` SCH_CAP_PROFILE_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `!y:real^3. y IN sch_slab_nbhd ==> y IN N` THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S1:real^3->bool` `sch_cap1`)) THEN
  REWRITE_TAC[IN_UNION] THEN
  SUBGOAL_THEN `(Theta:real^3->real^3) y IN IMAGE Theta sch_cap1 <=> y IN sch_cap1`
  SUBST1_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `y:real^3 = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
      UNDISCH_TAC `!y z. y IN N /\ z IN N /\ (Theta:real^3->real^3) y = Theta z ==> y = z` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(y:real^3) IN N`) o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `E1:real^3->bool`)) (concl th))) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[sch_cap1; IN_ELIM_THM; sch6_u1] THEN
  ASM_CASES_TAC `(y:real^3)$3 < -- &1` THENL
   [SUBGOAL_THEN `sch_cap_profile(--((y:real^3)$3)) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^3)$3 <= --(&1 / &2)` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `--((y:real^3)$3)` SCH_CAP_PROFILE_TIP) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPEC `(y:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
  ASM_REAL_ARITH_TAC);;

(* North of the cone the c2 frame is the model collar translated by 2 e3:  *)
(* high up, sch6_u is the layer parameter, and sch6_u1 > 0.                *)

let SCH6_NORTH_MODEL = prove
 (`!e0 z:real^3. &0 < e0 /\ e0 <= &1 / &16 /\ z IN sch_capcone /\ norm z / &4 <= z$3
        ==> &35 / &32 <= (sch_cap_collar e0 z + &2 % basis 3)$3 /\
            sch6_u(sch_cap_collar e0 z + &2 % basis 3) = e0 * (norm z - &1) /\
            &0 < sch6_u1(sch_cap_collar e0 z + &2 % basis 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e0:real`; `z:real^3`] SCH6_CAPCOLLAR_HEIGHT_TOP) THEN
  MP_TAC(SPECL [`e0:real`; `z:real^3`] SCH_CAP_COLLAR_LAYER) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `y = sch_cap_collar e0 (z:real^3)` THEN STRIP_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[sch6_u; sch6_u1; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `&2 - (y + &2) = --y`] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `--((y:real^3)$3 + &2)` SCH_CAP_PROFILE_TIP) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(SPEC `(y:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness of the model functions and their level sets; the               *)
(* box of the chart Theta used by the model chart; north of the cone c2 maps *)
(* the closed unit sphere into E2, away from S1 and from Theta(closed box),  *)
(* and so does a slightly bigger ball (compactness): sch6_radius.            *)
(* ------------------------------------------------------------------------- *)

let SCH6_SMOOTH_BASICS = prove
 (`(!k. smooth_map_on (:real^3) (\y:real^3. lift(y$k))) /\
   smooth_map_on (:real^3) (\y:real^3. lift(y$1 pow 2 + y$2 pow 2)) /\
   (!a b. smooth_map_on (:real^3) (\y:real^3. lift(sch_cap_profile(a + b * y$3)))) /\
   smooth_map_on (:real^3) (\y. lift(sch6_u y)) /\
   smooth_map_on (:real^3) (\y. lift(sch6_u1 y))`,
  SUBGOAL_THEN `!k. smooth_map_on (:real^3) (\y:real^3. lift(y$k))` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. y`; `k:num`]
      SMOOTH_MAP_ON_LIFT_COMPONENT) THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k n. smooth_map_on (:real^3) (\y:real^3. lift(y$k pow n))` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. lift(y$k)`; `n:num`] SMOOTH_MAP_ON_LIFT_POW) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\y:real^3. lift(y$1 pow 2 + y$2 pow 2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. smooth_map_on (:real^3) (\y:real^3. lift(sch_cap_profile(a + b * y$3)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `(\y:real^3. lift(sch_cap_profile(a + b * y$3))) =
                  (lift o sch_cap_profile o drop) o (\y:real^3. lift(a + b * y$3))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SCH_CAP_PROFILE_SMOOTH] THEN
    REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!a b. smooth_map_on (:real^3)
                  (\y:real^3. lift(y$1 pow 2 + y$2 pow 2) - lift(sch_cap_profile(a + b * y$3)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THENL
   [EXISTS_TAC `\y:real^3. lift(y$1 pow 2 + y$2 pow 2) -
                           lift(sch_cap_profile(&2 + --(&1) * y$3))`;
    EXISTS_TAC `\y:real^3. lift(y$1 pow 2 + y$2 pow 2) -
                           lift(sch_cap_profile(&0 + --(&1) * y$3))`] THEN
  ASM_REWRITE_TAC[IN_UNIV; GSYM LIFT_SUB; LIFT_EQ; sch6_u; sch6_u1] THEN
  GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `&2 + --(&1) * y = &2 - y`; REAL_ARITH `&0 + --(&1) * y = --y`] THEN
  REAL_ARITH_TAC);;

(* Strict sublevel and superlevel sets of smooth functions are open, weak    *)
(* ones closed.                                                              *)

let SCH6_LEVEL_SETS = prove
 (`!g:real^3->real.
        smooth_map_on (:real^3) (\y. lift(g y))
        ==> (!c. open {y | g y < c}) /\ (!c. open {y | c < g y}) /\
            (!c. closed {y | g y <= c}) /\ (!c. closed {y | c <= g y})`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. (\y. lift((g:real^3->real) y)) continuous (at x)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `c:real` THENL
   [SUBGOAL_THEN `{y:real^3 | g y < c} = {y | lift(g y) IN {x:real^1 | x$1 < c}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT];
    SUBGOAL_THEN `{y:real^3 | c < g y} = {y | lift(g y) IN {x:real^1 | x$1 > c}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP; real_gt]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT];
    SUBGOAL_THEN `{y:real^3 | g y <= c} = {y | lift(g y) IN {x:real^1 | x$1 <= c}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE];
    SUBGOAL_THEN `{y:real^3 | c <= g y} = {y | lift(g y) IN {x:real^1 | x$1 >= c}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP; real_ge]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE]]);;

(* The box of the chart Theta used by the model chart. *)

let sch6_box = new_definition
 `sch6_box = {y:real^3 | y$1 pow 2 + y$2 pow 2 < &2 /\
                         --(&79 / &64) < y$3 /\ y$3 < &17 / &16}`;;

let sch6_cbox = new_definition
 `sch6_cbox = {y:real^3 | y$1 pow 2 + y$2 pow 2 <= &2 /\
                          --(&79 / &64) <= y$3 /\ y$3 <= &17 / &16}`;;

let SCH6_BOX_FACTS = prove
 (`open sch6_box /\ compact sch6_cbox /\ sch6_box SUBSET sch6_cbox /\
   sch6_cbox SUBSET sch_slab_nbhd /\ sch_lat SUBSET sch6_box /\
   sch_cap1 SUBSET sch6_box /\ sch_cap2 SUBSET sch6_cbox`,
  MP_TAC SCH6_SMOOTH_BASICS THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCH6_LEVEL_SETS (CONJUNCT1(CONJUNCT2 th))) THEN
                       MP_TAC(MATCH_MP SCH6_LEVEL_SETS (SPEC `3` (CONJUNCT1 th)))) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o BETA_RULE) THEN DISCH_THEN(STRIP_ASSUME_TAC o BETA_RULE) THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `sch6_box = {y:real^3 | y$1 pow 2 + y$2 pow 2 < &2} INTER
                             {y | --(&79 / &64) < y$3} INTER {y | y$3 < &17 / &16}`
    SUBST1_TAC THENL
     [REWRITE_TAC[sch6_box; EXTENSION; IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [REWRITE_TAC[BOUNDED_POS] THEN EXISTS_TAC `&3` THEN REWRITE_TAC[REAL_ARITH `&0 < &3`] THEN
      REWRITE_TAC[sch6_cbox; IN_ELIM_THM; NORM_LE_SQUARE; DOT_3] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SUBGOAL_THEN `&0 <= (&2 - (y:real^3)$3) * (&2 + y$3)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 <= &2` THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `sch6_cbox = {y:real^3 | y$1 pow 2 + y$2 pow 2 <= &2} INTER
                                {y | --(&79 / &64) <= y$3} INTER {y | y$3 <= &17 / &16}`
      SUBST1_TAC THENL
       [REWRITE_TAC[sch6_cbox; EXTENSION; IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[sch6_box; sch6_cbox; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[sch6_cbox; sch_slab_nbhd; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[sch6_box; sch_lat; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[sch6_box; sch_cap1; SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN MP_TAC(SPEC `--((y:real^3)$3)` SCH6_PROFILE_LE1) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[sch6_cbox; sch_cap2; SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN MP_TAC(SPEC `(y:real^3)$3` SCH6_PROFILE_LE1) THEN ASM_REAL_ARITH_TAC]);;

(* North of the cone, c2 maps the unit sphere into E2, away from S1 and     *)
(* from Theta(closed box): Theta^-1(S2) in the box is the bowl, which is    *)
(* covered by the part of the sphere in the cone (SCH6_F_ONTO).            *)

let SCH6_PD_NORTH_SPHERE = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0
        ==> !z. norm z = &1 /\ norm z / &4 <= z$3
                ==> c2 z IN E2 /\ ~(c2 z IN S1) /\ ~(c2 z IN IMAGE Theta sch6_cbox)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "CH" o MATCH_MP SCH6_PD_S2_CHART) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH6_PD_SIDES) THEN
  UNDISCH_TAC `sch6_push_data S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0` THEN
  SCH6_PD_TAC THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN annulus (&1 / &2) (&2) /\ y IN annulus (&1 / &2) (&2) /\
                      (g2:real^3->real^3) x = g2 y ==> x = y` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_neck (g2:real^3->real^3) g2'` THEN
    REWRITE_TAC[sch_neck; diffeomorphism_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN annulus (&1 / &2) (&2) /\ z IN annulus (&3 / &4) (&2)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c2:real^3->real^3) z = g2 z /\ g2 z IN S2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `annulus (&3 / &4) (&2):real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `S2:real^3->bool` &&
        can (find_term ((=) `g2:real^3->real^3`)) (lhs(concl th)))) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((g2:real^3->real^3) z IN IMAGE Theta sch6_cbox)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN sch_slab_nbhd` ASSUME_TAC THENL
     [MP_TAC SCH6_BOX_FACTS THEN ASM SET_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "CH" (MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Theta:real^3->real^3) y IN S2` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; STRIP_TAC] THEN
    MP_TAC(SPECL [`e0:real`; `y:real^3`] SCH6_F_ONTO) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN sch6_cbox` THEN
      REWRITE_TAC[sch6_cbox; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `w:real^3 = z` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `annulus (&1 / &2) (&2):real^3->bool`)) (concl th) &&
        can (find_term ((=) `g2:real^3->real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `(w:real^3) IN sch6_fcone`) o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `sch6_fcone`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(w:real^3) IN sch6_fcone` THEN ASM_REWRITE_TAC[sch6_fcone; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(g2:real^3->real^3) z IN S2` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S2:real^3->bool` `sch_cap2`)) THEN
    REWRITE_TAC[IN_UNION] THEN MATCH_MP_TAC(TAUT `~b ==> a \/ b ==> a`) THEN
    UNDISCH_TAC `~((g2:real^3->real^3) z IN IMAGE Theta sch6_cbox)` THEN
    MP_TAC SCH6_BOX_FACTS THEN SET_TAC[];
    UNDISCH_TAC `S1 INTER (S2 UNION inside S2) = {}:real^3->bool` THEN
    UNDISCH_TAC `(g2:real^3->real^3) z IN S2` THEN SET_TAC[]]);;

(* A closed half-cone. *)

let SCH6_CLOSED_HALF = prove
 (`!a b. closed {x:real^3 | a * norm x <= b * x$3}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x:real^3 | a * norm x <= b * x$3} =
                {x | lift(b * x$3 - a * norm x) IN {y:real^1 | y$1 >= &0}}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
  REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE] THEN GEN_TAC THEN
  REWRITE_TAC[LIFT_SUB; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_CMUL THENL
   [SIMP_TAC[CONTINUOUS_AT_LIFT_COMPONENT; DIMINDEX_3; ARITH];
    REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_AT_LIFT_NORM]]);;

(* The radius of the model chart: north of the cone, c2 keeps away from S1 *)
(* and from Theta(closed box) on a ball slightly bigger than the unit ball. *)

let sch6_radius = new_definition
 `sch6_radius (S1:real^3->bool) (Theta:real^3->real^3) (c2:real^3->real^3) R <=>
    &1 < R /\ R <= &9 / &8 /\
    !z. norm z / &4 <= z$3 /\ &1 <= norm z /\ norm z <= R
        ==> ~(c2 z IN S1) /\ ~(c2 z IN IMAGE Theta sch6_cbox)`;;

let SCH6_PD_RADIUS = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0
        ==> ?R. sch6_radius S1 Theta c2 R`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH6_PD_NORTH_SPHERE) THEN
  UNDISCH_TAC `sch6_push_data S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0` THEN
  SCH6_PD_TAC THEN
  SUBGOAL_THEN `compact(S1:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S1:real^3->bool`; `sphere(vec 0:real^3,&1)`] HOMEOMORPHIC_COMPACTNESS) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c2:real^3->real^3`;
                 `{z:real^3 | norm z / &4 <= z$3 /\ &1 <= norm z /\ norm z <= &3 / &2}`;
                 `S1 UNION IMAGE (Theta:real^3->real^3) sch6_cbox`] SCH6_RADIAL_AVOID) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `{z:real^3 | norm z / &4 <= z$3 /\ &1 <= norm z /\ norm z <= &3 / &2} =
                    {x | &1 / &4 * norm x <= &1 * x$3} INTER
                    (cball(vec 0,&3 / &2) DIFF ball(vec 0,&1))` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
        REAL_ARITH_TAC;
        ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
        REWRITE_TAC[SCH6_CLOSED_HALF] THEN MATCH_MP_TAC COMPACT_DIFF THEN
        REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `sch_ball (c2:real^3->real^3) c2'` THEN
        SIMP_TAC[sch_ball; diffeomorphism_on; SMOOTH_MAP_ON_CONTINUOUS_ON];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL_0] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[SCH6_BOX_FACTS] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `N:real^3->bool` THEN CONJ_TAC THENL
       [UNDISCH_TAC `diffeomorphism_on N (IMAGE (Theta:real^3->real^3) N) Theta Theta'` THEN
        SIMP_TAC[diffeomorphism_on; SMOOTH_MAP_ON_CONTINUOUS_ON];
        MP_TAC SCH6_BOX_FACTS THEN UNDISCH_TAC `sch_slab_nbhd SUBSET (N:real^3->bool)` THEN
        SET_TAC[]];
      X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_ELIM_THM; IN_UNION; DE_MORGAN_THM] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sch6_cbox`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min R (&9 / &8)` THEN REWRITE_TAC[sch6_radius] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[DE_MORGAN_THM]]);;

(* ------------------------------------------------------------------------- *)
(* The model chart Xi of the push, glued from Theta on the box               *)
(* minus the core nu(cball(0,7/8)) of the flipped capsule (sch6_mlo) and    *)
(* from c2 o nu^-1 on nu(ball(0,R)) (sch6_mhi); the two agree on the        *)
(* overlap (there c2 = g2 = Theta o F and nu = F) and Xi is injective.      *)
(* ------------------------------------------------------------------------- *)

let sch6_mlo = new_definition
 `sch6_mlo (c:real^3->real^3) = sch6_box DIFF IMAGE (sch6_nu c) (cball(vec 0,&7 / &8))`;;

let sch6_mhi = new_definition
 `sch6_mhi (c:real^3->real^3) R = IMAGE (sch6_nu c) (ball(vec 0,R))`;;

let sch6_xi = new_definition
 `sch6_xi (Theta:real^3->real^3) (c2:real^3->real^3) (c:real^3->real^3) c' R (y:real^3) =
    if y IN sch6_mhi c R then c2(sch6_nu c' y) else Theta y`;;

let SCH6_NU_CHART = prove
 (`!c c' e0 R.
        sch6_capchart c c' e0 /\ &1 < R /\ R <= &2
        ==> diffeomorphism_on (ball(vec 0,R)) (sch6_mhi c R) (sch6_nu c) (sch6_nu c') /\
            open(sch6_mhi c R) /\
            (!z. z IN ball(vec 0,&2) ==> sch6_nu c' (sch6_nu c z) = z) /\
            (!y. y IN sch6_mhi c R
                 ==> sch6_nu c' y IN ball(vec 0,R) /\ sch6_nu c (sch6_nu c' y) = y) /\
            IMAGE (sch6_nu c) (cball(vec 0,&1)) SUBSET sch6_mhi c R /\
            compact(IMAGE (sch6_nu c) (cball(vec 0,&7 / &8)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP SCH6_NU_FACTS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `diffeomorphism_on (ball(vec 0,R)) (sch6_mhi c R) (sch6_nu c) (sch6_nu c')`
  ASSUME_TAC THENL
   [REWRITE_TAC[sch6_mhi] THEN MATCH_MP_TAC SCH2_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,&2)`;
                          `IMAGE (sch6_nu c) (ball(vec 0:real^3,&2))`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `diffeomorphism_on (ball(vec 0,R)) (sch6_mhi c R) (sch6_nu c) (sch6_nu c')` THEN
  UNDISCH_TAC `diffeomorphism_on (ball(vec 0,&2)) (IMAGE (sch6_nu c) (ball(vec 0,&2)))
                                 (sch6_nu c) (sch6_nu c')` THEN
  REWRITE_TAC[diffeomorphism_on] THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    ASM SET_TAC[];
    ASM_SIMP_TAC[];
    REWRITE_TAC[sch6_mhi] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_CBALL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC]);;

(* On the overlap of the two pieces, c2 o nu^-1 = Theta. *)

let SCH6_XI_OVERLAP = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0 c c' R.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0 /\
        sch6_capchart c c' e0 /\ sch6_radius S1 Theta c2 R
        ==> !y. y IN sch6_mlo c /\ y IN sch6_mhi c R ==> c2(sch6_nu c' y) = Theta y`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  SCH6_PD_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH6_NU_FACTS) THEN
  UNDISCH_TAC `sch6_radius S1 (Theta:real^3->real^3) c2 R` THEN
  REWRITE_TAC[sch6_radius] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real^3->real^3`; `c':real^3->real^3`; `e0:real`; `R:real`]
    SCH6_NU_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[sch6_mlo; IN_DIFF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) MP_TAC) THEN
  REWRITE_TAC[sch6_mhi; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(z:real^3) IN ball(vec 0,&2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN ball(vec 0,R)` THEN REWRITE_TAC[IN_BALL_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `&7 / &8 < norm(z:real^3) /\ norm z < R` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN ball(vec 0,R)` THEN REWRITE_TAC[IN_BALL_0] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(sch6_nu c (z:real^3) IN IMAGE (sch6_nu c) (cball(vec 0,&7 / &8)))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_CBALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN sch6_fcone` ASSUME_TAC THENL
   [REWRITE_TAC[sch6_fcone; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN sch_capcone` ASSUME_TAC THENL
     [REWRITE_TAC[sch_capcone; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`e0:real`; `z:real^3`] SCH6_NORTH_MODEL) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sch6_nu c (z:real^3) = sch_cap_collar e0 z + &2 % basis 3`
    (SUBST1_TAC o SYM) THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sch_capcone`)) (concl th) &&
        can (find_term ((=) `sch6_nu c`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `sch6_nu c (z:real^3) IN sch6_box` THEN
    REWRITE_TAC[sch6_box; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c2:real^3->real^3) z = g2 z` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `annulus (&3 / &4) (&2):real^3->bool`)) (concl th) &&
      can (find_term ((=) `c2:real^3->real^3`)) (concl th))) THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `(z:real^3) IN sch6_fcone`) o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `sch6_fcone`)) (concl th) &&
                     can (find_term ((=) `g2:real^3->real^3`)) (concl th))) THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `sch6_fcone`)) (concl th) &&
    can (find_term ((=) `sch6_nu c`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* A point of the box with Theta x = c2 z, |z| < R, lies in nu(ball(0,R)):  *)
(* for |z| <= 1 it is in the cup, i.e. in the flipped capsule; in the cone  *)
(* it is F z = nu z; north of the cone it cannot occur (sch6_radius).       *)

let SCH6_XI_CROSS = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0 c c' R.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0 /\
        sch6_capchart c c' e0 /\ sch6_radius S1 Theta c2 R
        ==> !x z. x IN sch6_box /\ z IN ball(vec 0,R) /\ Theta x = c2 z
                  ==> x IN sch6_mhi c R`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(LABEL_TAC "CUP" o MATCH_MP SCH6_PD_CUP) THEN
  UNDISCH_TAC `sch6_push_data S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0` THEN
  SCH6_PD_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH6_NU_FACTS) THEN
  UNDISCH_TAC `sch6_radius S1 (Theta:real^3->real^3) c2 R` THEN
  REWRITE_TAC[sch6_radius] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RAD"))) THEN
  MP_TAC(SPECL [`c:real^3->real^3`; `c':real^3->real^3`; `e0:real`; `R:real`]
    SCH6_NU_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `z:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN sch_slab_nbhd /\ x IN N /\ x IN sch6_cbox /\ x$3 < &17 / &16`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^3) IN sch6_cbox` ASSUME_TAC THENL
     [MP_TAC SCH6_BOX_FACTS THEN UNDISCH_TAC `(x:real^3) IN sch6_box` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN sch_slab_nbhd` ASSUME_TAC THENL
     [MP_TAC SCH6_BOX_FACTS THEN UNDISCH_TAC `(x:real^3) IN sch6_cbox` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `sch_slab_nbhd SUBSET (N:real^3->bool)` THEN
      UNDISCH_TAC `(x:real^3) IN sch_slab_nbhd` THEN SET_TAC[];
      UNDISCH_TAC `(x:real^3) IN sch6_box` THEN REWRITE_TAC[sch6_box; IN_ELIM_THM] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `norm(z:real^3) <= &1` THENL
   [SUBGOAL_THEN `(Theta:real^3->real^3) x IN S2 UNION inside S2` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `cball(vec 0:real^3,&1)`)) (lhs(concl th)) &&
        can (find_term ((=) `c2:real^3->real^3`)) (lhs(concl th)))) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_CBALL_0];
      ALL_TAC] THEN
    REMOVE_THEN "CUP" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^3) IN sch_slab_nbhd`)]) THEN
    DISCH_TAC THEN
    UNDISCH_TAC `IMAGE (sch6_nu c) (cball(vec 0,&1)) SUBSET sch6_mhi c R` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `&1 / &2 < (x:real^3)$3` THENL
     [MP_TAC(SPEC `x:real^3` SCH6_QQ_BOT) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3)$3 = &1 / &2 /\ x$1 pow 2 + x$2 pow 2 = &0` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `(x:real^3)$3` SCH_CAP_PROFILE_TIP) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> UNDISCH_TAC
        `(x:real^3)$1 pow 2 + x$2 pow 2 <= sch_cap_profile(x$3)` THEN REWRITE_TAC[th]) THEN
      MP_TAC(SPEC `(x:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(x:real^3)$2` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[sch6_qq] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^3)$3 < norm z / &4` THENL
   [SUBGOAL_THEN `(z:real^3) IN sch6_fcone /\ z IN annulus (&3 / &4) (&2)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(vec 0,R)` THEN
      ASM_REWRITE_TAC[sch6_fcone; annulus; IN_ELIM_THM; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(z:real^3) IN sch6_fcone`) o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `sch6_fcone`)) (concl th) &&
                       can (find_term ((=) `g2:real^3->real^3`)) (concl th))) THEN
    SUBGOAL_THEN `x = sch_flip3(sch_cap_collar e0 (sch_flip3 z))` SUBST1_TAC THENL
     [UNDISCH_TAC `!y z. y IN N /\ z IN N /\ (Theta:real^3->real^3) y = Theta z ==> y = z` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sch_flip3(sch_cap_collar e0 (sch_flip3 z)) = sch6_nu c z` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sch6_fcone`)) (concl th) &&
        can (find_term ((=) `sch6_nu c`)) (concl th))) THEN
      UNDISCH_TAC `(z:real^3) IN annulus (&3 / &4) (&2)` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      REWRITE_TAC[sch6_mhi] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "RAD" (MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN ball(vec 0,R)` THEN REWRITE_TAC[IN_BALL_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(Theta:real^3->real^3) x = (c2:real^3->real^3) z`)) THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);;

(* The model chart Xi is a diffeomorphism of M = mlo UNION mhi onto an     *)
(* open set; Xi = Theta on mlo and Xi o nu = c2 on ball(0,R).               *)

let SCH6_XI_DIFFEO = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0 c c' R.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0 /\
        sch6_capchart c c' e0 /\ sch6_radius S1 Theta c2 R
        ==> (!y. y IN sch6_mlo c ==> sch6_xi Theta c2 c c' R y = Theta y) /\
            (!z. z IN ball(vec 0,R) ==> sch6_xi Theta c2 c c' R (sch6_nu c z) = c2 z) /\
            open(sch6_mlo c UNION sch6_mhi c R) /\
            ?Xi'. diffeomorphism_on (sch6_mlo c UNION sch6_mhi c R)
                    (IMAGE (sch6_xi Theta c2 c c' R) (sch6_mlo c UNION sch6_mhi c R))
                    (sch6_xi Theta c2 c c' R) Xi'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "OV" o MATCH_MP SCH6_XI_OVERLAP) THEN
  FIRST_ASSUM(LABEL_TAC "CR" o MATCH_MP SCH6_XI_CROSS) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN SCH6_PD_TAC THEN
  UNDISCH_TAC `sch6_radius S1 (Theta:real^3->real^3) c2 R` THEN
  REWRITE_TAC[sch6_radius] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real^3->real^3`; `c':real^3->real^3`; `e0:real`; `R:real`]
    SCH6_NU_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `open(sch6_mlo c) /\ sch6_mlo c SUBSET sch6_box` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[sch6_mlo] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[SCH6_BOX_FACTS; COMPACT_IMP_CLOSED];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y. y IN sch6_mlo c ==> sch6_xi Theta c2 c c' R y = (Theta:real^3->real^3) y) /\
    (!y. y IN sch6_mhi c R
         ==> sch6_xi Theta c2 c c' R y = ((c2:real^3->real^3) o sch6_nu c') y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[sch6_xi; o_THM] THEN CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "OV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `sch6_nu c (z:real^3) IN sch6_mhi c R /\ z IN ball(vec 0,&2)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[sch6_mhi] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(z:real^3) IN ball(vec 0,R)` THEN REWRITE_TAC[IN_BALL_0] THEN
        ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[o_THM]];
    MATCH_MP_TAC OPEN_UNION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SCH2_GLUE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`Theta:real^3->real^3`; `Theta':real^3->real^3`;
                        `(c2:real^3->real^3) o sch6_nu c'`; `sch6_nu c o (c2':real^3->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SCH2_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`N:real^3->bool`; `IMAGE (Theta:real^3->real^3) N`] THEN
    ASM_REWRITE_TAC[] THEN MP_TAC SCH6_BOX_FACTS THEN
    UNDISCH_TAC `sch_slab_nbhd SUBSET (N:real^3->bool)` THEN
    UNDISCH_TAC `sch6_mlo c SUBSET sch6_box` THEN SET_TAC[];
    SUBGOAL_THEN `diffeomorphism_on (sch6_mhi c R) (ball(vec 0,R)) (sch6_nu c') (sch6_nu c)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC DIFFEOMORPHISM_ON_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `diffeomorphism_on (ball(vec 0,R)) (IMAGE (c2:real^3->real^3) (ball(vec 0,R)))
                                    c2 c2'` ASSUME_TAC THENL
     [MATCH_MP_TAC SCH2_DIFFEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,&2)`;
                            `IMAGE (c2:real^3->real^3) (ball(vec 0,&2))`] THEN
      REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [UNDISCH_TAC `sch_ball (c2:real^3->real^3) c2'` THEN REWRITE_TAC[sch_ball];
        MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`sch6_mhi c R`; `ball(vec 0:real^3,R)`;
                   `IMAGE (c2:real^3->real^3) (ball(vec 0,R))`;
                   `sch6_nu c'`; `sch6_nu c`; `c2:real^3->real^3`; `c2':real^3->real^3`]
      DIFFEOMORPHISM_ON_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE ((c2:real^3->real^3) o sch6_nu c') (sch6_mhi c R) =
                  IMAGE c2 (ball(vec 0,R))` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `diffeomorphism_on (sch6_mhi c R) (ball(vec 0,R)) (sch6_nu c') (sch6_nu c)` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z w. z IN ball(vec 0,&2) /\ w IN ball(vec 0,&2) /\
                      (c2:real^3->real^3) z = c2 w ==> z = w` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_ball (c2:real^3->real^3) c2'` THEN
    REWRITE_TAC[sch_ball; diffeomorphism_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN sch6_mhi c R ==> sch6_nu c' y IN ball(vec 0,&2)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `sch6_nu c' y IN ball(vec 0:real^3,R)` MP_TAC THENL
     [ASM_SIMP_TAC[]; REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN REWRITE_TAC[IN_UNION] THEN
  ASM_CASES_TAC `(x:real^3) IN sch6_mhi c R` THEN ASM_CASES_TAC `(y:real^3) IN sch6_mhi c R` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[sch6_xi] THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `sch6_nu c' (x:real^3) = sch6_nu c' y` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `c2:real^3->real^3`)) (concl th) &&
        can (find_term ((=) `ball(vec 0:real^3,&2)`)) (concl th) &&
        not (can (find_term ((=) `sch6_mhi c R`)) (concl th)))) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `sch6_nu c`) THEN ASM_SIMP_TAC[]];
    STRIP_TAC THEN
    USE_THEN "CR" (MP_TAC o SPECL [`y:real^3`; `sch6_nu c' (x:real^3)`]) THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    STRIP_TAC THEN
    USE_THEN "CR" (MP_TAC o SPECL [`x:real^3`; `sch6_nu c' (y:real^3)`]) THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    STRIP_TAC THEN
    UNDISCH_TAC `!y z. y IN N /\ z IN N /\ (Theta:real^3->real^3) y = Theta z ==> y = z` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC SCH6_BOX_FACTS THEN UNDISCH_TAC `sch_slab_nbhd SUBSET (N:real^3->bool)` THEN
    UNDISCH_TAC `sch6_mlo c SUBSET sch6_box` THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* In the model chart Xi, S is the level sch6_u = 0 and S1 the              *)
(* level sch6_u1 = 0, and outside the image of Xi the surfaces S and S1      *)
(* coincide (both are the part of E1 outside).                               *)
(* ------------------------------------------------------------------------- *)

let SCH6_XI_S = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0 c c' R.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0 /\
        sch6_capchart c c' e0 /\ sch6_radius S1 Theta c2 R
        ==> !y. y IN sch6_mlo c UNION sch6_mhi c R
                ==> (sch6_xi Theta c2 c c' R y IN S <=> sch6_u y = &0) /\
                    (sch6_xi Theta c2 c c' R y IN S1 <=> sch6_u1 y = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH6_XI_DIFFEO) THEN
  FIRST_ASSUM(LABEL_TAC "S1C" o MATCH_MP SCH6_SD_S1_CHART o MATCH_MP SCH6_PD_SLAB o CONJUNCT1) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH6_PD_SIDES o CONJUNCT1) THEN
  FIRST_ASSUM(LABEL_TAC "NS" o MATCH_MP SCH6_PD_NORTH_SPHERE o CONJUNCT1) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN SCH6_PD_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH6_NU_FACTS) THEN
  UNDISCH_TAC `sch6_radius S1 (Theta:real^3->real^3) c2 R` THEN REWRITE_TAC[sch6_radius] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RAD"))) THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(y:real^3) IN N /\ y$3 <= &9 / &8` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN sch6_mlo c` THEN REWRITE_TAC[sch6_mlo; IN_DIFF] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [MP_TAC SCH6_BOX_FACTS THEN UNDISCH_TAC `sch_slab_nbhd SUBSET (N:real^3->bool)` THEN
        UNDISCH_TAC `(y:real^3) IN sch6_box` THEN SET_TAC[];
        UNDISCH_TAC `(y:real^3) IN sch6_box` THEN REWRITE_TAC[sch6_box; IN_ELIM_THM] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SCH6_U_LOW] THEN USE_THEN "S1C" (fun th -> ASM_SIMP_TAC[th]);
    ALL_TAC] THEN
  UNDISCH_TAC `(y:real^3) IN sch6_mhi c R` THEN REWRITE_TAC[sch6_mhi; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `norm(z:real^3) < R` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN ball(vec 0,R)` THEN REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
  ASM_CASES_TAC `norm(z:real^3) < &1` THENL
   [SUBGOAL_THEN `(c2:real^3->real^3) z IN inside S2` ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `inside S2:real^3->bool`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((c2:real^3->real^3) z IN S) /\ ~(c2 z IN S1)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `S INTER inside S2 = {}:real^3->bool` THEN
        UNDISCH_TAC `(c2:real^3->real^3) z IN inside S2` THEN SET_TAC[];
        UNDISCH_TAC `S1 INTER (S2 UNION inside S2) = {}:real^3->bool` THEN
        UNDISCH_TAC `(c2:real^3->real^3) z IN inside S2` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `sch6_nu c z IN IMAGE (sch6_nu c) (ball(vec 0,&1))` MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `sch6_nu c z` SCH6_QQ_U) THEN MP_TAC(SPEC `sch6_nu c z` SCH6_QQ_U1) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^3)$3 < norm z / &4` THENL
   [SUBGOAL_THEN `(z:real^3) IN sch6_fcone /\ z IN annulus (&3 / &4) (&2)` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[sch6_fcone; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(z:real^3) IN sch6_fcone`) o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `sch6_fcone`)) (concl th) &&
                       can (find_term ((=) `g2:real^3->real^3`)) (concl th))) THEN
    SUBGOAL_THEN `sch6_nu c z = sch_flip3(sch_cap_collar e0 (sch_flip3 z))` SUBST1_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sch6_fcone`)) (concl th) &&
        can (find_term ((=) `sch6_nu c`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(c2:real^3->real^3) z = Theta(sch_flip3(sch_cap_collar e0 (sch_flip3 z)))`
    SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`e0:real`; `z:real^3`] SCH6_F_LAYER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[SCH6_U_LOW; REAL_LT_IMP_LE];
      USE_THEN "S1C" (fun th -> ASM_SIMP_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN sch_capcone /\ norm z / &4 <= z$3` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[sch_capcone; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e0:real`; `z:real^3`] SCH6_NORTH_MODEL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sch6_nu c z = sch_cap_collar e0 z + &2 % basis 3` SUBST1_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sch_capcone`)) (concl th) &&
      can (find_term ((=) `sch6_nu c`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(sch6_u1(sch_cap_collar e0 z + &2 % basis 3) = &0)` (fun th -> REWRITE_TAC[th])
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `norm(z:real^3) = &1` THENL
   [USE_THEN "NS" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S:real^3->bool` `sch_lat`)) THEN
    ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  USE_THEN "RAD" (MP_TAC o SPEC `z:real^3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(e0 * (norm(z:real^3) - &1) = &0)` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c2:real^3->real^3) z IN outside S2` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `outside S2:real^3->bool`)) (concl th))) THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((c2:real^3->real^3) z IN S2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(c2:real^3->real^3) z IN outside S2` THEN
    MP_TAC(ISPEC `S2:real^3->bool` OUTSIDE_NO_OVERLAP) THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S:real^3->bool` `sch_lat`)) THEN
  REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `~((c2:real^3->real^3) z IN S1)` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S1:real^3->bool` `sch_cap1`)) THEN
    SET_TAC[];
    UNDISCH_TAC `~((c2:real^3->real^3) z IN IMAGE Theta sch6_cbox)` THEN
    MP_TAC SCH6_BOX_FACTS THEN SET_TAC[];
    UNDISCH_TAC `~((c2:real^3->real^3) z IN S2)` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S2:real^3->bool` `sch_cap2`)) THEN
    SET_TAC[]]);;

(* Outside the image of the model chart, S and S1 coincide. *)

let SCH6_XI_REST = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0 c c' R.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0 /\
        sch6_capchart c c' e0 /\ sch6_radius S1 Theta c2 R
        ==> S DIFF IMAGE (sch6_xi Theta c2 c c' R) (sch6_mlo c UNION sch6_mhi c R) =
            S1 DIFF IMAGE (sch6_xi Theta c2 c c' R) (sch6_mlo c UNION sch6_mhi c R)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH6_XI_DIFFEO) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN SCH6_PD_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH6_NU_FACTS) THEN
  UNDISCH_TAC `sch6_radius S1 (Theta:real^3->real^3) c2 R` THEN
  REWRITE_TAC[sch6_radius] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(E2:real^3->bool) SUBSET IMAGE (sch6_xi Theta c2 c c' R) (sch6_mlo c UNION sch6_mhi c R)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(E2:real^3->bool) SUBSET IMAGE (c2:real^3->real^3) (sphere(vec 0,&1))` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S2:real^3->bool` `sch_cap2`)) THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_UNION] THEN MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC `p:real^3` THEN MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `sch6_nu c z` THEN
    SUBGOAL_THEN `(z:real^3) IN ball(vec 0,R)` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN DISJ2_TAC THEN REWRITE_TAC[sch6_mhi] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_lat SUBSET sch6_mlo c /\ sch_cap1 SUBSET sch6_mlo c` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[sch6_mlo] THEN
    SUBGOAL_THEN `!y:real^3. y IN IMAGE (sch6_nu c) (cball(vec 0,&7 / &8))
                             ==> y$1 pow 2 + y$2 pow 2 < &1 /\ &1 / &2 <= y$3`
    ASSUME_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN IMAGE (sch6_nu c) (ball(vec 0,&1))` MP_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN IMAGE (sch6_nu c) (cball(vec 0,&7 / &8))` THEN
        MATCH_MP_TAC(SET_RULE `!s t (f:real^3->real^3) y.
                                s SUBSET t ==> y IN IMAGE f s ==> y IN IMAGE f t`) THEN
        REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      MP_TAC(SPEC `y:real^3` SCH6_QQ_LE1) THEN MP_TAC(SPEC `y:real^3` SCH6_QQ_HEIGHT) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC SCH6_BOX_FACTS THEN STRIP_TAC THEN CONJ_TAC THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&7 / &8`)) (concl th)))) THEN
    (UNDISCH_TAC `(y:real^3) IN sch_lat` ORELSE UNDISCH_TAC `(y:real^3) IN sch_cap1`) THEN
    REWRITE_TAC[sch_lat; sch_cap1; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (Theta:real^3->real^3) sch_lat SUBSET
      IMAGE (sch6_xi Theta c2 c c' R) (sch6_mlo c UNION sch6_mhi c R) /\
    IMAGE (Theta:real^3->real^3) sch_cap1 SUBSET
      IMAGE (sch6_xi Theta c2 c c' R) (sch6_mlo c UNION sch6_mhi c R)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN REWRITE_TAC[IN_IMAGE; IN_UNION] THEN EXISTS_TAC `y:real^3` THEN
    (SUBGOAL_THEN `(y:real^3) IN sch6_mlo c` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S:real^3->bool` `sch_lat`)) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S1:real^3->bool` `sch_cap1`)) THEN
  UNDISCH_TAC `(E2:real^3->bool) SUBSET
               IMAGE (sch6_xi Theta c2 c c' R) (sch6_mlo c UNION sch6_mhi c R)` THEN
  UNDISCH_TAC `IMAGE (Theta:real^3->real^3) sch_lat SUBSET
               IMAGE (sch6_xi Theta c2 c c' R) (sch6_mlo c UNION sch6_mhi c R)` THEN
  UNDISCH_TAC `IMAGE (Theta:real^3->real^3) sch_cap1 SUBSET
               IMAGE (sch6_xi Theta c2 c c' R) (sch6_mlo c UNION sch6_mhi c R)` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The vertical field of the push.  w_d = -2 on the vertical                 *)
(* segments of length 2 below the model surface sch6_u <= 0 above height     *)
(* 9/8, and w_d = 0 off the compact set sch6_supp d; for small d this set   *)
(* lies in the domain of the model chart (a sublevel argument).             *)
(* ------------------------------------------------------------------------- *)

let sch6_w = new_definition
 `sch6_w (d:real) (y:real^3) =
    --(&2) * smooth_step(&8 * y$3 + &39 / &4) * (&1 - smooth_step(sch6_u y / d - &1))`;;

let sch6_supp = new_definition
 `sch6_supp (d:real) = {y:real^3 | --(&39 / &32) <= y$3 /\ sch6_u y <= &2 * d}`;;

let SCH6_W_SMOOTH = prove
 (`!d. smooth_map_on (:real^3) (\y. lift(sch6_w d y))`,
  GEN_TAC THEN REWRITE_TAC[sch6_w] THEN
  MP_TAC SCH6_SMOOTH_BASICS THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b. smooth_map_on (:real^3) (\y:real^3. lift(smooth_step(a * y$3 + b)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. lift(a * y$3 + b)`]
      SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
    REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\y. lift(smooth_step(sch6_u y / d - &1)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. lift(sch6_u y / d - &1)`]
      SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
    REWRITE_TAC[OPEN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[real_div; LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
  REWRITE_TAC[OPEN_UNIV] THEN
  MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. lift(smooth_step(&8 * y$3 + &39 / &4))`;
                 `\y:real^3. lift(&1 - smooth_step(sch6_u y / d - &1))`]
    SMOOTH_MAP_ON_LIFT_MUL) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST]);;

let SCH6_W_SUPPORT = prove
 (`!d y. &0 < d /\ ~(y IN sch6_supp d) ==> sch6_w d y = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch6_supp; IN_ELIM_THM; DE_MORGAN_THM; REAL_NOT_LE] THEN
  STRIP_TAC THEN REWRITE_TAC[sch6_w] THENL
   [SUBGOAL_THEN `smooth_step(&8 * (y:real^3)$3 + &39 / &4) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    SUBGOAL_THEN `smooth_step(sch6_u y / d - &1) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_1 THEN
      SUBGOAL_THEN `&2 <= sch6_u y / d` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      REAL_ARITH_TAC]]);;

let SCH6_SUPP_COMPACT = prove
 (`!d. &0 < d /\ d <= &1 / &4 ==> compact(sch6_supp d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [REWRITE_TAC[BOUNDED_POS] THEN EXISTS_TAC `&3` THEN REWRITE_TAC[REAL_ARITH `&0 < &3`] THEN
    REWRITE_TAC[sch6_supp; IN_ELIM_THM; NORM_LE_SQUARE; DOT_3] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBGOAL_THEN `(y:real^3)$1 pow 2 + y$2 pow 2 <= &3 / &2 /\ y$3 <= &2` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `sch6_u y <= &2 * d` THEN REWRITE_TAC[sch6_u] THEN
      MP_TAC(SPEC `&2 - (y:real^3)$3` SCH6_PROFILE_LE1) THEN
      MP_TAC(SPEC `(y:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
      ASM_CASES_TAC `&3 / &2 < (y:real^3)$3` THENL
       [MP_TAC(SPEC `&2 - (y:real^3)$3` SCH_CAP_PROFILE_TIP) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&2 - (y:real^3)$3) * (&2 + y$3)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 <= &3 / &2` THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `sch6_supp d = {y:real^3 | --(&39 / &32) <= y$3} INTER {y | sch6_u y <= &2 * d}`
    SUBST1_TAC THENL
     [REWRITE_TAC[sch6_supp; EXTENSION; IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_INTER THEN MP_TAC SCH6_SMOOTH_BASICS THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCH6_LEVEL_SETS (SPEC `3` (CONJUNCT1 th))) THEN
      MP_TAC(MATCH_MP SCH6_LEVEL_SETS (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))))) THEN
    SIMP_TAC[]]);;

(* On the model surface (sch6_u <= 0) above the slab, w_d = -2. *)

let SCH6_W_VALUE = prove
 (`!d p:real^3. &0 < d /\ --(&7 / &8) <= p$3 /\ sch6_u p <= &0 ==> sch6_w d p = --(&2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch6_w] THEN
  SUBGOAL_THEN `smooth_step(&8 * (p:real^3)$3 + &39 / &4) = &1 /\
                smooth_step(sch6_u p / d - &1) = &0` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_STEP_0 THEN
      SUBGOAL_THEN `sch6_u p / d <= &0` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    REAL_ARITH_TAC]);;

let SCH6_W_SEG = prove
 (`!d y:real^3. &0 < d /\ sch6_u y <= &0 /\ &9 / &8 <= y$3
        ==> !s. &0 <= s /\ s <= &1 ==> sch6_w d (y + s % (--(&2) % basis 3)) = --(&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC SCH6_W_VALUE THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y + s % (--(&2) % basis 3):real^3)$1 = y$1 /\
                (y + s % (--(&2) % basis 3):real^3)$2 = y$2 /\
                (y + s % (--(&2) % basis 3):real^3)$3 = y$3 - &2 * s`
  (fun th -> REWRITE_TAC[th; sch6_u]) THENL
   [REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sch_cap_profile(&2 - (y:real^3)$3) <= sch_cap_profile(&2 - (y$3 - &2 * s))`
  MP_TAC THENL
   [ASM_CASES_TAC `&2 - ((y:real^3)$3 - &2 * s) <= &3 / &2` THENL
     [MATCH_MP_TAC SCH6_PROFILE_MONO THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `sch_cap_profile(&2 - ((y:real^3)$3 - &2 * s)) = &1` SUBST1_TAC THENL
       [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[SCH6_PROFILE_LE1]]];
    ALL_TAC] THEN
  UNDISCH_TAC `sch6_u y <= &0` THEN REWRITE_TAC[sch6_u] THEN REAL_ARITH_TAC);;

(* Sublevel sets of a smooth function near a sublevel set inside an open set. *)

let SCH6_SUBLEVEL_NBHD = prove
 (`!(u:real^3->real) A M c.
        smooth_map_on (:real^3) (\y. lift(u y)) /\ closed A /\ open M /\ &0 < c /\
        bounded {y | y IN A /\ u y <= c} /\
        (!y. y IN A /\ u y <= &0 ==> y IN M)
        ==> ?d. &0 < d /\ d <= c /\ !y. y IN A /\ u y <= d ==> y IN M`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `C = {y:real^3 | y IN A /\ u y <= c /\ ~(y IN M)}` THEN
  SUBGOAL_THEN `compact(C:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `{y:real^3 | y IN A /\ u y <= c}` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN SET_TAC[];
      SUBGOAL_THEN `C = A INTER {y:real^3 | u y <= c} INTER ((:real^3) DIFF M)` SUBST1_TAC THENL
       [EXPAND_TAC "C" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC CLOSED_INTER THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_INTER THEN
      ASM_SIMP_TAC[GSYM OPEN_CLOSED] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP SCH6_LEVEL_SETS) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `C:real^3->bool = {}` THENL
   [EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `C:real^3->bool = {}` THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^3->real`; `C:real^3->bool`] CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV; o_DEF] THEN
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < (u:real^3->real) y0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `(y0:real^3) IN C` THEN EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min c ((u:real^3->real) y0 / &2)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(y:real^3) IN M` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:real^3) IN C` (fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* For small d the support of w_d lies in the domain of the model chart. *)

let SCH6_SUPP_IN_M = prove
 (`!c c' e0 R.
        sch6_capchart c c' e0 /\ &1 < R /\ R <= &2
        ==> ?d. &0 < d /\ d <= &1 / &8 /\
                sch6_supp d SUBSET sch6_mlo c UNION sch6_mhi c R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH6_NU_FACTS) THEN
  MP_TAC(SPECL [`c:real^3->real^3`; `c':real^3->real^3`; `e0:real`; `R:real`]
    SCH6_NU_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `open(sch6_mlo c UNION sch6_mhi c R)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_UNION THEN ASM_REWRITE_TAC[sch6_mlo] THEN MATCH_MP_TAC OPEN_DIFF THEN
    ASM_SIMP_TAC[SCH6_BOX_FACTS; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sch6_u`; `{y:real^3 | --(&39 / &32) <= y$3}`;
                 `sch6_mlo c UNION sch6_mhi c R`; `&1 / &4`] SCH6_SUBLEVEL_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SCH6_SMOOTH_BASICS] THEN REPEAT CONJ_TAC THENL
     [MP_TAC SCH6_SMOOTH_BASICS THEN
      DISCH_THEN(MP_TAC o MATCH_MP SCH6_LEVEL_SETS o SPEC `3` o CONJUNCT1) THEN SIMP_TAC[];
      REAL_ARITH_TAC;
      MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      SUBGOAL_THEN `{y:real^3 | y IN {y | --(&39 / &32) <= y$3} /\ sch6_u y <= &1 / &4} =
                    sch6_supp(&1 / &8)` SUBST1_TAC THENL
       [REWRITE_TAC[sch6_supp; EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC SCH6_SUPP_COMPACT THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3)$1 pow 2 + y$2 pow 2 <= sch_cap_profile(&2 - y$3)` ASSUME_TAC THENL
     [UNDISCH_TAC `sch6_u y <= &0` THEN REWRITE_TAC[sch6_u] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `(y:real^3)$3 < &17 / &16` THENL
     [ASM_CASES_TAC `(y:real^3) IN IMAGE (sch6_nu c) (cball(vec 0,&7 / &8))` THENL
       [DISJ2_TAC THEN
        UNDISCH_TAC `IMAGE (sch6_nu c) (cball(vec 0,&1)) SUBSET sch6_mhi c R` THEN
        UNDISCH_TAC `(y:real^3) IN IMAGE (sch6_nu c) (cball(vec 0,&7 / &8))` THEN
        MATCH_MP_TAC(SET_RULE `!(f:real^3->real^3) s t u y.
                                 s SUBSET t ==> y IN IMAGE f s ==> IMAGE f t SUBSET u
                                 ==> y IN u`) THEN
        REWRITE_TAC[SUBSET; IN_CBALL_0] THEN REAL_ARITH_TAC;
        DISJ1_TAC THEN ASM_REWRITE_TAC[sch6_mlo; IN_DIFF; sch6_box; IN_ELIM_THM] THEN
        MP_TAC(SPEC `&2 - (y:real^3)$3` SCH6_PROFILE_LE1) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISJ2_TAC THEN
    UNDISCH_TAC `IMAGE (sch6_nu c) (cball(vec 0,&1)) SUBSET sch6_mhi c R` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(y:real^3)$3 < &3 / &2` THENL
     [MP_TAC(SPEC `y:real^3` SCH6_QQ_TOP) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3)$3 = &3 / &2 /\ y$1 pow 2 + y$2 pow 2 = &0` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `&2 - (y:real^3)$3` SCH_CAP_PROFILE_TIP) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> UNDISCH_TAC
        `(y:real^3)$1 pow 2 + y$2 pow 2 <= sch_cap_profile(&2 - y$3)` THEN REWRITE_TAC[th]) THEN
      MP_TAC(SPEC `(y:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[sch6_qq] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d0 / &2` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; sch6_supp; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The time-one flow phi of w_d e3 carries the model surface                *)
(* sch6_u = 0 onto sch6_u1 = 0 (the top dome moves down by 2, the cylinder   *)
(* below 9/8 onto the cylinder below -7/8), and the push                     *)
(* Phi = Xi o phi o Xi^-1 (identity off the chart image) is a                 *)
(* diffeomorphism of R^3 carrying S onto S1 (SCH6_PUSH).                     *)
(* ------------------------------------------------------------------------- *)

let SCH6_VEC3 = prove
 (`!y:real^3. y = vector[y$1; y$2; y$3]`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3]);;

let SCH6_SHIFT3 = prove
 (`!(y:real^3) a. (y + a % basis 3)$1 = y$1 /\ (y + a % basis 3)$2 = y$2 /\
                  (y + a % basis 3)$3 = y$3 + a`,
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

(* The flow of w_d e3. *)

let SCH6_FLOW_FACTS = prove
 (`!d. &0 < d /\ d <= &1 / &4
       ==> diffeomorphism_on (:real^3) (:real^3) (sch6_vflow (sch6_w d) (&1))
                             (sch6_vflow (sch6_w d) (--(&1))) /\
           (!y. ~(y IN sch6_supp d)
                ==> sch6_vflow (sch6_w d) (&1) y = y /\
                    sch6_vflow (sch6_w d) (--(&1)) y = y) /\
           (!y. y IN sch6_supp d
                ==> sch6_vflow (sch6_w d) (&1) y IN sch6_supp d /\
                    sch6_vflow (sch6_w d) (--(&1)) y IN sch6_supp d) /\
           (!t y. (sch6_vflow (sch6_w d) t y)$1 = y$1 /\
                  (sch6_vflow (sch6_w d) t y)$2 = y$2) /\
           (!a b s t. s < t
                      ==> (sch6_vflow (sch6_w d) (&1) (vector[a; b; s]))$3 <
                          (sch6_vflow (sch6_w d) (&1) (vector[a; b; t]))$3) /\
           (!y. sch6_u y <= &0 /\ &9 / &8 <= y$3
                ==> sch6_vflow (sch6_w d) (&1) y = y + --(&2) % basis 3)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\y. lift(sch6_w d y)) /\ compact(sch6_supp d) /\
                (!y. ~(y IN sch6_supp d) ==> sch6_w d y = &0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCH6_W_SMOOTH; SCH6_SUPP_COMPACT; SCH6_W_SUPPORT]; ALL_TAC] THEN
  MP_TAC(SPECL [`sch6_w d`; `sch6_supp d`] SCH6_VFLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN MATCH_MP_TAC SCH6_VFLOW_HORIZ THEN
    EXISTS_TAC `sch6_supp d` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH6_VFLOW_MONO THEN
    EXISTS_TAC `sch6_supp d` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH6_VFLOW_TRANSLATE THEN
    EXISTS_TAC `sch6_supp d` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SCH6_W_SEG THEN ASM_REWRITE_TAC[]]);;

(* The flow carries the model surface of S onto that of S1. *)

let SCH6_FLOW_MODEL = prove
 (`!d M. &0 < d /\ d <= &1 / &4 /\ sch6_supp d SUBSET M
         ==> IMAGE (sch6_vflow (sch6_w d) (&1)) {y | y IN M /\ sch6_u y = &0} =
             {y | y IN M /\ sch6_u1 y = &0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:real` SCH6_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `phi = sch6_vflow (sch6_w d) (&1)` THEN
  ABBREV_TAC `phi' = sch6_vflow (sch6_w d) (--(&1))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ID")
    (CONJUNCTS_THEN2 (LABEL_TAC "K") (CONJUNCTS_THEN2 (LABEL_TAC "H")
      (CONJUNCTS_THEN2 (LABEL_TAC "MONO") (LABEL_TAC "TR")))))) THEN
  SUBGOAL_THEN `(!y. y IN M ==> (phi:real^3->real^3) y IN M) /\
                (!y. y IN M ==> (phi':real^3->real^3) y IN M) /\
                (!y. phi'(phi y) = y) /\ (!y. phi(phi' y) = y)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_CASES_TAC `(y:real^3) IN sch6_supp d` THENL
       [USE_THEN "K" (MP_TAC o SPEC `y:real^3`) THEN ASM SET_TAC[];
        USE_THEN "ID" (MP_TAC o SPEC `y:real^3`) THEN ASM_SIMP_TAC[]];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_CASES_TAC `(y:real^3) IN sch6_supp d` THENL
       [USE_THEN "K" (MP_TAC o SPEC `y:real^3`) THEN ASM SET_TAC[];
        USE_THEN "ID" (MP_TAC o SPEC `y:real^3`) THEN ASM_SIMP_TAC[]];
      UNDISCH_TAC `diffeomorphism_on (:real^3) (:real^3) (phi:real^3->real^3) phi'` THEN
      SIMP_TAC[diffeomorphism_on; IN_UNIV];
      UNDISCH_TAC `diffeomorphism_on (:real^3) (:real^3) (phi:real^3->real^3) phi'` THEN
      SIMP_TAC[diffeomorphism_on; IN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. a pow 2 + b pow 2 <= &1
                      ==> ((phi:real^3->real^3) (vector[a; b; &9 / &8]))$3 = --(&7 / &8)`
  (LABEL_TAC "TOP") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "TR" (MP_TAC o SPEC `vector[a; b; &9 / &8]:real^3`) THEN ANTS_TAC THENL
     [REWRITE_TAC[sch6_u; VECTOR_3] THEN
      SUBGOAL_THEN `sch_cap_profile(&2 - &9 / &8) = &1` SUBST1_TAC THENL
       [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SCH6_SHIFT3; VECTOR_3] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y:real^3 t. y$3 < t
                              ==> ((phi:real^3->real^3) y)$3 < (phi(vector[y$1; y$2; t]))$3) /\
                (!y:real^3 t. t < y$3
                              ==> ((phi:real^3->real^3) (vector[y$1; y$2; t]))$3 < (phi y)$3)`
  (CONJUNCTS_THEN2 (LABEL_TAC "MONO1") (LABEL_TAC "MONO2")) THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(phi:real^3->real^3) y = phi(vector[y$1; y$2; y$3])` SUBST1_TAC THEN
    (TRY(AP_TERM_TAC THEN ACCEPT_TAC(SPEC `y:real^3` SCH6_VEC3))) THEN
    REWRITE_TAC[VECTOR_3] THEN USE_THEN "MONO" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `q:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(y:real^3)$1 pow 2 + y$2 pow 2 = sch_cap_profile(&2 - y$3)` ASSUME_TAC THENL
     [UNDISCH_TAC `sch6_u y = &0` THEN REWRITE_TAC[sch6_u] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `&2 - (y:real^3)$3` SCH6_PROFILE_LE1) THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 < &1` THENL
     [SUBGOAL_THEN `&9 / &8 <= (y:real^3)$3` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        SUBGOAL_THEN `sch_cap_profile(&2 - (y:real^3)$3) = &1` MP_TAC THENL
         [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      USE_THEN "TR" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[sch6_u1; SCH6_SHIFT3] THEN
      REWRITE_TAC[REAL_ARITH `--(y + --(&2)) = &2 - y`] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3)$1 pow 2 + y$2 pow 2 = &1 /\ y$3 <= &9 / &8` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(SPEC `&2 - (y:real^3)$3` SCH6_PROFILE_LT1) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `((phi:real^3->real^3) y)$3 <= --(&7 / &8)` ASSUME_TAC THENL
     [USE_THEN "TOP" (MP_TAC o SPECL [`(y:real^3)$1`; `(y:real^3)$2`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      ASM_CASES_TAC `(y:real^3)$3 = &9 / &8` THENL
       [SUBGOAL_THEN `vector[(y:real^3)$1; y$2; &9 / &8] = y`
          (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM SCH6_VEC3];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "MONO1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[sch6_u1] THEN
    SUBGOAL_THEN `sch_cap_profile(--(((phi:real^3->real^3) y)$3)) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `((phi:real^3->real^3) y)$1 = y$1 /\ (phi y)$2 = y$2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "phi" THEN USE_THEN "H" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `(phi':real^3->real^3) q` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(q:real^3)$1 pow 2 + q$2 pow 2 = sch_cap_profile(--(q$3))` ASSUME_TAC THENL
     [UNDISCH_TAC `sch6_u1 q = &0` THEN REWRITE_TAC[sch6_u1] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `--((q:real^3)$3)` SCH6_PROFILE_LE1) THEN DISCH_TAC THEN
    SUBGOAL_THEN `((phi':real^3->real^3) q)$1 = (q:real^3)$1 /\ (phi' q)$2 = q$2`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "phi'" THEN USE_THEN "H" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    ASM_CASES_TAC `(q:real^3)$1 pow 2 + q$2 pow 2 < &1` THENL
     [SUBGOAL_THEN `--(&7 / &8) < (q:real^3)$3 /\ q$3 <= --(&1 / &2)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[GSYM REAL_NOT_LE]; REWRITE_TAC[GSYM REAL_NOT_LT]] THEN DISCH_TAC THENL
         [SUBGOAL_THEN `sch_cap_profile(--((q:real^3)$3)) = &1` MP_TAC THENL
           [MATCH_MP_TAC SCH_CAP_PROFILE_TOP THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
          MP_TAC(SPEC `--((q:real^3)$3)` SCH_CAP_PROFILE_TIP) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MP_TAC(SPEC `(q:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(q:real^3)$2` REAL_LE_POW_2) THEN
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `(phi':real^3->real^3) q = q + &2 % basis 3` SUBST1_TAC THENL
       [SUBGOAL_THEN `(phi:real^3->real^3) (q + &2 % basis 3) = q` MP_TAC THENL
         [USE_THEN "TR" (MP_TAC o SPEC `q + &2 % basis 3:real^3`) THEN ANTS_TAC THENL
           [REWRITE_TAC[sch6_u; SCH6_SHIFT3] THEN
            REWRITE_TAC[REAL_ARITH `&2 - (y + &2) = --y`] THEN ASM_REAL_ARITH_TAC;
            DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC];
          DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[sch6_u; SCH6_SHIFT3] THEN
      REWRITE_TAC[REAL_ARITH `&2 - (y + &2) = --y`] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^3)$1 pow 2 + q$2 pow 2 = &1 /\ q$3 <= --(&7 / &8)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(SPEC `--((q:real^3)$3)` SCH6_PROFILE_LT1) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `((phi':real^3->real^3) q)$3 <= &9 / &8` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      USE_THEN "MONO2" (MP_TAC o C MATCH_MP
        (ASSUME `&9 / &8 < ((phi':real^3->real^3) q)$3`) o
        SPECL [`(phi':real^3->real^3) q`; `&9 / &8`]) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "TOP" (MP_TAC o SPECL [`(q:real^3)$1`; `(q:real^3)$2`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `(phi':real^3->real^3) q` SCH6_U_LOW) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* The image of S under a conjugated map. *)

let SCH6_CONJ_IMAGE = prove
 (`!(Xi:real^3->real^3) Xi' (Phi:real^3->real^3) M X (D:real^3->real^3) Sm S1m S S1.
        X = IMAGE Xi M /\ (!y. y IN M ==> Xi' (Xi y) = y) /\
        (!p. p IN X ==> Phi p = Xi(D(Xi' p))) /\ (!p. ~(p IN X) ==> Phi p = p) /\
        (!y. y IN M ==> (Xi y IN S <=> y IN Sm)) /\
        (!y. y IN M ==> (Xi y IN S1 <=> y IN S1m)) /\
        IMAGE D (M INTER Sm) = M INTER S1m /\ S DIFF X = S1 DIFF X
        ==> IMAGE Phi S = S1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!(f:real^3->real^3) S S1 X.
     IMAGE f (S INTER X) = S1 INTER X /\ IMAGE f (S DIFF X) = S1 DIFF X ==> IMAGE f S = S1`) THEN
  EXISTS_TAC `X:real^3->bool` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `S INTER X = IMAGE (Xi:real^3->real^3) (M INTER Sm) /\
                  S1 INTER X = IMAGE Xi (M INTER S1m)` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `D:real^3->real^3`)) (lhs(concl th)))) THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^3->real^3) g s.
                             (!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
    REWRITE_TAC[o_THM; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Xi:real^3->real^3) y IN X` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `IMAGE (Phi:real^3->real^3) (S DIFF X) = S DIFF X` SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!(f:real^3->real^3) s. (!x. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
      ASM_SIMP_TAC[IN_DIFF];
      ASM_REWRITE_TAC[]]]);;

(* THE PUSH: a ball chart of S2 following its collar (case (a)) and the     *)
(* capsule chart give a diffeomorphism of R^3 carrying S onto S1.           *)

let SCH6_PUSH = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0 c c'.
        sch6_push_data S S1 S2 Theta Theta' N E1 E2 g2 g2' c2 c2' e0 /\
        sch6_capchart c c' e0
        ==> ?Phi Phi'. diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\ IMAGE Phi S = S1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `R:real` o MATCH_MP SCH6_PD_RADIUS) THEN
  SUBGOAL_THEN `&1 < R /\ R <= &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sch6_radius S1 (Theta:real^3->real^3) c2 R` THEN
    REWRITE_TAC[sch6_radius] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sch6_push_data S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0 /\
                sch6_capchart c c' e0 /\ sch6_radius S1 Theta c2 R` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH6_XI_DIFFEO) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH6_XI_S) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH6_XI_REST) THEN
  MP_TAC(SPECL [`c:real^3->real^3`; `c':real^3->real^3`; `e0:real`; `R:real`]
    SCH6_SUPP_IN_M) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(SPECL [`d:real`; `sch6_mlo c UNION sch6_mhi c R`] SCH6_FLOW_MODEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `d:real` SCH6_FLOW_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `M = sch6_mlo c UNION sch6_mhi c R` THEN
  ABBREV_TAC `Xi = sch6_xi Theta c2 c c' R` THEN
  ABBREV_TAC `phi = sch6_vflow (sch6_w d) (&1)` THEN
  ABBREV_TAC `phi' = sch6_vflow (sch6_w d) (--(&1))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ID")
    (CONJUNCTS_THEN2 (LABEL_TAC "K") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `IMAGE (phi:real^3->real^3) M = M` ASSUME_TAC THENL
   [SUBGOAL_THEN `(!y. y IN M ==> (phi:real^3->real^3) y IN M) /\
                  (!y. y IN M ==> (phi':real^3->real^3) y IN M) /\
                  (!y. phi(phi' y) = y)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_CASES_TAC `(y:real^3) IN sch6_supp d` THENL
         [USE_THEN "K" (MP_TAC o SPEC `y:real^3`) THEN ASM SET_TAC[];
          USE_THEN "ID" (MP_TAC o SPEC `y:real^3`) THEN ASM_SIMP_TAC[]];
        X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_CASES_TAC `(y:real^3) IN sch6_supp d` THENL
         [USE_THEN "K" (MP_TAC o SPEC `y:real^3`) THEN ASM SET_TAC[];
          USE_THEN "ID" (MP_TAC o SPEC `y:real^3`) THEN ASM_SIMP_TAC[]];
        UNDISCH_TAC `diffeomorphism_on (:real^3) (:real^3) (phi:real^3->real^3) phi'` THEN
        SIMP_TAC[diffeomorphism_on; IN_UNIV]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on M M (phi:real^3->real^3) phi'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`phi:real^3->real^3`; `phi':real^3->real^3`; `M:real^3->bool`]
      SCH_DIFFEO_RESTRICT_UNIV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Xi:real^3->real^3`; `Xi':real^3->real^3`; `M:real^3->bool`;
                 `phi:real^3->real^3`; `phi':real^3->real^3`; `sch6_supp d`]
    SCH6_CONJ_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SCH6_SUPP_COMPACT; REAL_ARITH `d <= &1 / &8 ==> d <= &1 / &4`] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN USE_THEN "ID" (MP_TAC o SPEC `y:real^3`) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  ABBREV_TAC `Phi = \p:real^3. if p IN IMAGE (Xi:real^3->real^3) M
                               then Xi((phi:real^3->real^3)((Xi':real^3->real^3) p)) else p` THEN
  ABBREV_TAC `Phi' = \p:real^3. if p IN IMAGE (Xi:real^3->real^3) M
                                then Xi((phi':real^3->real^3)((Xi':real^3->real^3) p)) else p` THEN
  MAP_EVERY EXISTS_TAC [`Phi:real^3->real^3`; `Phi':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SCH6_CONJ_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`Xi:real^3->real^3`; `Xi':real^3->real^3`; `M:real^3->bool`;
                        `IMAGE (Xi:real^3->real^3) M`; `phi:real^3->real^3`;
                        `{y:real^3 | sch6_u y = &0}`; `{y:real^3 | sch6_u1 y = &0}`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on M (IMAGE (Xi:real^3->real^3) M) Xi Xi'` THEN
    SIMP_TAC[diffeomorphism_on];
    EXPAND_TAC "Phi" THEN SIMP_TAC[];
    EXPAND_TAC "Phi" THEN SIMP_TAC[];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    SUBGOAL_THEN `!P. M INTER {y:real^3 | P y} = {y | y IN M /\ P y}`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM]; ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The gluing theorem.  SCH_COLLAR3 gives ball charts c2 of S2               *)
(* and c1 of S1 following their collars or the inverted collars.  If c2     *)
(* follows g2, the push gives Phi with Phi(S) = S1.  If c2 is inverted and  *)
(* c1 follows g1, the push for the reflected configuration gives            *)
(* Phi(flip S) = flip S2.  Both inverted is impossible: then S1 lies inside *)
(* S2 and S2 inside S1.                                                      *)
(* ------------------------------------------------------------------------- *)

let SCH6_SD_OF_CONFIG = prove
 (`!S S1 S2 (Theta:real^3->real^3).
        sch_slab_config S S1 S2 Theta /\
        S homeomorphic sphere(vec 0:real^3,&1) /\ S1 homeomorphic sphere(vec 0:real^3,&1) /\
        S2 homeomorphic sphere(vec 0:real^3,&1)
        ==> ?Theta' N E1 E2. sch6_slab_data S S1 S2 Theta Theta' N E1 E2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_slab_config] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `Theta':real^3->real^3`
    (X_CHOOSE_THEN `E1:real^3->bool` (X_CHOOSE_THEN `E2:real^3->bool`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))) STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`Theta':real^3->real^3`; `N:real^3->bool`; `E1:real^3->bool`;
                        `E2:real^3->bool`] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o
    check (fun th -> is_eq(concl th) && is_var(lhs(concl th))))) THEN
  ASM_REWRITE_TAC[sch6_slab_data]);;

(* An inverted ball chart of S2: then S1 lies inside S2. *)

let SCH6_INV_INSIDE = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0.
        sch6_slab_data S S1 S2 Theta Theta' N E1 E2 /\
        sch_neck g2 g2' /\ IMAGE g2 (sphere(vec 0,&1)) = S2 /\
        &0 < e0 /\ e0 <= &1 / &16 /\
        (!x. x IN sch_capcone ==> g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e0 x))) /\
        sch_ball c2 c2' /\ IMAGE c2 (cball(vec 0,&1)) = S2 UNION inside S2 /\
        (!x. x IN annulus (&3 / &4) (&2) ==> c2 x = g2(inv(norm x pow 2) % x))
        ==> S1 SUBSET inside S2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `A:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "AOUT") (LABEL_TAC "AIN"))))) o
    MATCH_MP SCH6_SD_SIDE_A) THEN
  FIRST_ASSUM(LABEL_TAC "CH" o MATCH_MP SCH6_SD_S2_CHART) THEN
  UNDISCH_TAC `sch6_slab_data S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2` THEN
  SCH6_SD_TAC THEN
  MP_TAC(ISPEC `S2:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c2:real^3->real^3`; `c2':real^3->real^3`; `S2:real^3->bool`]
    SCH1_BALL_INSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(E2:real^3->bool) SUBSET S /\ (E1:real^3->bool) SUBSET S` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S:real^3->bool` `sch_lat`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `A INTER (S2:real^3->bool) = {}` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S2:real^3->bool` `sch_cap2`)) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `p:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THENL
     [ASM SET_TAC[];
      FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(y:real^3) IN N /\ y$1 pow 2 + y$2 pow 2 <= &1` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN sch_cap2` THEN
        REWRITE_TAC[sch_cap2; IN_ELIM_THM] THEN STRIP_TAC THEN
        MP_TAC(SPEC `(y:real^3)$3` SCH_CAP_PROFILE_BOUNDS) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN CONJ_TAC THENL
         [UNDISCH_TAC `!y:real^3. y IN sch_slab_nbhd ==> y IN N` THEN DISCH_THEN MATCH_MP_TAC THEN
          REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_CASES_TAC `(y:real^3)$1 pow 2 + y$2 pow 2 = &1` THENL
       [SUBGOAL_THEN `(Theta:real^3->real^3) y IN S` MP_TAC THENL
         [ASM_SIMP_TAC[]; ASM SET_TAC[]];
        SUBGOAL_THEN `~((Theta:real^3->real^3) y IN A)` MP_TAC THENL
         [USE_THEN "AIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g2:real^3->real^3)(vector[&9 / &8; &0; &0]) IN A /\
                g2(vector[&9 / &8; &0; &0]) IN inside S2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`e0:real`; `&9 / &8`] SCH6_F_EQUATOR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `sch_flip3(vector[&9 / &8; &0; &0])` o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `sch_capcone`)) (concl th))) THEN
      REWRITE_TAC[SCH_FLIP3_INVOLUTION; GSYM SCH6_FCONE_FLIP] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      USE_THEN "AOUT" MATCH_MP_TAC THEN REWRITE_TAC[VECTOR_3] THEN CONJ_TAC THENL
       [UNDISCH_TAC `!y:real^3. y IN sch_slab_nbhd ==> y IN N` THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM; VECTOR_3] THEN
        SUBGOAL_THEN `sqrt(&1 + e0 * (&9 / &8 - &1)) pow 2 = &1 + e0 * (&9 / &8 - &1)`
        SUBST1_TAC THENL [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `sqrt(&1 + e0 * (&9 / &8 - &1)) pow 2 = &1 + e0 * (&9 / &8 - &1)`
        SUBST1_TAC THENL [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(g2:real^3->real^3)(vector[&9 / &8; &0; &0]) =
                    (c2:real^3->real^3)(vector[&8 / &9; &0; &0])`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `vector[&8 / &9; &0; &0]:real^3` o
          check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `annulus (&3 / &4) (&2):real^3->bool`)) (concl th))) THEN
        SUBGOAL_THEN `norm(vector[&8 / &9; &0; &0]:real^3) = &8 / &9` ASSUME_TAC THENL
         [REWRITE_TAC[NORM_EQ_SQUARE; DOT_3; VECTOR_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_MUL_COMPONENT] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `inside S2:real^3->bool`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_BALL_0] THEN
        SUBGOAL_THEN `norm(vector[&8 / &9; &0; &0]:real^3) = &8 / &9` SUBST1_TAC THENL
         [REWRITE_TAC[NORM_EQ_SQUARE; DOT_3; VECTOR_3] THEN REAL_ARITH_TAC; REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `A SUBSET inside(S2:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S2:real^3->bool`; `A:real^3->bool`;
                   `(g2:real^3->real^3)(vector[&9 / &8; &0; &0])`] SCH6_SIDE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(E1:real^3->bool) SUBSET inside S2` ASSUME_TAC THENL
   [SUBGOAL_THEN `(S:real^3->bool) SUBSET S2 UNION inside S2` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(inside S2:real^3->bool)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(A:real^3->bool)` THEN CONJ_TAC THENL
         [UNDISCH_TAC `frontier A = (S:real^3->bool)` THEN REWRITE_TAC[frontier] THEN SET_TAC[];
          MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC CLOSURE_INSIDE_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(E1:real^3->bool) INTER S2 = {}` MP_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S2:real^3->bool` `sch_cap2`)) THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; NOT_IN_EMPTY; IN_IMAGE] THEN
      X_GEN_TAC `p:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))) THENL
       [UNDISCH_TAC `DISJOINT (E1:real^3->bool) E2` THEN ASM SET_TAC[];
        UNDISCH_TAC `(p:real^3) IN E1` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y:real^3) IN sch_cap2` THEN REWRITE_TAC[sch_cap2; IN_ELIM_THM] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `(y:real^3) IN N` (fun th -> FIRST_ASSUM(MP_TAC o CONJUNCT1 o C MATCH_MP th o
          check (fun th -> is_forall(concl th) &&
                           can (find_term ((=) `E1:real^3->bool`)) (concl th))))
        THENL
         [UNDISCH_TAC `!y:real^3. y IN sch_slab_nbhd ==> y IN N` THEN DISCH_THEN MATCH_MP_TAC THEN
          REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM] THEN
          MP_TAC(SPEC `(y:real^3)$3` SCH_CAP_PROFILE_BOUNDS) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
          DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Theta:real^3->real^3) sch_cap1 SUBSET inside S2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S2:real^3->bool`;
                   `IMAGE (Theta:real^3->real^3) {y | y IN sch_slab_nbhd /\ y$3 < &1 / &2}`;
                   `(Theta:real^3->real^3)(vector[&3 / &2; &0; &0])`] SCH6_SIDE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        SIMP_TAC[STARLIKE_IMP_CONNECTED; SCH6_LOW_STARLIKE] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `N:real^3->bool` THEN CONJ_TAC THENL
         [UNDISCH_TAC `diffeomorphism_on N (IMAGE (Theta:real^3->real^3) N) Theta Theta'` THEN
          SIMP_TAC[diffeomorphism_on; SMOOTH_MAP_ON_CONTINUOUS_ON];
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM] THEN
        X_GEN_TAC `p:real^3` THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
        ASM_REWRITE_TAC[] THEN REMOVE_THEN "CH" (MP_TAC o SPEC `w:real^3`) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[IN_ELIM_THM; sch_slab_nbhd; VECTOR_3] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ANTS_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!(x:real^3) a b. x IN a /\ a SUBSET b ==> x IN b`) THEN
      EXISTS_TAC `A:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "AOUT" MATCH_MP_TAC THEN REWRITE_TAC[VECTOR_3] THEN CONJ_TAC THENL
       [UNDISCH_TAC `!y:real^3. y IN sch_slab_nbhd ==> y IN N` THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[sch_slab_nbhd; IN_ELIM_THM; VECTOR_3] THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^3->real^3) s t u. s SUBSET t ==> IMAGE f t SUBSET u
                                                       ==> IMAGE f s SUBSET u`) THEN
    REWRITE_TAC[SUBSET; sch_cap1; sch_slab_nbhd; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPEC `--((y:real^3)$3)` SCH_CAP_PROFILE_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (sch6_eq_with `S1:real^3->bool` `sch_cap1`)) THEN
  ASM_REWRITE_TAC[UNION_SUBSET]);;

(* Two spheres cannot each lie inside the other. *)

let SCH6_NOT_BOTH = prove
 (`!S1 S2:real^3->bool.
        S1 homeomorphic sphere(vec 0:real^3,&1) /\ S2 homeomorphic sphere(vec 0:real^3,&1) /\
        S1 SUBSET inside S2 /\ S2 SUBSET inside S1
        ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact(S1:real^3->bool) /\ compact(S2:real^3->bool) /\ connected S2 /\
                ~(S2 = {})` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`S1:real^3->bool`; `sphere(vec 0:real^3,&1)`] HOMEOMORPHIC_COMPACTNESS) THEN
      ASM_REWRITE_TAC[COMPACT_SPHERE];
      MP_TAC(ISPECL [`S2:real^3->bool`; `sphere(vec 0:real^3,&1)`] HOMEOMORPHIC_COMPACTNESS) THEN
      ASM_REWRITE_TAC[COMPACT_SPHERE];
      MP_TAC(ISPECL [`S2:real^3->bool`; `sphere(vec 0:real^3,&1)`]
        HOMEOMORPHIC_CONNECTEDNESS) THEN
      ASM_SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_3; ARITH];
      DISCH_TAC THEN UNDISCH_TAC `(S2:real^3->bool) homeomorphic sphere(vec 0:real^3,&1)` THEN
      ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY] THEN
      REWRITE_TAC[SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S1:real^3->bool`; `S2:real^3->bool`] INSIDE_INSIDE_COMPACT_CONNECTED) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  MP_TAC(ISPEC `S2:real^3->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[]);;

(* Case (a) of the gluing: the ball chart of S2 follows its collar. *)

let SCH6_CASE_A = prove
 (`!S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2 g2 g2' c2 c2' e0 c c'.
        sch6_slab_data S S1 S2 Theta Theta' N E1 E2 /\
        sch_neck g2 g2' /\ IMAGE g2 (sphere(vec 0,&1)) = S2 /\
        &0 < e0 /\ e0 <= &1 / &16 /\
        (!x. x IN sch_capcone ==> g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e0 x))) /\
        sch_ball c2 c2' /\ IMAGE c2 (cball(vec 0,&1)) = S2 UNION inside S2 /\
        (!x. x IN annulus (&3 / &4) (&2) ==> c2 x = g2 x) /\
        sch6_capchart c c' e0 /\ sch_bounds_ball S1
        ==> sch_bounds_ball S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`S:real^3->bool`; `S1:real^3->bool`; `S2:real^3->bool`; `Theta:real^3->real^3`;
                `Theta':real^3->real^3`; `N:real^3->bool`; `E1:real^3->bool`; `E2:real^3->bool`;
                `g2:real^3->real^3`; `g2':real^3->real^3`; `c2:real^3->real^3`;
                `c2':real^3->real^3`; `e0:real`; `c:real^3->real^3`; `c':real^3->real^3`]
    SCH6_PUSH) THEN
  ASM_REWRITE_TAC[sch6_push_data] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->real^3` (X_CHOOSE_THEN `Phi':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC SCH_BOUNDS_BALL_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`Phi:real^3->real^3`; `Phi':real^3->real^3`] THEN ASM_REWRITE_TAC[]);;

(* THE GLUING THEOREM, from SCH_COLLAR3_STATEMENT. *)

let SCH6_GLUE_FROM_COLLAR3 = prove
 (`SCH_COLLAR3_STATEMENT ==> SCH_SLAB_GLUE_STATEMENT`,
  DISCH_TAC THEN REWRITE_TAC[SCH_SLAB_GLUE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `g':real^3->real^3`; `g1:real^3->real^3`;
                       `g1':real^3->real^3`; `g2:real^3->real^3`; `g2':real^3->real^3`;
                       `Theta:real^3->real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC)
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `!f f':real^3->real^3. sch_neck f f'
                  ==> IMAGE f (sphere(vec 0,&1)) homeomorphic sphere(vec 0:real^3,&1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`f:real^3->real^3`; `f':real^3->real^3`; `&1`] SCH1_NECK_HOMEOMORPHIC) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC `S = IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `S1 = IMAGE (g1:real^3->real^3) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `S2 = IMAGE (g2:real^3->real^3) (sphere(vec 0,&1))` THEN
  SUBGOAL_THEN `(S:real^3->bool) homeomorphic sphere(vec 0:real^3,&1) /\
                (S1:real^3->bool) homeomorphic sphere(vec 0:real^3,&1) /\
                (S2:real^3->bool) homeomorphic sphere(vec 0:real^3,&1)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "S"; EXPAND_TAC "S1"; EXPAND_TAC "S2"] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `S1:real^3->bool`; `S2:real^3->bool`; `Theta:real^3->real^3`]
    SCH6_SD_OF_CONFIG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Theta':real^3->real^3` (X_CHOOSE_THEN `N:real^3->bool`
    (X_CHOOSE_THEN `E1:real^3->bool` (X_CHOOSE_THEN `E2:real^3->bool` ASSUME_TAC)))) THEN
  SUBGOAL_THEN `?c c'. sch6_capchart c c' e0` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[sch6_capchart] THEN MATCH_MP_TAC SCH6_CAPSULE_CHART THEN
    EXISTS_TAC `\y:real^3. (g1':real^3->real^3)(Theta y)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`g1:real^3->real^3`; `g1':real^3->real^3`; `Theta:real^3->real^3`;
                  `Theta':real^3->real^3`; `N:real^3->bool`; `e0:real`]
      SCH6_CAPCOLLAR_DIFFEO) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `sch6_slab_data S S1 S2 (Theta:real^3->real^3) Theta' N E1 E2` THEN
    REWRITE_TAC[sch6_slab_data] THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h h':real^3->real^3. sch_neck h h' /\ sch_bounds_ball (IMAGE h (sphere(vec 0,&1)))
                  ==> sch_fills h` (LABEL_TAC "C3") THENL
   [UNDISCH_TAC `SCH_COLLAR3_STATEMENT` THEN REWRITE_TAC[SCH_COLLAR3_STATEMENT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "C3" (MP_TAC o SPECL [`g2:real^3->real^3`; `g2':real^3->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[sch_fills]] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real^3->real^3` (X_CHOOSE_THEN `c2':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)))) THENL
   [MATCH_MP_TAC SCH6_CASE_A THEN
    MAP_EVERY EXISTS_TAC [`S1:real^3->bool`; `S2:real^3->bool`; `Theta:real^3->real^3`;
                          `Theta':real^3->real^3`; `N:real^3->bool`; `E1:real^3->bool`;
                          `E2:real^3->bool`; `g2:real^3->real^3`; `g2':real^3->real^3`;
                          `c2:real^3->real^3`; `c2':real^3->real^3`; `e0:real`;
                          `c:real^3->real^3`; `c':real^3->real^3`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* c2 is inverted: look at the ball chart of S1 *)
  USE_THEN "C3" (MP_TAC o SPECL [`g1:real^3->real^3`; `g1':real^3->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[sch_fills]] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real^3->real^3` (X_CHOOSE_THEN `c1':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  (* the reflected configuration *)
  MP_TAC(SPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCH6_NECK_FLIP) THEN
  MP_TAC(SPECL [`g1:real^3->real^3`; `g1':real^3->real^3`] SCH6_NECK_FLIP) THEN
  MP_TAC(SPECL [`g2:real^3->real^3`; `g2':real^3->real^3`] SCH6_NECK_FLIP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(SPECL [`S:real^3->bool`; `S1:real^3->bool`; `S2:real^3->bool`; `Theta:real^3->real^3`]
    SCH6_SLAB_FLIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`IMAGE sch_flip3 S`; `IMAGE sch_flip3 S2`; `IMAGE sch_flip3 S1`;
                 `sch_flip3 o (Theta:real^3->real^3) o sch_flip3`] SCH6_SD_OF_CONFIG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `IMAGE sch_flip3 (S:real^3->bool)`));
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `IMAGE sch_flip3 (S2:real^3->bool)`));
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `IMAGE sch_flip3 (S1:real^3->bool)`))] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Thf':real^3->real^3` (X_CHOOSE_THEN `Nf:real^3->bool`
    (X_CHOOSE_THEN `E1f:real^3->bool` (X_CHOOSE_THEN `E2f:real^3->bool` ASSUME_TAC)))) THEN
  MP_TAC(SPECL [`g1:real^3->real^3`; `g2:real^3->real^3`; `Theta:real^3->real^3`; `e0:real`]
    SCH6_COLLAR_FLIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `sch_ball (sch_flip3 o c1 o sch_flip3) (sch_flip3 o c1' o sch_flip3) /\
                IMAGE (sch_flip3 o c1 o sch_flip3) (cball(vec 0,&1)) =
                IMAGE sch_flip3 S1 UNION inside(IMAGE sch_flip3 S1)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCH6_BALL_FLIP] THEN
    REWRITE_TAC[SCH6_IMAGE_FLIP3_CONJ; SCH6_FLIP3_INSIDE] THEN
    SUBGOAL_THEN `IMAGE sch_flip3 (cball(vec 0:real^3,&1)) = cball(vec 0,&1)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; SCH6_IN_FLIP3; IN_CBALL_0; SCH6_NORM_FLIP3]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN annulus (&3 / &4) (&2) ==> sch_flip3 x IN annulus (&3 / &4) (&2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM; SCH6_NORM_FLIP3]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `c1:real^3->real^3`)) (concl th))) THENL
   [(* c1 follows g1: push in the reflected configuration *)
    SUBGOAL_THEN `sch_bounds_ball (IMAGE sch_flip3 S)` MP_TAC THENL
     [MATCH_MP_TAC SCH6_CASE_A THEN
      MAP_EVERY EXISTS_TAC [`IMAGE sch_flip3 S2`; `IMAGE sch_flip3 S1`;
                            `sch_flip3 o (Theta:real^3->real^3) o sch_flip3`;
                            `Thf':real^3->real^3`; `Nf:real^3->bool`; `E1f:real^3->bool`;
                            `E2f:real^3->bool`; `sch_flip3 o (g1:real^3->real^3) o sch_flip3`;
                            `sch_flip3 o (g1':real^3->real^3) o sch_flip3`;
                            `sch_flip3 o (c1:real^3->real^3) o sch_flip3`;
                            `sch_flip3 o (c1':real^3->real^3) o sch_flip3`; `e0:real`;
                            `c:real^3->real^3`; `c':real^3->real^3`] THEN
      ASM_SIMP_TAC[SCH6_BOUNDS_BALL_FLIP] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP SCH6_BOUNDS_BALL_FLIP) THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF; SCH_FLIP3_INVOLUTION; IMAGE_ID]];
    (* both inverted: impossible *)
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MATCH_MP_TAC SCH6_NOT_BOTH THEN
    MAP_EVERY EXISTS_TAC [`S1:real^3->bool`; `S2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCH6_INV_INSIDE THEN
      MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `Theta:real^3->real^3`; `Theta':real^3->real^3`;
                            `N:real^3->bool`; `E1:real^3->bool`; `E2:real^3->bool`;
                            `g2:real^3->real^3`; `g2':real^3->real^3`; `c2:real^3->real^3`;
                            `c2':real^3->real^3`; `e0:real`] THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `IMAGE sch_flip3 S2 SUBSET inside(IMAGE sch_flip3 S1)` MP_TAC THENL
       [MATCH_MP_TAC SCH6_INV_INSIDE THEN
        MAP_EVERY EXISTS_TAC [`IMAGE sch_flip3 S`; `sch_flip3 o (Theta:real^3->real^3) o sch_flip3`;
                              `Thf':real^3->real^3`; `Nf:real^3->bool`; `E1f:real^3->bool`;
                              `E2f:real^3->bool`; `sch_flip3 o (g1:real^3->real^3) o sch_flip3`;
                              `sch_flip3 o (g1':real^3->real^3) o sch_flip3`;
                              `sch_flip3 o (c1:real^3->real^3) o sch_flip3`;
                              `sch_flip3 o (c1':real^3->real^3) o sch_flip3`; `e0:real`] THEN
        ASM_SIMP_TAC[] THEN
        X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
        ASM_SIMP_TAC[SCH6_NORM_FLIP3] THEN AP_TERM_TAC THEN
        REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; SCH6_FLIP3_COMPONENTS;
                    VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
        REWRITE_TAC[SCH6_FLIP3_INSIDE; SUBSET; SCH6_IN_FLIP3] THEN
        DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `sch_flip3 y`) THEN
        REWRITE_TAC[SCH_FLIP3_INVOLUTION] THEN ASM_REWRITE_TAC[]]]]);;

(* The gluing step of the smooth Schoenflies induction. *)

let SCH6_SLAB_GLUE = prove
 (`SCH_SLAB_GLUE_STATEMENT`,
  MATCH_MP_TAC SCH6_GLUE_FROM_COLLAR3 THEN ACCEPT_TAC SCH_COLLAR3);;

