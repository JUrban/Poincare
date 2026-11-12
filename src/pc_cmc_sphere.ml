(* ========================================================================= *)
(* Unit pc_cmc_sphere: CMC_SPHERE_STATEMENT and CMC_TIGHT_STATEMENT.  Planar *)
(* harmonic maps of finite energy are harmonic spheres (the inversion z -> z *)
(* / |z|^2 is conformal, CM_REMOVABLE at the pole, CMR_SHARMONIC_FROM_CAPS), *)
(* and tightness at infinity after a rotation (pigeonhole over disjoint      *)
(* caps, the local theory, cap energies).  First: smooth maps on             *)
(* neighbourhoods of closures are W^{1,2}; energies of smooth maps.          *)
(* ========================================================================= *)

needs "src/pc_cmc_remove.ml";;
needs "src/pc_cmc_xfer.ml";;
needs "src/pc_cmr_crit.ml";;
needs "src/pc_cmr_l311.ml";;
needs "src/pc_smt_radial.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Smooth maps near compact closures.                                        *)
(* ------------------------------------------------------------------------- *)

let CMC_CONT_LSPACE = prove
 (`!(f:real^2->real^K) k s.
     compact k /\ s SUBSET k /\ measurable s /\ f continuous_on k ==> f IN lspace s (&2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (f:real^2->real^K) k` COMPACT_IMP_BOUNDED) THEN
  ANTS_TAC THENL [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[bounded; FORALL_IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `f:real^2->real^K`; `B:real`] CMC_BOUNDED_LNORM) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM SET_TAC[]]);;

let CMC_SMOOTH_W12_BOUNDED = prove
 (`!O s (u:real^2->real^K).
     open O /\ smooth_map_on O u /\ open s /\ bounded s /\ closure s SUBSET O
     ==> wan_w12 s u /\
         (!i. 1 <= i /\ i <= 2 ==> (\x. partial_derivative i u x) IN lspace s (&2)) /\
         !G:real^K->real^K^K.
            wan_gdir s G u =
            sum(1..2) (\i. drop(integral s (\x. lift(partial_derivative i u x dot
                                                     (G(u x) ** partial_derivative i u x)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact(closure(s:real^2->bool)) /\ s SUBSET closure s /\ measurable s`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_CLOSURE; CLOSURE_SUBSET; MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 1 s (u:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN EXISTS_TAC `O:real^2->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(s:real^2->bool)` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `smooth_map_on O (u:real^2->real^K)` THEN SIMP_TAC[smooth_map_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2 ==> (\x. partial_derivative i (u:real^2->real^K) x)
                                         IN lspace s (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_CONT_LSPACE THEN
    EXISTS_TAC `closure(s:real^2->bool)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^2->bool` THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CMC_PD_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (u:real^2->real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W12_C1) THEN REWRITE_TAC[WAN_W12_C1_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^2->bool`; `u:real^2->real^K`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[DIMINDEX_2] THEN
    MATCH_MP_TAC CMC_CONT_LSPACE THEN EXISTS_TAC `closure(s:real^2->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `O:real^2->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ASM_REWRITE_TAC[]] THEN
  GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `G:real^K->real^K^K`; `u:real^2->real^K`]
                HMC_GDIR_CLASSICAL) THEN
  ASM_REWRITE_TAC[DIMINDEX_2]);;

(* ------------------------------------------------------------------------- *)
(* Calculus of the inversion cml_inv z = z / |z|^2: the derivative bel_dT  *)
(* z is a reflection times |z|^-2, determinant and energy density.         *)
(* ------------------------------------------------------------------------- *)

let CMC_DT_COMPONENTS = prove
 (`!z:real^2. ?p q. p pow 2 + q pow 2 = inv(norm z pow 4) /\
                    (bel_dT z (basis 1))$1 = p /\ (bel_dT z (basis 1))$2 = --q /\
                    (bel_dT z (basis 2))$1 = --q /\ (bel_dT z (basis 2))$2 = --p`,
  GEN_TAC THEN MAP_EVERY EXISTS_TAC [`Re(--inv((z:complex) pow 2))`; `Im(--inv((z:complex) pow 2))`] THEN
  REWRITE_TAC[bel_dT; COMPLEX_BASIS; COMPLEX_MUL_RID; GSYM RE_DEF; GSYM IM_DEF; RE_CNJ; IM_CNJ;
              RE_MUL_II; IM_MUL_II] THEN
  REWRITE_TAC[GSYM COMPLEX_SQNORM; NORM_NEG; COMPLEX_NORM_INV; COMPLEX_NORM_POW] THEN
  REWRITE_TAC[REAL_POW_INV; GSYM REAL_POW_MUL; REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let CMC_DT_DET = prove
 (`!z:real^2. abs(det(matrix(bel_dT z))) = inv(norm z pow 4)`,
  GEN_TAC THEN MP_TAC(SPEC `z:real^2` CMC_DT_COMPONENTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC)) THEN
  SIMP_TAC[DET_2; MATRIX_COMPONENT; DIMINDEX_2; ARITH] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `p * --p - --q * --q = --(p pow 2 + q pow 2)`] THEN
  ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM]);;

let CMC_INV_HAS_DERIVATIVE = prove
 (`!z:real^2 s. ~(z = vec 0)
                ==> (cml_inv has_derivative bel_dT z) (at z within s) /\
                    cml_inv differentiable at z /\
                    (!i. partial_derivative i cml_inv z = bel_dT z (basis i))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_FRECHET) THEN ASM_REWRITE_TAC[partial_derivative] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

let CMC_INV_PD = prove
 (`!(w:real^2->real^K) z i.
     ~(z = vec 0) /\ w differentiable at (cml_inv z)
     ==> partial_derivative i (\y. w(cml_inv y)) z =
         frechet_derivative w (at (cml_inv z)) (bel_dT z (basis i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. (w:real^2->real^K)(cml_inv y)) = w o cml_inv` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`i:num`; `cml_inv`; `w:real^2->real^K`; `z:real^2`] PARTIAL_DERIVATIVE_CHAIN) THEN
  MP_TAC(ISPECL [`z:real^2`; `(:real^2)`] CMC_INV_HAS_DERIVATIVE) THEN
  ASM_SIMP_TAC[]);;

let CMC_QUAD2_ROT = prove
 (`!(M:real^K^K) (P1:real^K) P2 p q.
     transp M = M
     ==> (p % P1 + --q % P2) dot (M ** (p % P1 + --q % P2)) +
         (--q % P1 + --p % P2) dot (M ** (--q % P1 + --p % P2)) =
         (p pow 2 + q pow 2) * (P1 dot (M ** P1) + P2 dot (M ** P2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(P2:real^K) dot ((M:real^K^K) ** P1) = P1 dot (M ** P2)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [GSYM(ASSUME `transp(M:real^K^K) = M`)] THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_LADD; DOT_RADD;
              DOT_LMUL; DOT_RMUL] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CMC_INV_DENS = prove
 (`!(w:real^2->real^K) (M:real^K^K) z.
     ~(z = vec 0) /\ w differentiable at (cml_inv z) /\ transp M = M
     ==> sum(1..2) (\i. partial_derivative i (\y. w(cml_inv y)) z dot
                        (M ** partial_derivative i (\y. w(cml_inv y)) z)) =
         inv(norm z pow 4) *
         sum(1..2) (\j. partial_derivative j w (cml_inv z) dot
                        (M ** partial_derivative j w (cml_inv z)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMC_INV_PD] THEN
  MP_TAC(SPEC `z:real^2` CMC_DT_COMPONENTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `linear(frechet_derivative (w:real^2->real^K) (at (cml_inv z)))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `L = frechet_derivative (w:real^2->real^K) (at (cml_inv z))` THEN
  SUBGOAL_THEN
   `(L:real^2->real^K)(bel_dT z (basis 1)) = p % L(basis 1) + --q % L(basis 2) /\
    L(bel_dT z (basis 2)) = --q % L(basis 1) + --p % L(basis 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CML_BASIS_EXPAND2] THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL];
    ALL_TAC] THEN
  REWRITE_TAC[partial_derivative] THEN ASM_REWRITE_TAC[SUM_2] THEN
  MP_TAC(ISPECL [`M:real^K^K`; `(L:real^2->real^K)(basis 1)`; `(L:real^2->real^K)(basis 2)`;
                 `p:real`; `q:real`] CMC_QUAD2_ROT) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The G-energy is invariant under the inversion (smooth maps, bounded open  *)
(* sets with closure off the origin).                                        *)
(* ------------------------------------------------------------------------- *)

let CMC_INV_IMAGE = prove
 (`!s:real^2->bool.
     s SUBSET {z | ~(z = vec 0)}
     ==> IMAGE cml_inv s = {y | ~(y = vec 0) /\ cml_inv y IN s} /\
         IMAGE cml_inv s SUBSET {z | ~(z = vec 0)} /\
         IMAGE cml_inv (IMAGE cml_inv s) = s`,
  GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE cml_inv s = {y:real^2 | ~(y = vec 0) /\ cml_inv y IN s}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(x:real^2 = vec 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_NORM) THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN EXISTS_TAC `cml_inv(y:real^2)` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_NORM) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN EXISTS_TAC `cml_inv(x:real^2)` THEN
    SUBGOAL_THEN `~(x:real^2 = vec 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_NORM) THEN ASM_REWRITE_TAC[]]);;

let CMC_INV_CONT = prove
 (`smooth_map_on {z:real^2 | ~(z = vec 0)} cml_inv /\
   cml_inv continuous_on {z:real^2 | ~(z = vec 0)}`,
  SUBGOAL_THEN `cml_inv = (\x:real^2. inv(norm x pow 2) % x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; cml_inv]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  REWRITE_TAC[SMOOTH_MAP_ON_INVERSION; SMOOTH_MAP_ON_CONTINUOUS_ON]);;

let CMC_OPEN_INV_PREIMAGE = prove
 (`!O. open O ==> open {z:real^2 | ~(z = vec 0) /\ cml_inv z IN O}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cml_inv`; `{z:real^2 | ~(z = vec 0)}`; `O:real^2->bool`]
                CONTINUOUS_OPEN_PREIMAGE) THEN
  ASM_REWRITE_TAC[CMC_INV_CONT; OPEN_NONZERO; IN_ELIM_THM]);;

let CMC_INV_SETS = prove
 (`!s O.
     open s /\ bounded s /\ closure s SUBSET {z:real^2 | ~(z = vec 0)} /\
     IMAGE cml_inv (closure s) SUBSET O /\ open O
     ==> open (IMAGE cml_inv s) /\ bounded (IMAGE cml_inv s) /\
         closure (IMAGE cml_inv s) SUBSET O /\
         closure (IMAGE cml_inv s) SUBSET {z:real^2 | ~(z = vec 0)} /\
         open {z:real^2 | ~(z = vec 0) /\ cml_inv z IN O} /\
         closure s SUBSET {z:real^2 | ~(z = vec 0) /\ cml_inv z IN O}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^2->bool) SUBSET closure s` ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^2->bool) SUBSET {z | ~(z = vec 0)}` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE cml_inv (closure(s:real^2->bool)))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[COMPACT_CLOSURE] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^2 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[CMC_INV_CONT];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE cml_inv s SUBSET IMAGE cml_inv (closure(s:real^2->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[IMAGE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `closure(IMAGE cml_inv s) SUBSET IMAGE cml_inv (closure(s:real^2->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE cml_inv (closure s) SUBSET {z:real^2 | ~(z = vec 0)}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `closure s:real^2->bool` CMC_INV_IMAGE) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `s:real^2->bool` CMC_INV_IMAGE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN MATCH_MP_TAC CMC_OPEN_INV_PREIMAGE THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE cml_inv (closure(s:real^2->bool))` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
    ASM_MESON_TAC[SUBSET_TRANS];
    ASM_MESON_TAC[SUBSET_TRANS];
    MATCH_MP_TAC CMC_OPEN_INV_PREIMAGE THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `IMAGE cml_inv (closure s) SUBSET (O:real^2->bool)` THEN
    UNDISCH_TAC `closure s SUBSET {z:real^2 | ~(z = vec 0)}` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]]);;

let CMC_INV_SMOOTH = prove
 (`!(w:real^2->real^K) O.
     open O /\ smooth_map_on O w
     ==> smooth_map_on {z:real^2 | ~(z = vec 0) /\ cml_inv z IN O} (\z. w(cml_inv z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (w:real^2->real^K)(cml_inv z)) = w o cml_inv` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O:real^2->bool` THEN
  ASM_SIMP_TAC[CMC_OPEN_INV_PREIMAGE] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{z:real^2 | ~(z = vec 0)}` THEN
    REWRITE_TAC[CMC_INV_CONT] THEN SET_TAC[]]);;

let CMC_INT2_ADD = prove
 (`!(f:real^2->real) g s.
     (\x. lift(f x)) absolutely_integrable_on s /\ (\x. lift(g x)) absolutely_integrable_on s
     ==> drop(integral s (\x. lift(f x))) + drop(integral s (\x. lift(g x))) =
         drop(integral s (\x. lift(f x + g x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DROP_ADD; LIFT_ADD] THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_ADD THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

let CMC_INV_GDIR = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) O s.
     cm_target S G d /\ open O /\ smooth_map_on O w /\
     open s /\ bounded s /\ closure s SUBSET {z:real^2 | ~(z = vec 0)} /\
     IMAGE cml_inv (closure s) SUBSET O
     ==> wan_gdir s G (\z. w(cml_inv z)) = wan_gdir (IMAGE cml_inv s) G w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] CMC_GQUAD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `O:real^2->bool`] CMC_INV_SETS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real^2->real^K`; `O:real^2->bool`] CMC_INV_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{z:real^2 | ~(z = vec 0) /\ cml_inv z IN O}`; `s:real^2->bool`;
                 `\z. (w:real^2->real^K)(cml_inv z)`] CMC_SMOOTH_W12_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "L1") (LABEL_TAC "E1"))) THEN
  MP_TAC(ISPECL [`O:real^2->bool`; `IMAGE cml_inv s`; `w:real^2->real^K`]
                CMC_SMOOTH_W12_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "L2") (LABEL_TAC "E2"))) THEN
  USE_THEN "E1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "E2" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[SUM_2] THEN
  SUBGOAL_THEN `lebesgue_measurable(s:real^2->bool) /\
                lebesgue_measurable(IMAGE cml_inv (s:real^2->bool))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift(partial_derivative i (\z. (w:real^2->real^K)(cml_inv z)) x dot
                      (G(w(cml_inv x)) ** partial_derivative i (\z. w(cml_inv z)) x)))
            absolutely_integrable_on s /\
            (\x. lift(partial_derivative i w x dot (G(w x) ** partial_derivative i w x)))
            absolutely_integrable_on IMAGE cml_inv s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`G:real^K->real^K^K`; `\z. (w:real^2->real^K)(cml_inv z)`;
                     `\x. partial_derivative i (\z. (w:real^2->real^K)(cml_inv z)) x`;
                     `s:real^2->bool`; `Lam:real`] CMR_GQUAD_INTEGRABLE);
      MP_TAC(ISPECL [`G:real^K->real^K^K`; `w:real^2->real^K`;
                     `\x. partial_derivative i (w:real^2->real^K) x`;
                     `IMAGE cml_inv (s:real^2->bool)`; `Lam:real`] CMR_GQUAD_INTEGRABLE)] THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{z:real^2 | ~(z = vec 0) /\ cml_inv z IN O}` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^2->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CMC_INT2_ADD; ARITH] THEN
  MP_TAC(ISPECL [`\y. lift(partial_derivative 1 (w:real^2->real^K) y dot
                           (G(w y) ** partial_derivative 1 w y) +
                           partial_derivative 2 w y dot (G(w y) ** partial_derivative 2 w y))`;
                 `cml_inv`; `bel_dT`; `s:real^2->bool`] INTEGRAL_CHANGE_OF_VARIABLES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`x:real^2`; `s:real^2->bool`] CMC_INV_HAS_DERIVATIVE) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      UNDISCH_TAC `closure s SUBSET {z:real^2 | ~(z = vec 0)}` THEN
      MP_TAC(ISPEC `s:real^2->bool` CLOSURE_SUBSET) THEN
      UNDISCH_TAC `(x:real^2) IN s` THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(x:real^2 = vec 0) /\ ~(y:real^2 = vec 0)` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `closure s SUBSET {z:real^2 | ~(z = vec 0)}` THEN
        MP_TAC(ISPEC `s:real^2->bool` CLOSURE_SUBSET) THEN
        UNDISCH_TAC `(x:real^2) IN s` THEN UNDISCH_TAC `(y:real^2) IN s` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_MESON_TAC[CML_INV_NORM];
      DISJ1_TAC THEN REWRITE_TAC[LIFT_ADD] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN ASM_SIMP_TAC[ARITH]];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  REWRITE_TAC[CMC_DT_DET; GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(x:real^2 = vec 0) /\ cml_inv x IN O` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `closure s SUBSET {z:real^2 | ~(z = vec 0) /\ cml_inv z IN O}` THEN
    MP_TAC(ISPEC `s:real^2->bool` CLOSURE_SUBSET) THEN
    UNDISCH_TAC `(x:real^2) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^2->real^K`; `(G:real^K->real^K^K)(w(cml_inv(x:real^2)))`;
                 `x:real^2`] CMC_INV_DENS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `O:real^2->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_2]]);;

(* ------------------------------------------------------------------------- *)
(* Harmonicity is invariant under the inversion.                             *)
(* ------------------------------------------------------------------------- *)

let CMC_INV_VTEST = prove
 (`!s (phi:real^2->real^K).
     s SUBSET {z:real^2 | ~(z = vec 0)} /\ wan_vtest s phi
     ==> wan_vtest (IMAGE cml_inv s) (\y. if y = vec 0 then vec 0 else phi(cml_inv y)) /\
         (!x. ~(x = vec 0)
              ==> (\y. if y = vec 0 then vec 0 else phi(cml_inv y)) (cml_inv x) = phi x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_vtest] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!x:real^2. ~(x = vec 0)
                 ==> (if cml_inv x = vec 0 then vec 0
                      else (phi:real^2->real^K)(cml_inv(cml_inv x))) = phi x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_NORM) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(k:real^2->bool) SUBSET {z | ~(z = vec 0)}` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `?Rk. &0 < Rk /\ !x:real^2. x IN k ==> norm x < Rk` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN REWRITE_TAC[bounded] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `abs B + &1` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_MESON_TAC[REAL_ARITH `x <= B ==> x < abs B + &1`]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `y:real^2` THEN ASM_CASES_TAC `y:real^2 = vec 0` THENL
     [EXISTS_TAC `ball(vec 0:real^2,inv Rk)` THEN
      ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_INV_EQ] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\y:real^2. vec 0:real^K` THEN
      REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST; IN_BALL_0] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_NORM) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `cml_inv x:real^2` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Rk:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `norm(x:real^2) < inv Rk` THEN
      SUBGOAL_THEN `&0 < norm(x:real^2)` MP_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
      UNDISCH_TAC `&0 < Rk` THEN
      SPEC_TAC(`norm(x:real^2)`,`t:real`) THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `Rk < inv t` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
        MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      EXISTS_TAC `{z:real^2 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `\z. (phi:real^2->real^K)(cml_inv z)` THEN
      REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN CONJ_TAC THENL
       [SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`phi:real^2->real^K`; `(:real^2)`] CMC_INV_SMOOTH) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE cml_inv (k:real^2->bool)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^2 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[CMC_INV_CONT];
    ASM_SIMP_TAC[IMAGE_SUBSET];
    X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_IMAGE] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    DISCH_TAC THEN UNDISCH_TAC `~(?x:real^2. y = cml_inv x /\ x IN k)` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `cml_inv y:real^2` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_NORM) THEN ASM_REWRITE_TAC[]]);;

let CMC_INV_HARMONIC = prove
 (`!S (G:real^K->real^K^K) d U (b:real^2->real^K).
     cm_target S G d /\ open U /\ U SUBSET {z:real^2 | ~(z = vec 0)} /\ cm_harmonic S G U b
     ==> cm_harmonic S G (IMAGE cml_inv U) (\z. b(cml_inv z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  MP_TAC(ISPEC `U:real^2->bool` CMC_INV_IMAGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IU") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[cm_harmonic] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "IU" SUBST1_TAC THEN MATCH_MP_TAC CMC_INV_SMOOTH THEN ASM_REWRITE_TAC[];
    USE_THEN "IU" SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`phi:real^2->real^K`; `s:real^2->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closure s SUBSET {z:real^2 | ~(z = vec 0)} /\
                IMAGE cml_inv (closure s) SUBSET (U:real^2->bool) /\
                (s:real^2->bool) SUBSET {z | ~(z = vec 0)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `closure s SUBSET IMAGE cml_inv (U:real^2->bool)` THEN
    USE_THEN "IU" SUBST1_TAC THEN MP_TAC(ISPEC `s:real^2->bool` CLOSURE_SUBSET) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `U:real^2->bool`] CMC_INV_SETS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `phi:real^2->real^K`] CMC_INV_VTEST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `phi2 = \y:real^2. if y = vec 0 then vec 0 else (phi:real^2->real^K)(cml_inv y)` THEN
  SUBGOAL_THEN
   `((\e. cm_gen G (IMAGE cml_inv s)
             (\x. closest_point S ((b:real^2->real^K) x + e % phi2 x))) has_real_derivative &0)
    (atreal (&0))`
  MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (phi2:real^2->real^K) /\
                ?k2. compact k2 /\ k2 SUBSET IMAGE cml_inv s /\
                     !x. ~(x IN k2) ==> phi2 x = vec 0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `wan_vtest (IMAGE cml_inv s) (phi2:real^2->real^K)` THEN
    REWRITE_TAC[wan_vtest];
    ALL_TAC] THEN
  SUBGOAL_THEN `?B. &0 < B /\ !x. norm((phi2:real^2->real^K) x) <= B` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (phi2:real^2->real^K) k2` COMPACT_IMP_BOUNDED) THEN ANTS_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `B:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN
    ASM_CASES_TAC `(x:real^2) IN k2` THEN ASM_SIMP_TAC[NORM_0; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `e1 = d / (B + &1)` THEN
  SUBGOAL_THEN `&0 < e1` ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!e p (q:real^K). abs e < e1 /\ p IN S /\ norm q <= B ==> p + e % q IN cm_tube S d`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[cm_tube; IN_ELIM_THM] THEN EXISTS_TAC `p:real^K` THEN
    ASM_REWRITE_TAC[dist; VECTOR_ARITH `(p + e % q) - p:real^K = e % q`; NORM_MUL] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e1 * B` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE; REAL_ABS_POS] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "e1" THEN REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < B ==> &0 < B + &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. abs e < e1
                    ==> smooth_map_on U
                          (\x. closest_point S ((b:real^2->real^K) x + e % phi2 x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\x. closest_point S ((b:real^2->real^K) x + e % phi2 x)) =
                  closest_point S o (\x. b x + e % phi2 x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC
   [`\e. cm_gen G (IMAGE cml_inv s)
           (\x. closest_point S ((b:real^2->real^K) x + e % phi2 x))`; `e1:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_TAC THEN REWRITE_TAC[cm_gen] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `\x. closest_point S ((b:real^2->real^K) x + e % phi2 x)`;
                 `U:real^2->bool`; `s:real^2->bool`] CMC_INV_GDIR) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CMT_WAN_GDIR_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(x:real^2 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "phi2" THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A planar harmonic map of finite energy, inverted, is harmonic and W^{1,2} *)
(* on the punctured unit disc, hence extends across the origin.              *)
(* ------------------------------------------------------------------------- *)

let CMC_INV_NORM_LT1 = prove
 (`!y:real^2. ~(y = vec 0) ==> (norm(cml_inv y) < &1 <=> &1 < norm y) /\
                              (&1 < norm(cml_inv y) <=> norm y < &1)`,
  GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_NORM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < norm(y:real^2)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SPEC_TAC(`norm(y:real^2)`,`t:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv t = &1 / t` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC);;

let CMC_INV_OUTER = prove
 (`IMAGE cml_inv {y:real^2 | &1 < norm y} = ball(vec 0,&1) DELETE vec 0 /\
   IMAGE cml_inv (ball(vec 0:real^2,&1) DELETE vec 0) = {y:real^2 | &1 < norm y} /\
   {y:real^2 | &1 < norm y} SUBSET {z:real^2 | ~(z = vec 0)} /\
   ball(vec 0:real^2,&1) DELETE vec 0 SUBSET {z:real^2 | ~(z = vec 0)}`,
  SUBGOAL_THEN `{y:real^2 | &1 < norm y} SUBSET {z:real^2 | ~(z = vec 0)} /\
                ball(vec 0:real^2,&1) DELETE vec 0 SUBSET {z:real^2 | ~(z = vec 0)}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_BALL_0] THEN
    MESON_TAC[NORM_0; REAL_ARITH `~(&1 < &0)`];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPEC `{y:real^2 | &1 < norm y}` CMC_INV_IMAGE) THEN
  MP_TAC(ISPEC `ball(vec 0:real^2,&1) DELETE vec 0` CMC_INV_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE; IN_BALL_0] THEN
  X_GEN_TAC `y:real^2` THEN ASM_CASES_TAC `y:real^2 = vec 0` THEN
  ASM_SIMP_TAC[NORM_0; REAL_LT_01; REAL_ARITH `~(&1 < &0)`; CMC_INV_NORM_LT1;
               MESON[CML_INV_NORM] `!y:real^2. ~(y = vec 0) ==> ~(cml_inv y = vec 0)`] THEN
  CONV_TAC TAUT);;

let CMC_LAM_LNORM_LE = prove
 (`!(G:real^K->real^K^K) (u:real^2->real^K) (f:real^2->real^K) s lam Lam.
     lebesgue_measurable s /\ u measurable_on s /\ f IN lspace s (&2) /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2) /\
     (!z v. lam * norm v pow 2 <= v dot (G z ** v))
     ==> lam * lnorm s (&2) f pow 2 <= drop(integral s (\x. lift(f x dot (G(u x) ** f x)))) /\
         &0 <= drop(integral s (\x. lift(f x dot (G(u x) ** f x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^2->real^K`; `f:real^2->real^K`;
                 `s:real^2->bool`; `Lam:real`] CMR_GQUAD_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ] THEN
    SUBGOAL_THEN `lam * drop(integral s (\x. lift(norm((f:real^2->real^K) x) pow 2))) =
                  drop(integral s (\x. lam % lift(norm(f x) pow 2)))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL; WAN_LSPACE2_SQNORM_INTEGRABLE]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL; WAN_LSPACE2_SQNORM_INTEGRABLE;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_DROP]]);;

let CMC_INV_PD_L2 = prove
 (`!S (G:real^K->real^K^K) d (b:real^2->real^K) i.
     cm_target S G d /\ cmc_pharm S G b /\ cmc_pmap S b /\ 1 <= i /\ i <= 2
     ==> (\x. partial_derivative i (\z. b(cml_inv z)) x)
         IN lspace (ball(vec 0,&1) DELETE vec 0) (&2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] CMC_GQUAD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (b:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cmc_pharm; cm_harmonic]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {z:real^2 | ~(z = vec 0)} (\z. (b:real^2->real^K)(cml_inv z))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`b:real^2->real^K`; `(:real^2)`] CMC_INV_SMOOTH) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `A = \j:num. ball(vec 0:real^2,&1) DIFF cball(vec 0,inv(&j + &2))` THEN
  SUBGOAL_THEN
   `!j. open((A:num->real^2->bool) j) /\ bounded(A j) /\
        closure(A j) SUBSET {z:real^2 | ~(z = vec 0)} /\ A j SUBSET A (SUC j) /\
        lebesgue_measurable (A j)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "A" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < inv(&j + &2) /\ inv(&(SUC j) + &2) <= inv(&j + &2)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ; GSYM REAL_OF_NUM_SUC] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SIMP_TAC[OPEN_DIFF; OPEN_BALL; CLOSED_CBALL; LEBESGUE_MEASURABLE_DIFF;
             LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_CBALL] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
      REWRITE_TAC[BOUNDED_BALL] THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(vec 0:real^2,&1) DIFF ball(vec 0,inv(&j + &2))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN
        SIMP_TAC[CLOSED_DIFF; CLOSED_CBALL; OPEN_BALL] THEN
        MP_TAC(ISPECL [`vec 0:real^2`; `&1`] BALL_SUBSET_CBALL) THEN
        MP_TAC(ISPECL [`vec 0:real^2`; `inv(&j + &2)`] BALL_SUBSET_CBALL) THEN SET_TAC[];
        REWRITE_TAC[SUBSET; IN_DIFF; IN_BALL_0; IN_ELIM_THM] THEN
        X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN DISCH_TAC THEN
        UNDISCH_TAC `~(norm(z:real^2) < inv(&j + &2))` THEN
        ASM_REWRITE_TAC[NORM_0]];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
      UNDISCH_TAC `inv(&(SUC j) + &2) <= inv(&j + &2)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1) DELETE vec 0`; `A:num->real^2->bool`;
                 `\x. partial_derivative i (\z. (b:real^2->real^K)(cml_inv z)) x`;
                 `cmc_pen G (:real^2) (b:real^2->real^K) / lam`] WAN_LNORM2_EXHAUST) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "A" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_DIFF; IN_DELETE; IN_BALL_0;
                IN_CBALL_0; IN_UNIV] THEN
    X_GEN_TAC `z:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `j:num` ASSUME_TAC) MP_TAC)) THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_BALL_0; IN_CBALL_0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(norm(z:real^2) <= inv(&j + &2))` THEN
      ASM_REWRITE_TAC[NORM_0] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      STRIP_TAC THEN
      MP_TAC(SPEC `norm(z:real^2)` REAL_ARCH_INV) THEN
      ASM_REWRITE_TAC[NORM_POS_LT] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `ball(vec 0:real^2,&1) DIFF cball(vec 0,inv(&n + &2))` THEN
      CONJ_TAC THENL [EXISTS_TAC `n:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_BALL_0; IN_CBALL_0; REAL_NOT_LE] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&n)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      UNDISCH_TAC `~(n = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
      MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `j:num` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t && fst(dest_const t) = "closure"))
      (concl th))) THEN
  MP_TAC(ISPECL [`{z:real^2 | ~(z = vec 0)}`; `(A:num->real^2->bool) j`;
                 `\z. (b:real^2->real^K)(cml_inv z)`] CMC_SMOOTH_W12_BOUNDED) THEN
  ASM_REWRITE_TAC[OPEN_NONZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "L") (LABEL_TAC "F"))) THEN
  CONJ_TAC THENL [USE_THEN "L" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= 2
        ==> lam * lnorm ((A:num->real^2->bool) j) (&2)
                    (\x. partial_derivative k (\z. (b:real^2->real^K)(cml_inv z)) x) pow 2 <=
            drop(integral (A j) (\x. lift(partial_derivative k (\z. b(cml_inv z)) x dot
                 (G(b(cml_inv x)) ** partial_derivative k (\z. b(cml_inv z)) x)))) /\
            &0 <= drop(integral (A j) (\x. lift(partial_derivative k (\z. b(cml_inv z)) x dot
                 (G(b(cml_inv x)) ** partial_derivative k (\z. b(cml_inv z)) x))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `\z. (b:real^2->real^K)(cml_inv z)`;
                   `\x. partial_derivative k (\z. (b:real^2->real^K)(cml_inv z)) x`;
                   `(A:num->real^2->bool) j`; `lam:real`; `Lam:real`] CMC_LAM_LNORM_LE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{z:real^2 | ~(z = vec 0)}` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_gdir ((A:num->real^2->bool) j) G (\z. (b:real^2->real^K)(cml_inv z)) <=
    cmc_pen G (:real^2) b`
  MP_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `b:real^2->real^K`;
                   `(:real^2)`; `(A:num->real^2->bool) j`] CMC_INV_GDIR) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`(A:num->real^2->bool) j`; `(:real^2)`] CMC_INV_SETS) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `b:real^2->real^K`;
                   `IMAGE cml_inv ((A:num->real^2->bool) j)`] CMC_GDIR_PEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; LEBESGUE_MEASURABLE_UNIV; SUBSET_UNIV];
    ALL_TAC] THEN
  USE_THEN "F" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[SUM_2] THEN
  FIRST_ASSUM(MP_TAC o SPEC `1`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
  REWRITE_TAC[ARITH] THEN
  SUBGOAL_THEN `i = 1 \/ i = 2` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  REAL_ARITH_TAC);;

let CMC_INV_EXTEND = prove
 (`!S (G:real^K->real^K^K) d (b:real^2->real^K).
     CM_REMOVABLE_STATEMENT (:K) /\ cm_target S G d /\ cmc_pharm S G b /\ cmc_pmap S b
     ==> ?h. cm_harmonic S G (ball(vec 0,&1)) h /\
             !x. x IN ball(vec 0,&1) DELETE vec 0 ==> h x = b(cml_inv x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (b:real^2->real^K) /\ cm_harmonic S G (:real^2) b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cmc_pharm; cm_harmonic]; ALL_TAC] THEN
  SUBGOAL_THEN
   `cm_harmonic S G (ball(vec 0:real^2,&1) DELETE vec 0) (\z. (b:real^2->real^K)(cml_inv z))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `{y:real^2 | &1 < norm y}`; `b:real^2->real^K`] CMC_INV_HARMONIC) THEN
    REWRITE_TAC[CMC_INV_OUTER] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `{y:real^2 | &1 < norm y} = (:real^2) DIFF cball(vec 0,&1)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN REAL_ARITH_TAC;
        SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL]];
      MATCH_MP_TAC HMC_HARMONIC_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_w12 (ball(vec 0:real^2,&1) DELETE vec 0) (\z. (b:real^2->real^K)(cml_inv z))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W12_C1) THEN REWRITE_TAC[WAN_W12_C1_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`ball(vec 0:real^2,&1) DELETE vec 0`;
                               `\z. (b:real^2->real^K)(cml_inv z)`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    SIMP_TAC[OPEN_DELETE; OPEN_BALL; DIMINDEX_2] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `cm_harmonic S G (ball(vec 0:real^2,&1) DELETE vec 0)
                     (\z. (b:real^2->real^K)(cml_inv z))` THEN
      SIMP_TAC[cm_harmonic; smooth_map_on];
      SUBGOAL_THEN `?MS. !z:real^K. z IN S ==> norm z <= MS` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[COMPACT_IMP_BOUNDED; bounded]; ALL_TAC] THEN
      MP_TAC(ISPECL [`ball(vec 0:real^2,&1) DELETE vec 0`;
                     `\z. (b:real^2->real^K)(cml_inv z)`; `MS:real`] CMC_BOUNDED_LNORM) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      SIMP_TAC[MEASURABLE_OPEN; OPEN_DELETE; OPEN_BALL; BOUNDED_DELETE; BOUNDED_BALL] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
        SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_DELETE; OPEN_BALL] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        UNDISCH_TAC `cm_harmonic S G (ball(vec 0:real^2,&1) DELETE vec 0)
                       (\z. (b:real^2->real^K)(cml_inv z))` THEN SIMP_TAC[cm_harmonic];
        REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC[cmc_pmap]];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_INV_PD_L2 THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `CM_REMOVABLE_STATEMENT (:K)` THEN REWRITE_TAC[CM_REMOVABLE_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^2`; `&1`; `\z. (b:real^2->real^K)(cml_inv z)`]) THEN
  ASM_REWRITE_TAC[REAL_LT_01]);;

(* ------------------------------------------------------------------------- *)
(* The sphere map of a planar harmonic map of finite energy:                 *)
(* CMC_SPHERE_STATEMENT.  Charts: the identity (north chart, all of R^2) and *)
(* the reflection cmc_d3 (third coordinate reversed; it maps the north chart *)
(* picture of the inverted plane onto a neighbourhood of the pole).          *)
(* ------------------------------------------------------------------------- *)

let cmc_d3 = new_definition
 `cmc_d3 = (lambda i j. if i = j then (if i = 3 then --(&1) else &1) else &0):real^3^3`;;

let CMC_D3_FACTS = prove
 (`orthogonal_matrix cmc_d3 /\
   (!y:real^2. cmc_d3 ** stereo2_n_inv y = stereo2_s_inv y) /\
   cm_capmap cmc_d3 (vec 0) = basis 3`,
  SUBGOAL_THEN `!x:real^3. cmc_d3 ** x = vector[x$1; x$2; --(x$3)]` ASSUME_TAC THENL
   [GEN_TAC THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MATRIX_VECTOR_MUL_COMPONENT; ARITH;
             VECTOR_3; DOT_3; cmc_d3; LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ORTHOGONAL_MATRIX] THEN
    SUBGOAL_THEN `transp cmc_d3 = cmc_d3` SUBST1_TAC THENL
     [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; transp; cmc_d3; LAMBDA_BETA; ARITH];
      ALL_TAC] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; matrix_mul; mat; cmc_d3; LAMBDA_BETA;
             SUM_3; ARITH] THEN REAL_ARITH_TAC;
    GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; STEX_STEREO2_N_INV_COMPONENTS;
             STEX_STEREO2_S_INV_COMPONENTS] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN REAL_ARITH_TAC;
    REWRITE_TAC[cm_capmap] THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; STEX_STEREO2_N_INV_COMPONENTS;
             BASIS_COMPONENT; ARITH; VEC_COMPONENT; NORM_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let CMC_SPHERE = prove
 (`CM_REMOVABLE_STATEMENT (:K) ==> CMC_SPHERE_STATEMENT (:K)`,
  DISCH_TAC THEN REWRITE_TAC[CMC_SPHERE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`b:real^2->real^K`; `TT:real^K->bool`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `cmc_pmap S (b:real^2->real^K) /\ cm_harmonic S G (:real^2) b`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[cmc_pharm];
      DISCH_TAC THEN MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`;
                                    `b:real^2->real^K`] CMC_PHARM_PMAP) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[cmc_pharm]; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. (b:real^2->real^K) x IN S` ASSUME_TAC THENL
   [ASM_MESON_TAC[cmc_pmap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `b:real^2->real^K`]
                CMC_INV_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^K` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HB"))) THEN
  SUBGOAL_THEN `smooth_map_on (ball(vec 0:real^2,&1)) (h:real^2->real^K) /\
                (!x. x IN ball(vec 0,&1) ==> h x IN S)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cm_harmonic]; ALL_TAC] THEN
  ABBREV_TAC `v = \z:real^3. if z = basis 3 then (h:real^2->real^K)(vec 0)
                             else (b:real^2->real^K)(stereo2_n z)` THEN
  SUBGOAL_THEN `!y. (v:real^3->real^K)(cm_capmap (mat 1) y) = b y` (LABEL_TAC "V1") THENL
   [GEN_TAC THEN EXPAND_TAC "v" THEN REWRITE_TAC[cm_capmap; MATRIX_VECTOR_MUL_LID] THEN
    MP_TAC(SPEC `y:real^2` STEX_STEREO2_N_INV_IN) THEN REWRITE_TAC[IN_DELETE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[STEX_STEREO2_N_RIGHT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(vec 0,&1) ==> (v:real^3->real^K)(cm_capmap cmc_d3 y) = h y`
  (LABEL_TAC "V2") THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN ASM_CASES_TAC `y:real^2 = vec 0` THENL
     [ASM_REWRITE_TAC[CMC_D3_FACTS] THEN EXPAND_TAC "v" THEN REWRITE_TAC[];
      EXPAND_TAC "v" THEN REWRITE_TAC[cm_capmap; CMC_D3_FACTS] THEN
      MP_TAC(SPEC `y:real^2` STEX_STEREO2_TRANSITION) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[GSYM cml_inv] THEN CONV_TAC SYM_CONV THEN
      USE_THEN "HB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN sphere(vec 0,&1)
               ==> z IN IMAGE (cm_capmap (mat 1)) (:real^2) \/
                   z IN IMAGE (cm_capmap cmc_d3) (ball(vec 0,&1))`
  (LABEL_TAC "CV") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN ASM_CASES_TAC `z:real^3 = basis 3` THENL
     [DISJ2_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN
      ASM_REWRITE_TAC[CMC_D3_FACTS; CENTRE_IN_BALL; REAL_LT_01];
      DISJ1_TAC THEN REWRITE_TAC[IN_IMAGE; IN_UNIV; cm_capmap; MATRIX_VECTOR_MUL_LID] THEN
      EXISTS_TAC `stereo2_n z` THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC STEX_STEREO2_N_LEFT THEN ASM_REWRITE_TAC[IN_DELETE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= 2
        ==> orthogonal_matrix (if k = 1 then mat 1 else cmc_d3) /\
            open (if k = 1 then (:real^2) else ball(vec 0,&1)) /\
            cm_harmonic S G (if k = 1 then (:real^2) else ball(vec 0,&1))
              (\x. (v:real^3->real^K) (cm_capmap (if k = 1 then mat 1 else cmc_d3) x))`
  (LABEL_TAC "CH") THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `k = 1 \/ k = 2` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[ARITH] THENL
     [REWRITE_TAC[ORTHOGONAL_MATRIX_ID; OPEN_UNIV] THEN MATCH_MP_TAC HMD_HARMONIC_CONG THEN
      EXISTS_TAC `b:real^2->real^K` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[CMC_D3_FACTS; OPEN_BALL] THEN MATCH_MP_TAC HMD_HARMONIC_CONG THEN
      EXISTS_TAC `h:real^2->real^K` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN sphere(vec 0,&1)
       ==> ?k. 1 <= k /\ k <= 2 /\
               y IN IMAGE (cm_capmap (if k = 1 then mat 1 else cmc_d3))
                          (if k = 1 then (:real^2) else ball(vec 0,&1))`
  (LABEL_TAC "CV2") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "CV" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
     [EXISTS_TAC `1` THEN ASM_REWRITE_TAC[ARITH];
      EXISTS_TAC `2` THEN ASM_REWRITE_TAC[ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (v:real^3->real^K))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_REXT_FROM_CHARTS THEN
    MAP_EVERY EXISTS_TAC [`2`; `\k. if k = 1 then mat 1 else cmc_d3:real^3^3`;
                          `\k. if k = 1 then (:real^2) else ball(vec 0:real^2,&1)`] THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN USE_THEN "CH" (MP_TAC o SPEC `k:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[cm_harmonic]];
      USE_THEN "CV2" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^2->real^K)(vec 0) IN TT` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `at (vec 0:real^2)` LIM_IN_CLOSED_SET) THEN
    EXISTS_TAC `h:real^2->real^K` THEN ASM_REWRITE_TAC[TRIVIAL_LIMIT_AT] THEN CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_AT] THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; DIST_0] THEN
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      USE_THEN "HB" (MP_TAC o SPEC `x:real^2`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_DELETE; IN_BALL_0; GSYM NORM_POS_LT];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[GSYM CONTINUOUS_AT] THEN
      MP_TAC(ISPECL [`h:real^2->real^K`; `ball(vec 0:real^2,&1)`]
                    CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
      REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_01]];
    ALL_TAC] THEN
  EXISTS_TAC `v:real^3->real^K` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[cm_smap; wan_s2_w12] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `wan_rext (v:real^3->real^K)` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_SPHERE_0; wan_rext] THEN
        SIMP_TAC[REAL_INV_1; VECTOR_MUL_LID];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
        REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN
        MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`]];
      MP_TAC(ISPEC `v:real^3->real^K` CMT_REXT_WD_AE) THEN ANTS_TAC THENL
       [ASM_MESON_TAC[smooth_map_on]; SIMP_TAC[]];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "v" THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_01]];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "v" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^2` THEN USE_THEN "V1" (MP_TAC o SPEC `x:real^2`) THEN
    REWRITE_TAC[cm_capmap; MATRIX_VECTOR_MUL_LID];
    ASM_CASES_TAC `?c. !x. (b:real^2->real^K) x = c` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMR_SHARMONIC_FROM_CAPS THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `2`; `\k. if k = 1 then mat 1 else cmc_d3:real^3^3`;
                          `\k. if k = 1 then (:real^2) else ball(vec 0:real^2,&1)`] THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    (DISCH_THEN(X_CHOOSE_TAC `c:real^K`) THEN
      UNDISCH_TAC `~(?c. !x. (b:real^2->real^K) x = c)` THEN REWRITE_TAC[] THEN
      EXISTS_TAC `c:real^K` THEN X_GEN_TAC `x:real^2` THEN
      USE_THEN "V1" (fun th -> REWRITE_TAC[GSYM th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[cm_capmap; MATRIX_VECTOR_MUL_LID] THEN
      MP_TAC(SPEC `x:real^2` STEX_STEREO2_N_INV_IN) THEN SIMP_TAC[IN_DELETE])]);;

(* ------------------------------------------------------------------------- *)
(* Tools for the tightness: rotations and the chart map, (B) in a rotated    *)
(* chart, infinite pigeonhole, a rotation taking the pole to a given point,  *)
(* small caps at the pole and comparison of chart energies.                  *)
(* ------------------------------------------------------------------------- *)

let CMC_ROT_FACTS = prove
 (`!(R:real^3^3).
     orthogonal_matrix R /\ det R = &1
     ==> orthogonal_matrix(transp R) /\ det(transp R) = &1 /\
         (!y. transp R ** (R ** y) = y) /\ (!y. R ** (transp R ** y) = y) /\
         (!y. y IN sphere(vec 0,&1) ==> R ** y IN sphere(vec 0,&1)) /\
         (!y. y IN sphere(vec 0,&1) ==> transp R ** y IN sphere(vec 0,&1))`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSP; DET_TRANSP] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; ORTHOGONAL_MATRIX_TRANSP_LMUL;
               ORTHOGONAL_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_MUL_LID] THEN
  REWRITE_TAC[IN_SPHERE_0] THEN
  ASM_MESON_TAC[ORTHOGONAL_MATRIX_NORM; ORTHOGONAL_MATRIX_TRANSP]);;

let CMC_STEREO_SPHERE = prove
 (`!y:real^2. stereo2_n_inv y IN sphere(vec 0:real^3,&1)`,
  MESON_TAC[STEX_STEREO2_N_INV_IN; IN_DELETE]);;

let CMC_CAPMAP_INJ = prove
 (`!(R:real^3^3) x y.
     orthogonal_matrix R /\ cm_capmap R x = cm_capmap R y ==> x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_capmap] THEN STRIP_TAC THEN
  SUBGOAL_THEN `stereo2_n_inv x = stereo2_n_inv (y:real^2)` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `\z:real^3. transp(R:real^3^3) ** z`) THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; ORTHOGONAL_MATRIX_TRANSP_LMUL;
                 MATRIX_VECTOR_MUL_LID];
    DISCH_THEN(MP_TAC o AP_TERM `stereo2_n`) THEN REWRITE_TAC[STEX_STEREO2_N_RIGHT]]);;

(* The property (B) of a map of S^2 gives (B) of its picture in a rotated   *)
(* chart: take all rotations of the family equal to R.                       *)

let CMC_AH_CHART = prove
 (`!S (G:real^K->real^K^K) e0 eta (u:real^3->real^K) (R:real^3^3).
     orthogonal_matrix R /\ det R = &1 /\ cm_almost_harmonic S G e0 eta u
     ==> cmc_ah S G e0 eta (\y. u(R ** stereo2_n_inv y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_almost_harmonic; cmc_ah] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `c:num->real^2`; `r:num->real`;
                       `v:num->real^2->real^K`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `(\k:num. R:real^3^3)`; `c:num->real^2`;
                                `r:num->real`; `v:num->real^2->real^K`]) THEN
  REWRITE_TAC[cm_capmap] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `l:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (cball((c:num->real^2) k,(r:num->real) k)) (cball(c l,r l))`
  MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^2. cm_capmap R x = cm_capmap R y ==> x = y` MP_TAC THENL
   [ASM_MESON_TAC[CMC_CAPMAP_INJ]; ALL_TAC] THEN
  SET_TAC[]);;

let CMC_PIGEONHOLE = prove
 (`!(f:num->num) N. (!k. f k < N)
                    ==> ?i (s:num->num). (!m n. m < n ==> s m < s n) /\ (!j. f(s j) = i)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?i. INFINITE {k | (f:num->num) k = i}` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` MP_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP INFINITE_ENUMERATE) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:num->num` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `s:num->num`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN
    SUBGOAL_THEN `(s:num->num) j IN IMAGE s (:num)` MP_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; INFINITE]) THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(:num)` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[REWRITE_RULE[INFINITE] num_INFINITE]] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `UNIONS (IMAGE (\i. {k | (f:num->num) k = i}) {i | i < N})` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE];
    REWRITE_TAC[SUBSET; IN_UNIV; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `k:num` THEN EXISTS_TAC `(f:num->num) k` THEN ASM_REWRITE_TAC[]]);;

let CMC_ROT_TO_POLE = prove
 (`!p:real^3. norm p = &1 ==> ?R. orthogonal_matrix R /\ det R = &1 /\ R ** basis 3 = p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `p:real^3` ROTATION_MATRIX_EXISTS_BASIS) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH; rotation_matrix] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `P = (lambda i j. if j = 3 then (if i = 1 then &1 else &0)
                               else if j = 1 then (if i = 2 then &1 else &0)
                               else (if i = 3 then &1 else &0)):real^3^3` THEN
  SUBGOAL_THEN `orthogonal_matrix (P:real^3^3) /\ det P = &1 /\ P ** basis 3 = basis 1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ORTHOGONAL_MATRIX] THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; matrix_mul; transp; mat; LAMBDA_BETA;
               SUM_3; ARITH] THEN REAL_ARITH_TAC;
      SIMP_TAC[DET_3; LAMBDA_BETA; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MATRIX_VECTOR_MUL_COMPONENT; DOT_3;
               LAMBDA_BETA; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(A:real^3^3) ** (P:real^3^3)` THEN
  ASM_SIMP_TAC[ORTHOGONAL_MATRIX_MUL; DET_MUL; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  REAL_ARITH_TAC);;

let CMC_POLE_NBHD = prove
 (`!(R:real^3^3) (c:real^2) dl.
     orthogonal_matrix R /\ R ** basis 3 = stereo2_n_inv c /\ &0 < dl
     ==> ?r. &0 < r /\
             !y. r < norm y ==> R ** stereo2_n_inv y IN IMAGE stereo2_n_inv (ball(c,dl))`,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC STEX_STEREO2_N_CHART THEN
  ABBREV_TAC `W = {x:real^3 | x IN {x | x$3 < &1} /\ stereo2_n x IN ball(c:real^2,dl)}` THEN
  SUBGOAL_THEN `open(W:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `stereo2_n_inv c IN (W:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    UNDISCH_TAC `sphere(vec 0:real^3,&1) DELETE basis 3 SUBSET {x | x$3 < &1}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `W:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `stereo2_n_inv c:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&2 / eta` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(R:real^3^3) ** stereo2_n_inv y IN ball(stereo2_n_inv c,eta)` ASSUME_TAC THENL
   [SUBGOAL_THEN `norm((R:real^3^3) ** stereo2_n_inv y - stereo2_n_inv c) =
                  norm(stereo2_n_inv y - basis 3)` ASSUME_TAC THENL
     [UNDISCH_TAC `(R:real^3^3) ** basis 3 = stereo2_n_inv c` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
      ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(stereo2_n_inv y - basis 3) pow 2 = &4 / (norm(y:real^2) pow 2 + &1)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`mat 1:real^3^3`; `y:real^2`] CMR_CAPMAP_POLE_DIST) THEN
      REWRITE_TAC[ORTHOGONAL_MATRIX_ID; cm_capmap; MATRIX_VECTOR_MUL_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 / (norm(y:real^2) pow 2 + &1) < eta pow 2` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < norm(y:real^2) pow 2 + &1` ASSUME_TAC THENL
       [MP_TAC(ISPEC `norm(y:real^2)` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      SUBGOAL_THEN `&2 < eta * norm(y:real^2)` ASSUME_TAC THENL
       [UNDISCH_TAC `&2 / eta < norm(y:real^2)` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&2 pow 2 < (eta * norm(y:real^2)) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_MUL] THEN
      MP_TAC(ISPEC `eta:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`norm(stereo2_n_inv y - basis 3:real^3)`; `eta:real`] REAL_LT_SQUARE_ABS) THEN
    ASM_SIMP_TAC[REAL_ABS_NORM; REAL_ARITH `&0 < eta ==> abs eta = eta`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(R:real^3^3) ** stereo2_n_inv y IN W` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `stereo2_n((R:real^3^3) ** stereo2_n_inv y)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `y:real^2` CMC_STEREO_SPHERE) THEN
    REWRITE_TAC[IN_SPHERE_0] THEN ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM];
    DISCH_TAC THEN UNDISCH_TAC `((R:real^3^3) ** stereo2_n_inv y)$3 < &1` THEN
    ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC]);;

let CMC_CHART_ENERGY_LE = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) (R:real^3^3) D1 D2.
     cm_target S G d /\ cm_smap S u /\ orthogonal_matrix R /\ det R = &1 /\
     open D1 /\ open D2 /\
     IMAGE (\y. R ** stereo2_n_inv y) D1 SUBSET IMAGE stereo2_n_inv D2
     ==> wan_gdir D1 G (\y. u(R ** stereo2_n_inv y)) <=
         wan_gdir D2 G (\y. u(stereo2_n_inv y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] CMR_TARGET_GCOND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [CMR_GCOND]) THEN
  MP_TAC(SPEC `(:K)` CMCX_XFER) THEN REWRITE_TAC[CMC_XFER_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^3->real^K`; `R:real^3^3`] o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_s2_w12 (u:real^3->real^K) /\ wan_s2_w12 (\y. u((R:real^3^3) ** y))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `\y. (u:real^3->real^K)((R:real^3^3) ** y)`;
                 `Lam:real`; `D1:real^2->bool`] CMR_S2_GLOC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`;
                 `D2:real^2->bool`] CMR_S2_GLOC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `R:real^3^3`; `Lam:real`;
                 `IMAGE stereo2_n_inv (D1:real^2->bool)`] CMR_ROT_SEN) THEN
  ASM_SIMP_TAC[CMR_CONE_STEREO_OPEN; LEBESGUE_MEASURABLE_OPEN] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_ON_BASICS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
  DISCH_THEN(MP_TAC o SPECL [`IMAGE (\y:real^3. (R:real^3^3) ** y) (IMAGE stereo2_n_inv D1)`;
                             `IMAGE stereo2_n_inv (D2:real^2->bool)`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CMR_CONE_STEREO_OPEN; LEBESGUE_MEASURABLE_OPEN] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM CMR_ROT_CONE] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN THEN
      ASM_SIMP_TAC[MATRIX_VECTOR_MUL_LINEAR; LE_REFL; CMR_CONE_STEREO_OPEN;
                   LEBESGUE_MEASURABLE_OPEN];
      REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tightness at infinity after a rotation: CMC_TIGHT_STATEMENT.              *)
(* ------------------------------------------------------------------------- *)

let CMC_SPH_PMAP_LSPACE = prove
 (`!S (w:real^2->real^K) E.
     compact S /\ cmc_pmap S w /\ measurable E ==> w IN lspace E (&2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?MS. !z:real^K. z IN S ==> norm z <= MS` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IMP_BOUNDED; bounded]; ALL_TAC] THEN
  MP_TAC(ISPECL [`E:real^2->bool`; `w:real^2->real^K`; `MS:real`] CMC_BOUNDED_LNORM) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[cmc_pmap];
    ASM_MESON_TAC[cmc_pmap]]);;

let CMC_LOCAL_SMALL = prove
 (`!S (G:real^K->real^K^K) d (V:num->real^2->real^K) U c rho.
     cm_target S G d /\ (!j. cmc_pmap S (V j)) /\ &0 < rho /\
     cm_harmonic S G (ball(c,rho)) U /\ cmc_l2conv (ball(c,rho)) V U
     ==> !e. &0 < e
             ==> ?dl. &0 < dl /\ dl < rho /\
                      eventually (\j. cmc_pen G (ball(c,dl)) (V j) < e) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `G:real^K->real^K^K`]
                CMC_JDENS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `r1 = rho / &2` THEN
  SUBGOAL_THEN `&0 < r1 /\ r1 < rho /\ cball(c:real^2,r1) SUBSET ball(c,rho)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r1" THEN REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `f = \x:real^2. sum(1..3) (\i. cmw_edens G i ((U:real^2->real^K) x)
                                (cmc_j3 (partial_derivative 1 U x) (partial_derivative 2 U x)))` THEN
  SUBGOAL_THEN `(\x. lift((f:real^2->real) x)) continuous_on ball(c:real^2,rho)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\x. lift((f:real^2->real) x)) =
      (\z:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
          lift(sum(1..3) (\i. cmw_edens G i (fstcart z) (sndcart z)))) o
      (\x. pastecart ((U:real^2->real^K) x)
                     (pastecart (partial_derivative 1 U x)
                                (pastecart (partial_derivative 2 U x) (vec 0))))`
    SUBST1_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART;
                                      SNDCART_PASTECART; cmc_j3];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CONTINUOUS_ON_CONST; OPEN_BALL; ETA_AX;
                   CMC_PD_CONTINUOUS];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?B. !x:real^2. x IN cball(c,r1) ==> abs((f:real^2->real) x) <= B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (\x. lift((f:real^2->real) x)) (cball(c:real^2,r1))`
            COMPACT_IMP_BOUNDED) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_CBALL] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[bounded; FORALL_IN_IMAGE; NORM_LIFT]];
    ALL_TAC] THEN
  ABBREV_TAC `dl = min r1 (min (&1) (e / (&8 * (abs B + &1))))` THEN
  SUBGOAL_THEN `&0 < dl /\ dl <= r1 /\ dl <= &1 /\ dl <= e / (&8 * (abs B + &1))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN
    SUBGOAL_THEN `&0 < e / (&8 * (abs B + &1))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `dl:real` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ball(c:real^2,dl) SUBSET cball(c,r1) /\ ball(c,dl) SUBSET ball(c,rho)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `G:real^K->real^K^K`;
                 `V:num->real^2->real^K`; `U:real^2->real^K`;
                 `\x. partial_derivative 1 (U:real^2->real^K) x`;
                 `\x. partial_derivative 2 (U:real^2->real^K) x`; `ball(c:real^2,dl)`]
                CMC_DENS_JET_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[cmc_pmap];
      ASM_MESON_TAC[SUBSET];
      GEN_TAC THEN MATCH_MP_TAC CMC_JET_LSPACE THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CMC_SPH_PMAP_LSPACE THEN EXISTS_TAC `S:real^K->bool` THEN
        ASM_REWRITE_TAC[MEASURABLE_BALL];
        MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; SUBSET_UNIV] THEN
        ASM_MESON_TAC[CMC_PMAP_WD; ARITH_RULE `1 <= 1 /\ 1 <= 2`];
        MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; SUBSET_UNIV] THEN
        ASM_MESON_TAC[CMC_PMAP_WD; ARITH_RULE `1 <= 2 /\ 2 <= 2`]];
      MATCH_MP_TAC CMC_JET_LSPACE THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC CMC_CONT_LSPACE THEN EXISTS_TAC `cball(c:real^2,r1)` THEN
      ASM_REWRITE_TAC[COMPACT_CBALL; MEASURABLE_BALL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(c:real^2,rho)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; ETA_AX; CMC_PD_CONTINUOUS; OPEN_BALL];
      MP_TAC(ISPECL [`V:num->real^2->real^K`;
                     `\j. wan_wd (:real^2) 1 ((V:num->real^2->real^K) j)`;
                     `\j. wan_wd (:real^2) 2 ((V:num->real^2->real^K) j)`;
                     `U:real^2->real^K`; `\x. partial_derivative 1 (U:real^2->real^K) x`;
                     `\x. partial_derivative 2 (U:real^2->real^K) x`; `ball(c:real^2,dl)`]
                    CMC_JET_TOZERO) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      SUBGOAL_THEN `cmc_l2conv (ball(c:real^2,dl)) (V:num->real^2->real^K) U` MP_TAC THENL
       [MATCH_MP_TAC CMC_L2CONV_SUBSET THEN EXISTS_TAC `ball(c:real^2,rho)` THEN
        ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
        ALL_TAC] THEN
      REWRITE_TAC[cmc_l2conv] THEN STRIP_TAC THEN
      MP_TAC(SPEC `1` (ASSUME
       `!i. 1 <= i /\ i <= 2
            ==> (!j. (\x. wan_wd (:real^2) i ((V:num->real^2->real^K) j) x -
                          partial_derivative i U x) IN lspace (ball(c,dl)) (&2)) /\
                ((\j. lnorm (ball(c,dl)) (&2) (\x. wan_wd (:real^2) i (V j) x -
                                                  partial_derivative i U x)) ---> &0)
                sequentially`)) THEN
      MP_TAC(SPEC `2` (ASSUME
       `!i. 1 <= i /\ i <= 2
            ==> (!j. (\x. wan_wd (:real^2) i ((V:num->real^2->real^K) j) x -
                          partial_derivative i U x) IN lspace (ball(c,dl)) (&2)) /\
                ((\j. lnorm (ball(c,dl)) (&2) (\x. wan_wd (:real^2) i (V j) x -
                                                  partial_derivative i U x)) ---> &0)
                sequentially`)) THEN
      REWRITE_TAC[ARITH] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `L = drop(integral (ball(c:real^2,dl)) (\x. lift((f:real^2->real) x)))` THEN
  SUBGOAL_THEN
   `drop(integral (ball(c:real^2,dl))
          (\x. lift(sum(1..3) (\i. cmw_edens G i ((U:real^2->real^K) x)
                 (cmc_j3 (partial_derivative 1 U x) (partial_derivative 2 U x)))))) = L`
  SUBST1_TAC THENL [EXPAND_TAC "L" THEN EXPAND_TAC "f" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `L < e / &2` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `drop(integral (ball(c:real^2,dl)) (\x. lift(abs B)))` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:real^2. lift(abs B)) integrable_on ball(c,dl)` ASSUME_TAC THENL
       [REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_BALL]; ALL_TAC] THEN
      MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
        EXISTS_TAC `\x:real^2. lift(abs B)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
          REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
          X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
          MATCH_MP_TAC(REAL_ARITH `a <= B ==> a <= abs B`) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
        X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
        MATCH_MP_TAC(REAL_ARITH `abs a <= B ==> a <= abs B`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
      SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP] THEN
      SUBGOAL_THEN `measure(ball(c:real^2,dl)) <= &4 * dl` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * dl) pow dimindex(:2)` THEN
        CONJ_TAC THENL [MATCH_MP_TAC MEASURE_BALL_BOUND THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[DIMINDEX_2; REAL_POW_2] THEN
        SUBGOAL_THEN `dl * dl <= dl * &1` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `measure(ball(c:real^2,dl)) * abs B <= (&4 * dl) * abs B` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
      SUBGOAL_THEN `dl * (&8 * (abs B + &1)) <= e` ASSUME_TAC THENL
       [UNDISCH_TAC `dl <= e / (&8 * (abs B + &1))` THEN
        SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &8 * (abs B + &1)`];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CMC_BALLS_PIGEON = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) P a N.
     cm_target S G d /\ cmc_pmap S w /\ cmc_pen G (:real^2) w <= P /\ &0 < a /\
     P < (&N + &1) * a
     ==> ?i. i <= N /\ cmc_pen G (ball((&3 * &i) % basis 1,&1)) w < a`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?i. i <= N /\
                     cmc_pen G (ball((&3 * &i) % basis 1,&1)) (w:real^2->real^K) < a` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!i. i <= N ==> a <= cmc_pen G (ball((&3 * &i) % basis 1,&1)) (w:real^2->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[REAL_NOT_LT]; ALL_TAC] THEN
  ABBREV_TAC `cc = \i:num. (&3 * &i) % basis 1:real^2` THEN
  SUBGOAL_THEN `!i j. (cc:num->real^2) i = cc j ==> i = j` ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^2. v$1`) THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_EQ_MUL_LCANCEL; REAL_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. ~(i = j) ==> DISJOINT (ball((cc:num->real^2) i,&1)) (ball(cc j,&1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_BALL; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^2` THEN
    SUBGOAL_THEN `&3 <= norm((cc:num->real^2) i - cc j)` MP_TAC THENL
     [EXPAND_TAC "cc" THEN REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL; REAL_ABS_NUM] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &3 <= &3 * x`) THEN
      UNDISCH_TAC `~(i:num = j)` THEN
      DISJ_CASES_TAC(ARITH_RULE `i < j \/ j < (i:num) \/ i = j`) THENL
       [DISCH_TAC THEN SUBGOAL_THEN `&i + &1 <= &j` MP_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
        FIRST_X_ASSUM DISJ_CASES_TAC THENL
         [DISCH_TAC THEN SUBGOAL_THEN `&j + &1 <= &i` MP_TAC THENL
           [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
          ASM_REWRITE_TAC[]]];
      CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `\y:real^2. ball(y,&1)`; `IMAGE (cc:num->real^2) (0..N)`] CMC_PEN_UNIONS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; LEBESGUE_MEASURABLE_BALL] THEN
    REWRITE_TAC[IN_IMAGE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    DISCH_TAC THEN UNDISCH_TAC `~((y:real^2) = y')` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `(&N + &1) * a <= sum (IMAGE (cc:num->real^2) (0..N))
                        (\y. cmc_pen G (ball(y,&1)) (w:real^2->real^K))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cc:num->real^2`; `\y:real^2. cmc_pen G (ball(y,&1)) (w:real^2->real^K)`;
                   `0..N`] SUM_IMAGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..N) (\i:num. a)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; GSYM REAL_OF_NUM_ADD; REAL_LE_REFL];
      MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[o_THM] THEN EXPAND_TAC "cc" THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmc_pen G (UNIONS (IMAGE (\y:real^2. ball(y,&1)) (IMAGE (cc:num->real^2) (0..N))))
            (w:real^2->real^K) <= cmc_pen G (:real^2) w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN MATCH_MP_TAC OPEN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tightness (CMC_TIGHT): pigeonhole over disjoint unit balls, the local     *)
(* theory on the selected ball, and a rotation moving the north pole to the  *)
(* selected point, so that the energy near infinity in the rotated chart is  *)
(* controlled by the energy of a small ball.                                 *)
(* ------------------------------------------------------------------------- *)

let CMC_TIGHT_TAIL = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) (R:real^3^3) (c:real^2) dl r.
     cm_target S G d /\ cm_smap S u /\ orthogonal_matrix R /\ det R = &1 /\
     (!y. r < norm y ==> R ** stereo2_n_inv y IN IMAGE stereo2_n_inv (ball(c,dl)))
     ==> cmc_pen G {y:real^2 | r < norm y} (\y. u(R ** stereo2_n_inv y)) <=
         cmc_pen G (ball(c,dl)) (\y. u(stereo2_n_inv y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(:K)` CMCX_XFER) THEN REWRITE_TAC[CMC_XFER_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "X1") (CONJUNCTS_THEN2 (LABEL_TAC "X2") (K ALL_TAC))) THEN
  SUBGOAL_THEN `cmc_pmap S (\y:real^2. (u:real^3->real^K)(stereo2_n_inv y)) /\
                cmc_pmap S (\y:real^2. u(R ** stereo2_n_inv y))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "X1" (MP_TAC o SPEC `u:real^3->real^K`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      USE_THEN "X2" (MP_TAC o SPECL [`u:real^3->real^K`; `R:real^3^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "X1" (MP_TAC o SPEC `\y:real^3. (u:real^3->real^K)(R ** y)`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {y:real^2 | r < norm y}` ASSUME_TAC THENL
   [SUBGOAL_THEN `{y:real^2 | r < norm y} = (:real^2) DIFF cball(vec 0,r)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL_0; REAL_NOT_LE];
      SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `\y:real^2. (u:real^3->real^K)(R ** stereo2_n_inv y)`; `{y:real^2 | r < norm y}`]
                CMC_GDIR_PEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `\y:real^2. (u:real^3->real^K)(stereo2_n_inv y)`; `ball(c:real^2,dl)`]
                CMC_GDIR_PEN) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CMC_CHART_ENERGY_LE THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]);;

let CMC_TIGHT_SELECT = prove
 (`!S (G:real^K->real^K^K) d (u:num->real^3->real^K) P a.
     cm_target S G d /\
     (!k. cmc_pmap S (\y. u k (stereo2_n_inv y)) /\
          cmc_pen G (:real^2) (\y. u k (stereo2_n_inv y)) <= P) /\ &0 < a
     ==> ?(c:real^2) (s:num->num).
            (!m n. m < n ==> s m < s n) /\
            !j. cmc_pen G (ball(c,&1)) (\y. u (s j) (stereo2_n_inv y)) < a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `P / a` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  SUBGOAL_THEN `P < (&N + &1) * a` ASSUME_TAC THENL
   [SUBGOAL_THEN `P <= &N * a` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < a` THEN REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. ?i. i <= N /\
            cmc_pen G (ball((&3 * &i) % basis 1,&1))
                      (\y. (u:num->real^3->real^K) k (stereo2_n_inv y)) < a`
  MP_TAC THENL
   [X_GEN_TAC `k:num` THEN MATCH_MP_TAC CMC_BALLS_PIGEON THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`; `P:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num` (LABEL_TAC "F")) THEN
  MP_TAC(ISPECL [`f:num->num`; `N + 1`] CMC_PIGEONHOLE) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "F" (MP_TAC o SPEC `k:num`) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `s:num->num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FS")))) THEN
  EXISTS_TAC `(&3 * &i) % basis 1:real^2` THEN EXISTS_TAC `s:num->num` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN X_GEN_TAC `j:num` THEN
  USE_THEN "F" (MP_TAC o SPEC `(s:num->num) j`) THEN
  USE_THEN "FS" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[]);;

let CMC_TIGHT_LOCAL = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0 (w:num->real^2->real^K) eta c.
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < e0 /\ e0 <= eL /\
     (eta ---> &0) sequentially /\
     (!j. cmc_pmap S (w j) /\ cmc_ah S G e0 (eta j) (w j)) /\
     (!j. cmc_pen G (ball(c,&1)) (w j) < e0)
     ==> ?t:num->num. (!m n. m < n ==> t m < t n) /\
                      !e. &0 < e
                          ==> ?dl. &0 < dl /\
                                   eventually (\j. cmc_pen G (ball(c,dl)) (w (t j)) < e)
                                              sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `e0:real`; `w:num->real^2->real^K`; `eta:num->real`; `c:real^2`; `&1`]
                CMC_LOCAL_EV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `(w:num->real^2->real^K) j`; `ball(c:real^2,&1)`] CMC_GDIR_PEN) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` (X_CHOOSE_THEN `U:real^2->real^K` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `t:num->num` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `\j. (w:num->real^2->real^K) ((t:num->num) j)`; `U:real^2->real^K`; `c:real^2`;
                 `&1 / &32`] CMC_LOCAL_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "LS") THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "LS" (MP_TAC o SPEC `e:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `dl:real` THEN ASM_REWRITE_TAC[]);;

let CMC_TIGHT = prove
 (`CM_EPS_REG_STATEMENT (:K) /\ CM_REPLACEMENT_STATEMENT (:K)
   ==> CMC_TIGHT_STATEMENT (:K)`,
  STRIP_TAC THEN REWRITE_TAC[CMC_TIGHT_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] CMC_REGC_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eL:real` (X_CHOOSE_TAC `C:num->real`)) THEN
  EXISTS_TAC `eL:real` THEN CONJ_TAC THENL [ASM_MESON_TAC[cmc_regc]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`e0:real`; `E0:real`; `u:num->real^3->real^K`; `eta:num->real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UK")))) THEN
  MP_TAC(ISPEC `(:K)` CMCX_XFER) THEN REWRITE_TAC[CMC_XFER_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "X1") (K ALL_TAC)) THEN
  SUBGOAL_THEN
   `!k. cmc_pmap S (\y. (u:num->real^3->real^K) k (stereo2_n_inv y)) /\
        cmc_pen G (:real^2) (\y. u k (stereo2_n_inv y)) <= &2 * E0 /\
        cmc_ah S G e0 ((eta:num->real) k) (\y. u k (stereo2_n_inv y))`
  (LABEL_TAC "PK") THENL
   [X_GEN_TAC `k:num` THEN
    USE_THEN "UK" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    USE_THEN "X1" (MP_TAC o SPEC `(u:num->real^3->real^K) k`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "SE") (K ALL_TAC))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                     `\y. (u:num->real^3->real^K) k (stereo2_n_inv y)`; `(:real^2)`]
                    CMC_GDIR_PEN) THEN
      ASM_REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ASSUME `cm_sen G ((u:num->real^3->real^K) k) <= E0`) THEN
      USE_THEN "SE" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e0:real`; `(eta:num->real) k`;
                     `(u:num->real^3->real^K) k`; `mat 1:real^3^3`] CMC_AH_CHART) THEN
      ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID; DET_I; MATRIX_VECTOR_MUL_LID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:num->real^3->real^K`;
                 `&2 * E0`; `e0:real`] CMC_TIGHT_SELECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2` (X_CHOOSE_THEN `s1:num->num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `((\j. (eta:num->real) ((s1:num->num) j)) ---> &0) sequentially` ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_REALLIM_SUBSEQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `e0:real`;
                 `\j (y:real^2). (u:num->real^3->real^K) ((s1:num->num) j) (stereo2_n_inv y)`;
                 `\j. (eta:num->real) ((s1:num->num) j)`; `c:real^2`] CMC_TIGHT_LOCAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LOC"))) THEN
  MP_TAC(ISPEC `stereo2_n_inv (c:real^2)` CMC_ROT_TO_POLE) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `c:real^2` CMC_STEREO_SPHERE) THEN REWRITE_TAC[IN_SPHERE_0];
    DISCH_THEN(X_CHOOSE_THEN `R:real^3^3` STRIP_ASSUME_TAC)] THEN
  MAP_EVERY EXISTS_TAC [`\j. (s1:num->num) ((t:num->num) j)`; `R:real^3^3`] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "LOC" (MP_TAC o SPEC `e:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`R:real^3^3`; `c:real^2`; `dl:real`] CMC_POLE_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `eventually (\j. cmc_pen G (ball(c,dl))
                      (\y. (u:num->real^3->real^K) ((s1:num->num) ((t:num->num) j))
                             (stereo2_n_inv y)) < e) sequentially` THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
  MATCH_MP_TAC CMC_TIGHT_TAIL THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[]);;

