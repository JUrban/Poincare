(* ========================================================================= *)
(* pc_smt_radial: radial reparametrizations and unions of parametrizations,  *)
(* as used in the Appendix. Scaling, the inversion x / |x|^2, the power maps *)
(* |x|^p x / |x| and radial extensions of sphere diffeomorphisms are         *)
(* diffeomorphisms of annuli (and scaling of balls); the union of two        *)
(* parametrizations that agree on the overlap, with no further               *)
(* identifications, is a parametrization.                                    *)
(* ========================================================================= *)

needs "src/pc_smt_glue.ml";;
needs "src/pc_smt_sphere.ml";;

prioritize_real();;
type_invention_error := true;;

let SMT_DIFFEOMORPHISM_ON_INVERSES = prove
 (`!s t (f:real^M->real^N) g.
        open s /\ open t /\ smooth_map_on s f /\ smooth_map_on t g /\
        (!x. x IN s ==> f x IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g y IN s /\ f(g y) = y)
        ==> diffeomorphism_on s t f g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN
  ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

let SMT_SUBSET_NONZERO_ANNULUS = prove
 (`!r1 r2. &0 <= r1 ==> annulus r1 r2 SUBSET {x:real^N | ~(x = vec 0)}`,
  REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `r1 < norm(x:real^N)` THEN ASM_REWRITE_TAC[NORM_0] THEN
  ASM_REAL_ARITH_TAC);;

(* Scaling. *)

let SMT_DIFFEO_SCALING_ANNULUS = prove
 (`!c r1 r2.
        &0 < c
        ==> diffeomorphism_on (annulus r1 r2) (annulus (c * r1) (c * r2))
                              (\x:real^N. c % x) (\x. inv c % x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  REWRITE_TAC[OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    REWRITE_TAC[OPEN_ANNULUS; SMOOTH_MAP_ON_ID];
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    REWRITE_TAC[OPEN_ANNULUS; SMOOTH_MAP_ON_ID];
    REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_LT_LMUL_EQ];
    REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs(inv c) = inv c /\ &0 < inv c` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < c ==> abs c = c`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `c:real`;
      MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `c:real`] THEN
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID]]);;

let SMT_DIFFEO_SCALING_BALL = prove
 (`!c r.
        &0 < c
        ==> diffeomorphism_on (ball(vec 0,r)) (ball(vec 0,c * r))
                              (\x:real^N. c % x) (\x. inv c % x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_ID];
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_ID];
    REWRITE_TAC[IN_BALL_0; NORM_MUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_LT_LMUL_EQ];
    REWRITE_TAC[IN_BALL_0; NORM_MUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs(inv c) = inv c` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < c ==> abs c = c`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `c:real` THEN
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID]]);;

(* The inversion x / |x|^2, an involution of R^N minus 0. *)

let SMT_INVERSION_NORM = prove
 (`!x:real^N. ~(x = vec 0) ==> norm(inv(norm x pow 2) % x) = inv(norm x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  UNDISCH_TAC `~(x:real^N = vec 0)` THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
  CONV_TAC REAL_FIELD);;

let SMT_INVERSION_INVOLUTION = prove
 (`!x:real^N. ~(x = vec 0)
              ==> inv(norm(inv(norm x pow 2) % x) pow 2) % (inv(norm x pow 2) % x) = x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SMT_INVERSION_NORM; VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `~(x:real^N = vec 0)` THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
  CONV_TAC REAL_FIELD);;

let SMOOTH_MAP_ON_INVERSION = prove
 (`smooth_map_on {x:real^N | ~(x = vec 0)} (\x. inv(norm x pow 2) % x)`,
  MP_TAC(ISPECL [`{x:real^N | ~(x = vec 0)}`; `\x:real^N. lift(inv(norm x pow 2))`;
                 `\x:real^N. x`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_ID] THEN
  MP_TAC(ISPECL [`{x:real^N | ~(x = vec 0)}`; `\x:real^N. lift(norm x pow 2)`]
    SMOOTH_MAP_ON_LIFT_INV) THEN
  REWRITE_TAC[LIFT_DROP; IN_ELIM_THM; OPEN_NONZERO; REAL_POW_EQ_0; NORM_EQ_0] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`{x:real^N | ~(x = vec 0)}`; `\x:real^N. x`]
      SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_ID];
    ARITH_TAC]);;

let SMT_DIFFEO_INVERSION_ANNULUS = prove
 (`!r1 r2.
        &0 < r1 /\ r1 <= r2
        ==> diffeomorphism_on (annulus r1 r2) (annulus (inv r2) (inv r1))
                              (\x:real^N. inv(norm x pow 2) % x)
                              (\x. inv(norm x pow 2) % x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r2 /\ &0 <= inv r2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  REWRITE_TAC[OPEN_ANNULUS] THEN
  SUBGOAL_THEN `annulus r1 r2 SUBSET {x:real^N | ~(x = vec 0)} /\
                annulus (inv r2) (inv r1) SUBSET {x:real^N | ~(x = vec 0)}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMT_SUBSET_NONZERO_ANNULUS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^N | ~(x = vec 0)}` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_INVERSION];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^N | ~(x = vec 0)}` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_INVERSION];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(x:real^N = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_INVERSION_INVOLUTION] THEN
    UNDISCH_TAC `(x:real^N) IN annulus r1 r2` THEN
    ASM_SIMP_TAC[annulus; IN_ELIM_THM; SMT_INVERSION_NORM] THEN STRIP_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^N = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_INVERSION_INVOLUTION] THEN
    UNDISCH_TAC `(y:real^N) IN annulus (inv r2) (inv r1)` THEN
    ASM_SIMP_TAC[annulus; IN_ELIM_THM; SMT_INVERSION_NORM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(y:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ]]]);;

(* Power maps |x|^p x / |x| = norm x rpow (p - 1) % x. *)

let SMT_POWER_MAP_NORM = prove
 (`!p x:real^N. ~(x = vec 0) ==> norm(norm x rpow (p - &1) % x) = norm x rpow p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL] THEN
  ASM_SIMP_TAC[RPOW_POS_LT; REAL_ARITH `&0 < a ==> abs a = a`] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_POW_1] THEN
  REWRITE_TAC[GSYM RPOW_POW] THEN ASM_SIMP_TAC[GSYM RPOW_ADD] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let SMT_POWER_MAP_COMPOSE = prove
 (`!p q x:real^N.
        ~(x = vec 0)
        ==> norm(norm x rpow (p - &1) % x) rpow (q - &1) % (norm x rpow (p - &1) % x) =
            norm x rpow (p * q - &1) % x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[SMT_POWER_MAP_NORM; VECTOR_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE; GSYM RPOW_ADD] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let SMOOTH_MAP_ON_POWER_MAP = prove
 (`!p. smooth_map_on {x:real^N | ~(x = vec 0)} (\x. norm x rpow (p - &1) % x)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`{x:real^N | ~(x = vec 0)}`; `\x:real^N. lift(norm x rpow (p - &1))`;
                 `\x:real^N. x`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_ID] THEN
  MP_TAC(ISPECL [`{x:real^N | ~(x = vec 0)}`; `\x:real^N. lift(norm x)`; `p - &1`]
    SMOOTH_MAP_ON_LIFT_RPOW) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_NONZERO; SMOOTH_MAP_ON_LIFT_NORM_NONZERO;
              IN_ELIM_THM; NORM_POS_LT]);;

let SMT_DIFFEO_POWER_ANNULUS = prove
 (`!p r1 r2.
        &0 < p /\ &0 < r1 /\ r1 <= r2
        ==> diffeomorphism_on (annulus r1 r2) (annulus (r1 rpow p) (r2 rpow p))
                              (\x:real^N. norm x rpow (p - &1) % x)
                              (\x. norm x rpow (inv p - &1) % x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r2 /\ &0 < inv p /\ p * inv p = &1 /\ inv p * p = &1 /\
                &0 < r1 rpow p /\ (r1 rpow p) rpow (inv p) = r1 /\
                (r2 rpow p) rpow (inv p) = r2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_MUL_RINV; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                 RPOW_POS_LT; RPOW_RPOW; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[RPOW_POW; REAL_POW_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `annulus r1 r2 SUBSET {x:real^N | ~(x = vec 0)} /\
                annulus (r1 rpow p) (r2 rpow p) SUBSET {x:real^N | ~(x = vec 0)}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMT_SUBSET_NONZERO_ANNULUS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  REWRITE_TAC[OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^N | ~(x = vec 0)}` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_POWER_MAP];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^N | ~(x = vec 0)}` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_POWER_MAP];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(x:real^N = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_POWER_MAP_COMPOSE; RPOW_0; VECTOR_MUL_LID; REAL_SUB_REFL] THEN
    UNDISCH_TAC `(x:real^N) IN annulus r1 r2` THEN
    ASM_SIMP_TAC[annulus; IN_ELIM_THM; SMT_POWER_MAP_NORM] THEN STRIP_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC RPOW_LT2 THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^N = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_POWER_MAP_COMPOSE; RPOW_0; VECTOR_MUL_LID; REAL_SUB_REFL] THEN
    UNDISCH_TAC `(y:real^N) IN annulus (r1 rpow p) (r2 rpow p)` THEN
    ASM_SIMP_TAC[annulus; IN_ELIM_THM; SMT_POWER_MAP_NORM] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [SYM(ASSUME `r1 rpow p rpow inv p = r1`)] THEN
      MATCH_MP_TAC RPOW_LT2 THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [SYM(ASSUME `r2 rpow p rpow inv p = r2`)] THEN
      MATCH_MP_TAC RPOW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE]]]);;

(* Radial extensions of sphere diffeomorphisms. *)

let SMOOTH_MAP_ON_RADIAL_EXT = prove
 (`!g:real^N->real^N.
        smooth_near (sphere(vec 0,&1)) g
        ==> smooth_map_on {x | ~(x = vec 0)} (radial_ext g)`,
  REWRITE_TAC[smooth_near] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `radial_ext (g:real^N->real^N) = \x. norm x % g(inv(norm x) % x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; radial_ext]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^N | ~(x = vec 0)}`; `\x:real^N. lift(norm x)`;
                 `\x:real^N. (g:real^N->real^N)(inv(norm x) % x)`]
                SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_NONZERO; SMOOTH_MAP_ON_LIFT_NORM_NONZERO] THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. (g:real^N->real^N)(inv(norm x) % x)) =
                g o (\x. inv(norm x) % x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `u:real^N->bool` THEN
  ASM_REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_NORMALIZE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  UNDISCH_TAC `sphere(vec 0:real^N,&1) SUBSET u` THEN REWRITE_TAC[SUBSET] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE]);;

let SMT_DIFFEO_RADIAL_EXT_ANNULUS = prove
 (`!(g:real^N->real^N) g' r1 r2.
        sphere_diffeo g g' /\ &0 <= r1
        ==> diffeomorphism_on (annulus r1 r2) (annulus r1 r2)
                              (radial_ext g) (radial_ext g')`,
  REWRITE_TAC[sphere_diffeo] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `annulus r1 r2 SUBSET {x:real^N | ~(x = vec 0)}` ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_SUBSET_NONZERO_ANNULUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  REWRITE_TAC[OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^N | ~(x = vec 0)}` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_RADIAL_EXT];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^N | ~(x = vec 0)}` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_RADIAL_EXT];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^N->real^N`; `x:real^N`] SMT_RADIAL_EXT_NORM) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMT_RADIAL_EXT_INVERSE THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`g':real^N->real^N`; `x:real^N`] SMT_RADIAL_EXT_NORM) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMT_RADIAL_EXT_INVERSE THEN
    ASM_SIMP_TAC[]]);;

(* The union of two parametrizations agreeing on the overlap, with no other  *)
(* common image points, is a parametrization of the union.                   *)

let MFD_PARAM_UNION = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s1 s2 (e1:real^N->A) e2 e.
        smooth_manifold_atlas top atlas /\
        mfd_param top atlas s1 e1 /\ mfd_param top atlas s2 e2 /\
        (!x. x IN s1 ==> e x = e1 x) /\ (!x. x IN s2 ==> e x = e2 x) /\
        IMAGE e1 s1 INTER IMAGE e2 s2 = IMAGE e (s1 INTER s2)
        ==> mfd_param top atlas (s1 UNION s2) e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
   (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `e2':A->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1':A->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  REWRITE_TAC[mfd_param] THEN
  EXISTS_TAC `\p. if p IN IMAGE (e1:real^N->A) s1 then (e1':A->real^N) p
                  else e2' p` THEN
  SUBGOAL_THEN `IMAGE (e:real^N->A) (s1 UNION s2) = IMAGE e1 s1 UNION IMAGE e2 s2`
  SUBST1_TAC THENL [REWRITE_TAC[IMAGE_UNION] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_DIFFEO_GLUE_OPEN THEN
  MAP_EVERY EXISTS_TAC
   [`e1:real^N->A`; `e1':A->real^N`; `e2:real^N->A`; `e2':A->real^N`] THEN
  ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(e2:real^N->A) x IN IMAGE (e:real^N->A) (s1 INTER s2)` MP_TAC THENL
   [UNDISCH_TAC `IMAGE (e1:real^N->A) s1 INTER IMAGE e2 s2 = IMAGE e (s1 INTER s2)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e2:real^N->A) x = e2 z /\ (e2:real^N->A) x = e1 z`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `x:real^N = z` (fun th -> ASM_SIMP_TAC[th]) THEN
  ASM_MESON_TAC[]);;

