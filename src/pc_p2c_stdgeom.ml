(* ========================================================================= *)
(* Unit pc_p2c_stdgeom (Part 2C): P2C_STD_BOUNDED_GEOM for                   *)
(* every standard initial metric g0 (p3_std_initial g0 A0).  Beyond the     *)
(* distance A0 from the tip, g0 is the pullback of the cylinder metric      *)
(* cylinder_flow (&0) by the neck coordinates p3_std_nc, a diffeomorphism   *)
(* onto annuli (P3S_NC_DIFFEO); the cylinder is invariant under dilations,  *)
(* so its curvature derivatives are bounded (compactness of the sphere).    *)
(* The exhaustion is phi = psi(d) with d the distance from the tip and psi  *)
(* constant near 0 and linear far out; its gradient and Laplacian are read  *)
(* on the cylinder; the volume growth comes from Bishop-Gromov (sec >= 0).  *)
(* ========================================================================= *)

needs "src/pc_p2c_iface.ml";;
needs "src/pc_p2c_stdinit.ml";;
needs "src/pc_p3_s13met.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_cmp_bg.ml";;
needs "src/pc_rfa_spread.ml";;
needs "src/pc_rfa_slcalc.ml";;
needs "src/pc_grg_vol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The curvature derivatives of the cylinder cylinder_flow (&0)               *)
(* are constant along rays and bounded, at every order l (APX_CYL0_RM_CONST   *)
(* and APX_CYL0_RM_BOUND of pc_apx_neck are the case l = 0).                 *)
(* ------------------------------------------------------------------------- *)

let P2CN_CYL0_RMD_CONST = prove
 (`!l y:real^3.
        ~(y = vec 0)
        ==> lrm_deriv_norm2 l (cylinder_flow (&0)) y =
            lrm_deriv_norm2 l (cylinder_flow (&0)) (inv(norm y) % y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `c = inv(norm(y:real^3))` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:3`,`:N`]
   (ISPECL [`c:real`; `norm(y:real^3) / &2`; `&2 * norm(y:real^3)`]
           SMT_DIFFEO_SCALING_ANNULUS)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN annulus (norm y / &2) (&2 * norm y)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN annulus (norm(y:real^3) / &2) (&2 * norm y) ==> ~(z = vec 0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (annulus (c * norm(y:real^3) / &2) (c * &2 * norm y))
                 (cylinder_flow (&0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`; OPEN_ANNULUS] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `c * norm(y:real^3) / &2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:num`; `annulus (c * norm(y:real^3) / &2) (c * &2 * norm y):real^3->bool`;
                 `annulus (norm(y:real^3) / &2) (&2 * norm y):real^3->bool`; `\x:real^3. c % x`;
                 `\x:real^3. inv c % x`; `cylinder_flow (&0)`; `y:real^3`]
                LRM_DERIV_NORM2_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c * norm(y:real^3) / &2 = c * (norm y / &2)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN
  EXISTS_TAC `annulus (norm(y:real^3) / &2) (&2 * norm y):real^3->bool` THEN
  ASM_REWRITE_TAC[OPEN_ANNULUS] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC APX_CYL0_DILATION THEN ASM_SIMP_TAC[]);;

let P2CN_CYL0_RMD_BOUND = prove
 (`!l. ?K0. !y:real^3. ~(y = vec 0)
                       ==> lrm_deriv_norm2 l (cylinder_flow (&0)) y <= K0 pow 2`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`l:num`; `(:real^3) DELETE vec 0`; `cylinder_flow (&0)`]
                LRM_DERIV_NORM2_CONTINUOUS) THEN
  SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\y:real^3. lift(lrm_deriv_norm2 l (cylinder_flow (&0)) y)`;
                 `sphere(vec 0:real^3,&1)`] COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_SPHERE] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_DELETE; IN_UNIV] THEN
    MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sqrt B` THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SPEC `l:num` P2CN_CYL0_RMD_CONST)) THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= b ==> x <= b`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0]);;


(* ------------------------------------------------------------------------- *)
(* Bounded curvature derivatives of every standard initial                   *)
(* metric: continuity on a compact ball, the cylinder beyond distance A0.    *)
(* ------------------------------------------------------------------------- *)

let P2CN_STD_FAR_PULLBACK = prove
 (`!g0 A0 (x:real^3).
     p3_std_initial g0 A0 /\ A0 < p3_std_dist g0 x
     ==> ?V W. open V /\ open W /\ x IN V /\ W SUBSET (:real^3) DELETE vec 0 /\
               diffeomorphism_on V W (p3_std_nc g0 A0) (p3s_ncinv g0 A0) /\
               !z. z IN V ==> A0 < p3_std_dist g0 z /\
                              g0 z = mpullback (p3_std_nc g0 A0) (cylinder_flow (&0)) z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &3 - p3_std_dist g0 (x:real^3)`;
                 `&4`] P3S_NC_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`{z:real^3 | A0 + &3 - p3_std_dist g0 x < A0 + &4 - p3_std_dist g0 z /\
                 A0 + &4 - p3_std_dist g0 z < &4}`;
    `{y:real^3 | exp((A0 + &3 - p3_std_dist g0 x) / sqrt(&2)) < norm y /\
                 norm y < exp(&4 / sqrt(&2))}`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `exp((A0 + &3 - p3_std_dist g0 (x:real^3)) / sqrt(&2))` THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `A0 < p3_std_dist g0 (z:real^3)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `p3_std_initial g0 A0`) THEN REWRITE_TAC[p3_std_initial] THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[]]);;

let P2CN_STD_RMD_BOUND = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> !l. ?Cl. !x:real^3. lrm_deriv_norm2 l g0 x <= Cl`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `l:num` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  X_CHOOSE_TAC `K0:real` (SPEC `l:num` P2CN_CYL0_RMD_BOUND) THEN
  MP_TAC(ISPECL [`l:num`; `(:real^3)`; `g0:real^3->real^3^3`] LRM_DERIV_NORM2_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\y:real^3. lift(lrm_deriv_norm2 l g0 y)`;
                 `cball(vec 0:real^3,p3s_rad_rinv g0 A0)`] COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `max B (K0 pow 2)` THEN X_GEN_TAC `x:real^3` THEN
  ASM_CASES_TAC `norm(x:real^3) <= p3s_rad_rinv g0 A0` THENL
   [MATCH_MP_TAC(REAL_ARITH `abs a <= b ==> a <= max b c`) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_CBALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `A0 < p3_std_dist g0 (x:real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_ALT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0:real`] P3S_RINV) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 A0`;
                   `norm(x:real^3)`] P3S_RHO_STRICT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P2CN_STD_FAR_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->bool` (X_CHOOSE_THEN `W:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `metric_field (W:real^3->bool) (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `lrm_deriv_norm2 l g0 (x:real^3) =
                lrm_deriv_norm2 l (cylinder_flow (&0)) (p3_std_nc g0 A0 x)` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lrm_deriv_norm2 l (mpullback (p3_std_nc g0 A0) (cylinder_flow (&0)))
                                  (x:real^3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN EXISTS_TAC `V:real^3->bool` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC LRM_DERIV_NORM2_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`W:real^3->bool`; `V:real^3->bool`; `p3s_ncinv g0 A0`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= c ==> a <= max b c`) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `p3_std_nc g0 A0 (x:real^3) IN W` MP_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on V W (p3_std_nc g0 A0) (p3s_ncinv g0 A0)` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (p3_std_nc g0 A0) V = (W:real^3->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(W:real^3->bool) SUBSET (:real^3) DELETE vec 0` THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The Laplacian and the squared gradient of a smooth function               *)
(* are continuous (the Laplacian from RFA_LLAP_JOINT_SMOOTH with a constant  *)
(* family; the gradient from llap (f f) = 2 f llap f + 2 lgrad2 f).          *)
(* ------------------------------------------------------------------------- *)

let P2CN_LLAP_CONTINUOUS = prove
 (`!U (G:real^N->real^N^N) f.
     metric_field U G /\ smooth_map_on U (\z. lift(f z))
     ==> (\y. lift(llap G f y)) continuous_on U`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `&0`; `&1`; `\t:real. (G:real^N->real^N^N)`;
                 `f:real^N->real`] RFA_LLAP_JOINT_SMOOTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[lrg_lsmooth; REAL_LT_01] THEN
    SUBGOAL_THEN
     `(\z:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod) (G (sndcart z))) =
      ((vectorize:real^N^N->real^(N,N)finite_prod) o G) o (sndcart o (\z. z))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; SMOOTH_MAP_ON_SNDCART_OPEN; SMOOTH_MAP_ON_ID] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; o_THM; SNDCART_PASTECART] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\y:real^N. lift(llap G f y)) =
    (\w. lift(llap ((\t:real. (G:real^N->real^N^N)) (drop(fstcart w))) f (sndcart w))) o
    (\y. pastecart (lift(&1 / &2)) y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(&0),lift(&1)) PCROSS (U:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]]);;

let P2CN_LGRAD2_CONTINUOUS = prove
 (`!U (G:real^N->real^N^N) f.
     metric_field U G /\ smooth_map_on U (\z. lift(f z))
     ==> (\y. lift(lgrad2 G f y)) continuous_on U`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift((f:real^N->real) z * f z))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `\z. lift((f:real^N->real) z)`;
                   `\z. lift((f:real^N->real) z)`] SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\y. inv(&2) % (lift(llap (G:real^N->real^N^N) (\z. f z * f z) y) -
                             (&2 * f y) % lift(llap G f y))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`;
                   `f:real^N->real`; `y:real^N`] RFA_LLAP_MUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[RFA_LGRAD2_D1; GSYM LIFT_CMUL; GSYM LIFT_SUB; LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CN_LLAP_CONTINUOUS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2CN_LLAP_CONTINUOUS THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The distance from the tip read on the cylinder,                          *)
(* theta(y) = c - sqrt 2 log |y|: smooth on R^3 minus 0, and its squared   *)
(* gradient and Laplacian for cylinder_flow (&0) are invariant under        *)
(* dilations, hence bounded (compactness of the sphere).                    *)
(* ------------------------------------------------------------------------- *)

let p2cn_theta = new_definition
 `p2cn_theta (c:real) (y:real^3) = c - sqrt(&2) * log(norm y)`;;

let P2CN_THETA_SMOOTH = prove
 (`!c. smooth_map_on ((:real^3) DELETE vec 0) (\z. lift(p2cn_theta c z))`,
  GEN_TAC THEN
  SUBGOAL_THEN `(:real^3) DELETE vec 0 = {x:real^3 | ~(x = vec 0)}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DELETE; IN_UNIV; IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[p2cn_theta; LIFT_SUB; LIFT_CMUL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_NONZERO] THEN
  MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `\x:real^3. lift(norm x)`]
                SMOOTH_MAP_ON_LIFT_LOG) THEN
  REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_LIFT_NORM_NONZERO; LIFT_DROP; IN_ELIM_THM] THEN
  SIMP_TAC[NORM_POS_LT]);;

(* Shifting a function by a constant changes neither its squared gradient *)
(* nor its Laplacian.                                                        *)

let P2CN_SHIFT_LGRAD2_LLAP = prove
 (`!U (G:real^N->real^N^N) f a y.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> lgrad2 G (\z. f z + a) y = lgrad2 G f y /\
         llap G (\z. f z + a) y = llap G f y`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`;
                   `\t:real. t + a`; `&1`; `y:real^N`] RFA_LGRAD2_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REAL_DIFF_TAC THEN REAL_ARITH_TAC; REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPECL [`U:real^N->bool`; `(:real)`; `G:real^N->real^N^N`; `f:real^N->real`;
                   `\t:real. t + a`; `\t:real. &1`; `\t:real. &0`; `y:real^N`]
                  RFA_LLAP_COMPOSE) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
     [GEN_TAC THEN CONJ_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
    REAL_ARITH_TAC]);;

let P2CN_THETA_DILATE = prove
 (`!c lam z:real^3. &0 < lam /\ ~(z = vec 0)
                    ==> p2cn_theta c (lam % z) = p2cn_theta c z + --(sqrt(&2) * log lam)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cn_theta; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`; LOG_MUL; NORM_POS_LT] THEN
  REAL_ARITH_TAC);;

(* The squared gradient and the Laplacian of theta are constant along rays. *)

let P2CN_THETA_RAYS = prove
 (`!c y:real^3.
     ~(y = vec 0)
     ==> lgrad2 (cylinder_flow (&0)) (p2cn_theta c) y =
         lgrad2 (cylinder_flow (&0)) (p2cn_theta c) (inv(norm y) % y) /\
         llap (cylinder_flow (&0)) (p2cn_theta c) y =
         llap (cylinder_flow (&0)) (p2cn_theta c) (inv(norm y) % y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `lam = inv(norm(y:real^3))` THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  ABBREV_TAC `U' = annulus (norm(y:real^3) / &2) (&2 * norm y):real^3->bool` THEN
  ABBREV_TAC `U = annulus (lam * norm(y:real^3) / &2) (lam * &2 * norm y):real^3->bool` THEN
  MP_TAC(INST_TYPE [`:3`,`:N`]
   (ISPECL [`lam:real`; `norm(y:real^3) / &2`; `&2 * norm(y:real^3)`]
           SMT_DIFFEO_SCALING_ANNULUS)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lam * norm(y:real^3) / &2 = lam * (norm y / &2)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `annulus (lam * norm(y:real^3) / &2) (lam * &2 * norm y):real^3->bool = U`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lam * norm(y:real^3) / &2 = lam * (norm y / &2)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN U'` ASSUME_TAC THENL
   [EXPAND_TAC "U'" THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN U' ==> ~(z = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "U'" THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open (U':real^3->bool) /\ open (U:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "U'"] THEN REWRITE_TAC[OPEN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:real^3->bool) SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `lam * norm(y:real^3) / &2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (U:real^3->bool) (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (U:real^3->bool) (\z. lift(p2cn_theta c z))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_REWRITE_TAC[P2CN_THETA_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (U':real^3->bool) (\z. lift(p2cn_theta c z))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    REWRITE_TAC[P2CN_THETA_SMOOTH] THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN U'
               ==> mpullback (\x:real^3. lam % x) (cylinder_flow (&0)) z =
                   cylinder_flow (&0) z /\
                   (p2cn_theta c o (\x:real^3. lam % x)) z =
                   (\z. p2cn_theta c z + --(sqrt(&2) * log lam)) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[APX_CYL0_DILATION; o_THM; P2CN_THETA_DILATE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `U':real^3->bool`; `\x:real^3. lam % x`;
                   `\x:real^3. inv lam % x`; `cylinder_flow (&0)`; `p2cn_theta c`;
                   `y:real^3`] LGRAD2_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lgrad2 (cylinder_flow (&0)) (\z. p2cn_theta c z + --(sqrt(&2) * log lam))
                       (y:real^3)` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`U':real^3->bool`; `cylinder_flow (&0)`; `p2cn_theta c`;
                     `--(sqrt(&2) * log lam)`; `y:real^3`] P2CN_SHIFT_LGRAD2_LLAP) THEN
      ASM_SIMP_TAC[ETA_AX];
      MATCH_MP_TAC LGRAD2_LOCAL THEN EXISTS_TAC `U':real^3->bool` THEN
      ASM_SIMP_TAC[]];
    MP_TAC(ISPECL [`U:real^3->bool`; `U':real^3->bool`; `\x:real^3. lam % x`;
                   `\x:real^3. inv lam % x`; `cylinder_flow (&0)`; `p2cn_theta c`;
                   `y:real^3`] LLAP_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `llap (cylinder_flow (&0)) (\z. p2cn_theta c z + --(sqrt(&2) * log lam))
                     (y:real^3)` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`U':real^3->bool`; `cylinder_flow (&0)`; `p2cn_theta c`;
                     `--(sqrt(&2) * log lam)`; `y:real^3`] P2CN_SHIFT_LGRAD2_LLAP) THEN
      ASM_SIMP_TAC[ETA_AX];
      MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `U':real^3->bool` THEN
      ASM_SIMP_TAC[]]]);;

(* Hence they are bounded on R^3 minus 0. *)

let P2CN_THETA_BOUND = prove
 (`!c. ?K. !y:real^3.
         ~(y = vec 0)
         ==> abs(lgrad2 (cylinder_flow (&0)) (p2cn_theta c) y) <= K /\
             abs(llap (cylinder_flow (&0)) (p2cn_theta c) y) <= K`,
  GEN_TAC THEN
  SUBGOAL_THEN `metric_field ((:real^3) DELETE vec 0) (cylinder_flow (&0))` ASSUME_TAC THENL
   [SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `!h:real^3->real^1.
                  h continuous_on ((:real^3) DELETE vec 0)
                  ==> ?B. !y. norm y = &1 ==> norm(h y) <= B`
  (LABEL_TAC "cpt") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`h:real^3->real^1`; `sphere(vec 0:real^3,&1)`] COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_SPHERE] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_DELETE; IN_UNIV] THEN
      MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_SPHERE_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "cpt" (MP_TAC o SPEC `\y. lift(lgrad2 (cylinder_flow (&0)) (p2cn_theta c) y)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC P2CN_LGRAD2_CONTINUOUS THEN ASM_REWRITE_TAC[P2CN_THETA_SMOOTH]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` (LABEL_TAC "B1")) THEN
  USE_THEN "cpt" (MP_TAC o SPEC `\y. lift(llap (cylinder_flow (&0)) (p2cn_theta c) y)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC P2CN_LLAP_CONTINUOUS THEN ASM_REWRITE_TAC[P2CN_THETA_SMOOTH]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` (LABEL_TAC "B2")) THEN
  EXISTS_TAC `max B1 B2` THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `y:real^3`] P2CN_THETA_RAYS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN `norm(inv(norm(y:real^3)) % y) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  USE_THEN "B1" (MP_TAC o C MP (ASSUME `norm(inv(norm(y:real^3)) % y) = &1`) o
                 SPEC `inv(norm(y:real^3)) % y`) THEN
  USE_THEN "B2" (MP_TAC o C MP (ASSUME `norm(inv(norm(y:real^3)) % y) = &1`) o
                 SPEC `inv(norm(y:real^3)) % y`) THEN
  REWRITE_TAC[NORM_LIFT] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The exhaustion phi = psi(d), d the distance from the tip,                 *)
(* psi(r) = A0 + 3 + smooth_step(2 (r - A0 - 1) - 1) (r - A0 - 1): constant  *)
(* A0 + 3 for d < A0 + 3/2 (so phi is smooth at the tip), d + 2 for         *)
(* d > A0 + 2, and A0 + 3 <= phi, d <= phi everywhere.  Level sets of d are *)
(* round spheres: d x < c iff |x| < rinv c.                                  *)
(* ------------------------------------------------------------------------- *)

let p2cn_phi = new_definition
 `p2cn_phi (g0:real^3->real^3^3) (A0:real) (x:real^3) =
    A0 + &3 + smooth_step(&2 * (p3_std_dist g0 x - (A0 + &1)) - &1) *
              (p3_std_dist g0 x - (A0 + &1))`;;

let P2CN_DIST_COMPARE = prove
 (`!g0 A0 c (x:real^3).
     p3_std_initial g0 A0 /\ &0 <= c
     ==> (p3_std_dist g0 x < c <=> norm x < p3s_rad_rinv g0 c) /\
         (c < p3_std_dist g0 x <=> p3s_rad_rinv g0 c < norm x) /\
         (p3_std_dist g0 x <= c <=> norm x <= p3s_rad_rinv g0 c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_ALT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`] P3S_RINV) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r = p3s_rad_rinv g0 c` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`; `r:real`]
                P3S_RHO_LT_EQ) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`; `norm(x:real^3)`]
                P3S_RHO_LT_EQ) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN SIMP_TAC[]);;

let P2CN_PHI_VALUES = prove
 (`!g0 A0 (x:real^3).
     p3_std_initial g0 A0
     ==> (p3_std_dist g0 x < A0 + &3 / &2 ==> p2cn_phi g0 A0 x = A0 + &3) /\
         (A0 + &2 < p3_std_dist g0 x ==> p2cn_phi g0 A0 x = p3_std_dist g0 x + &2) /\
         A0 + &3 <= p2cn_phi g0 A0 x /\ p3_std_dist g0 x <= p2cn_phi g0 A0 x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p2cn_phi] THEN
  ABBREV_TAC `d = p3_std_dist g0 (x:real^3)` THEN
  MP_TAC(SPEC `&2 * (d - (A0 + &1)) - &1` SMOOTH_STEP_BOUNDS) THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPEC `&2 * (d - (A0 + &1)) - &1` SMOOTH_STEP_0) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
    DISCH_TAC THEN
    MP_TAC(SPEC `&2 * (d - (A0 + &1)) - &1` SMOOTH_STEP_1) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
    ASM_CASES_TAC `d < A0 + &1` THENL
     [MP_TAC(SPEC `&2 * (d - (A0 + &1)) - &1` SMOOTH_STEP_0) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> A0 + &3 <= A0 + &3 + y`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ASM_CASES_TAC `A0 + &2 < d` THENL
     [MP_TAC(SPEC `&2 * (d - (A0 + &1)) - &1` SMOOTH_STEP_1) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
      ASM_CASES_TAC `d < A0 + &1` THENL
       [MP_TAC(SPEC `&2 * (d - (A0 + &1)) - &1` SMOOTH_STEP_0) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC(REAL_ARITH `d <= A0 + &3 /\ &0 <= y ==> d <= A0 + &3 + y`) THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]]]);;

let P2CN_PHI_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on (:real^3) (\x. lift(p2cn_phi g0 A0 x))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `x:real^3` THEN
  ASM_CASES_TAC `p3_std_dist g0 (x:real^3) < A0 + &3 / &2` THENL
   [EXISTS_TAC `ball(vec 0:real^3,p3s_rad_rinv g0 (A0 + &3 / &2))` THEN
    REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &3 / &2`; `x:real^3`]
                  P2CN_DIST_COMPARE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT1 th)]) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\x:real^3. lift(A0 + &3)` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST; OPEN_BALL; IN_BALL_0] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`] P2CN_PHI_VALUES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &3 / &2`; `z:real^3`]
                  P2CN_DIST_COMPARE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(:real^3) DELETE vec 0` THEN
  REWRITE_TAC[P3S_OPEN_PUNCT; IN_DELETE; IN_UNIV] THEN CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(p3_std_dist g0 (vec 0:real^3) < A0 + &3 / &2)` THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_ALT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NORM_0; P3S_RHO_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_ROT_DIST_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  REWRITE_TAC[p2cn_phi; LIFT_ADD] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  REWRITE_TAC[P3S_OPEN_PUNCT; SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  REWRITE_TAC[P3S_OPEN_PUNCT; SMOOTH_MAP_ON_CONST] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`;
                 `\x:real^3. lift(smooth_step(&2 * (p3_std_dist g0 x - (A0 + &1)) - &1))`;
                 `\x:real^3. lift(p3_std_dist g0 x - (A0 + &1))`] SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
  REWRITE_TAC[LIFT_DROP; P3S_OPEN_PUNCT] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on ((:real^3) DELETE vec 0) (\x. lift(p3_std_dist g0 x - (A0 + &1)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[P3S_OPEN_PUNCT; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`;
                 `\x:real^3. lift(&2 * (p3_std_dist g0 x - (A0 + &1)) - &1)`]
                SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  REWRITE_TAC[LIFT_DROP; P3S_OPEN_PUNCT] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[LIFT_SUB; LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  REWRITE_TAC[P3S_OPEN_PUNCT; SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
  ASM_REWRITE_TAC[P3S_OPEN_PUNCT; GSYM LIFT_SUB]);;

(* ------------------------------------------------------------------------- *)
(* The squared gradient and the Laplacian of phi are bounded:               *)
(* continuity on a compact ball, and beyond distance A0 + 2 phi is theta   *)
(* composed with the neck coordinates, read on the cylinder.                *)
(* ------------------------------------------------------------------------- *)

let P2CN_DIST_NONZERO = prove
 (`!g0 A0 (z:real^3). p3_std_initial g0 A0 /\ &0 < p3_std_dist g0 z ==> ~(z = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `&0 < p3_std_dist g0 (vec 0:real^3)` THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_ALT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NORM_0; P3S_RHO_0; REAL_LT_REFL]);;

let P2CN_THETA_NC = prove
 (`!g0 A0 (z:real^3).
     ~(z = vec 0)
     ==> p2cn_theta (A0 + &6) (p3_std_nc g0 A0 z) = p3_std_dist g0 z + &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cn_theta] THEN
  ASM_SIMP_TAC[P3S_NC_NORM; LOG_EXP] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` MP_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

(* Far out: the gradient and the Laplacian of phi at x equal those of theta *)
(* at the neck coordinates of x.                                            *)

let P2CN_PHI_FAR = prove
 (`!g0 A0 (x:real^3).
     p3_std_initial g0 A0 /\ A0 + &2 < p3_std_dist g0 x
     ==> ~(p3_std_nc g0 A0 x = vec 0) /\
         lgrad2 g0 (p2cn_phi g0 A0) x =
         lgrad2 (cylinder_flow (&0)) (p2cn_theta (A0 + &6)) (p3_std_nc g0 A0 x) /\
         llap g0 (p2cn_phi g0 A0) x =
         llap (cylinder_flow (&0)) (p2cn_theta (A0 + &6)) (p3_std_nc g0 A0 x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P2CN_STD_FAR_PULLBACK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->bool` (X_CHOOSE_THEN `W:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `V' = (V:real^3->bool) DIFF cball(vec 0,p3s_rad_rinv g0 (A0 + &2))` THEN
  SUBGOAL_THEN `~(norm(x:real^3) <= p3s_rad_rinv g0 (A0 + &2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &2`; `x:real^3`]
                  P2CN_DIST_COMPARE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2 th))]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open (V':real^3->bool) /\ (x:real^3) IN V'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V'" THEN ASM_SIMP_TAC[OPEN_DIFF; CLOSED_CBALL; IN_DIFF; IN_CBALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN V' ==> z IN V /\ A0 + &2 < p3_std_dist g0 z`
  ASSUME_TAC THENL
   [EXPAND_TAC "V'" THEN REWRITE_TAC[IN_DIFF; IN_CBALL_0] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &2`; `z:real^3`]
                  P2CN_DIST_COMPARE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (W:real^3->bool) (cylinder_flow (&0)) /\
                smooth_map_on W (\z. lift(p2cn_theta (A0 + &6) z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_REWRITE_TAC[P2CN_THETA_SMOOTH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN V'
               ==> g0 z = mpullback (p3_std_nc g0 A0) (cylinder_flow (&0)) z /\
                   p2cn_phi g0 A0 z = (p2cn_theta (A0 + &6) o p3_std_nc g0 A0) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN V /\ A0 + &2 < p3_std_dist g0 z` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `p2cn_phi g0 A0 (z:real^3) = p3_std_dist g0 z + &2` SUBST1_TAC THENL
     [ASM_MESON_TAC[P2CN_PHI_VALUES]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2CN_THETA_NC THEN
    MATCH_MP_TAC P2CN_DIST_NONZERO THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_nc g0 A0 (x:real^3) IN W` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on V W (p3_std_nc g0 A0) (p3s_ncinv g0 A0)` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (p3_std_nc g0 A0) V = (W:real^3->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(W:real^3->bool) SUBSET (:real^3) DELETE vec 0` THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lgrad2 (mpullback (p3_std_nc g0 A0) (cylinder_flow (&0)))
                       (p2cn_theta (A0 + &6) o p3_std_nc g0 A0) (x:real^3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LGRAD2_LOCAL THEN EXISTS_TAC `V':real^3->bool` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC LGRAD2_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`W:real^3->bool`; `V:real^3->bool`; `p3s_ncinv g0 A0`] THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `llap (mpullback (p3_std_nc g0 A0) (cylinder_flow (&0)))
                     (p2cn_theta (A0 + &6) o p3_std_nc g0 A0) (x:real^3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `V':real^3->bool` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC LLAP_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`W:real^3->bool`; `V:real^3->bool`; `p3s_ncinv g0 A0`] THEN
      ASM_SIMP_TAC[]]]);;

let P2CN_PHI_GRAD_LAP_BOUND = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> ?K. !x:real^3. abs(lgrad2 g0 (p2cn_phi g0 A0) x) <= K /\
                              abs(llap g0 (p2cn_phi g0 A0) x) <= K`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2CN_PHI_SMOOTH) THEN
  X_CHOOSE_THEN `K1:real` (LABEL_TAC "K1") (SPEC `A0 + &6` P2CN_THETA_BOUND) THEN
  SUBGOAL_THEN
   `!h:real^3->real^1.
      h continuous_on (:real^3)
      ==> ?B. !y. y IN cball(vec 0:real^3,p3s_rad_rinv g0 (A0 + &2)) ==> norm(h y) <= B`
  (LABEL_TAC "cpt") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`h:real^3->real^1`; `cball(vec 0:real^3,p3s_rad_rinv g0 (A0 + &2))`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[bounded; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "cpt" (MP_TAC o SPEC `\y:real^3. lift(lgrad2 g0 (p2cn_phi g0 A0) y)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC P2CN_LGRAD2_CONTINUOUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` (LABEL_TAC "B1")) THEN
  USE_THEN "cpt" (MP_TAC o SPEC `\y:real^3. lift(llap g0 (p2cn_phi g0 A0) y)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC P2CN_LLAP_CONTINUOUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` (LABEL_TAC "B2")) THEN
  EXISTS_TAC `max (max B1 B2) K1` THEN X_GEN_TAC `x:real^3` THEN
  ASM_CASES_TAC `norm(x:real^3) <= p3s_rad_rinv g0 (A0 + &2)` THENL
   [SUBGOAL_THEN `(x:real^3) IN cball(vec 0,p3s_rad_rinv g0 (A0 + &2))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_CBALL_0]; ALL_TAC] THEN
    USE_THEN "B1" (MP_TAC o C MP
      (ASSUME `(x:real^3) IN cball(vec 0,p3s_rad_rinv g0 (A0 + &2))`) o SPEC `x:real^3`) THEN
    USE_THEN "B2" (MP_TAC o C MP
      (ASSUME `(x:real^3) IN cball(vec 0,p3s_rad_rinv g0 (A0 + &2))`) o SPEC `x:real^3`) THEN
    REWRITE_TAC[NORM_LIFT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `A0 + &2 < p3_std_dist g0 (x:real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &2`; `x:real^3`]
                  P2CN_DIST_COMPARE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P2CN_PHI_FAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)) THEN
  USE_THEN "K1" (MP_TAC o C MP (ASSUME `~(p3_std_nc g0 A0 (x:real^3) = vec 0)`) o
                 SPEC `p3_std_nc g0 A0 (x:real^3)`) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The chart conversions of the open set atlas of R^3, the                  *)
(* sublevel sets of phi are compact, their volumes grow at most             *)
(* exponentially (Bishop-Gromov with sec >= 0: a geodesic ball of radius r  *)
(* has volume at most 4 pi r^3 / 3), and the theorem P2CN_STD_BOUNDED_GEOM. *)
(* ------------------------------------------------------------------------- *)

let P2CN_OPEN_UNIV_CHART = prove
 (`!x:real^3. chart_at (open_set_atlas (:real^3)) x = ((:real^3),(\x. x)) /\
              chart_inv ((:real^3),(\x:real^3. x)) = (\x. x)`,
  REWRITE_TAC[FUN_EQ_THM] THEN SIMP_TAC[RFB_OPEN_SET_CHART_AT; MFDM_CHART_INV_ID; IN_UNIV]);;

let P2CN_OPEN_UNIV_CONV = prove
 (`!(g:real^3->real^3^3) f l x.
     p2c_fgrad2 (open_set_atlas (:real^3)) g f x = lgrad2 g f x /\
     p2c_flap (open_set_atlas (:real^3)) g f x = llap g f x /\
     lrm_deriv_norm2 l (metric_local (open_set_atlas (:real^3))
                          (chart_at (open_set_atlas (:real^3)) x) g)
                       (SND(chart_at (open_set_atlas (:real^3)) x) x) =
     lrm_deriv_norm2 l g x`,
  REWRITE_TAC[p2c_fgrad2; p2c_flap; P2CN_OPEN_UNIV_CHART; P2C_OPEN_SET_METRIC_LOCAL_UNIV;
              SND] THEN
  REWRITE_TAC[o_DEF; ETA_AX]);;

let P2CN_MFD_SMOOTH_UNIV = prove
 (`!f:real^3->real^1. smooth_map_on (:real^3) f ==> mfd_smooth (open_set_atlas (:real^3)) f`,
  REWRITE_TAC[mfd_smooth; RFB_OPEN_SET_ATLAS_CASES; FORALL_UNWIND_THM2; FST; SND; IMAGE_ID;
              P2CN_OPEN_UNIV_CHART] THEN
  REWRITE_TAC[o_DEF; ETA_AX]);;

(* The sublevel sets of phi are compact and lie in sublevel sets of d. *)

let P2CN_PHI_SUBLEVEL = prove
 (`!g0 A0 c. p3_std_initial g0 A0
             ==> compact {x:real^3 | p2cn_phi g0 A0 x <= c} /\
                 {x:real^3 | p2cn_phi g0 A0 x <= c} SUBSET {x | p3_std_dist g0 x <= c}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2CN_PHI_SMOOTH) THEN
  SUBGOAL_THEN `{x:real^3 | p2cn_phi g0 A0 x <= c} SUBSET {x | p3_std_dist g0 x <= c}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P2CN_PHI_VALUES) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `cball(vec 0:real^3,p3s_rad_rinv g0 (abs c))` THEN
    REWRITE_TAC[BOUNDED_CBALL; SUBSET; IN_CBALL_0; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `abs c`; `x:real^3`]
                  P2CN_DIST_COMPARE) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2 th))]) THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P2CN_PHI_VALUES) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`\x:real^3. lift(p2cn_phi g0 A0 x)`; `{y:real^1 | y$1 <= c}`]
                  CONTINUOUS_CLOSED_PREIMAGE_UNIV) THEN
    REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE; IN_ELIM_THM; GSYM drop; LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON
             (ASSUME `smooth_map_on (:real^3) (\x. lift(p2cn_phi g0 A0 x))`)) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]]);;

(* Volume growth: {phi <= s} is empty below A0 + 3 and otherwise lies in the *)
(* geodesic ball of radius s + 1 about the tip.                             *)

let P2CN_PHI_VOLUME = prove
 (`!g0 A0 s v.
     p3_std_initial g0 A0 /\
     mfd_has_volume (euclidean,open_set_atlas (:real^3)) g0
                    {x:real^3 | p2cn_phi g0 A0 x <= s} v
     ==> v <= &36 * pi * exp(s + &1) /\ (s < A0 + &3 ==> v = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `p3_std_initial g0 A0`) THEN REWRITE_TAC[p3_std_initial] THEN STRIP_TAC THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] P2C_EUCLID_FACTS) THEN STRIP_TAC THEN
  ASM_CASES_TAC `s < A0 + &3` THENL
   [SUBGOAL_THEN `{x:real^3 | p2cn_phi g0 A0 x <= s} = {}` ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^3` THEN
      MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P2CN_PHI_VALUES) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `mfd_has_volume (euclidean,open_set_atlas (:real^3)) g0
                   {x:real^3 | p2cn_phi g0 A0 x <= s} v` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `v = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                            `g0:real^3->real^3^3`; `{}:real^3->bool`]
                           MFD_HAS_VOLUME_UNIQUE) THEN
      ASM_REWRITE_TAC[MFD_HAS_VOLUME_EMPTY];
      REWRITE_TAC[] THEN SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_EXP_POS_LE; PI_POS_LE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < s + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `B = mfd_ball (euclidean,open_set_atlas (:real^3)) g0 (vec 0:real^3) (s + &1)` THEN
  SUBGOAL_THEN `{x:real^3 | p2cn_phi g0 A0 x <= s} SUBSET B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; mfd_ball; P2C_RAD_JOINABLE; GSYM p3_std_dist] THEN
    X_GEN_TAC `x:real^3` THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P2CN_PHI_VALUES) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact_in euclidean
      (mfd_cball (euclidean,open_set_atlas (:real^3)) g0 (vec 0:real^3) (s + &1))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_complete (euclidean,open_set_atlas (:real^3)) g0` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `g0:real^3->real^3^3`;
                 `mfd_cball (euclidean,open_set_atlas (:real^3)) g0 (vec 0:real^3) (s + &1)`]
                MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `g0:real^3->real^3^3`;
                 `B:real^3->bool`;
                 `mfd_cball (euclidean,open_set_atlas (:real^3)) g0 (vec 0:real^3) (s + &1)`;
                 `w:real`] MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "B" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "B" THEN REWRITE_TAC[SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN
      SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `mfd_volume (euclidean,open_set_atlas (:real^3)) g0 (B:real^3->bool) <=
                &4 / &3 * pi * (s + &1) pow 3`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^3)` CMP_T3_BISHOP_GROMOV_P2B) THEN
    REWRITE_TAC[CMP_T3_BISHOP_GROMOV_P2B_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `g0:real^3->real^3^3`;
      `vec 0:real^3`; `s + &1`; `s + &1`;
      `mfd_volume (euclidean,open_set_atlas (:real^3)) g0 (B:real^3->bool)`;
      `mfd_volume (euclidean,open_set_atlas (:real^3)) g0 (B:real^3->bool)`]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `v <= mfd_volume (euclidean,open_set_atlas (:real^3)) g0 (B:real^3->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                          `g0:real^3->real^3^3`; `{x:real^3 | p2cn_phi g0 A0 x <= s}`;
                          `B:real^3->bool`] MFD_HAS_VOLUME_MONO) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`3`; `s + &1`] CUTOFF_POW_LE_EXP) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_RAT_REDUCE_CONV `&3 pow 3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `pi * (s + &1) pow 3 <= pi * (&27 * exp(s + &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[PI_POS_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The theorem. *)

let P2CN_STD_BOUNDED_GEOM = prove
 (`P2C_STD_BOUNDED_GEOM_STATEMENT`,
  REWRITE_TAC[P2C_STD_BOUNDED_GEOM_STATEMENT; P2CN_OPEN_UNIV_CONV] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP P2CN_STD_RMD_BOUND); ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2CN_PHI_SMOOTH) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Kb:real` (LABEL_TAC "Kb") o MATCH_MP P2CN_PHI_GRAD_LAP_BOUND) THEN
  MAP_EVERY EXISTS_TAC [`p2cn_phi g0 A0`; `max (max Kb (&2)) (&36 * pi)`] THEN
  ABBREV_TAC `C = max (max Kb (&2)) (&36 * pi)` THEN
  SUBGOAL_THEN `Kb <= C /\ &2 <= C /\ &36 * pi <= C` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CN_MFD_SMOOTH_UNIV THEN REWRITE_TAC[o_DEF] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `c:real` THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`] P2CN_PHI_SUBLEVEL) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^3` THEN USE_THEN "Kb" (MP_TAC o SPEC `x:real^3`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `v:real`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`; `v:real`] P2CN_PHI_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s < A0 + &3` THENL
   [SUBGOAL_THEN `v = &0` SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&36 * pi * exp(s + &1)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
  CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (C - &2) * s` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

