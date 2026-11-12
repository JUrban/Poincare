(* ========================================================================= *)
(* Unit pc_cmw_pos: CMW_POS_STATEMENT (pc_cmw_defs) from CM_REPLACEMENT and  *)
(* WAN_S2_STEREO: sweepouts of small energy with C^1 slices are homotopic to *)
(* sweepouts with constant slices (CM after Cor 3.4: replacement on          *)
(* shrinking discs, a C^0 estimate from the continuity of replacement        *)
(* against reflected data, and the straight-line contraction).               *)
(*                                                                           *)
(* Dirichlet integrals of C^1 planar maps on balls.                          *)
(* ========================================================================= *)

needs "src/pc_cmw_defs.ml";;
needs "src/pc_an_beltrami.ml";;

prioritize_real();;
type_invention_error := true;;

let CMW_CONT_LSPACE_CBALL = prove
 (`!(f:real^N->real^K) a r.
        f continuous_on cball(a,r) ==> f IN lspace (ball(a,r)) (&2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_BOUNDED_MEASURABLE_SIMPLE THEN
  REWRITE_TAC[MEASURABLE_BALL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; BALL_SUBSET_CBALL];
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (f:real^N->real^K) (cball(a,r))` THEN
    SIMP_TAC[IMAGE_SUBSET; BALL_SUBSET_CBALL] THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_CBALL]]);;

(* C^1 maps on the plane: W^{1,2} on every ball, with the classical partial *)
(* derivatives as weak partials, and the classical Dirichlet integrals.     *)

let CMW_C1_PARTIAL_CONT = prove
 (`!(u:real^N->real^K) i.
        continuously_differentiable 1 (:real^N) u
        ==> (\x. partial_derivative i u x) continuous_on (:real^N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  MP_TAC(ISPECL [`0`; `(:real^N)`; `u:real^N->real^K`] CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; GSYM ONE] THEN
  DISCH_THEN(MP_TAC o SPEC `basis i:real^N`) THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0]);;

let CMW_C1_BALL = prove
 (`!(u:real^N->real^K) (G:real^K->real^K^K) a r.
        continuously_differentiable 1 (:real^N) u /\ &0 < r
        ==> wan_w12 (ball(a,r)) u /\
            (!i. 1 <= i /\ i <= dimindex(:N)
                 ==> wan_wpd (ball(a,r)) i u (\x. partial_derivative i u x)) /\
            wan_dir (ball(a,r)) u =
            sum(1..dimindex(:N))
              (\i. drop(integral (ball(a,r)) (\x. lift(norm(partial_derivative i u x) pow 2)))) /\
            wan_gdir (ball(a,r)) G u =
            sum(1..dimindex(:N))
              (\i. drop(integral (ball(a,r))
                     (\x. lift(partial_derivative i u x dot
                               (G(u x) ** partial_derivative i u x)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:N)`; `(:K)`] WAN_W12_C1) THEN REWRITE_TAC[WAN_W12_C1_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`ball(a:real^N,r)`; `u:real^N->real^K`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
      EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC CMW_CONT_LSPACE_CBALL THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
      EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CMW_CONT_LSPACE_CBALL THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; CMW_C1_PARTIAL_CONT]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wan_gdir] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | x IN ball(a:real^N,r) /\
                   ~(wan_wd (ball(a,r)) i (u:real^N->real^K) x =
                     partial_derivative i u x)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_WD_UNIQUE THEN ASM_SIMP_TAC[OPEN_BALL];
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]]);;

let CMW_CONT_INTEGRABLE_COMPACT = prove
 (`!(f:real^M->real^N) k.
        f continuous_on k /\ compact k
        ==> f absolutely_integrable_on k /\ f integrable_on k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  SUBGOAL_THEN `bounded (IMAGE (f:real^M->real^N) k)` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE]] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real^M. lift B` THEN
  ASM_SIMP_TAC[LIFT_DROP; INTEGRABLE_ON_CONST; MEASURABLE_COMPACT] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT]);;

let CMW_CONT_INTEGRABLE_BALL = prove
 (`!(f:real^M->real^N) a r.
        f continuous_on cball(a,r)
        ==> f absolutely_integrable_on ball(a,r) /\ f integrable_on ball(a,r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `cball(a:real^M,r)` THEN
  REWRITE_TAC[BALL_SUBSET_CBALL; LEBESGUE_MEASURABLE_BALL] THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `cball(a:real^M,r)`] CMW_CONT_INTEGRABLE_COMPACT) THEN
  ASM_SIMP_TAC[COMPACT_CBALL]);;

let CMW_CONT_INTEGRABLE_BALL_INT = prove
 (`!(f:real^M->real^N) a r.
        f continuous_on cball(a,r) ==> f integrable_on ball(a,r)`,
  MESON_TAC[CMW_CONT_INTEGRABLE_BALL]);;

(* The G-energy of a C^1 map on a ball is at most Lam times its Dirichlet  *)
(* integral.                                                                *)

let CMW_C1_GDIR_LE = prove
 (`!(u:real^N->real^K) (G:real^K->real^K^K) a r Lam.
        continuously_differentiable 1 (:real^N) u /\ &0 < r /\
        (vectorize:real^K^K->real^(K,K)finite_prod) o G continuous_on (:real^K) /\
        (!z v. v dot (G z ** v) <= Lam * norm v pow 2)
        ==> wan_gdir (ball(a,r)) G u <= Lam * wan_dir (ball(a,r)) u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^N->real^K`; `G:real^K->real^K^K`; `a:real^N`; `r:real`]
                CMW_C1_BALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `(\x. partial_derivative i (u:real^N->real^K) x) continuous_on (:real^N)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[CMW_C1_PARTIAL_CONT]; ALL_TAC] THEN
  SUBGOAL_THEN `partial_derivative i (u:real^N->real^K) continuous_on (:real^N)`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `(\x. partial_derivative i (u:real^N->real^K) x) continuous_on (:real^N)`) THEN
    REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->real^K) continuous_on (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(partial_derivative i (u:real^N->real^K) x dot
              ((G:real^K->real^K^K)(u x) ** partial_derivative i u x)))
    continuous_on cball(a,r) /\
    (\x. lift(norm(partial_derivative i (u:real^N->real^K) x) pow 2)) continuous_on cball(a,r)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[SUBSET_UNIV] THENL
     [MATCH_MP_TAC CMT_CONT_QUAD THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[NORM_POW_2] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `drop(integral (ball(a,r))
           (\x. Lam % lift(norm(partial_derivative i (u:real^N->real^K) x) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[CMW_CONT_INTEGRABLE_BALL];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_SIMP_TAC[CMW_CONT_INTEGRABLE_BALL];
      REPEAT STRIP_TAC THEN REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[INTEGRAL_CMUL; CMW_CONT_INTEGRABLE_BALL; DROP_CMUL; REAL_LE_REFL]]);;

(* Scaling: the Dirichlet integral of x |-> u(c x) on the unit ball is that *)
(* of u on ball(0,c) (two dimensions).                                      *)

let CMW_PARTIAL_SCALE = prove
 (`!(u:real^N->real^K) c i x.
        u differentiable at (c % x)
        ==> partial_derivative i (\x. u(c % x)) x = c % partial_derivative i u (c % x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. (u:real^N->real^K)(c % x)) = u o (\x. c % x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_CHAIN o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFFERENTIABLE_CMUL THEN
    REWRITE_TAC[DIFFERENTIABLE_ID];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `partial_derivative i (\x:real^N. c % x) x = c % basis i` SUBST1_TAC THENL
   [REWRITE_TAC[partial_derivative] THEN
    MP_TAC(ISPECL [`\x:real^N. c % x`; `\h:real^N. c % h`; `x:real^N`] FRECHET_DERIVATIVE_AT) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_DERIVATIVE_ID];
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[partial_derivative] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL
    (MATCH_MP LINEAR_FRECHET_DERIVATIVE th)]));;

let CMW_C1_DIFFERENTIABLE = prove
 (`!(u:real^N->real^K) x.
        continuously_differentiable 1 (:real^N) u ==> u differentiable at x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1; WITHIN_UNIV; IN_UNIV] THEN
  MESON_TAC[differentiable]);;

let CMW_IMAGE_SCALE_BALL = prove
 (`!c. &0 < c ==> IMAGE (\x:real^N. inv c % x) (ball(vec 0,c)) = ball(vec 0,&1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0; IN_IMAGE; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < c ==> abs c = c`] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_MUL_LID];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `c % x:real^N` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]]);;

let CMW_INTEGRAL_SCALE_BALL = prove
 (`!(f:real^2->real^1) c.
        &0 < c /\ f integrable_on ball(vec 0,c)
        ==> integral (ball(vec 0,&1)) (\x. f(c % x)) =
            inv(c pow 2) % integral (ball(vec 0,c)) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MP_TAC(ISPECL [`f:real^2->real^1`; `integral (ball(vec 0:real^2,c)) (f:real^2->real^1)`;
                 `ball(vec 0:real^2,c)`; `c:real`; `vec 0:real^2`] HAS_INTEGRAL_AFFINITY) THEN
  ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_ADD_RID; VECTOR_MUL_RZERO; VECTOR_NEG_0; DIMINDEX_2] THEN
  ASM_SIMP_TAC[CMW_IMAGE_SCALE_BALL; REAL_ARITH `&0 < c ==> abs c = c`] THEN
  REWRITE_TAC[ETA_AX]);;

let CMW_C1_DIR_SCALE = prove
 (`!(u:real^2->real^K) c.
        continuously_differentiable 1 (:real^2) u /\ &0 < c
        ==> wan_dir (ball(vec 0,&1)) (\x. u(c % x)) = wan_dir (ball(vec 0,c)) u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^2) (\x. (u:real^2->real^K)(c % x))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. (u:real^2->real^K)(c % x)) = u o (\x. c % x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; linear] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (u:real^2->real^K)(c % x)`; `(\z. mat 1):real^K->real^K^K`;
                 `vec 0:real^2`; `&1`] CMW_C1_BALL) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `(\z. mat 1):real^K->real^K^K`;
                 `vec 0:real^2`; `c:real`] CMW_C1_BALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `!x. partial_derivative i (\x. (u:real^2->real^K)(c % x)) x =
        c % partial_derivative i u (c % x)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC CMW_PARTIAL_SCALE THEN ASM_SIMP_TAC[CMW_C1_DIFFERENTIABLE];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_POW2_ABS; LIFT_CMUL] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(partial_derivative i (u:real^2->real^K) x) pow 2)) integrable_on
    ball(vec 0,c)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMW_CONT_INTEGRABLE_BALL_INT THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV; NORM_POW_2] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    ASM_SIMP_TAC[CMW_C1_PARTIAL_CONT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(norm(partial_derivative i (u:real^2->real^K) x) pow 2)`;
                 `c:real`] CMW_INTEGRAL_SCALE_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_CMUL o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC CMW_CONT_INTEGRABLE_BALL_INT THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV; NORM_POW_2] THEN
    SUBGOAL_THEN
     `(\x. partial_derivative i (u:real^2->real^K) (c % x)) continuous_on (:real^2)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\x:real^2. c % x`; `\x. partial_derivative i (u:real^2->real^K) x`;
                     `(:real^2)`] (REWRITE_RULE[o_DEF] CONTINUOUS_ON_COMPOSE)) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; CMW_C1_PARTIAL_CONT];
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[DROP_CMUL; VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `~(c pow 2 = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_MUL_LID]);;

(* For a C^1 map of the plane with weak partials in L^2(R^2), the Dirichlet *)
(* integral on a ball is at most the one on the plane.                      *)

let CMW_C1_DIR_MONO_UNIV = prove
 (`!(u:real^2->real^K) a r.
        continuously_differentiable 1 (:real^2) u /\ &0 < r /\
        (!i. 1 <= i /\ i <= 2
             ==> ?v. v IN lspace (:real^2) (&2) /\ wan_wpd (:real^2) i u v)
        ==> wan_dir (ball(a,r)) u <= wan_dir (:real^2) u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `(\z. mat 1):real^K->real^K^K`;
                 `a:real^2`; `r:real`] CMW_C1_BALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wan_dir; DIMINDEX_2] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `(:real^2)`)) (concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "lspace")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `wan_wd (:real^2) i (u:real^2->real^K) IN lspace (:real^2) (&2) /\
    wan_wpd (:real^2) i u (wan_wd (:real^2) i u)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[wan_wd] THEN CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `negligible {x | x IN (:real^2) /\
                    ~(wan_wd (:real^2) i (u:real^2->real^K) x = partial_derivative i u x)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_WPD_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `u:real^2->real^K`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN
    MP_TAC(ISPECL [`(:real^2)`; `u:real^2->real^K`; `i:num`] WAN_WPD_C1) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(wan_wd (:real^2) i (u:real^2->real^K) x) pow 2)) integrable_on (:real^2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN (:real^2) DIFF
            {x | x IN (:real^2) /\
                 ~(wan_wd (:real^2) i (u:real^2->real^K) x = partial_derivative i u x)}
        ==> lift(norm(partial_derivative i u x) pow 2) =
            lift(norm(wan_wd (:real^2) i u x) pow 2)`
  ASSUME_TAC THENL [REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(partial_derivative i (u:real^2->real^K) x) pow 2)) integrable_on (:real^2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
    EXISTS_TAC `\x. lift(norm(wan_wd (:real^2) i (u:real^2->real^K) x) pow 2)` THEN
    EXISTS_TAC
     `{x | x IN (:real^2) /\
           ~(wan_wd (:real^2) i (u:real^2->real^K) x = partial_derivative i u x)}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^2) (\x. lift(norm(wan_wd (:real^2) i (u:real^2->real^K) x) pow 2)) =
    integral (:real^2) (\x. lift(norm(partial_derivative i u x) pow 2))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC
     `{x | x IN (:real^2) /\
           ~(wan_wd (:real^2) i (u:real^2->real^K) x = partial_derivative i u x)}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  MATCH_MP_TAC CMW_CONT_INTEGRABLE_BALL_INT THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[SUBSET_UNIV; NORM_POW_2] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN ASM_SIMP_TAC[CMW_C1_PARTIAL_CONT]);;

(* ========================================================================= *)
(* Maps of S^2 with C^1 radial extension: the shell Dirichlet                *)
(* integral, its bound by the energy, and its invariance under the          *)
(* reflection bel_refl3 (which turns stereo2_n_inv into stereo2_s_inv).     *)
(* ========================================================================= *)

let CMW_S2_C1_DIR = prove
 (`!(u:real^3->real^K).
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u)
        ==> wan_s2_w12 u /\
            wan_s2_dir u =
            &2 / &3 * sum(1..3) (\i. drop(integral wan_shell
                                   (\x. lift(norm(partial_derivative i (wan_rext u) x) pow 2))))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (u:real^3->real^K)`] CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:3)`; `(:K)`] WAN_W12_C1) THEN REWRITE_TAC[WAN_W12_C1_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`wan_shell`; `wan_rext (u:real^3->real^K)`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CMT_SHELL_OPEN] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; wan_shell] THEN GEN_TAC THEN
      DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CMT_CONT_LSPACE_SHELL THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CMT_CONT_LSPACE_SHELL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[wan_s2_w12; wan_s2_dir]);;

let CMW_S2_DIR_LE_SEN = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) lam.
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
        smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
        (!z v. lam * norm v pow 2 <= v dot (G z ** v))
        ==> lam * wan_s2_dir u <= &2 * cm_sen G u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `u:real^3->real^K` CMW_S2_C1_DIR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`] CMT_SEN_SHELL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (u:real^3->real^K)`] CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ETA_AX]) THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K))
    continuous_on (:real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `0` THEN
    UNDISCH_TAC `smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G)` THEN
    SIMP_TAC[smooth_map_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(vec 0 IN wan_shell)` ASSUME_TAC THENL
   [REWRITE_TAC[wan_shell; IN_ELIM_THM; NORM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `wan_shell SUBSET {z:real^3 | ~(z = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN wan_shell
        ==> lam * sum(1..3) (\i. norm(partial_derivative i (wan_rext (u:real^3->real^K)) x)
                                 pow 2) <=
            trace(transp(jacobian (wan_rext u) (at x)) ** G(wan_rext u x) **
                  jacobian (wan_rext u) (at x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[trace; DIMINDEX_3; GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[CMT_GRAM_ENTRY; DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(trace(transp(jacobian (wan_rext (u:real^3->real^K)) (at x)) **
                    (G:real^K->real^K^K)(wan_rext u x) ** jacobian (wan_rext u) (at x))))
    continuous_on {z:real^3 | ~(z = vec 0)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC
     `\x. lift(sum(1..3) (\i. partial_derivative i (wan_rext (u:real^3->real^K)) x dot
                             ((G:real^K->real^K^K)(wan_rext u x) **
                              partial_derivative i (wan_rext u) x)))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[trace; DIMINDEX_3] THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
      ASM_SIMP_TAC[CMT_GRAM_ENTRY; DIMINDEX_3];
      REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC CMT_CONT_QUAD THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (\x. lift(norm(partial_derivative i (wan_rext (u:real^3->real^K)) x) pow 2))
        continuous_on {z:real^3 | ~(z = vec 0)}`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `lam * a <= b ==> lam * (&2 / &3 * a) <= &2 * (b / &3)`) THEN
  SUBGOAL_THEN
   `sum(1..3) (\i. drop(integral wan_shell
                    (\x. lift(norm(partial_derivative i (wan_rext (u:real^3->real^K)) x)
                              pow 2)))) =
    drop(integral wan_shell
          (\x. lift(sum(1..3) (\i. norm(partial_derivative i (wan_rext u) x) pow 2))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIFT_SUM; o_DEF] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_VSUM o rand o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC CMT_CONT_ABSINT_SHELL THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_VSUM; o_DEF]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(sum(1..3) (\i. norm(partial_derivative i (wan_rext (u:real^3->real^K)) x)
                             pow 2))) continuous_on {z:real^3 | ~(z = vec 0)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DROP_CMUL] THEN
  W(MP_TAC o PART_MATCH (rand o rand) INTEGRAL_CMUL o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC CMT_CONT_ABSINT_SHELL THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC CMT_CONT_ABSINT_SHELL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC CMT_CONT_ABSINT_SHELL THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN ASM_SIMP_TAC[]]);;

let CMW_REFL3_FACTS = prove
 (`(!z:real^3. norm(bel_refl3 z) = norm z) /\
   (!z:real^3. ~(bel_refl3 z = vec 0) <=> ~(z = vec 0)) /\
   (!c z:real^3. bel_refl3(c % z) = c % bel_refl3 z) /\
   (!z:real^3. bel_refl3(bel_refl3 z) = z) /\
   IMAGE bel_refl3 wan_shell = wan_shell /\
   abs(det(matrix bel_refl3)) = &1 /\
   (!i. 1 <= i /\ i <= 3
        ==> bel_refl3(basis i) = (if i = 3 then --(basis 3) else basis i))`,
  SUBGOAL_THEN `!z:real^3. norm(bel_refl3 z) = norm z` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_EQ; BEL_REFL3_DOT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[];
    MESON_TAC[BEL_REFL3_LINEAR; LINEAR_CMUL];
    REWRITE_TAC[BEL_REFL3_DOT];
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; wan_shell; IN_ELIM_THM; IN_IMAGE] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `bel_refl3 z` THEN ASM_REWRITE_TAC[BEL_REFL3_DOT];
    SIMP_TAC[matrix; DET_3; LAMBDA_BETA; DIMINDEX_3; ARITH; BEL_REFL3_COMPONENTS;
             BASIS_COMPONENT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; BEL_REFL3_COMPONENTS; BASIS_COMPONENT;
             VECTOR_NEG_COMPONENT; ARITH] THEN
    REAL_ARITH_TAC]);;

let CMW_S2_DIR_REFL = prove
 (`!(u:real^3->real^K).
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u)
        ==> continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
              (wan_rext (u o bel_refl3)) /\
            wan_s2_dir (u o bel_refl3) = wan_s2_dir u`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `wan_rext ((u:real^3->real^K) o bel_refl3) = wan_rext u o bel_refl3`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; wan_rext; CMW_REFL3_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
      (wan_rext ((u:real^3->real^K) o bel_refl3))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM;
                    CMW_REFL3_FACTS] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
    REWRITE_TAC[CMT_OPEN_NONZERO; BEL_REFL3_LINEAR];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `(u:real^3->real^K) o bel_refl3` CMW_S2_C1_DIR) THEN
  MP_TAC(ISPEC `u:real^3->real^K` CMW_S2_C1_DIR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (u:real^3->real^K)`] CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ETA_AX]) THEN
  SUBGOAL_THEN
   `!z:real^3. ~(z = vec 0)
        ==> norm(partial_derivative i (wan_rext (u:real^3->real^K) o bel_refl3) z) pow 2 =
            norm(partial_derivative i (wan_rext u) (bel_refl3 z)) pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`i:num`; `bel_refl3`; `wan_rext (u:real^3->real^K)`; `z:real^3`]
                  PARTIAL_DERIVATIVE_CHAIN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_LINEAR THEN REWRITE_TAC[BEL_REFL3_LINEAR];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[CMW_REFL3_FACTS]];
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `partial_derivative i bel_refl3 z = bel_refl3(basis i)` SUBST1_TAC THENL
     [REWRITE_TAC[partial_derivative] THEN
      MP_TAC(ISPECL [`bel_refl3`; `bel_refl3`; `z:real^3`] FRECHET_DERIVATIVE_AT) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[BEL_REFL3_LINEAR];
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(SPEC `i:num` (last(CONJUNCTS CMW_REFL3_FACTS))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `linear(frechet_derivative (wan_rext (u:real^3->real^K)) (at (bel_refl3 z)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[CMW_REFL3_FACTS];
      COND_CASES_TAC THEN REWRITE_TAC[partial_derivative] THEN
      ASM_SIMP_TAC[LINEAR_NEG; NORM_NEG]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `integral wan_shell
      ((\x. lift(norm(partial_derivative i (wan_rext (u:real^3->real^K)) x) pow 2)) o
       bel_refl3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[wan_shell; IN_ELIM_THM] THEN
    DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(norm(partial_derivative i (wan_rext (u:real^3->real^K)) x) pow 2)`;
                 `bel_refl3`; `wan_shell`] INTEGRAL_CHANGE_OF_VARIABLES_LINEAR) THEN
  REWRITE_TAC[BEL_REFL3_LINEAR; CMW_REFL3_FACTS; VECTOR_MUL_LID] THEN
  ANTS_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC CMT_CONT_ABSINT_SHELL THEN
    REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    ASM_REWRITE_TAC[ETA_AX];
    SIMP_TAC[]]);;

(* Planar pictures of a map of S^2 with C^1 radial extension, through the  *)
(* chart stereo2_n_inv composed with a dilation: C^1, and the Dirichlet and *)
(* G-energies on the unit ball are bounded by the energy on S^2.             *)

let CMW_P_SCALED_C1 = prove
 (`!(u:real^3->real^K) c.
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u)
        ==> continuously_differentiable 1 (:real^2) (\x. u(stereo2_n_inv x)) /\
            continuously_differentiable 1 (:real^2) (\x. u(stereo2_n_inv(c % x)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^2) (\x. (u:real^3->real^K)(stereo2_n_inv x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
    EXISTS_TAC `wan_rext (u:real^3->real^K) o stereo2_n_inv` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV; o_THM] THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC CM_REXT_SPHERE THEN
      REWRITE_TAC[IN_SPHERE_0; BEL_P_CHART];
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; CMT_OPEN_NONZERO; SUBSET; FORALL_IN_IMAGE; IN_UNIV;
                      IN_ELIM_THM] THEN
      CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[GSYM NORM_EQ_0; BEL_P_CHART] THEN REAL_ARITH_TAC;
        MP_TAC STEX_STEREO2_N_INV_SMOOTH THEN SIMP_TAC[smooth_map_on]]];
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\x. (u:real^3->real^K)(stereo2_n_inv(c % x))) = (\x. u(stereo2_n_inv x)) o (\x. c % x)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC]);;

let CMW_P_SCALED_ENERGY = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) c lam Lam.
        WAN_S2_STEREO_STATEMENT (:K) /\
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
        smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
        &0 < lam /\
        (!z v. lam * norm v pow 2 <= v dot (G z ** v)) /\
        (!z v. v dot (G z ** v) <= Lam * norm v pow 2) /\ &0 < c
        ==> wan_dir (ball(vec 0,&1)) (\x. u(stereo2_n_inv(c % x))) <= &2 / lam * cm_sen G u /\
            wan_gdir (ball(vec 0,&1)) G (\x. u(stereo2_n_inv(c % x)))
            <= Lam * (&2 / lam * cm_sen G u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `c:real`] CMW_P_SCALED_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `wan_dir (ball(vec 0,&1)) (\x. (u:real^3->real^K)(stereo2_n_inv(c % x))) <=
    &2 / lam * cm_sen G u`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. (u:real^3->real^K)(stereo2_n_inv x)`; `c:real`] CMW_C1_DIR_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `WAN_S2_STEREO_STATEMENT (:K)` THEN
    REWRITE_TAC[WAN_S2_STEREO_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^3->real^K` o CONJUNCT1) THEN
    MP_TAC(ISPEC `u:real^3->real^K` CMW_S2_C1_DIR) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    TRANS_TAC REAL_LE_TRANS `wan_dir (:real^2) (\y. (u:real^3->real^K)(stereo2_n_inv y))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMW_C1_DIR_MONO_UNIV THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `lam:real`]
                    CMW_S2_DIR_LE_SEN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ (ASSUME `&0 < lam`))] THEN
      SUBGOAL_THEN `lam * (&2 / lam * cm_sen G (u:real^3->real^K)) = &2 * cm_sen G u`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  TRANS_TAC REAL_LE_TRANS
   `Lam * wan_dir (ball(vec 0,&1)) (\x. (u:real^3->real^K)(stereo2_n_inv(c % x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMW_C1_GDIR_LE THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `0` THEN
    UNDISCH_TAC `smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G)` THEN
    SIMP_TAC[smooth_map_on];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^K`; `basis 1:real^K`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^K`; `basis 1:real^K`]) THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN ASM_REAL_ARITH_TAC]);;

let CMW_P_SCALED_DIR_S2 = prove
 (`!(u:real^3->real^K) c.
        WAN_S2_STEREO_STATEMENT (:K) /\
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\ &0 < c
        ==> wan_dir (ball(vec 0,&1)) (\x. u(stereo2_n_inv(c % x))) <= wan_s2_dir u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `c:real`] CMW_P_SCALED_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (u:real^3->real^K)(stereo2_n_inv x)`; `c:real`] CMW_C1_DIR_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `WAN_S2_STEREO_STATEMENT (:K)` THEN
  REWRITE_TAC[WAN_S2_STEREO_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `u:real^3->real^K` o CONJUNCT1) THEN
  MP_TAC(ISPEC `u:real^3->real^K` CMW_S2_C1_DIR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CMW_C1_DIR_MONO_UNIV THEN ASM_REWRITE_TAC[]);;

let CMW_Q_SCALED = prove
 (`!(u:real^3->real^K) c.
        WAN_S2_STEREO_STATEMENT (:K) /\
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\ &0 < c
        ==> continuously_differentiable 1 (:real^2) (\x. u(stereo2_s_inv(c % x))) /\
            wan_dir (ball(vec 0,&1)) (\x. u(stereo2_s_inv(c % x))) <= wan_s2_dir u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `u:real^3->real^K` CMW_S2_DIR_REFL) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. (u:real^3->real^K)(stereo2_s_inv(c % x))) =
    (\x. (u o bel_refl3)(stereo2_n_inv(c % x)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; BEL_Q_FORM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(u:real^3->real^K) o bel_refl3`; `c:real`] CMW_P_SCALED_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  MATCH_MP_TAC CMW_P_SCALED_DIR_S2 THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Constants, positivity of the G-energy, and the C^0 estimate               *)
(* for small-energy minimizers (from the continuity clause of               *)
(* CM_REPLACEMENT by compactness: the limit data and minimizer are a        *)
(* constant).                                                               *)
(* ========================================================================= *)

let CMW_MEASURABLE_COMPOSE_CONT = prove
 (`!(h:real^K->real^P) (w:real^N->real^K) s.
        lebesgue_measurable s /\ w measurable_on s /\ h continuous_on (:real^K)
        ==> (\x. h(w x)) measurable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (h:real^K->real^P)((w:real^N->real^K) x)) =
                (\x. (\z. h z - h(vec 0)) (w x) + h(vec 0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_ADD THEN
  ASM_REWRITE_TAC[MEASURABLE_ON_CONST_EQ] THEN
  MP_TAC(ISPECL [`w:real^N->real^K`; `\z. (h:real^K->real^P) z - h(vec 0)`; `s:real^N->bool`]
                MEASURABLE_ON_COMPOSE_CONTINUOUS_0) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; VECTOR_SUB_REFL; o_DEF]);;

let CMW_GDIR_INTEGRAND = prove
 (`!s (G:real^K->real^K^K) (w:real^N->real^K) Lam i.
        open s /\ wan_w12 s w /\ 1 <= i /\ i <= dimindex(:N) /\
        ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
        (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2)
        ==> (\x. lift(wan_wd s i w x dot (G(w x) ** wan_wd s i w x))) integrable_on s /\
            &0 <= drop(integral s (\x. lift(wan_wd s i w x dot (G(w x) ** wan_wd s i w x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `w:real^N->real^K`] WAN_WD_WORKS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lebesgue_measurable(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N->real^K) measurable_on s /\
                wan_wd s i w measurable_on s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `wan_w12 s (w:real^N->real^K)` THEN
    UNDISCH_TAC `wan_wd s i (w:real^N->real^K) IN lspace s (&2)` THEN
    REWRITE_TAC[wan_w12; LSPACE_ALT; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(wan_wd s i (w:real^N->real^K) x dot
              ((G:real^K->real^K^K)(w x) ** wan_wd s i w x))) measurable_on s`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\a b:real^K. lift(a dot b)`; `wan_wd s i (w:real^N->real^K)`;
                   `\x. (G:real^K->real^K^K)(w x) ** wan_wd s i (w:real^N->real^K) x`;
                   `s:real^N->bool`] MEASURABLE_ON_BILINEAR) THEN
    REWRITE_TAC[BILINEAR_DOT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                   `\x. (vectorize:real^K^K->real^(K,K)finite_prod)((G:real^K->real^K^K)
                                                                 ((w:real^N->real^K) x))`;
                   `wan_wd s i (w:real^N->real^K)`; `s:real^N->bool`]
                  MEASURABLE_ON_BILINEAR) THEN
    REWRITE_TAC[GRGE_BILINEAR_MATRIFY_MUL; MATRIFY_VECTORIZE; ETA_AX] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)`;
                   `w:real^N->real^K`; `s:real^N->bool`] CMW_MEASURABLE_COMPOSE_CONT) THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(wan_wd s i (w:real^N->real^K) x dot
              ((G:real^K->real^K^K)(w x) ** wan_wd s i w x))) integrable_on s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x. lift(Lam * norm(wan_wd s i (w:real^N->real^K) x) pow 2)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[ETA_AX];
      REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let CMW_GDIR_POS = prove
 (`!s (G:real^K->real^K^K) (w:real^N->real^K) Lam.
        open s /\ wan_w12 s w /\
        ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
        (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2)
        ==> &0 <= wan_gdir s G w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_gdir] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^K->real^K^K`; `w:real^N->real^K`;
                 `Lam:real`; `i:num`] CMW_GDIR_INTEGRAND) THEN
  ASM_SIMP_TAC[]);;

let CMW_CONST_FACTS = prove
 (`!S (G:real^K->real^K^K) (q:real^K) (a:real^2) r Lam.
        q IN S /\ &0 < r /\
        ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
        (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2)
        ==> cm_cmap S (ball(a,r)) (\x. q) /\
            wan_gdir (ball(a,r)) G (\x. q) = &0 /\
            wan_dir (ball(a,r)) (\x. q) = &0 /\
            cm_minimizer S G (ball(a,r)) (\x. q) /\
            !i. 1 <= i /\ i <= dimindex(:2) ==> wan_wpd (ball(a,r)) i (\x. q) (\x. vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^2. (q:real^K)`; `G:real^K->real^K^K`; `a:real^2`; `r:real`]
                CMW_C1_BALL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_CONST; OPEN_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[PARTIAL_DERIVATIVE_CONST; NORM_0; DOT_LZERO] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[LIFT_NUM; INTEGRAL_0; DROP_VEC; SUM_0] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cm_cmap S (ball(a:real^2,r)) (\x. (q:real^K))` ASSUME_TAC THENL
   [REWRITE_TAC[cm_cmap; CONTINUOUS_ON_CONST] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[cm_minimizer; cm_wmap; cm_gen] THEN CONJ_TAC THENL
   [EXISTS_TAC `{}:real^2->bool` THEN ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY];
    REPEAT STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC CMW_GDIR_POS THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL]]);;

let CMW_DIR_SUB_CONST = prove
 (`!(u:real^N->real^K) c a r.
        &0 < r /\ wan_w12 (ball(a,r)) u
        ==> wan_w12 (ball(a,r)) (\x. u x - c) /\
            wan_dir (ball(a,r)) (\x. u x - c) = wan_dir (ball(a,r)) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. (c:real^K)`; `(\z. mat 1):real^K->real^K^K`; `a:real^N`; `r:real`]
                CMW_C1_BALL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_CONST; OPEN_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[PARTIAL_DERIVATIVE_CONST] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `wan_w12 (ball(a:real^N,r)) (\x. (u:real^N->real^K) x - c)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ball(a:real^N,r)`; `\x. (u:real^N->real^K) x - c`;
                 `\i. wan_wd (ball(a:real^N,r)) i (u:real^N->real^K)`] WAN_DIR_EQ) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^N,r)`; `i:num`; `u:real^N->real^K`;
                   `wan_wd (ball(a:real^N,r)) i (u:real^N->real^K)`;
                   `\x:real^N. (c:real^K)`; `\x:real^N. vec 0:real^K`] WAN_WPD_SUB) THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`ball(a:real^N,r)`; `i:num`; `u:real^N->real^K`] WAN_WD_WORKS) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_wpd")) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[wan_dir]]);;

(* The existence and continuity clauses of CM_REPLACEMENT, named.            *)

let cmw_repex = new_definition
 `cmw_repex S (G:real^K->real^K^K) e <=>
    !(a:real^2) r (u:real^2->real^K).
       &0 < r /\ cm_cmap S (ball(a,r)) u /\ wan_gdir (ball(a,r)) G u <= e
       ==> ?w. cm_minimizer S G (ball(a,r)) w /\
               wan_w120 (ball(a,r)) (\x. w x - u x) /\
               cm_cmap S (ball(a,r)) w /\ cm_harmonic S G (ball(a,r)) w /\
               (!x. x IN sphere(a,r) ==> w x = u x) /\
               !w'. cm_minimizer S G (ball(a,r)) w' /\
                    wan_w120 (ball(a,r)) (\x. w' x - u x)
                    ==> negligible {x | x IN ball(a,r) /\ ~(w' x = w x)}`;;

let cmw_repcont = new_definition
 `cmw_repcont S (G:real^K->real^K^K) e <=>
    !(a:real^2) r (u:num->real^2->real^K) u0 w w0.
       &0 < r /\
       (!n. cm_cmap S (ball(a,r)) (u n) /\ wan_gdir (ball(a,r)) G (u n) <= e /\
            cm_minimizer S G (ball(a,r)) (w n) /\ cm_cmap S (ball(a,r)) (w n) /\
            (!x. x IN sphere(a,r) ==> w n x = u n x)) /\
       cm_cmap S (ball(a,r)) u0 /\ wan_gdir (ball(a,r)) G u0 <= e /\
       cm_minimizer S G (ball(a,r)) w0 /\ cm_cmap S (ball(a,r)) w0 /\
       (!x. x IN sphere(a,r) ==> w0 x = u0 x) /\
       (!x. ((\n. u n x) --> u0 x) sequentially) /\
       (!e'. &0 < e' ==> eventually (\n. !x. x IN cball(a,r) ==> norm(u n x - u0 x) < e')
                                    sequentially) /\
       ((\n. wan_dir (ball(a,r)) (\x. u n x - u0 x)) ---> &0) sequentially
       ==> (!e'. &0 < e' ==> eventually (\n. !x. x IN cball(a,r) ==> norm(w n x - w0 x) < e')
                                        sequentially) /\
           ((\n. wan_dir (ball(a,r)) (\x. w n x - w0 x)) ---> &0) sequentially`;;

let CMW_REPLACEMENT_UNPACK = prove
 (`!S (G:real^K->real^K^K) d.
        CM_REPLACEMENT_STATEMENT (:K) /\ cm_target S G d
        ==> ?e. &0 < e /\ cmw_repex S G e /\ cmw_repcont S G e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CM_REPLACEMENT_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[cmw_repex; cmw_repcont]);;

let CMW_CMAP_EQ = prove
 (`!S (u:real^2->real^K) u' a r.
        &0 < r /\ (!x. x IN cball(a,r) ==> u x = u' x)
        ==> (cm_cmap S (ball(a,r)) u <=> cm_cmap S (ball(a,r)) u')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_cmap] THEN
  ASM_SIMP_TAC[CLOSURE_BALL] THEN
  SUBGOAL_THEN `!x. x IN ball(a:real^2,r) ==> (u:real^2->real^K) x = u' x` ASSUME_TAC THENL
   [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `u:real^2->real^K`; `u':real^2->real^K`]
                CMT_WAN_W12_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(TAUT `(b <=> b') /\ (c <=> c') ==> (a /\ b /\ c <=> a /\ b' /\ c')`) THEN
  CONJ_TAC THENL
   [EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let CMW_DIR_EQ_ON = prove
 (`!s (u:real^N->real^K) u'.
        (!x. x IN s ==> u x = u' x) ==> wan_dir s u = wan_dir s u'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dir] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CMT_WAN_WD_EQ th]));;

let CMW_UNIF_AUX = prove
 (`!(uu:num->real^2->real^K) (qq:num->real^K) (r:num->num) l.
        (!n. n <= r n) /\ ((qq o r) --> l) sequentially /\
        (!n x. x IN cball(vec 0,&1) ==> norm(uu n x - qq n) <= inv(&n + &1))
        ==> !ep. &0 < ep
                 ==> ?N. !n. N <= n
                             ==> norm(qq (r n) - l) < ep /\
                                 !x. x IN cball(vec 0:real^2,&1)
                                     ==> norm(uu (r n) x - l) < ep`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
  UNDISCH_TAC `(((qq:num->real^K) o (r:num->num)) --> l) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; o_THM; dist] THEN
  DISCH_THEN(MP_TAC o SPEC `ep / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MP_TAC(SPEC `ep / &2` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm((qq:num->real^K) ((r:num->num) n) - l) < ep / &2` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(r:num->num) n`; `x:real^2`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `uu:num->real^2->real^K`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv(&((r:num->num) n) + &1) < ep / &2` MP_TAC THENL
   [TRANS_TAC REAL_LET_TRANS `inv(&N2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    SUBGOAL_THEN `N2 <= (r:num->num) n` MP_TAC THENL
     [TRANS_TAC LE_TRANS `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(N2 = 0)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_EQ] THEN
    MP_TAC(SPEC `N2:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `norm((qq:num->real^K) ((r:num->num) n) - l) < ep / &2` THEN
  CONV_TAC NORM_ARITH);;

let CMW_C0EST = prove
 (`!S (G:real^K->real^K^K) d e eta.
     cm_target S G d /\ &0 < e /\ cmw_repcont S G e /\ &0 < eta
     ==> ?delta. &0 < delta /\
           !u w q. q IN S /\ cm_cmap S (ball(vec 0,&1)) u /\
                   wan_dir (ball(vec 0,&1)) u <= delta /\
                   wan_gdir (ball(vec 0,&1)) G u <= e /\
                   (!x. x IN cball(vec 0,&1) ==> norm(u x - q) <= delta) /\
                   cm_minimizer S G (ball(vec 0,&1)) w /\ cm_cmap S (ball(vec 0,&1)) w /\
                   (!x. x IN sphere(vec 0,&1) ==> w x = u x)
                   ==> !x. x IN cball(vec 0,&1) ==> norm(w x - q) < eta`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tg") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rc") ASSUME_TAC))) THEN
  USE_THEN "tg" (STRIP_ASSUME_TAC o REWRITE_RULE[cm_target]) THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K))
    continuous_on (:real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `0` THEN
    UNDISCH_TAC `smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G)` THEN
    SIMP_TAC[smooth_map_on];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z v. &0 <= v dot ((G:real^K->real^K^K) z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `lam * norm(v:real^K) pow 2` THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "neg" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN
   `!n. ?(u:real^2->real^K) (w:real^2->real^K) q x.
          q IN S /\ cm_cmap S (ball(vec 0,&1)) u /\
          wan_dir (ball(vec 0,&1)) u <= inv(&n + &1) /\
          wan_gdir (ball(vec 0,&1)) G u <= e /\
          (!x. x IN cball(vec 0,&1) ==> norm(u x - q) <= inv(&n + &1)) /\
          cm_minimizer S G (ball(vec 0,&1)) w /\ cm_cmap S (ball(vec 0,&1)) w /\
          (!x. x IN sphere(vec 0,&1) ==> w x = u x) /\
          x IN cball(vec 0,&1) /\ eta <= norm(w x - q)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN REMOVE_THEN "neg" (MP_TAC o SPEC `inv(&n + &1)`) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM; GSYM CONJ_ASSOC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:num->real^2->real^K` (X_CHOOSE_THEN `ww:num->real^2->real^K`
    (X_CHOOSE_THEN `qq:num->real^K` (X_CHOOSE_THEN `xx:num->real^2` (LABEL_TAC "ch"))))) THEN
  SUBGOAL_THEN `!n. (qq:num->real^K) n IN S` ASSUME_TAC THENL
   [USE_THEN "ch" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  UNDISCH_TAC `compact(S:real^K->bool)` THEN REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC `qq:num->real^K`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^K` (X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MONOTONE_BIGGER) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `l:real^K`; `vec 0:real^2`;
                 `&1`; `Lam:real`] CMW_CONST_FACTS) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. inv(&((r:num->num) n) + &1) <= inv(&n + &1)` (LABEL_TAC "rinv") THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[REAL_LE_RADD; REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!ep. &0 < ep
         ==> ?N. !n. N <= n
                     ==> norm((qq:num->real^K) ((r:num->num) n) - l) < ep /\
                         !x. x IN cball(vec 0:real^2,&1)
                             ==> norm((uu:num->real^2->real^K) (r n) x - l) < ep`
  (LABEL_TAC "unif") THENL
   [MATCH_MP_TAC CMW_UNIF_AUX THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ch" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  USE_THEN "rc" (MP_TAC o SPECL
   [`vec 0:real^2`; `&1`;
    `\n x. if x IN cball(vec 0:real^2,&1) then (uu:num->real^2->real^K) ((r:num->num) n) x
           else (qq:num->real^K) (r n)`;
    `\x:real^2. (l:real^K)`; `\n. (ww:num->real^2->real^K) ((r:num->num) n)`;
    `\x:real^2. (l:real^K)`] o REWRITE_RULE[cmw_repcont]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01; REAL_LE_REFL; ETA_AX] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN USE_THEN "ch" (MP_TAC o SPEC `(r:num->num) n`) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`S:real^K->bool`;
                       `\x. if x IN cball(vec 0:real^2,&1)
                            then (uu:num->real^2->real^K) ((r:num->num) n) x
                            else (qq:num->real^K) (r n)`;
                       `(uu:num->real^2->real^K) ((r:num->num) n)`;
                       `vec 0:real^2`; `&1`] CMW_CMAP_EQ) THEN
        ASM_SIMP_TAC[REAL_LT_01];
        MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `G:real^K->real^K^K`;
                       `\x. if x IN cball(vec 0:real^2,&1)
                            then (uu:num->real^2->real^K) ((r:num->num) n) x
                            else (qq:num->real^K) (r n)`;
                       `(uu:num->real^2->real^K) ((r:num->num) n)`] CMT_WAN_GDIR_EQ) THEN
        ANTS_TAC THENL [MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; DISCH_THEN SUBST1_TAC] THEN
        ASM_REWRITE_TAC[];
        X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(x:real^2) IN cball(vec 0,&1)` ASSUME_TAC THENL
         [ASM_MESON_TAC[SPHERE_SUBSET_CBALL; SUBSET]; ASM_SIMP_TAC[]]];
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN
      X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
      USE_THEN "unif" (MP_TAC o C MATCH_MP (ASSUME `&0 < ep`) o SPEC `ep:real`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
      DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[];
      X_GEN_TAC `ep:real` THEN DISCH_TAC THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      USE_THEN "unif" (MP_TAC o C MATCH_MP (ASSUME `&0 < ep`) o SPEC `ep:real`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
      DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN SIMP_TAC[];
      MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN EXISTS_TAC `\n. inv(&n + &1)` THEN
      REWRITE_TAC[REALLIM_1_OVER_N_OFFSET] THEN
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
      USE_THEN "ch" (MP_TAC o SPEC `(r:num->num) n`) THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `wan_dir (ball(vec 0:real^2,&1))
          (\x. (if x IN cball(vec 0,&1) then (uu:num->real^2->real^K) ((r:num->num) n) x
                else (qq:num->real^K) (r n)) - l) =
        wan_dir (ball(vec 0,&1)) (uu (r n))`
      SUBST1_TAC THENL
       [TRANS_TAC EQ_TRANS
         `wan_dir (ball(vec 0:real^2,&1))
            (\x. (uu:num->real^2->real^K) ((r:num->num) n) x - l)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CMW_DIR_EQ_ON THEN
          SIMP_TAC[] THEN MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
          MP_TAC(ISPECL [`(uu:num->real^2->real^K) ((r:num->num) n)`; `l:real^K`;
                         `vec 0:real^2`; `&1`] CMW_DIR_SUB_CONST) THEN
          ANTS_TAC THENL
           [REWRITE_TAC[REAL_LT_01] THEN
            UNDISCH_TAC `cm_cmap S (ball(vec 0:real^2,&1)) ((uu:num->real^2->real^K) ((r:num->num) n))` THEN
            SIMP_TAC[cm_cmap];
            SIMP_TAC[]]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= wan_dir (ball(vec 0:real^2,&1)) ((uu:num->real^2->real^K) ((r:num->num) n))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC WAN_DIR_POS THEN
        UNDISCH_TAC `cm_cmap S (ball(vec 0:real^2,&1)) ((uu:num->real^2->real^K) ((r:num->num) n))` THEN
        SIMP_TAC[cm_cmap];
        ALL_TAC] THEN
      USE_THEN "rinv" (MP_TAC o SPEC `n:num`) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `eta / &2` o CONJUNCT1 o BETA_RULE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3")) THEN
  USE_THEN "unif" (MP_TAC o SPEC `eta / &2`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N4:num` (LABEL_TAC "N4")) THEN
  USE_THEN "ch" (MP_TAC o SPEC `(r:num->num) (N3 + N4)`) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `norm((ww:num->real^2->real^K) ((r:num->num) (N3 + N4)) ((xx:num->real^2) (r (N3 + N4))) - l)
    < eta / &2`
  ASSUME_TAC THENL
   [USE_THEN "N3" (MP_TAC o SPEC `N3 + N4:num`) THEN REWRITE_TAC[LE_ADD] THEN
    DISCH_THEN(MP_TAC o SPEC `(xx:num->real^2) ((r:num->num) (N3 + N4))`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((qq:num->real^K) ((r:num->num) (N3 + N4)) - l) < eta / &2`
  ASSUME_TAC THENL
   [USE_THEN "N4" (MP_TAC o SPEC `N3 + N4:num`) THEN
    ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `eta <= norm((ww:num->real^2->real^K) ((r:num->num) (N3 + N4))
                           ((xx:num->real^2) (r (N3 + N4))) - (qq:num->real^K) (r (N3 + N4)))` THEN
  UNDISCH_TAC `norm((qq:num->real^K) ((r:num->num) (N3 + N4)) - l) < eta / &2` THEN
  UNDISCH_TAC `norm((ww:num->real^2->real^K) ((r:num->num) (N3 + N4))
                    ((xx:num->real^2) (r (N3 + N4))) - l) < eta / &2` THEN
  CONV_TAC NORM_ARITH);;

(* ========================================================================= *)
(* The planar data of a sweepout on shrinking discs and the                  *)
(* reflected data, their partial derivatives, and Dirichlet limits of C^1   *)
(* maps from uniform limits of the partials.                                *)
(* ========================================================================= *)

(* Data on the unit ball: the slice at t on the disc stereo2_n_inv(ball(0,R s)). *)

let cmw_dat = new_definition
 `cmw_dat (W:real^3->real->real^K) R t s = \x:real^2. W (stereo2_n_inv((R * s) % x)) t`;;

let cmw_rdat = new_definition
 `cmw_rdat (W:real^3->real->real^K) R t = \x:real^2. W (stereo2_s_inv(inv R % x)) t`;;

let CMW_STEREO_CIRCLE = prove
 (`!R x:real^2. &0 < R /\ norm x = &1
                ==> stereo2_n_inv(R % x) = stereo2_s_inv(inv R % x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO2_N_INV_COMPONENTS;
              STEX_STEREO2_S_INV_COMPONENTS; NORM_MUL; VECTOR_MUL_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < R ==> abs R = R`; REAL_MUL_RID] THEN
  SUBGOAL_THEN `&0 < R pow 2 /\ &0 < inv R pow 2` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_INV]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD);;

let CMW_DAT_CIRCLE = prove
 (`!(W:real^3->real->real^K) R t x.
        &0 < R /\ x IN sphere(vec 0,&1) ==> cmw_dat W R t (&1) x = cmw_rdat W R t x`,
  REWRITE_TAC[cmw_dat; cmw_rdat; IN_SPHERE_0; REAL_MUL_RID] THEN
  SIMP_TAC[CMW_STEREO_CIRCLE]);;

let CMW_STEREO_S_NEAR_N = prove
 (`!v:real^2. norm(stereo2_s_inv v - basis 3) <= &2 * norm v`,
  GEN_TAC THEN
  SUBGOAL_THEN `stereo2_s_inv v - basis 3 =
                (&2 / (norm v pow 2 + &1)) %
                ((lambda i. if i = 3 then --(norm v pow 2) else v$i):real^3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO2_S_INV_COMPONENTS;
                VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[LAMBDA_BETA; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    MP_TAC(ISPEC `v:real^2` STEX_INV_STEREO_DENOM) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN `&0 < norm(v:real^2) pow 2 + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `v:real^2` STEX_INV_STEREO_DENOM) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_ABS_NUM] THEN
  SUBGOAL_THEN
   `norm((lambda i. if i = 3 then --(norm v pow 2) else (v:real^2)$i):real^3) =
    norm v * sqrt(norm v pow 2 + &1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[NORM_EQ_SQUARE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `sqrt(norm(v:real^2) pow 2 + &1) pow 2 = norm v pow 2 + &1`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DOT_3; NORM_POW_2; DOT_2] THEN
    SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(norm(v:real^2) pow 2 + &1) <= norm v pow 2 + &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= norm(v:real^2) pow 2 + &1` ASSUME_TAC THENL
     [MP_TAC(ISPEC `norm(v:real^2)` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 / (norm(v:real^2) pow 2 + &1) * (norm v * (norm v pow 2 + &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < norm(v:real^2) pow 2 + &1` THEN
    CONV_TAC REAL_FIELD]);;

(* The two charts are related by the inversion in the unit circle.          *)

let CMW_STEREO_INVERSION = prove
 (`!y:real^2. ~(y = vec 0)
              ==> stereo2_n_inv y = stereo2_s_inv(inv(norm y pow 2) % y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `y:real^2` STEX_STEREO2_TRANSITION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)))) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC STEX_STEREO2_S_LEFT THEN ASM_REWRITE_TAC[]);;

(* Points outside the big disc of the north chart are near the north pole, *)
(* and points near the north pole are outside the big disc.                 *)

let CMW_NORTH_CAP = prove
 (`!y:real^3 R. y IN sphere(vec 0,&1) /\ &0 < R /\ (y = basis 3 \/ R <= norm(stereo2_n y))
                ==> norm(y - basis 3) <= &2 / R`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `y:real^3 = basis 3` THEN
  ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(stereo2_n(y:real^3))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(stereo2_n(y:real^3) = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `y IN sphere(vec 0:real^3,&1) DELETE basis 3` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP STEX_STEREO2_N_LEFT) THEN
  ASM_SIMP_TAC[CMW_STEREO_INVERSION] THEN
  W(MP_TAC o PART_MATCH lhand CMW_STEREO_S_NEAR_N o lhand o snd) THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  SUBGOAL_THEN `inv(norm(stereo2_n(y:real^3)) pow 2) * norm(stereo2_n y) =
                inv(norm(stereo2_n y))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < norm(stereo2_n(y:real^3))` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]);;

let CMW_NORTH_FAR = prove
 (`!y:real^3 R. y IN sphere(vec 0,&1) /\ ~(y = basis 3) /\ &1 <= R /\
                norm(y - basis 3) < inv R
                ==> R <= norm(stereo2_n y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `y IN sphere(vec 0:real^3,&1) DELETE basis 3`
   (STRIP_ASSUME_TAC o MATCH_MP STEX_STEREO2_N_NORM2) THENL
   [ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(y - basis 3:real^3) pow 2 = &2 - &2 * y$3` ASSUME_TAC THENL
   [UNDISCH_TAC `y IN sphere(vec 0:real^3,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; NORM_POW_2; DOT_3; VECTOR_SUB_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((y:real^3)$3) <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    UNDISCH_TAC `y IN sphere(vec 0:real^3,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `a = &1 - (y:real^3)$3` THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R pow 2 /\ &1 <= R pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * a < inv(R pow 2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(y - basis 3:real^3) pow 2 < inv R pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE; ARITH_EQ];
      ASM_REWRITE_TAC[REAL_POW_INV] THEN EXPAND_TAC "a" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `R pow 2 * (&2 * a) < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `R pow 2 * inv(R pow 2)` THEN
    ASM_SIMP_TAC[REAL_LT_LMUL; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(R pow 2) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[NORM_POS_LE; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 + (y:real^3)$3 = &2 - a` SUBST1_TAC THENL
   [EXPAND_TAC "a" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* Sequential continuity of a jointly continuous family on sphere x [0,1].  *)

let CMW_SWEEP_SEQ = prove
 (`!(W:real^3->real->real^K) y t (yn:num->real^3) (tn:num->real).
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
          (\(y,t). W y t) /\
        y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] /\
        (!n. yn n IN sphere(vec 0,&1) /\ tn n IN real_interval[&0,&1]) /\
        (yn --> y) sequentially /\ ((\n. lift(tn n)) --> lift t) sequentially
        ==> ((\n. W (yn n) (tn n)) --> W y t) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`sequentially`;
    `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                   (subtopology euclideanreal (real_interval[&0,&1]))`;
    `euclidean:(real^K)topology`;
    `\n. (yn:num->real^3) n,(tn:num->real) n`;
    `\(y,t). (W:real^3->real->real^K) y t`;
    `y:real^3,t:real`] CONTINUOUS_MAP_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[LIMIT_PAIRWISE; o_DEF; LIMIT_SUBTOPOLOGY; LIMIT_EUCLIDEAN; LIM_EQ_LIFT] THEN
    ASM_REWRITE_TAC[EVENTUALLY_TRUE; ETA_AX];
    REWRITE_TAC[o_DEF; LIMIT_EUCLIDEAN] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]]);;

(* Limits along scalings, matrix-vector products and slow subsequences.     *)

let CMW_SCALE_SEQ = prove
 (`!R s x (sn:num->real) (xn:num->real^N).
        ((\n. lift(sn n)) --> lift s) sequentially /\ (xn --> x) sequentially
        ==> ((\n. (R * sn n) % xn n) --> (R * s) % x) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sequentially`; `xn:num->real^N`; `x:real^N`;
                 `\n. R * (sn:num->real) n`; `R * s`] LIM_MUL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[o_DEF; LIFT_CMUL] THEN
  MATCH_MP_TAC LIM_CMUL THEN ASM_REWRITE_TAC[]);;

let CMW_LIM_MATRIX_VECTOR = prove
 (`!(A:num->real^M^N) A0 (v:num->real^M) v0.
        (!k j. 1 <= k /\ k <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:M)
               ==> ((\n. lift(A n$k$j)) --> lift(A0$k$j)) sequentially) /\
        (v --> v0) sequentially
        ==> ((\n. A n ** v n) --> A0 ** v0) sequentially`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC LIM_MUL THEN ASM_SIMP_TAC[o_DEF] THEN
  UNDISCH_TAC `((v:num->real^M) --> v0) sequentially` THEN
  DISCH_THEN(MP_TAC o SPEC `j:num` o GEN_REWRITE_RULE I [LIM_COMPONENTWISE_LIFT]) THEN
  ASM_REWRITE_TAC[]);;

let CMW_LIM_GE = prove
 (`!(a:num->real^N) l (q:num->num).
        (!k. k <= q k) /\ (a --> l) sequentially ==> ((\k. a(q k)) --> l) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `N:num` o C MATCH_MP (ASSUME `&0 < e`)) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN TRANS_TAC LE_TRANS `k:num` THEN ASM_REWRITE_TAC[]);;

(* The data are jointly continuous in (s,t,x).                              *)

let CMW_DAT_SEQ = prove
 (`!(W:real^3->real->real^K) R s t x (sn:num->real) (tn:num->real) (xn:num->real^2).
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
          (\(y,t). W y t) /\
        t IN real_interval[&0,&1] /\ (!n. tn n IN real_interval[&0,&1]) /\
        ((\n. lift(sn n)) --> lift s) sequentially /\
        ((\n. lift(tn n)) --> lift t) sequentially /\ (xn --> x) sequentially
        ==> ((\n. cmw_dat W R (tn n) (sn n) (xn n)) --> cmw_dat W R t s x) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmw_dat] THEN
  MATCH_MP_TAC CMW_SWEEP_SEQ THEN ASM_REWRITE_TAC[IN_SPHERE_0; BEL_P_CHART] THEN
  MATCH_MP_TAC LIM_CONTINUOUS_FUNCTION THEN
  SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT; BEL_P_CHART] THEN
  MATCH_MP_TAC CMW_SCALE_SEQ THEN ASM_REWRITE_TAC[]);;

(* Partial derivatives of the slices in the north chart and of the data.    *)

let CMW_PT_PARTIAL = prove
 (`!(u:real^3->real^K) i z.
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u)
        ==> partial_derivative i (\z. u(stereo2_n_inv z)) z =
            jacobian (wan_rext u) (at (stereo2_n_inv z)) ** partial_derivative i stereo2_n_inv z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (u:real^3->real^K)(stereo2_n_inv z)) = wan_rext u o stereo2_n_inv`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CM_REXT_SPHERE THEN REWRITE_TAC[IN_SPHERE_0; BEL_P_CHART];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_rext (u:real^3->real^K) differentiable at (stereo2_n_inv z)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMT_C1_DIFFERENTIABLE_AT THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM; GSYM NORM_EQ_0; BEL_P_CHART] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_CHAIN o lhand o snd) THEN
  ASM_REWRITE_TAC[BEL_P_CHART] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[partial_derivative] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[JACOBIAN_WORKS]) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[]);;

let CMW_PT_PARTIAL_SEQ = prove
 (`!(W:real^3->real->real^K) i z t (zn:num->real^2) (tn:num->real).
        cmw_c1sweep W /\
        t IN real_interval[&0,&1] /\ (!n. tn n IN real_interval[&0,&1]) /\
        (zn --> z) sequentially /\ ((\n. lift(tn n)) --> lift t) sequentially
        ==> ((\n. partial_derivative i (\z. W (stereo2_n_inv z) (tn n)) (zn n)) -->
             partial_derivative i (\z. W (stereo2_n_inv z) t) z) sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [cmw_c1sweep]) THEN
  SUBGOAL_THEN
   `!t'. t' IN real_interval[&0,&1]
         ==> !z'. partial_derivative i (\z. (W:real^3->real->real^K) (stereo2_n_inv z) t') z' =
                  jacobian (wan_rext (\y. W y t')) (at (stereo2_n_inv z')) **
                  partial_derivative i stereo2_n_inv z'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\y. (W:real^3->real->real^K) y t'`; `i:num`; `z':real^2`]
                  CMW_PT_PARTIAL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC CMW_LIM_MATRIX_VECTOR THEN REWRITE_TAC[DIMINDEX_3] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `j:num`] THEN STRIP_TAC THEN
    UNDISCH_TAC `cmw_c1sweep (W:real^3->real->real^K)` THEN REWRITE_TAC[cmw_c1sweep] THEN
    DISCH_THEN(MP_TAC o SPECL [`k:num`; `j:num`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`\n. pastecart (stereo2_n_inv((zn:num->real^2) n)) (lift((tn:num->real) n))`;
      `pastecart (stereo2_n_inv(z:real^2)) (lift t)`]) THEN
    REWRITE_TAC[o_DEF; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SPHERE_0; BEL_P_CHART] THEN
    MATCH_MP_TAC LIM_PASTECART THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LIM_CONTINUOUS_FUNCTION THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT; BEL_P_CHART];
    MP_TAC(ISPECL [`stereo2_n_inv`; `i:num`] CMW_C1_PARTIAL_CONT) THEN
    ANTS_TAC THENL [MP_TAC STEX_STEREO2_N_INV_SMOOTH THEN SIMP_TAC[smooth_map_on]; ALL_TAC] THEN
    REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPECL [`zn:num->real^2`; `z:real^2`]) THEN
    ASM_REWRITE_TAC[o_DEF]]);;

let CMW_DAT_C1 = prove
 (`!(W:real^3->real->real^K) R t s.
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext (\y. W y t))
        ==> continuously_differentiable 1 (:real^2) (\z. W (stereo2_n_inv z) t) /\
            continuously_differentiable 1 (:real^2) (cmw_dat W R t s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\y. (W:real^3->real->real^K) y t`; `R * s`] CMW_P_SCALED_C1) THEN
  ASM_REWRITE_TAC[cmw_dat]);;

let CMW_DAT_PARTIAL = prove
 (`!(W:real^3->real->real^K) R t s i x.
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext (\y. W y t))
        ==> partial_derivative i (cmw_dat W R t s) x =
            (R * s) % partial_derivative i (\z. W (stereo2_n_inv z) t) ((R * s) % x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmw_dat] THEN
  MP_TAC(ISPECL [`\z. (W:real^3->real->real^K) (stereo2_n_inv z) t`; `R * s`; `i:num`;
                 `x:real^2`] CMW_PARTIAL_SCALE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC CMW_C1_DIFFERENTIABLE THEN
  ASM_MESON_TAC[CMW_DAT_C1]);;

let CMW_DAT_PARTIAL_SEQ = prove
 (`!(W:real^3->real->real^K) R i s t x (sn:num->real) (tn:num->real) (xn:num->real^2).
        cmw_c1sweep W /\
        t IN real_interval[&0,&1] /\ (!n. tn n IN real_interval[&0,&1]) /\
        ((\n. lift(sn n)) --> lift s) sequentially /\
        ((\n. lift(tn n)) --> lift t) sequentially /\ (xn --> x) sequentially
        ==> ((\n. partial_derivative i (cmw_dat W R (tn n) (sn n)) (xn n)) -->
             partial_derivative i (cmw_dat W R t s) x) sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [cmw_c1sweep]) THEN
  ASM_SIMP_TAC[CMW_DAT_PARTIAL] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_MUL) THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_CMUL] THEN MATCH_MP_TAC LIM_CMUL THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`W:real^3->real->real^K`; `i:num`; `(R * s) % x:real^2`; `t:real`;
                   `\n. (R * (sn:num->real) n) % (xn:num->real^2) n`; `tn:num->real`]
                  CMW_PT_PARTIAL_SEQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMW_SCALE_SEQ THEN ASM_REWRITE_TAC[]]);;

(* Joint sequential continuity on [0,1] x [0,1] x cball(0,1) gives uniform  *)
(* convergence on the closed disc (sequential compactness).                 *)

let CMW_UNIF_SEQ = prove
 (`!(FF:real->real->real^2->real^N) s t (sn:num->real) (tn:num->real).
        (!s t x (sk:num->real) (tk:num->real) (xk:num->real^2).
            s IN real_interval[&0,&1] /\ t IN real_interval[&0,&1] /\ x IN cball(vec 0,&1) /\
            (!k. sk k IN real_interval[&0,&1] /\ tk k IN real_interval[&0,&1] /\
                 xk k IN cball(vec 0,&1)) /\
            ((\k. lift(sk k)) --> lift s) sequentially /\
            ((\k. lift(tk k)) --> lift t) sequentially /\ (xk --> x) sequentially
            ==> ((\k. FF (sk k) (tk k) (xk k)) --> FF s t x) sequentially) /\
        s IN real_interval[&0,&1] /\ t IN real_interval[&0,&1] /\
        (!n. sn n IN real_interval[&0,&1] /\ tn n IN real_interval[&0,&1]) /\
        ((\n. lift(sn n)) --> lift s) sequentially /\
        ((\n. lift(tn n)) --> lift t) sequentially
        ==> !e. &0 < e
                ==> eventually (\n. !x. x IN cball(vec 0,&1)
                                        ==> norm(FF (sn n) (tn n) x - FF s t x) < e)
                               sequentially`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sc") STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REFUTE_THEN(MP_TAC o REWRITE_RULE[EVENTUALLY_SEQUENTIALLY; NOT_EXISTS_THM; NOT_FORALL_THM;
                                    NOT_IMP; REAL_NOT_LT; RIGHT_AND_EXISTS_THM;
                                    SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:num->num` (X_CHOOSE_THEN `xx:num->real^2` (LABEL_TAC "bad"))) THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] COMPACT_CBALL) THEN REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC `xx:num->real^2`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^2` (X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MONOTONE_BIGGER) THEN
  SUBGOAL_THEN `!k. k <= (nn:num->num) ((r:num->num) k)` ASSUME_TAC THENL
   [GEN_TAC THEN TRANS_TAC LE_TRANS `(r:num->num) k` THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. (FF:real->real->real^2->real^N) (sn((nn:num->num)((r:num->num) k)))
            (tn(nn(r k))) ((xx:num->real^2)(r k))) --> FF s t l) sequentially`
  ASSUME_TAC THENL
   [USE_THEN "sc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!k. (xx:num->real^2)((r:num->num) k) IN cball(vec 0,&1)`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`\n. lift((sn:num->real) n)`; `lift s`;
                     `\k. (nn:num->num)((r:num->num) k)`] CMW_LIM_GE) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`\n. lift((tn:num->real) n)`; `lift t`;
                     `\k. (nn:num->num)((r:num->num) k)`] CMW_LIM_GE) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(((xx:num->real^2) o (r:num->num)) --> l) sequentially` THEN
      REWRITE_TAC[o_DEF]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. (FF:real->real->real^2->real^N) s t ((xx:num->real^2)((r:num->num) k))) --> FF s t l)
    sequentially`
  ASSUME_TAC THENL
   [USE_THEN "sc" (MP_TAC o ISPECL
     [`s:real`; `t:real`; `l:real^2`; `\k:num. s:real`; `\k:num. t:real`;
      `\k. (xx:num->real^2)((r:num->num) k)`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LIM_CONST] THEN
    SUBGOAL_THEN `!k. (xx:num->real^2)((r:num->num) k) IN cball(vec 0,&1)`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(((xx:num->real^2) o (r:num->num)) --> l) sequentially` THEN
    REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`sequentially`;
    `\k. (FF:real->real->real^2->real^N) (sn((nn:num->num)((r:num->num) k)))
           (tn(nn(r k))) ((xx:num->real^2)(r k))`;
    `\k. (FF:real->real->real^2->real^N) s t ((xx:num->real^2)((r:num->num) k))`;
    `(FF:real->real->real^2->real^N) s t l`; `(FF:real->real->real^2->real^N) s t l`]
   LIM_SUB) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; LIM_SEQUENTIALLY; DIST_0] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M0:num` (MP_TAC o SPEC `M0:num`)) THEN
  REWRITE_TAC[LE_REFL; REAL_NOT_LT] THEN
  USE_THEN "bad" (MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `(r:num->num) M0`) THEN
  REAL_ARITH_TAC);;

(* Dirichlet integrals on the unit disc from bounds on classical partials. *)

let CMW_DIR_SMALL = prove
 (`!(v:real^2->real^K) eps.
        continuously_differentiable 1 (:real^2) v /\
        (!i x. 1 <= i /\ i <= 2 /\ x IN cball(vec 0,&1)
               ==> norm(partial_derivative i v x) <= eps)
        ==> &0 <= wan_dir (ball(vec 0,&1)) v /\
            wan_dir (ball(vec 0,&1)) v <= &2 * measure(ball(vec 0:real^2,&1)) * eps pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^2->real^K`; `G:real^K->real^K^K`; `vec 0:real^2`; `&1`]
                CMW_C1_BALL) THEN
  ASM_REWRITE_TAC[REAL_LT_01; DIMINDEX_2] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 th))]) THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> &0 <= drop(integral (ball(vec 0,&1))
                     (\x. lift(norm(partial_derivative i (v:real^2->real^K) x) pow 2))) /\
            drop(integral (ball(vec 0,&1))
                     (\x. lift(norm(partial_derivative i v x) pow 2)))
            <= measure(ball(vec 0:real^2,&1)) * eps pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(\x. lift(norm(partial_derivative i (v:real^2->real^K) x) pow 2))
      integrable_on ball(vec 0,&1)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CMW_CONT_INTEGRABLE_BALL_INT THEN REWRITE_TAC[NORM_POW_2] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; CMW_C1_PARTIAL_CONT];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `drop(integral (ball(vec 0:real^2,&1)) (\x. lift(eps pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_REWRITE_TAC[LIFT_DROP; INTEGRABLE_ON_CONST; MEASURABLE_BALL] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      REWRITE_TAC[NORM_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
      SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP; REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_2] THEN
  FIRST_ASSUM(MP_TAC o SPEC `1`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
  REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC);;

let CMW_DIR_LIM = prove
 (`!(v:num->real^2->real^K).
        (!n. continuously_differentiable 1 (:real^2) (v n)) /\
        (!e. &0 < e
             ==> eventually (\n. !i x. 1 <= i /\ i <= 2 /\ x IN cball(vec 0,&1)
                                     ==> norm(partial_derivative i (v n) x) < e)
                            sequentially)
        ==> ((\n. wan_dir (ball(vec 0,&1)) (v n)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `M = measure(ball(vec 0:real^2,&1))` THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC MEASURE_POS_LE THEN REWRITE_TAC[MEASURABLE_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `m = min (&1) (e / (&2 * M + &1))` THEN
  SUBGOAL_THEN `&0 < m /\ m <= &1 /\ m * (&2 * M + &1) <= e` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * M + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < e / (&2 * M + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `m <= e / (&2 * M + &1)` MP_TAC THENL
     [EXPAND_TAC "m" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:real`) THEN ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(v:num->real^2->real^K) n`; `m:real`] CMW_DIR_SMALL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `M * m pow 2 <= M * m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Convergence of the data along (s_n,t_n) -> (s,t): pointwise, uniformly *)
(* on the closed disc, and in the Dirichlet integral on the open disc.      *)

let CMW_DAT_CONV = prove
 (`!(W:real^3->real->real^K) R s t (sn:num->real) (tn:num->real).
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
          (\(y,t). W y t) /\
        cmw_c1sweep W /\
        s IN real_interval[&0,&1] /\ t IN real_interval[&0,&1] /\
        (!n. sn n IN real_interval[&0,&1] /\ tn n IN real_interval[&0,&1]) /\
        ((\n. lift(sn n)) --> lift s) sequentially /\
        ((\n. lift(tn n)) --> lift t) sequentially
        ==> (!x. ((\n. cmw_dat W R (tn n) (sn n) x) --> cmw_dat W R t s x) sequentially) /\
            (!e. &0 < e
                 ==> eventually (\n. !x. x IN cball(vec 0,&1)
                                         ==> norm(cmw_dat W R (tn n) (sn n) x -
                                                  cmw_dat W R t s x) < e)
                                sequentially) /\
            ((\n. wan_dir (ball(vec 0,&1))
                    (\x. cmw_dat W R (tn n) (sn n) x - cmw_dat W R t s x)) ---> &0)
            sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [cmw_c1sweep]) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN
    MP_TAC(ISPECL [`W:real^3->real->real^K`; `R:real`; `s:real`; `t:real`; `x:real^2`;
                   `sn:num->real`; `tn:num->real`; `\n:num. x:real^2`] CMW_DAT_SEQ) THEN
    ASM_REWRITE_TAC[LIM_CONST];
    MP_TAC(ISPECL [`\s t x. cmw_dat (W:real^3->real->real^K) R t s x`; `s:real`; `t:real`;
                   `sn:num->real`; `tn:num->real`] CMW_UNIF_SEQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMW_DAT_SEQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CMW_DIR_LIM THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUB_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV; ETA_AX; CMW_DAT_C1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i e. &0 < e
          ==> eventually
               (\n. !x. x IN cball(vec 0,&1)
                        ==> norm(partial_derivative i
                                   (cmw_dat (W:real^3->real->real^K) R (tn n) (sn n)) x -
                                 partial_derivative i (cmw_dat W R t s) x) < e)
               sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`\s t x. partial_derivative i (cmw_dat (W:real^3->real->real^K) R t s) x`;
                   `s:real`; `t:real`; `sn:num->real`; `tn:num->real`] CMW_UNIF_SEQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMW_DAT_PARTIAL_SEQ THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(CONJ (SPECL [`1`; `e:real`] th) (SPECL [`2`; `e:real`] th))) THEN
  ASM_REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `x:real^2`] THEN
  STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_SUB o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CMW_C1_DIFFERENTIABLE THEN ASM_SIMP_TAC[CMW_DAT_C1; ETA_AX];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `i = 1 \/ i = 2` (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[ETA_AX]; ASM_SIMP_TAC[ETA_AX]]);;

(* ========================================================================= *)
(* The replacements of the data, their uniqueness and joint                  *)
(* continuity (clause 2 of CM_REPLACEMENT), and the gluing lemma.           *)
(* ========================================================================= *)

let CMW_EVENTUALLY_LT = prove
 (`!(a:num->real) (b:num->real) a0 b0.
        ((\n. lift(a n)) --> lift a0) sequentially /\
        ((\n. lift(b n)) --> lift b0) sequentially /\ a0 < b0
        ==> eventually (\n. a n < b n) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tendsto; DIST_LIFT] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `(b0 - a0) / &2`)) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_SUB_LT] THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN REWRITE_TAC[] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let CMW_SCALE_IN_BALL = prove
 (`!a (z:real^2). norm z < a
                  ==> inv a % z IN ball(vec 0,&1) /\ inv a % z IN cball(vec 0,&1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [MP_TAC(ISPEC `z:real^2` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(inv a % z:real^2) < &1` MP_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_MUL_LID];
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC]);;

(* Gluing: replacement on the disc of radius c s (rescaled to the unit    *)
(* disc), the outer map outside; joint sequential continuity in (s,t,z).    *)

let CMW_GLUE_SEQ = prove
 (`!(f:real->real^2->real^K) (r:real->real->real^2->real^K) c s t z
    (sn:num->real) (tn:num->real) (zn:num->real^2).
        &0 < c /\
        ((\n. f (tn n) (zn n)) --> f t z) sequentially /\
        (!e. &0 < e
             ==> eventually (\n. !x. x IN cball(vec 0,&1)
                                     ==> norm(r (tn n) (sn n) x - r t s x) < e)
                            sequentially) /\
        r t s continuous_on cball(vec 0,&1) /\
        (&0 < s ==> !x. x IN sphere(vec 0,&1) ==> r t s x = f t ((c * s) % x)) /\
        (s = &0 ==> !x. x IN cball(vec 0,&1) ==> r t s x = f t (vec 0)) /\
        &0 <= s /\
        ((\n. lift(sn n)) --> lift s) sequentially /\ (zn --> z) sequentially
        ==> ((\n. if norm(zn n) < c * sn n then r (tn n) (sn n) (inv(c * sn n) % zn n)
                  else f (tn n) (zn n)) -->
             (if norm z < c * s then r t s (inv(c * s) % z) else f t z)) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "fl") (CONJUNCTS_THEN2 (LABEL_TAC "unif")
   (CONJUNCTS_THEN2 (LABEL_TAC "rc") (CONJUNCTS_THEN2 (LABEL_TAC "circ")
   (CONJUNCTS_THEN2 (LABEL_TAC "zero") STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `((\n. lift(c * (sn:num->real) n)) --> lift(c * s)) sequentially`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LIM_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((\n. lift(norm((zn:num->real^2) n))) --> lift(norm(z:real^2))) sequentially`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_NORM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `L = if norm(z:real^2) < c * s
                  then (r:real->real->real^2->real^K) t s (inv(c * s) % z) else f t z` THEN
  REWRITE_TAC[tendsto] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `eventually (\n. ~(norm((zn:num->real^2) n) < c * sn n)
                    ==> dist((f:real->real^2->real^K) (tn n) (zn n),L) < e) sequentially`
  (LABEL_TAC "neg") THENL
   [ASM_CASES_TAC `norm(z:real^2) < c * s` THENL
     [MP_TAC(ISPECL [`\n. norm((zn:num->real^2) n)`; `\n. c * (sn:num->real) n`;
                     `norm(z:real^2)`; `c * s`] CMW_EVENTUALLY_LT) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN SIMP_TAC[];
      USE_THEN "fl" (MP_TAC o SPEC `e:real` o REWRITE_RULE[tendsto]) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN
      REWRITE_TAC[ASSUME `~(norm(z:real^2) < c * s)`] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `eventually (\n. norm((zn:num->real^2) n) < c * sn n
                    ==> dist((r:real->real->real^2->real^K) (tn n) (sn n)
                               (inv(c * sn n) % zn n),L) < e) sequentially`
  (LABEL_TAC "pos") THENL
   [ASM_CASES_TAC `c * s < norm(z:real^2)` THENL
     [MP_TAC(ISPECL [`\n. c * (sn:num->real) n`; `\n. norm((zn:num->real^2) n)`;
                     `c * s`; `norm(z:real^2)`] CMW_EVENTUALLY_LT) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN REWRITE_TAC[] THEN
      GEN_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < e / &2` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
    USE_THEN "unif" (LABEL_TAC "u2" o C MP (ASSUME `&0 < e / &2`) o SPEC `e / &2`) THEN
    ASM_CASES_TAC `s = &0` THENL
     [SUBGOAL_THEN `z:real^2 = vec 0` SUBST_ALL_TAC THENL
       [REWRITE_TAC[GSYM NORM_EQ_0] THEN MP_TAC(ISPEC `z:real^2` NORM_POS_LE) THEN
        UNDISCH_TAC `~(c * s < norm(z:real^2))` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `L = (f:real->real^2->real^K) t (vec 0)` SUBST1_TAC THENL
       [EXPAND_TAC "L" THEN
        REWRITE_TAC[NORM_0; ASSUME `s = &0`; REAL_MUL_RZERO; REAL_LT_REFL]; ALL_TAC] THEN
      USE_THEN "u2" (MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] EVENTUALLY_MONO)) THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `inv(c * (sn:num->real) n) % (zn:num->real^2) n`) THEN
      ASM_SIMP_TAC[CMW_SCALE_IN_BALL] THEN
      USE_THEN "zero" (MP_TAC o SPEC `inv(c * (sn:num->real) n) % (zn:num->real^2) n` o
                       C MP (ASSUME `s = &0`)) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[CMW_SCALE_IN_BALL]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < c * s` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `x0:real^2 = inv(c * s) % z` THEN
    SUBGOAL_THEN `(x0:real^2) IN cball(vec 0,&1)` ASSUME_TAC THENL
     [EXPAND_TAC "x0" THEN REWRITE_TAC[IN_CBALL_0; NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `L = (r:real->real->real^2->real^K) t s x0` SUBST1_TAC THENL
     [EXPAND_TAC "L" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "circ" (MP_TAC o SPEC `x0:real^2` o C MP (ASSUME `&0 < s`)) THEN
      ANTS_TAC THENL
       [EXPAND_TAC "x0" THEN REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
        SUBGOAL_THEN `norm(z:real^2) = c * s` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ]];
        DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "x0" THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]];
      ALL_TAC] THEN
    USE_THEN "rc" (MP_TAC o SPEC `x0:real^2` o REWRITE_RULE[continuous_on]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `((\n. inv(c * (sn:num->real) n) % (zn:num->real^2) n) --> x0) sequentially`
    MP_TAC THENL
     [EXPAND_TAC "x0" THEN
      MP_TAC(ISPECL [`sequentially`; `zn:num->real^2`; `z:real^2`;
                     `\n. inv(c * (sn:num->real) n)`; `inv(c * s)`] LIM_MUL) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`sequentially`; `\n. c * (sn:num->real) n`; `c * s`] LIM_INV) THEN
      ASM_SIMP_TAC[o_DEF; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    REWRITE_TAC[tendsto] THEN DISCH_THEN(MP_TAC o SPEC `dd:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REMOVE_THEN "u2" MP_TAC THEN
    UNDISCH_TAC `eventually (\n. dist(inv(c * (sn:num->real) n) % (zn:num->real^2) n,x0) < dd)
                 sequentially` THEN
    REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv(c * (sn:num->real) n) % (zn:num->real^2) n`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv(c * (sn:num->real) n) % (zn:num->real^2) n`) THEN
    ASM_SIMP_TAC[CMW_SCALE_IN_BALL] THEN REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  REMOVE_THEN "pos" MP_TAC THEN REMOVE_THEN "neg" MP_TAC THEN
  REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* Facts about the target, in usable form.                                  *)

let CMW_TARGET_FACTS = prove
 (`!S (G:real^K->real^K^K) d.
        cm_target S G d
        ==> compact S /\ ~(S = {}) /\ &0 < d /\
            smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
            ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
            ?lam Lam. &0 < lam /\ lam <= Lam /\
                      (!z v. lam * norm v pow 2 <= v dot (G z ** v)) /\
                      (!z v. v dot (G z ** v) <= Lam * norm v pow 2) /\
                      (!z v. &0 <= v dot (G z ** v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_target] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `0` THEN
    UNDISCH_TAC `smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G)` THEN
    SIMP_TAC[smooth_map_on];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!z v. lam * norm v pow 2 <= v dot ((G:real^K->real^K^K) z ** v)) /\
    (!z v. v dot (G z ** v) <= Lam * norm v pow 2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `Lam:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN TRANS_TAC REAL_LE_TRANS `lam * norm(v:real^K) pow 2` THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2]);;

let CMW_DIR_ZERO = prove
 (`wan_dir (ball(vec 0,&1)) (\x:real^2. vec 0:real^K) = &0`,
  MP_TAC(ISPECL [`\x:real^2. vec 0:real^K`; `&0`] CMW_DIR_SMALL) THEN
  REWRITE_TAC[PARTIAL_DERIVATIVE_CONST; NORM_0; REAL_LE_REFL] THEN
  SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_CONST; OPEN_UNIV] THEN REAL_ARITH_TAC);;

(* The replacement of the data at (t,s): a minimizer with the circle        *)
(* values of the data (unique on the closed disc by clause 2).              *)

let cmw_rep = new_definition
 `cmw_rep (S:real^K->bool) (G:real^K->real^K^K) (W:real^3->real->real^K) R t s =
    @w:real^2->real^K. cm_minimizer S G (ball(vec 0,&1)) w /\
                       cm_cmap S (ball(vec 0,&1)) w /\
                       (!x. x IN sphere(vec 0,&1) ==> w x = cmw_dat W R t s x)`;;

let CMW_REP_UNIQUE = prove
 (`!S (G:real^K->real^K^K) e u w1 w2.
        cmw_repcont S G e /\
        cm_cmap S (ball(vec 0,&1)) u /\ wan_gdir (ball(vec 0,&1)) G u <= e /\
        cm_minimizer S G (ball(vec 0,&1)) w1 /\ cm_cmap S (ball(vec 0,&1)) w1 /\
        (!x. x IN sphere(vec 0,&1) ==> w1 x = u x) /\
        cm_minimizer S G (ball(vec 0,&1)) w2 /\ cm_cmap S (ball(vec 0,&1)) w2 /\
        (!x. x IN sphere(vec 0,&1) ==> w2 x = u x)
        ==> !x. x IN cball(vec 0,&1) ==> w1 x = w2 x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmw_repcont] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`vec 0:real^2`; `&1`; `\n:num. (u:real^2->real^K)`; `u:real^2->real^K`;
    `\n:num. (w1:real^2->real^K)`; `w2:real^2->real^K`]) THEN
  ASM_REWRITE_TAC[REAL_LT_01; LIM_CONST; VECTOR_SUB_REFL; NORM_0; CMW_DIR_ZERO;
                  REALLIM_CONST] THEN
  ANTS_TAC THENL [SIMP_TAC[EVENTUALLY_TRUE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VECTOR_SUB_EQ; GSYM NORM_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ ~(&0 < a) ==> a = &0`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `norm((w1:real^2->real^K) x - w2 x)`) THEN
  ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
  ASM_REWRITE_TAC[REAL_LT_REFL]);;

let CMW_REP_WORKS = prove
 (`!S (G:real^K->real^K^K) e (W:real^3->real->real^K) R t s.
        cmw_repex S G e /\
        cm_cmap S (ball(vec 0,&1)) (cmw_dat W R t s) /\
        wan_gdir (ball(vec 0,&1)) G (cmw_dat W R t s) <= e
        ==> cm_minimizer S G (ball(vec 0,&1)) (cmw_rep S G W R t s) /\
            cm_cmap S (ball(vec 0,&1)) (cmw_rep S G W R t s) /\
            (!x. x IN sphere(vec 0,&1) ==> cmw_rep S G W R t s x = cmw_dat W R t s x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmw_repex] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?w. cm_minimizer S G (ball(vec 0,&1)) w /\ cm_cmap S (ball(vec 0,&1)) w /\
        (!x. x IN sphere(vec 0,&1) ==> w x = cmw_dat (W:real^3->real->real^K) R t s x)`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
     [`vec 0:real^2`; `&1`; `cmw_dat (W:real^3->real->real^K) R t s`]) THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN MESON_TAC[];
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM cmw_rep]]);;

let CMW_REP_EQ = prove
 (`!S (G:real^K->real^K^K) e (W:real^3->real->real^K) R t s w.
        cmw_repex S G e /\ cmw_repcont S G e /\
        cm_cmap S (ball(vec 0,&1)) (cmw_dat W R t s) /\
        wan_gdir (ball(vec 0,&1)) G (cmw_dat W R t s) <= e /\
        cm_minimizer S G (ball(vec 0,&1)) w /\ cm_cmap S (ball(vec 0,&1)) w /\
        (!x. x IN sphere(vec 0,&1) ==> w x = cmw_dat W R t s x)
        ==> !x. x IN cball(vec 0,&1) ==> cmw_rep S G W R t s x = w x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`;
                 `W:real^3->real->real^K`; `R:real`; `t:real`; `s:real`] CMW_REP_WORKS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC CMW_REP_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`;
                        `cmw_dat (W:real^3->real->real^K) R t s`] THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let CMW_REP_CONST = prove
 (`!S (G:real^K->real^K^K) d e (W:real^3->real->real^K) R t s q.
        cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
        q IN S /\ (!x. cmw_dat W R t s x = q)
        ==> !x. x IN cball(vec 0,&1) ==> cmw_rep S G W R t s x = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMW_TARGET_FACTS) THEN
  SUBGOAL_THEN `cmw_dat (W:real^3->real->real^K) R t s = (\x. q)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `q:real^K`; `vec 0:real^2`; `&1`;
                 `Lam:real`] CMW_CONST_FACTS) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`;
                 `W:real^3->real->real^K`; `R:real`; `t:real`; `s:real`; `\x:real^2. (q:real^K)`]
                CMW_REP_EQ) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* The data and the reflected data are C^0 /\ W^{1,2} maps into S with     *)
(* energies bounded by the slice energies.                                   *)

let CMW_DAT_CMAP = prove
 (`!S (W:real^3->real->real^K) R t s.
        cm_sweep S W /\ cmw_c1sweep W /\ t IN real_interval[&0,&1]
        ==> cm_cmap S (ball(vec 0,&1)) (cmw_dat W R t s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [cmw_c1sweep]) THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^2) (cmw_dat (W:real^3->real->real^K) R t s)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[CMW_DAT_C1]; ALL_TAC] THEN
  REWRITE_TAC[cm_cmap] THEN SIMP_TAC[CLOSURE_BALL; REAL_LT_01] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`cmw_dat (W:real^3->real->real^K) R t s`; `G:real^K->real^K^K`;
                   `vec 0:real^2`; `&1`] CMW_C1_BALL) THEN
    ASM_SIMP_TAC[REAL_LT_01];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[cmw_dat] THEN
    UNDISCH_TAC `cm_sweep S (W:real^3->real->real^K)` THEN REWRITE_TAC[cm_sweep; cm_smap] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[IN_SPHERE_0; BEL_P_CHART]]);;

let CMW_DAT_GDIR = prove
 (`!S (G:real^K->real^K^K) d (W:real^3->real->real^K) R t s lam Lam.
        WAN_S2_STEREO_STATEMENT (:K) /\ cm_target S G d /\
        &0 < lam /\ (!z v. lam * norm v pow 2 <= v dot (G z ** v)) /\
        (!z v. v dot (G z ** v) <= Lam * norm v pow 2) /\
        cm_sweep S W /\ cmw_c1sweep W /\ t IN real_interval[&0,&1] /\
        &0 <= s /\ &0 < R
        ==> wan_gdir (ball(vec 0,&1)) G (cmw_dat W R t s)
            <= max (&0) (Lam * (&2 / lam * cm_sen G (\y. W y t)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMW_TARGET_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [cmw_c1sweep]) THEN
  ASM_CASES_TAC `s = &0` THENL
   [ASM_REWRITE_TAC[cmw_dat; REAL_MUL_RZERO; VECTOR_MUL_LZERO] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`;
                   `(W:real^3->real->real^K) (stereo2_n_inv(vec 0)) t`; `vec 0:real^2`; `&1`;
                   `Lam:real`] CMW_CONST_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_01] THEN
      UNDISCH_TAC `cm_sweep S (W:real^3->real->real^K)` THEN
      REWRITE_TAC[cm_sweep; cm_smap] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      REWRITE_TAC[IN_SPHERE_0; BEL_P_CHART];
      SIMP_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `\y. (W:real^3->real->real^K) y t`; `R * s`;
                 `lam:real`; `Lam:real`] CMW_P_SCALED_ENERGY) THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[cmw_dat] THEN REAL_ARITH_TAC);;

let CMW_RDAT_FACTS = prove
 (`!S (G:real^K->real^K^K) d (W:real^3->real->real^K) R t lam Lam.
        WAN_S2_STEREO_STATEMENT (:K) /\ cm_target S G d /\
        &0 < lam /\ (!z v. lam * norm v pow 2 <= v dot (G z ** v)) /\
        (!z v. v dot (G z ** v) <= Lam * norm v pow 2) /\
        cm_sweep S W /\ cmw_c1sweep W /\ t IN real_interval[&0,&1] /\ &0 < R
        ==> cm_cmap S (ball(vec 0,&1)) (cmw_rdat W R t) /\
            wan_dir (ball(vec 0,&1)) (cmw_rdat W R t) <= &2 / lam * cm_sen G (\y. W y t) /\
            wan_gdir (ball(vec 0,&1)) G (cmw_rdat W R t)
            <= Lam * (&2 / lam * cm_sen G (\y. W y t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMW_TARGET_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [cmw_c1sweep]) THEN
  MP_TAC(ISPECL [`\y. (W:real^3->real->real^K) y t`; `inv R`] CMW_Q_SCALED) THEN
  ASM_SIMP_TAC[REAL_LT_INV] THEN REWRITE_TAC[GSYM cmw_rdat] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `wan_dir (ball(vec 0,&1)) (cmw_rdat (W:real^3->real->real^K) R t) <=
    &2 / lam * cm_sen G (\y. W y t)`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `wan_s2_dir (\y. (W:real^3->real->real^K) y t)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `\y. (W:real^3->real->real^K) y t`; `lam:real`]
                  CMW_S2_DIR_LE_SEN) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ (ASSUME `&0 < lam`))] THEN
    SUBGOAL_THEN `lam * (&2 / lam * cm_sen G (\y. (W:real^3->real->real^K) y t)) =
                  &2 * cm_sen G (\y. W y t)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[cm_cmap] THEN SIMP_TAC[CLOSURE_BALL; REAL_LT_01] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`cmw_rdat (W:real^3->real->real^K) R t`; `G:real^K->real^K^K`;
                     `vec 0:real^2`; `&1`] CMW_C1_BALL) THEN
      ASM_SIMP_TAC[REAL_LT_01];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `1` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[cmw_rdat] THEN
      UNDISCH_TAC `cm_sweep S (W:real^3->real->real^K)` THEN REWRITE_TAC[cm_sweep; cm_smap] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      REWRITE_TAC[IN_SPHERE_0; BEL_P_CHART]];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `Lam * wan_dir (ball(vec 0,&1)) (cmw_rdat (W:real^3->real->real^K) R t)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMW_C1_GDIR_LE THEN ASM_REWRITE_TAC[REAL_LT_01];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^K`; `basis 1:real^K`] o
      check (fun th -> can (find_term ((=) `Lam:real`)) (concl th) && is_forall(concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^K`; `basis 1:real^K`] o
      check (fun th -> can (find_term ((=) `lam:real`)) (concl th) && is_forall(concl th))) THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN ASM_REAL_ARITH_TAC]);;

(* Joint continuity of the replacements in (t,s), uniformly on the disc.    *)

let CMW_REP_CONV = prove
 (`!S (G:real^K->real^K^K) e (W:real^3->real->real^K) R s t (sn:num->real) (tn:num->real).
        cmw_repex S G e /\ cmw_repcont S G e /\ cm_sweep S W /\ cmw_c1sweep W /\
        (!t s. t IN real_interval[&0,&1] /\ s IN real_interval[&0,&1]
               ==> wan_gdir (ball(vec 0,&1)) G (cmw_dat W R t s) <= e) /\
        s IN real_interval[&0,&1] /\ t IN real_interval[&0,&1] /\
        (!n. sn n IN real_interval[&0,&1] /\ tn n IN real_interval[&0,&1]) /\
        ((\n. lift(sn n)) --> lift s) sequentially /\
        ((\n. lift(tn n)) --> lift t) sequentially
        ==> !e'. &0 < e'
                 ==> eventually (\n. !x. x IN cball(vec 0,&1)
                                         ==> norm(cmw_rep S G W R (tn n) (sn n) x -
                                                  cmw_rep S G W R t s x) < e')
                                sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t1 s1. t1 IN real_interval[&0,&1] /\ s1 IN real_interval[&0,&1]
            ==> cm_cmap S (ball(vec 0,&1)) (cmw_dat (W:real^3->real->real^K) R t1 s1) /\
                wan_gdir (ball(vec 0,&1)) G (cmw_dat W R t1 s1) <= e /\
                cm_minimizer S G (ball(vec 0,&1)) (cmw_rep S G W R t1 s1) /\
                cm_cmap S (ball(vec 0,&1)) (cmw_rep S G W R t1 s1) /\
                (!x. x IN sphere(vec 0,&1)
                     ==> cmw_rep S G W R t1 s1 x = cmw_dat W R t1 s1 x)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t1:real`; `s1:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `W:real^3->real->real^K`; `R:real`; `t1:real`; `s1:real`]
                  CMW_DAT_CMAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `wan_gdir (ball(vec 0,&1)) G (cmw_dat (W:real^3->real->real^K) R t1 s1) <= e`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMW_REP_WORKS THEN EXISTS_TAC `e:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^3->real->real^K`; `R:real`; `s:real`; `t:real`; `sn:num->real`;
                 `tn:num->real`] CMW_DAT_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cm_sweep S (W:real^3->real->real^K)` THEN
    SIMP_TAC[cm_sweep];
    STRIP_TAC] THEN
  UNDISCH_TAC `cmw_repcont (S:real^K->bool) (G:real^K->real^K^K) e` THEN
  REWRITE_TAC[cmw_repcont] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`vec 0:real^2`; `&1`;
    `\n. cmw_dat (W:real^3->real->real^K) R ((tn:num->real) n) ((sn:num->real) n)`;
    `cmw_dat (W:real^3->real->real^K) R t s`;
    `\n. cmw_rep S G (W:real^3->real->real^K) R ((tn:num->real) n) ((sn:num->real) n)`;
    `cmw_rep S G (W:real^3->real->real^K) R t s`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_01]; SIMP_TAC[]]);;

(* The homotopy: replacement on the north-chart disc of radius R s.        *)

let cmw_h1 = new_definition
 `cmw_h1 (S:real^K->bool) (G:real^K->real^K^K) (W:real^3->real->real^K) R s (y:real^3) t =
    if ~(y = basis 3) /\ norm(stereo2_n y) < R * s
    then cmw_rep S G W R t s (inv(R * s) % stereo2_n y)
    else W y t`;;

let CMW_STEREO_N_CONT_AT = prove
 (`!y:real^3. y IN sphere(vec 0,&1) /\ ~(y = basis 3) ==> stereo2_n continuous at y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `stereo2_n continuous_on {x:real^3 | x$3 < &1}` MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `0` THEN
    MP_TAC STEX_STEREO2_N_SMOOTH THEN SIMP_TAC[smooth_map_on];
    ALL_TAC] THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_HALFSPACE_COMPONENT_LT] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC STEX_STEREO2_N_DOMAIN THEN REWRITE_TAC[SUBSET; IN_DELETE] THEN ASM_MESON_TAC[]);;

let CMW_H1_SEQ = prove
 (`!S (G:real^K->real^K^K) d e (W:real^3->real->real^K) R s y t
    (sn:num->real) (yn:num->real^3) (tn:num->real).
        cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
        cm_sweep S W /\ cmw_c1sweep W /\ &1 <= R /\
        (!t s. t IN real_interval[&0,&1] /\ s IN real_interval[&0,&1]
               ==> wan_gdir (ball(vec 0,&1)) G (cmw_dat W R t s) <= e) /\
        s IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] /\
        (!n. sn n IN real_interval[&0,&1] /\ yn n IN sphere(vec 0,&1) /\
             tn n IN real_interval[&0,&1]) /\
        ((\n. lift(sn n)) --> lift s) sequentially /\ (yn --> y) sequentially /\
        ((\n. lift(tn n)) --> lift t) sequentially
        ==> ((\n. cmw_h1 S G W R (sn n) (yn n) (tn n)) --> cmw_h1 S G W R s y t)
            sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [cm_sweep]) THEN
  SUBGOAL_THEN `((\n. (W:real^3->real->real^K) (yn n) (tn n)) --> W y t) sequentially`
  ASSUME_TAC THENL [MATCH_MP_TAC CMW_SWEEP_SEQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `y:real^3 = basis 3` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n. (W:real^3->real->real^K) ((yn:num->real^3) n) ((tn:num->real) n)` THEN
    REWRITE_TAC[cmw_h1] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `((yn:num->real^3) --> basis 3) sequentially` THEN REWRITE_TAC[tendsto] THEN
    DISCH_THEN(MP_TAC o SPEC `inv R`) THEN
    ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    MP_TAC(SPEC `n:num` (ASSUME
     `!n. (sn:num->real) n IN real_interval[&0,&1] /\ (yn:num->real^3) n IN sphere(vec 0,&1) /\
          (tn:num->real) n IN real_interval[&0,&1]`)) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(yn:num->real^3) n`; `R:real`] CMW_NORTH_FAR) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `R * (sn:num->real) n <= R` MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT DISCH_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `y IN sphere(vec 0:real^3,&1) DELETE basis 3` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN `((\n. stereo2_n((yn:num->real^3) n)) --> stereo2_n y) sequentially`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_CONTINUOUS_FUNCTION THEN ASM_SIMP_TAC[CMW_STEREO_N_CONT_AT]; ALL_TAC] THEN
  SUBGOAL_THEN `eventually (\n. ~((yn:num->real^3) n = basis 3)) sequentially` ASSUME_TAC THENL
   [UNDISCH_TAC `((yn:num->real^3) --> y) sequentially` THEN REWRITE_TAC[tendsto] THEN
    DISCH_THEN(MP_TAC o SPEC `dist(y:real^3,basis 3)`) THEN ASM_SIMP_TAC[DIST_POS_LT] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC(TAUT `(q ==> ~p) ==> p ==> ~q`) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIST_SYM; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmw_h1 S G (W:real^3->real->real^K) R s y t =
    (if norm(stereo2_n y) < R * s then cmw_rep S G W R t s (inv(R * s) % stereo2_n y)
     else W (stereo2_n_inv(stereo2_n y)) t)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[cmw_h1; STEX_STEREO2_N_LEFT]; ALL_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\n. if norm(stereo2_n((yn:num->real^3) n)) < R * (sn:num->real) n
        then cmw_rep S G (W:real^3->real->real^K) R ((tn:num->real) n) (sn n)
               (inv(R * sn n) % stereo2_n(yn n))
        else W (stereo2_n_inv(stereo2_n(yn n))) (tn n)` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `eventually (\n. ~((yn:num->real^3) n = basis 3)) sequentially` THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[cmw_h1] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(yn:num->real^3) n IN sphere(vec 0,&1) DELETE basis 3` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_DELETE]; ASM_SIMP_TAC[STEX_STEREO2_N_LEFT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cm_minimizer S G (ball(vec 0,&1)) (cmw_rep S G (W:real^3->real->real^K) R t s) /\
    cm_cmap S (ball(vec 0,&1)) (cmw_rep S G W R t s) /\
    (!x. x IN sphere(vec 0,&1) ==> cmw_rep S G W R t s x = cmw_dat W R t s x)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC CMW_REP_WORKS THEN EXISTS_TAC `e:real` THEN
    ASM_SIMP_TAC[CMW_DAT_CMAP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t z. (W:real^3->real->real^K) (stereo2_n_inv z) t`;
                 `\t s. cmw_rep S G (W:real^3->real->real^K) R t s`; `R:real`; `s:real`;
                 `t:real`; `stereo2_n(y:real^3)`; `sn:num->real`; `tn:num->real`;
                 `\n. stereo2_n((yn:num->real^3) n)`] CMW_GLUE_SEQ) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CMW_SWEEP_SEQ THEN ASM_REWRITE_TAC[IN_SPHERE_0; BEL_P_CHART] THEN
    MATCH_MP_TAC LIM_CONTINUOUS_FUNCTION THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT; BEL_P_CHART];
    MATCH_MP_TAC CMW_REP_CONV THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `cm_cmap S (ball(vec 0,&1)) (cmw_rep S G (W:real^3->real->real^K) R t s)` THEN
    SIMP_TAC[cm_cmap; CLOSURE_BALL; REAL_LT_01];
    DISCH_TAC THEN ASM_SIMP_TAC[cmw_dat];
    DISCH_TAC THEN MATCH_MP_TAC CMW_REP_CONST THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `e:real`] THEN
    ASM_REWRITE_TAC[cmw_dat; REAL_MUL_RZERO; VECTOR_MUL_LZERO] THEN
    UNDISCH_TAC `cm_sweep S (W:real^3->real->real^K)` THEN REWRITE_TAC[cm_sweep; cm_smap] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[IN_SPHERE_0; BEL_P_CHART];
    UNDISCH_TAC `s IN real_interval[&0,&1]` THEN SIMP_TAC[IN_REAL_INTERVAL]]);;

(* Sweep facts; uniform continuity of a sweep in the sphere variable.        *)

let CMW_SWEEP_FACTS = prove
 (`!S (W:real^3->real->real^K).
        cm_sweep S W
        ==> continuous_map
              (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                             (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
              (\(y,t). W y t) /\
            (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> W y t IN S) /\
            (!y t. y IN sphere(vec 0,&1) /\ (t = &0 \/ t = &1) ==> W y t = W (basis 3) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_sweep; cm_smap] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN SUBST1_TAC)) THEN
  ASM_MESON_TAC[]);;

let CMW_SWEEP_UNIF = prove
 (`!(W:real^3->real->real^K).
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
          (\(y,t). W y t)
        ==> !e. &0 < e
                ==> ?r. &0 < r /\
                        !y y' t. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1) /\
                                 t IN real_interval[&0,&1] /\ norm(y - y') < r
                                 ==> norm(W y t - W y' t) < e`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `KK = {x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                             drop(sndcart x) IN real_interval[&0,&1]}` THEN
  SUBGOAL_THEN `compact (KK:real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `KK = (sphere(vec 0:real^3,&1)) PCROSS (interval[vec 0:real^1,vec 1])`
    SUBST1_TAC THENL
     [EXPAND_TAC "KK" THEN
      REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_REAL_INTERVAL; IN_INTERVAL_1;
                  DROP_VEC];
      MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_SPHERE; COMPACT_INTERVAL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^(3,1)finite_sum. (W:real^3->real->real^K) (fstcart x) (drop(sndcart x)))
    continuous_on KK`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY; o_DEF] THEN
    MAP_EVERY X_GEN_TAC [`pp:num->real^(3,1)finite_sum`; `a:real^(3,1)finite_sum`] THEN
    EXPAND_TAC "KK" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`W:real^3->real->real^K`; `fstcart(a:real^(3,1)finite_sum)`;
                   `drop(sndcart(a:real^(3,1)finite_sum))`;
                   `\n. fstcart((pp:num->real^(3,1)finite_sum) n)`;
                   `\n. drop(sndcart((pp:num->real^(3,1)finite_sum) n))`] CMW_SWEEP_SEQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN CONJ_TAC THEN
    MATCH_MP_TAC LIM_LINEAR THEN ASM_REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^(3,1)finite_sum. (W:real^3->real->real^K) (fstcart x) (drop(sndcart x))`;
                 `KK:real^(3,1)finite_sum->bool`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `y':real^3`; `t:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (y':real^3) (lift t)`;
                                `pastecart (y:real^3) (lift t)`]) THEN
  EXPAND_TAC "KK" THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                  DIST_PASTECART_CANCEL] THEN
  REWRITE_TAC[dist] THEN ASM_REWRITE_TAC[]);;

(* The homotopy is continuous, takes values in S and has constant ends.     *)

let CMW_H1_CONT = prove
 (`!S (G:real^K->real^K^K) d e (W:real^3->real->real^K) R.
        cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
        cm_sweep S W /\ cmw_c1sweep W /\ &1 <= R /\
        (!t s. t IN real_interval[&0,&1] /\ s IN real_interval[&0,&1]
               ==> wan_gdir (ball(vec 0,&1)) G (cmw_dat W R t s) <= e)
        ==> continuous_map
              (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                 (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                                (subtopology euclideanreal (real_interval[&0,&1]))),
               euclidean)
              (\(s,(y,t)). cmw_h1 S G W R s y t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMW_PROD3_SEQ_CONT THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CMW_H1_SEQ THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `e:real`] THEN ASM_REWRITE_TAC[]);;

let CMW_H1_FACTS = prove
 (`!S (G:real^K->real^K^K) d e (W:real^3->real->real^K) R.
        cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
        cm_sweep S W /\ cmw_c1sweep W /\ &1 <= R /\
        (!t s. t IN real_interval[&0,&1] /\ s IN real_interval[&0,&1]
               ==> wan_gdir (ball(vec 0,&1)) G (cmw_dat W R t s) <= e)
        ==> (!s y t. s IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) /\
                     t IN real_interval[&0,&1] ==> cmw_h1 S G W R s y t IN S) /\
            (!s y t. s IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) /\
                     (t = &0 \/ t = &1) ==> cmw_h1 S G W R s y t = W (basis 3) t) /\
            (!y t. cmw_h1 S G W R (&0) y t = W y t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP CMW_SWEEP_FACTS (ASSUME `cm_sweep S (W:real^3->real->real^K)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "ins") (LABEL_TAC "ends"))) THEN
  SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t s. t IN real_interval[&0,&1] /\ s IN real_interval[&0,&1]
          ==> cm_cmap S (ball(vec 0,&1)) (cmw_rep S G (W:real^3->real->real^K) R t s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`;
                   `W:real^3->real->real^K`; `R:real`; `t:real`; `s:real`] CMW_REP_WORKS) THEN
    ASM_SIMP_TAC[CMW_DAT_CMAP];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[cmw_h1] THEN COND_CASES_TAC THENL
     [ALL_TAC; USE_THEN "ins" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `cm_cmap S (ball(vec 0,&1)) (cmw_rep S G (W:real^3->real->real^K) R t s)`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SIMP_TAC[cm_cmap; CLOSURE_BALL; REAL_LT_01] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[CMW_SCALE_IN_BALL];
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `t IN real_interval[&0,&1]` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[cmw_h1] THEN COND_CASES_TAC THENL
     [ALL_TAC; USE_THEN "ends" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`;
                   `W:real^3->real->real^K`; `R:real`; `t:real`; `s:real`;
                   `(W:real^3->real->real^K) (basis 3) t`] CMW_REP_CONST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "ins" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `x:real^2` THEN REWRITE_TAC[cmw_dat] THEN
        USE_THEN "ends" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SPHERE_0; BEL_P_CHART]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[CMW_SCALE_IN_BALL]];
    REWRITE_TAC[cmw_h1; REAL_MUL_RZERO; NORM_ARITH `!x:real^2. ~(norm x < &0)`]]);;

(* ========================================================================= *)
(* The homotopy to constant slices and CMW_POS_STATEMENT.                    *)
(* ========================================================================= *)

let CMW_H1_HOMOTOPY = prove
 (`!S (G:real^K->real^K^K) d e (W:real^3->real->real^K) R.
        cm_target S G d /\ cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
        cm_sweep S W /\ cmw_c1sweep W /\ &1 <= R /\
        (!t s. t IN real_interval[&0,&1] /\ s IN real_interval[&0,&1]
               ==> wan_gdir (ball(vec 0,&1)) G (cmw_dat W R t s) <= e)
        ==> cm_shomotopic S W (cmw_h1 S G W R (&1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMW_H1_CONT) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMW_H1_FACTS) THEN
  REWRITE_TAC[cm_shomotopic] THEN EXISTS_TAC `cmw_h1 S G (W:real^3->real->real^K) R` THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let CMW_END_CONT = prove
 (`!H:real->real^3->real->real^K.
        continuous_map
          (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
             (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                            (subtopology euclideanreal (real_interval[&0,&1]))),
           euclidean)
          (\(s,(y,t)). H s y t)
        ==> continuous_map
              (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                             (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
              (\(y,t). H (&1) y t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\(y,t). (H:real->real^3->real->real^K) (&1) y t) =
    (\(s,(y,t)). H s y t) o (\z:real^3#real. (&1,z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC
   `prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
      (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                     (subtopology euclideanreal (real_interval[&0,&1])))` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL; REAL_POS;
                  REAL_LE_REFL]);;

let CMW_CONST_SLICE_CONT = prove
 (`!(W:real^3->real->real^K) y0.
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
          (\(y,t). W y t) /\ y0 IN sphere(vec 0,&1)
        ==> continuous_map
              (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                             (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
              (\(y,t). W y0 t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\(y,t). (W:real^3->real->real^K) y0 t) =
    (\(y,t). W y t) o (\z:real^3#real. (y0,SND z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC
   `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                  (subtopology euclideanreal (real_interval[&0,&1]))` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_CONST; CONTINUOUS_MAP_SND;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]);;

(* At s = 1 the replaced sweep is within d/2 of the constant slices at the *)
(* north pole: C0EST applied to the reflected data.                          *)

let CMW_V_CLOSE = prove
 (`!S (G:real^K->real^K^K) d e delta (W:real^3->real->real^K) R lam Lam rho.
        (!u w q. q IN S /\ cm_cmap S (ball(vec 0,&1)) u /\
                 wan_dir (ball(vec 0,&1)) u <= delta /\ wan_gdir (ball(vec 0,&1)) G u <= e /\
                 (!x. x IN cball(vec 0,&1) ==> norm(u x - q) <= delta) /\
                 cm_minimizer S G (ball(vec 0,&1)) w /\ cm_cmap S (ball(vec 0,&1)) w /\
                 (!x. x IN sphere(vec 0,&1) ==> w x = u x)
                 ==> !x. x IN cball(vec 0,&1) ==> norm(w x - q) < d / &2) /\
        (!y y' t. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1) /\
                  t IN real_interval[&0,&1] /\ norm(y - y') < rho
                  ==> norm(W y t - W y' t) < min delta (d / &2)) /\
        (!t. t IN real_interval[&0,&1]
             ==> &2 / lam * cm_sen G (\y. W y t) <= delta /\
                 Lam * (&2 / lam * cm_sen G (\y. W y t)) <= e) /\
        (!t s. t IN real_interval[&0,&1] /\ s IN real_interval[&0,&1]
               ==> wan_gdir (ball(vec 0,&1)) G (cmw_dat W R t s) <= e) /\
        WAN_S2_STEREO_STATEMENT (:K) /\ cm_target S G d /\
        cmw_repex S G e /\ cmw_repcont S G e /\ &0 < e /\
        &0 < lam /\ (!z v. lam * norm v pow 2 <= v dot (G z ** v)) /\
        (!z v. v dot (G z ** v) <= Lam * norm v pow 2) /\
        cm_sweep S W /\ cmw_c1sweep W /\ &1 <= R /\ &2 / R < rho
        ==> !y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                  ==> norm(cmw_h1 S G W R (&1) y t - W (basis 3) t) < d / &2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c0") (CONJUNCTS_THEN2 (LABEL_TAC "uc")
   (CONJUNCTS_THEN2 (LABEL_TAC "en") (CONJUNCTS_THEN2 (LABEL_TAC "gd") STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `t:real`] THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP CMW_SWEEP_FACTS (ASSUME `cm_sweep S (W:real^3->real->real^K)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ins") (LABEL_TAC "ends"))) THEN
  SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 IN real_interval[&0,&1]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[cmw_h1; REAL_MUL_RID] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `x < min delta b ==> x < b`) THEN
    USE_THEN "uc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 / R` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMW_NORTH_CAP THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_NOT_LT]] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `W:real^3->real->real^K`;
                 `R:real`; `t:real`; `lam:real`; `Lam:real`] CMW_RDAT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`;
                 `W:real^3->real->real^K`; `R:real`; `t:real`; `&1`] CMW_REP_WORKS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CMW_DAT_CMAP] THEN USE_THEN "gd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  USE_THEN "en" (MP_TAC o C MP (ASSUME `t IN real_interval[&0,&1]`) o SPEC `t:real`) THEN
  STRIP_TAC THEN
  USE_THEN "c0" (MP_TAC o SPECL
   [`cmw_rdat (W:real^3->real->real^K) R t`; `cmw_rep S G (W:real^3->real->real^K) R t (&1)`;
    `(W:real^3->real->real^K) (basis 3) t`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "ins" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[REAL_LE_TRANS];
      ASM_MESON_TAC[REAL_LE_TRANS];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[cmw_rdat] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC(REAL_ARITH `x < min a (d / &2) ==> x < a`) THEN
      USE_THEN "uc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SPHERE_0; BEL_P_CHART] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 / R` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC REAL_LE_TRANS `&2 * norm(inv R % x:real^2)` THEN
      REWRITE_TAC[CMW_STEREO_S_NEAR_N] THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs R = R`; real_div] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      UNDISCH_TAC `x IN cball(vec 0:real^2,&1)` THEN REWRITE_TAC[IN_CBALL_0];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`W:real^3->real->real^K`; `R:real`; `t:real`; `x:real^2`]
                    CMW_DAT_CIRCLE) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `inv R % stereo2_n(y:real^3) IN cball(vec 0,&1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`R:real`; `stereo2_n(y:real^3)`] CMW_SCALE_IN_BALL) THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[]]);;

let CMW_ENERGY_ARITH = prove
 (`!lam Lam e0 delta x.
        &0 < lam /\ &0 < Lam /\ x < min (lam * e0 / (&2 * Lam)) (lam * delta / &2)
        ==> &2 / lam * x <= delta /\ Lam * (&2 / lam * x) <= e0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    TRANS_TAC REAL_LTE_TRANS `&2 / lam * (lam * delta / &2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    TRANS_TAC REAL_LTE_TRANS `Lam * (&2 / lam * (lam * e0 / (&2 * Lam)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `&0 < Lam` THEN CONV_TAC REAL_FIELD]]);;

(* CM's positivity: sweepouts of small energy with C^1 slices are homotopic *)
(* to sweepouts with constant slices.                                        *)

let CMW_POS = prove
 (`CM_REPLACEMENT_STATEMENT (:K) /\ WAN_S2_STEREO_STATEMENT (:K)
   ==> CMW_POS_STATEMENT (:K)`,
  STRIP_TAC THEN REWRITE_TAC[CMW_POS_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] CMW_REPLACEMENT_UNPACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMW_TARGET_FACTS) THEN
  SUBGOAL_THEN `&0 < Lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`; `d / &2`]
                CMW_C0EST) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (lam * e0 / (&2 * Lam)) (lam * delta / &2)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  X_GEN_TAC `W:real^3->real->real^K` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> &2 / lam * cm_sen G (\y. (W:real^3->real->real^K) y t) <= delta /\
            Lam * (&2 / lam * cm_sen G (\y. W y t)) <= e0`
  (LABEL_TAC "en") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CMW_ENERGY_ARITH THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP CMW_SWEEP_FACTS (ASSUME `cm_sweep S (W:real^3->real->real^K)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ins") (K ALL_TAC))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `min delta (d / &2)` o MATCH_MP CMW_SWEEP_UNIF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc"))) THEN
  ABBREV_TAC `R = &1 + &4 / rho` THEN
  SUBGOAL_THEN `&1 <= R /\ &2 / R < rho` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &4 / rho` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [EXPAND_TAC "R" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [EXPAND_TAC "R" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN EXPAND_TAC "R" THEN
    SUBGOAL_THEN `rho * (&1 + &4 / rho) = rho + &4` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t s. t IN real_interval[&0,&1] /\ s IN real_interval[&0,&1]
          ==> wan_gdir (ball(vec 0,&1)) G (cmw_dat (W:real^3->real->real^K) R t s) <= e0`
  (LABEL_TAC "gd") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `W:real^3->real->real^K`;
                   `R:real`; `t:real`; `s:real`; `lam:real`; `Lam:real`] CMW_DAT_GDIR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s IN real_interval[&0,&1]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "en" (MP_TAC o C MP (ASSUME `t IN real_interval[&0,&1]`) o SPEC `t:real`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\t. (W:real^3->real->real^K) (basis 3) t` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CMW_SHOMOTOPIC_TRANS THEN
  EXISTS_TAC `cmw_h1 S G (W:real^3->real->real^K) R (&1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMW_H1_HOMOTOPY THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `e0:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`;
                 `W:real^3->real->real^K`; `R:real`] CMW_H1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`; `delta:real`;
                 `W:real^3->real->real^K`; `R:real`; `lam:real`; `Lam:real`; `rho:real`]
                CMW_V_CLOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC CMW_CLOSE_SHOMOTOPIC THEN
  MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 IN real_interval[&0,&1]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`;
                   `W:real^3->real->real^K`; `R:real`] CMW_H1_CONT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP CMW_END_CONT) THEN REWRITE_TAC[];
    MATCH_MP_TAC CMW_CONST_SLICE_CONT THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THENL
     [ASM_SIMP_TAC[];
      USE_THEN "ins" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `d / &2` THEN ASM_SIMP_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

