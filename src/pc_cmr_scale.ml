(* ========================================================================= *)
(* Unit pc_cmr_scale (a unit of the replacement chain of pc_cm_replacement): *)
(* the planar similarities x |-> r % x + c (r > 0) transport W^{1,2}, the    *)
(* energies wan_gdir / wan_dir (conformal invariance in dimension 2),        *)
(* W^{1,2}_0, the map classes and the minimizer property, with preimage sets *)
(* IMAGE (\x. inv r % x + --(inv r % c)) s as in HAS_INTEGRAL_AFFINITY.      *)
(*                                                                           *)
(* Sets, measurability, L^2 and null sets.                                   *)
(* ========================================================================= *)

needs "src/pc_cmr_ball.ml";;
needs "src/pc_hm_convexity.ml";;

prioritize_real();;
type_invention_error := true;;

let CMR_AFF_INV = prove
 (`!r (c:real^N) x. ~(r = &0)
     ==> inv r % (r % x + c) + --(inv r % c) = x /\
         r % (inv r % x + --(inv r % c)) + c = x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; VECTOR_MUL_RNEG] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RINV; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC);;

let CMR_AFF_PREIMAGE = prove
 (`!r (c:real^N) s. ~(r = &0)
     ==> IMAGE (\x. inv r % x + --(inv r % c)) s = {x | r % x + c IN s} /\
         IMAGE (\x. r % x + c) (IMAGE (\x. inv r % x + --(inv r % c)) s) = s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[CMR_AFF_INV];
      DISCH_TAC THEN EXISTS_TAC `r % x + c:real^N` THEN ASM_SIMP_TAC[CMR_AFF_INV]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN EXISTS_TAC `inv r % y + --(inv r % c):real^N` THEN
      ASM_SIMP_TAC[CMR_AFF_INV]]]);;

let CMR_AFF_BALLS = prove
 (`!r (c:real^N) a e. &0 < r
     ==> IMAGE (\x. inv r % x + --(inv r % c)) (ball(a,e)) =
           ball(inv r % a + --(inv r % c),e / r) /\
         IMAGE (\x. inv r % x + --(inv r % c)) (cball(a,e)) =
           cball(inv r % a + --(inv r % c),e / r) /\
         IMAGE (\x. inv r % x + --(inv r % c)) (sphere(a,e)) =
           sphere(inv r % a + --(inv r % c),e / r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CMR_AFF_PREIMAGE; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL; IN_CBALL; IN_SPHERE] THEN
  SUBGOAL_THEN
   `!x:real^N. dist(a,r % x + c) = r * dist(inv r % a + --(inv r % c),x)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[dist] THEN
    SUBGOAL_THEN `a - (r % x + c):real^N = r % ((inv r % a + --(inv r % c)) - x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC;
                  VECTOR_MUL_RNEG] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_RDIV_EQ; REAL_EQ_RDIV_EQ] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let CMR_AFF_MEASURABLE = prove
 (`!(f:real^N->real^K) s r c.
     ~(r = &0) /\ f measurable_on s
     ==> (\x. f(r % x + c)) measurable_on (IMAGE (\x. inv r % x + --(inv r % c)) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (f:real^N->real^K)(r % x + c)) = (\y. f(c + y)) o (\x. r % x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTOR_ADD_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. r % x`; `\y:real^N. (f:real^N->real^K)(c + y)`;
                 `IMAGE (\x:real^N. inv r % x + --(inv r % c)) s`]
                MEASURABLE_ON_LINEAR_IMAGE_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LINEAR_SCALING] THEN ASM_MESON_TAC[VECTOR_MUL_LCANCEL];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MEASURABLE_ON_TRANSLATION_EQ; GSYM IMAGE_o; o_DEF] THEN
  SUBGOAL_THEN `IMAGE (\x:real^N. c + r % (inv r % x + --(inv r % c))) s = s`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
  ASM_SIMP_TAC[ONCE_REWRITE_RULE[VECTOR_ADD_SYM] CMR_AFF_INV; UNWIND_THM1] THEN
  MESON_TAC[]);;

let CMR_AFF_NEGLIGIBLE = prove
 (`!(t:real^N->bool) r c.
     ~(r = &0) /\ negligible t
     ==> negligible (IMAGE (\x. inv r % x + --(inv r % c)) t)`,
  SIMP_TAC[NEGLIGIBLE_AFFINITY]);;

let CMR_AFF_SET = prove
 (`!(P:real^N->bool) s r c.
     ~(r = &0)
     ==> {x | x IN IMAGE (\x. inv r % x + --(inv r % c)) s /\ P(r % x + c)} =
         IMAGE (\x. inv r % x + --(inv r % c)) {y | y IN s /\ P y}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMR_AFF_PREIMAGE] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM]);;

let CMR_AFF_INTEGRAL = prove
 (`!(f:real^2->real^1) s r c.
     &0 < r /\ f integrable_on s
     ==> (\x. f(r % x + c)) integrable_on (IMAGE (\x. inv r % x + --(inv r % c)) s) /\
         integral (IMAGE (\x. inv r % x + --(inv r % c)) s) (\x. f(r % x + c)) =
         inv(r pow 2) % integral s f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^2->real^1`; `integral s (f:real^2->real^1)`; `s:real^2->bool`;
                 `r:real`; `c:real^2`] HAS_INTEGRAL_AFFINITY) THEN
  ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL; REAL_LT_IMP_NZ; DIMINDEX_2;
               REAL_ARITH `&0 < r ==> abs r = r`] THEN
  MESON_TAC[integrable_on; INTEGRAL_UNIQUE]);;

let CMR_AFF_LSPACE = prove
 (`!(f:real^2->real^K) s r c.
     &0 < r /\ f IN lspace s (&2)
     ==> (\x. f(r % x + c)) IN lspace (IMAGE (\x. inv r % x + --(inv r % c)) s) (&2) /\
         lnorm (IMAGE (\x. inv r % x + --(inv r % c)) s) (&2) (\x. f(r % x + c)) =
         lnorm s (&2) f / r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(f:real^2->real^K) IN lspace s (&2)` THEN
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift(norm((f:real^2->real^K) x) rpow &2)`; `s:real^2->bool`;
                 `r:real`; `c:real^2`] CMR_AFF_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMR_AFF_MEASURABLE; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[lnorm] THEN ASM_REWRITE_TAC[DROP_CMUL] THEN
  SUBGOAL_THEN `&0 <= drop(integral s (\x. lift(norm((f:real^2->real^K) x) rpow &2)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    SIMP_TAC[RPOW_POS_LE; NORM_POS_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_MUL; REAL_LE_INV_EQ; REAL_LE_POW_2; real_div] THEN
  SUBGOAL_THEN `inv(r pow 2) rpow inv(&2) = inv r` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_INV] THEN
    SUBGOAL_THEN `&0 <= inv r` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM RPOW_POW; RPOW_RPOW] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[RPOW_POW; REAL_POW_1];
    REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* W^{1,2}, weak partials and the energies under planar                      *)
(* similarities (WAN_W12_DIFFEO; conformal invariance of wan_gdir and       *)
(* wan_dir in dimension 2).                                                  *)
(* ========================================================================= *)

let CMR_AFF_SMOOTH = prove
 (`!r (c:real^N). smooth_map_on (:real^N) (\x. r % x + c)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. r % x`; `c:real^N`] WAN_SMOOTH_AFFINE) THEN
  REWRITE_TAC[LINEAR_SCALING]);;

let CMR_AFF_DERIV = prove
 (`!r (c:real^N) x. frechet_derivative (\x. r % x + c) (at x) = (\h. r % h)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MP_TAC(ISPECL [`\x:real^N. r % x`; `\h:real^N. r % h`; `\x:real^N. c:real^N`;
                 `\h:real^N. vec 0:real^N`; `at (x:real^N)`] HAS_DERIVATIVE_ADD) THEN
  REWRITE_TAC[VECTOR_ADD_RID; HAS_DERIVATIVE_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SCALING]);;

let CMR_VSUM2_BASIS = prove
 (`!r (f:num->real^K) i.
     1 <= i /\ i <= 2
     ==> vsum(1..dimindex(:2)) (\j. (r % basis i:real^2)$j % f j) = r % f i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[DIMINDEX_2; VSUM_2; VECTOR_MUL_COMPONENT] THEN
  SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; VECTOR_MUL_LZERO; VECTOR_ADD_LID;
              VECTOR_ADD_RID]);;

let CMR_AFF_W12 = prove
 (`!(s:real^2->bool) (u:real^2->real^K) r c.
     open s /\ &0 < r /\ wan_w12 s u
     ==> wan_w12 (IMAGE (\x. inv r % x + --(inv r % c)) s) (\x. u(r % x + c)) /\
         !i. 1 <= i /\ i <= 2
             ==> wan_wpd (IMAGE (\x. inv r % x + --(inv r % c)) s) i (\x. u(r % x + c))
                   (\x. r % wan_wd s i u (r % x + c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W12_DIFFEO) THEN
  REWRITE_TAC[WAN_W12_DIFFEO_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`s:real^2->bool`; `IMAGE (\x:real^2. inv r % x + --(inv r % c)) s`;
    `\x:real^2. r % x + c`; `\x:real^2. inv r % x + --(inv r % c)`; `u:real^2->real^K`]) THEN
  REWRITE_TAC[CMR_AFF_DERIV] THEN
  SUBGOAL_THEN `~(r = &0) /\ ~(inv r = &0)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_AFFINITY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV; REWRITE_RULE[smooth_map_on] CMR_AFF_SMOOTH];
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV; REWRITE_RULE[smooth_map_on] CMR_AFF_SMOOTH];
      ASM_SIMP_TAC[CMR_AFF_PREIMAGE; IN_ELIM_THM; CMR_AFF_INV];
      ASM_SIMP_TAC[CMR_AFF_PREIMAGE; IN_ELIM_THM; CMR_AFF_INV];
      EXISTS_TAC `abs r` THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`\x:real^2. x`; `r:real`] ONORM_CMUL) THEN
      REWRITE_TAC[LINEAR_ID; ONORM_ID; REAL_MUL_RID] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th; REAL_LE_REFL]);
      REWRITE_TAC[CMR_AFF_DERIV] THEN
      EXISTS_TAC `abs(inv r)` THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`\x:real^2. x`; `inv r:real`] ONORM_CMUL) THEN
      REWRITE_TAC[LINEAR_ID; ONORM_ID; REAL_MUL_RID] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th; REAL_LE_REFL])];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[DIMINDEX_2] THEN
  ASM_SIMP_TAC[GSYM DIMINDEX_2; CMR_VSUM2_BASIS]);;

let CMR_AFF_WD = prove
 (`!(s:real^2->bool) (u:real^2->real^K) r c i.
     open s /\ &0 < r /\ wan_w12 s u /\ 1 <= i /\ i <= 2
     ==> negligible {x | x IN IMAGE (\x. inv r % x + --(inv r % c)) s /\
                         ~(wan_wd (IMAGE (\x. inv r % x + --(inv r % c)) s) i
                                  (\x. u(r % x + c)) x =
                           r % wan_wd s i u (r % x + c))}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WD_UNIQUE THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `u:real^2->real^K`; `r:real`; `c:real^2`] CMR_AFF_W12) THEN
  ASM_SIMP_TAC[OPEN_AFFINITY; REAL_INV_EQ_0; REAL_LT_IMP_NZ; DIMINDEX_2]);;

let CMR_AFF_QUAD = prove
 (`!(s:real^2->bool) (u:real^2->real^K) (a:real^2->real^K) (G:real^K->real^K^K) Lam r c.
     lebesgue_measurable s /\ &0 < r /\ u measurable_on s /\ a IN lspace s (&2) /\
     CMR_GCOND G Lam
     ==> integral (IMAGE (\x. inv r % x + --(inv r % c)) s)
           (\x. lift((r % a(r % x + c)) dot (G(u(r % x + c)) ** (r % a(r % x + c))))) =
         integral s (\y. lift(a y dot (G(u y) ** a y)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CMR_GCOND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\y. lift((a:real^2->real^K) y dot ((G:real^K->real^K^K)(u y) ** a y)))
                integrable_on s` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC CMR_GQUAD_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL; REAL_MUL_ASSOC; LIFT_CMUL] THEN
  MP_TAC(ISPECL [`\y. lift((a:real^2->real^K) y dot ((G:real^K->real^K^K)(u y) ** a y))`;
                 `s:real^2->bool`; `r:real`; `c:real^2`] CMR_AFF_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL] THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `(r * r) * inv(r pow 2) = &1` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
  UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD);;

let CMR_AFF_GDIR = prove
 (`!(s:real^2->bool) (G:real^K->real^K^K) (u:real^2->real^K) Lam r c.
     open s /\ &0 < r /\ wan_w12 s u /\ CMR_GCOND G Lam
     ==> wan_gdir (IMAGE (\x. inv r % x + --(inv r % c)) s) G (\x. u(r % x + c)) =
         wan_gdir s G u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_gdir; DIMINDEX_2] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `i:num`; `u:real^2->real^K`] WAN_WD_WORKS) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^2->real^K) measurable_on s` ASSUME_TAC THENL
   [UNDISCH_TAC `wan_w12 s (u:real^2->real^K)` THEN
    REWRITE_TAC[wan_w12; lspace; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `integral (IMAGE (\x. inv r % x + --(inv r % c)) s)
      (\x. lift((r % wan_wd s i (u:real^2->real^K) (r % x + c)) dot
                ((G:real^K->real^K^K)(u(r % x + c)) ** (r % wan_wd s i u (r % x + c)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC
     `{x | x IN IMAGE (\x. inv r % x + --(inv r % c)) s /\
           ~(wan_wd (IMAGE (\x. inv r % x + --(inv r % c)) s) i (\x. (u:real^2->real^K)(r % x + c)) x =
             r % wan_wd s i u (r % x + c))}` THEN
    ASM_SIMP_TAC[CMR_AFF_WD] THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC CMR_AFF_QUAD THEN EXISTS_TAC `Lam:real` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]]);;

let CMR_AFF_DIR = prove
 (`!(s:real^2->bool) (u:real^2->real^K) r c.
     open s /\ &0 < r /\ wan_w12 s u
     ==> wan_dir (IMAGE (\x. inv r % x + --(inv r % c)) s) (\x. u(r % x + c)) =
         wan_dir s u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CMR_GCOND (\z:real^K. mat 1:real^K^K) (&1)` ASSUME_TAC THENL
   [REWRITE_TAC[CMR_GCOND; o_DEF; CONTINUOUS_ON_CONST; TRANSP_MAT; MATRIX_VECTOR_MUL_LID] THEN
    REWRITE_TAC[DOT_POS_LE; GSYM NORM_POW_2; REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t (v:real^2->real^K). wan_dir t v = wan_gdir t (\z:real^K. mat 1:real^K^K) v`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[wan_dir; wan_gdir; MATRIX_VECTOR_MUL_LID; GSYM NORM_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC CMR_AFF_GDIR THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* W^{1,2}_0, the map classes, cm_gen and the minimizer                      *)
(* property under planar similarities.                                      *)
(* ========================================================================= *)

let CMR_AFF_INV2 = prove
 (`!r (c:real^N). ~(r = &0)
     ==> (\x. inv(inv r) % x + --(inv(inv r) % --(inv r % c))) = (\x. r % x + c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; REAL_INV_INV; VECTOR_MUL_RNEG;
    VECTOR_NEG_NEG; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID]);;

let CMR_AFF_W120 = prove
 (`!(s:real^2->bool) (h:real^2->real^K) r c.
     open s /\ &0 < r /\ wan_w120 s h
     ==> wan_w120 (IMAGE (\x. inv r % x + --(inv r % c)) s) (\x. h(r % x + c))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_w120] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `f:num->real^2->real^K` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `~(r = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CMR_AFF_W12] THEN
  EXISTS_TAC `\n x. (f:num->real^2->real^K) n (r % x + c)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n. wan_w12 s (\x. (f:num->real^2->real^K) n x - h x)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `(f:num->real^2->real^K) n`] WAN_VTEST_W12) THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_vtest")) (concl th))) THEN
    REWRITE_TAC[wan_vtest] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(\x. (f:num->real^2->real^K) n (r % x + c)) = f n o (\x. r % x + c)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; CMR_AFF_SMOOTH];
      ALL_TAC] THEN
    EXISTS_TAC `IMAGE (\x:real^2. inv r % x + --(inv r % c)) k` THEN
    ASM_SIMP_TAC[COMPACT_AFFINITY; IMAGE_SUBSET] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    DISCH_TAC THEN UNDISCH_TAC `~((x:real^2) IN IMAGE (\x. inv r % x + --(inv r % c)) k)` THEN
    ASM_SIMP_TAC[CMR_AFF_PREIMAGE; IN_ELIM_THM];
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n. lnorm s (&2) (\x. (f:num->real^2->real^K) n x - h x) * inv r` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\x. (f:num->real^2->real^K) n x - h x`; `s:real^2->bool`;
                     `r:real`; `c:real^2`] CMR_AFF_LSPACE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_w12")) (concl th))) THEN
        REWRITE_TAC[wan_w12] THEN SIMP_TAC[];
        REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[real_div]];
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `&0 = &0 * inv r`] THEN
      MATCH_MP_TAC REALLIM_RMUL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n. wan_dir s (\x. (f:num->real^2->real^K) n x - h x)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `\x. (f:num->real^2->real^K) n x - h x`;
                   `r:real`; `c:real^2`] CMR_AFF_DIR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM)]);;

let CMR_AFF_WMAP = prove
 (`!S (s:real^2->bool) (w:real^2->real^K) r c.
     open s /\ &0 < r /\ cm_wmap S s w
     ==> cm_wmap S (IMAGE (\x. inv r % x + --(inv r % c)) s) (\x. w(r % x + c))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_wmap] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMR_AFF_W12] THEN
  EXISTS_TAC `IMAGE (\x:real^2. inv r % x + --(inv r % c)) Z` THEN
  ASM_SIMP_TAC[CMR_AFF_NEGLIGIBLE; REAL_LT_IMP_NZ] THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF] THEN
  ASM_SIMP_TAC[CMR_AFF_PREIMAGE; REAL_LT_IMP_NZ; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF]);;

let CMR_AFF_CMAP = prove
 (`!S (s:real^2->bool) (w:real^2->real^K) r c.
     open s /\ &0 < r /\ cm_cmap S s w
     ==> cm_cmap S (IMAGE (\x. inv r % x + --(inv r % c)) s) (\x. w(r % x + c))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_cmap; CLOSURE_AFFINITY] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMR_AFF_W12; CMR_AFF_PREIMAGE; REAL_LT_IMP_NZ; IN_ELIM_THM] THEN
  SUBGOAL_THEN `(\x. (w:real^2->real^K)(r % x + c)) = w o (\x. r % x + c)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[CMR_AFF_SMOOTH];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `closure(s:real^2->bool)` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]]);;

let CMR_AFF_MINIMIZER = prove
 (`!S (G:real^K->real^K^K) (s:real^2->bool) (w:real^2->real^K) Lam r c.
     open s /\ &0 < r /\ CMR_GCOND G Lam /\ cm_minimizer S G s w
     ==> cm_minimizer S G (IMAGE (\x. inv r % x + --(inv r % c)) s) (\x. w(r % x + c))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_minimizer] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMR_AFF_WMAP] THEN
  X_GEN_TAC `w':real^2->real^K` THEN STRIP_TAC THEN
  ABBREV_TAC `t = IMAGE (\x:real^2. inv r % x + --(inv r % c)) s` THEN
  SUBGOAL_THEN `~(r = &0) /\ &0 < inv r` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `open(t:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[OPEN_AFFINITY; REAL_INV_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^2. inv(inv r) % x + --(inv(inv r) % --(inv r % c))) t = s`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CMR_AFF_INV2] THEN EXPAND_TAC "t" THEN ASM_SIMP_TAC[CMR_AFF_PREIMAGE];
    ALL_TAC] THEN
  ABBREV_TAC `w'' = \y:real^2. (w':real^2->real^K)(inv r % y + --(inv r % c))` THEN
  SUBGOAL_THEN `(\x:real^2. (w'':real^2->real^K)(r % x + c)) = w'` ASSUME_TAC THENL
   [EXPAND_TAC "w''" THEN ASM_SIMP_TAC[FUN_EQ_THM; CMR_AFF_INV; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `cm_wmap S s (w'':real^2->real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `t:real^2->bool`; `w':real^2->real^K`;
                   `inv r:real`; `--(inv r % c):real^2`] CMR_AFF_WMAP) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "w''" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w120 s (\x. (w'':real^2->real^K) x - w x)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^2->bool`; `\x. (w':real^2->real^K) x - w(r % x + c)`;
                   `inv r:real`; `--(inv r % c):real^2`] CMR_AFF_W120) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    EXPAND_TAC "w''" THEN REWRITE_TAC[FUN_EQ_THM] THEN
    ASM_SIMP_TAC[CMR_AFF_INV];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `cm_gen G s (w:real^2->real^K)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[cm_gen] THEN EXPAND_TAC "t" THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `G:real^K->real^K^K`; `w:real^2->real^K`; `Lam:real`;
                   `r:real`; `c:real^2`] CMR_AFF_GDIR) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_wmap]; SIMP_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `cm_gen G s (w'':real^2->real^K)` THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[cm_gen] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `G:real^K->real^K^K`; `w'':real^2->real^K`; `Lam:real`;
                 `r:real`; `c:real^2`] CMR_AFF_GDIR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cm_wmap]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LE_REFL]);;

