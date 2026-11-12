(* ========================================================================= *)
(* pc_p2a_asv: MT Thm 9.59 (a 3-dimensional kappa-solution has asymptotic    *)
(* volume ratio 0 at time 0) in route form, the statement                    *)
(* P2B_THM_9_59_ROUTE_STATEMENT, on Tao's route (Prop 3.18.3, which avoids   *)
(* MT Props 9.39 and 9.56): the asymptotic soliton                           *)
(* (P2B_ASYM_SOLITON_STATEMENT), Bishop-Gromov (P2B_REQ_CMP_BISHOP_GROMOV)   *)
(* and Hamilton's distance distortion (P2C_REQ_DIST_DISTORTION).  Proof by   *)
(* contradiction: if vol B_0(p,r) > eta r^3 for arbitrarily large r,         *)
(* Bishop-Gromov at time 0 gives vol B_0(p,rho) >= eta rho^3 for all rho.    *)
(* Going back to time -T (T >= 1) the volume of a fixed set does not         *)
(* decrease (R >= 0, up to the endpoint 0 by the smooth extension of the     *)
(* flow), d_-1 <= exp(B) d_0 (Ric <= B g on [-2,0]) and d_-T <= d_-1 + C_T   *)
(* (distance distortion), so balls about p at time -T have volume >=         *)
(* eta (R - C_T)^3 exp(-3B); by Bishop-Gromov at time -T every ball          *)
(* about every point has volume >= eta' rho^3, eta' = eta exp(-3B) / 2,      *)
(* uniformly in T.  The rescalings by 1/tau k keep this bound, so by LIM_VOL *)
(* the limit balls B(xl,2r) have volume >= eta' r^3 - 1.  A compact limit    *)
(* has bounded volume and the cylinder model has linear volume growth        *)
(* (P2ACM_STD_BALL_UPPER of pc_p2a_cylm): a contradiction for large r.       *)
(* ========================================================================= *)

needs "src/pc_p2a_kap0.ml";;
needs "src/pc_p2a_dd.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Comparisons up to the final time b of a flow smooth up to b              *)
(* (p2a_flow_upto): continuity at b from the smooth extension, then the     *)
(* mean value theorem on [s,b] for the density (R >= 0) and for exp(2 B (r  *)
(* - s)) times the quadratic form (Ric <= B g), the distance comparison d_s *)
(* <= exp(B (b - s)) d_b and volume monotonicity.                           *)
(* ========================================================================= *)

let P2AV9_UPTO_VEC_CONT = prove
 (`!top atlas a b (g:real->A->real^N^N) x s.
     p2a_flow_upto (top,atlas) a b g /\ x IN topspace top /\ a < s /\ s <= b
     ==> (\t. (vectorize:real^N^N->real^(N,N)finite_prod) (g (drop t) x))
         continuous_on interval[lift s,lift b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_flow_upto] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "PCROSS")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `Fx:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  ABBREV_TAC `p = SND(c:(A->bool)#(A->real^N)) x` THEN
  SUBGOAL_THEN `(p:real^N) IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Fx:real^(1,N)finite_sum->real^(N,N)finite_prod) continuous_on
                 (interval(lift a,lift(b + e)) PCROSS
                                  IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `smooth_map_on (interval(lift a,lift(b + e)) PCROSS
                                IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                  (Fx:real^(1,N)finite_sum->real^(N,N)finite_prod)` THEN
    REWRITE_TAC[smooth_map_on] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[continuously_differentiable];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `(Fx:real^(1,N)finite_sum->real^(N,N)finite_prod) o
              (\w:real^1. pastecart w (p:real^N))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`drop w`; `p:real^N`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "vectorize")) (concl th))) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "p" THEN EXPAND_TAC "c" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift(b + e)) PCROSS
                  IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                      LIFT_DROP] THEN
      X_GEN_TAC `w:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC]]);;

let P2AV9_UPTO_DENS_CONT = prove
 (`!top atlas a b (g:real->A->real^N^N) x s.
     p2a_flow_upto (top,atlas) a b g /\ x IN topspace top /\ a < s /\ s <= b
     ==> (\t. sqrt(det(g t x))) real_continuous_on real_interval[s,b]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_DET_VECTORIZE THEN BETA_TAC THEN
  MATCH_MP_TAC P2AV9_UPTO_VEC_CONT THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`] THEN
  ASM_REWRITE_TAC[]);;

let P2AV9_UPTO_QF_CONT = prove
 (`!top atlas a b (g:real->A->real^N^N) x s (w:real^N).
     p2a_flow_upto (top,atlas) a b g /\ x IN topspace top /\ a < s /\ s <= b
     ==> (\t. w dot (g t x ** w)) real_continuous_on real_interval[s,b]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `x:A`; `s:real`] P2AV9_UPTO_VEC_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\t:real^1. lift(w dot ((g:real->A->real^N^N) (drop t) x ** w))) =
                (\m:real^(N,N)finite_prod. lift(w dot ((matrify m:real^N^N) ** w))) o
                (\t. vectorize(g (drop t) x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_LMUL; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL]);;

(* The density does not increase up to b where R >= 0. *)

let P2AV9_UPTO_DENSITY_MONO = prove
 (`!top atlas a b (g:real->A->real^N^N) s x.
     p2a_flow_upto (top,atlas) a b g /\ a < s /\ s <= b /\ x IN topspace top /\
     (!t. s < t /\ t < b ==> &0 <= mfd_scalar atlas (g t) x)
     ==> sqrt(det(g b x)) <= sqrt(det(g s x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real = b` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `s < b:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2a_flow_upto]) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
                !t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^N^N) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. sqrt(det((g:real->A->real^N^N) t x))`;
                 `\t. --(mfd_scalar atlas ((g:real->A->real^N^N) t) x) * sqrt(det(g t x))`;
                 `s:real`; `b:real`] REAL_MVT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AV9_UPTO_DENS_CONT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC GRGT_DENSITY_EVOLUTION_PREF THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` MP_TAC) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= mfd_scalar atlas ((g:real->A->real^N^N) t) x` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(det((g:real->A->real^N^N) t x))` ASSUME_TAC THENL
   [MATCH_MP_TAC GRGV_SQRT_DET_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= mfd_scalar atlas ((g:real->A->real^N^N) t) x * sqrt(det(g t x)) * (b - s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Under Ric <= B g the metric shrinks at most like exp(-2 B), up to b. *)

let P2AV9_UPTO_QFORM = prove
 (`!top atlas a b (g:real->A->real^N^N) B s z w.
     p2a_flow_upto (top,atlas) a b g /\ a < s /\ s <= b /\ z IN topspace top /\
     (!r. s < r /\ r < b ==> mfd_ricci atlas (g r) z w w <= B * (w dot (g r z ** w)))
     ==> w dot (g s z ** w) <= exp(&2 * B * (b - s)) * (w dot (g b z ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real = b` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < b:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2a_flow_upto]) THEN
  MP_TAC(ISPECL
   [`\r. exp(&2 * B * (r - s)) * (w dot ((g:real->A->real^N^N) r z ** w))`;
    `\r. exp(&2 * B * (r - s)) * (--(&2) * mfd_ricci atlas ((g:real->A->real^N^N) r) z w w) +
         (&2 * B * exp(&2 * B * (r - s))) * (w dot (g r z ** w))`;
    `s:real`; `b:real`] REAL_MVT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        X_GEN_TAC `r:real` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
        EXISTS_TAC `&2 * B * exp(&2 * B * (r - s))` THEN REWRITE_TAC[P2AD_EXP_DERIV];
        MATCH_MP_TAC P2AV9_UPTO_QF_CONT THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                              `a:real`] THEN
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `a:real`; `b:real`; `g:real->A->real^N^N`; `r:real`; `z:A`;
                     `w:real^N`] RFA_QFORM_DERIV) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      MP_TAC(ISPECL [`\r. exp(&2 * B * (r - s))`; `&2 * B * exp(&2 * B * (r - s))`;
                     `\r. w dot ((g:real->A->real^N^N) r z ** w)`;
                     `--(&2) * mfd_ricci atlas ((g:real->A->real^N^N) r) z w w`;
                     `r:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
      ASM_REWRITE_TAC[P2AD_EXP_DERIV]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` MP_TAC) THEN
  REWRITE_TAC[IN_REAL_INTERVAL; REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_LID] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_ricci atlas ((g:real->A->real^N^N) t) z w w <= B * (w dot (g t z ** w))`
  ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= exp(&2 * B * (t - s)) *
          (B * (w dot ((g:real->A->real^N^N) t z ** w)) - mfd_ricci atlas (g t) z w w) *
          (b - s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Hence d_s <= exp(B (b - s)) d_b. *)

let P2AV9_UPTO_DIST = prove
 (`!top atlas a b (g:real->A->real^N^N) B s x y.
     p2a_flow_upto (top,atlas) a b g /\ a < s /\ s <= b /\
     (!r z w. s < r /\ r < b /\ z IN topspace top
              ==> mfd_ricci atlas (g r) z w w <= B * (w dot (g r z ** w))) /\
     mfd_joinable (top,atlas) x y
     ==> mfd_dist (top,atlas) (g s) x y <= exp(B * (b - s)) * mfd_dist (top,atlas) (g b) x y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2a_flow_upto]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) b`; `(g:real->A->real^N^N) s`;
                 `exp(&2 * B * (b - s))`; `x:A`; `y:A`] RFAH_DIST_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN CONJ_TAC THENL
     [ASM_CASES_TAC `s:real = b` THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`z:A`; `w:real^N`] THEN DISCH_TAC THEN
      MATCH_MP_TAC P2AV9_UPTO_QFORM THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `a:real`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[RFAH_SQRT_EXP2]]);;

(* The volume of a fixed set does not increase up to b where R >= 0. *)

let P2AV9_UPTO_VOL_MONO = prove
 (`!top atlas a b (g:real->A->real^N^N) s S vb vs.
     p2a_flow_upto (top,atlas) a b g /\ a < s /\ s <= b /\
     (!t x. s < t /\ t < b /\ x IN topspace top ==> &0 <= mfd_scalar atlas (g t) x) /\
     mfd_has_volume (top,atlas) (g b) S vb /\ mfd_has_volume (top,atlas) (g s) S vs
     ==> vb <= vs`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2a_flow_upto]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) s)` ASSUME_TAC THENL
   [ASM_CASES_TAC `s:real = b` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) s`; `\x:A. &1`; `S:A->bool`; `vs:real`]
                  MFD_HAS_INTEGRAL_IMP_MEASURABLE) THEN
    ASM_REWRITE_TAC[GSYM mfd_has_volume] THEN SIMP_TAC[mfd_lebesgue_measurable];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) s`; `(g:real->A->real^N^N) b`; `S:A->bool`;
                 `vs:real`; `vb:real`; `&1`] MFD_HAS_VOLUME_COMPARE) THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2AV9_UPTO_DENSITY_MONO THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Going back in time along a kappa-solution: volumes of fixed sets do not  *)
(* decrease, d_-1 <= exp(B) d_0 (B from the Ricci bound on [-2,0]),         *)
(* d_-tb <= d_-1 + C (distance distortion with the Ricci bound on           *)
(* [-tb-1,0]), hence vol_0 B_0(p,rho) is at most the volume at -tb of       *)
(* B_-tb(p, exp(B) rho + C).                                                *)
(* ========================================================================= *)

let P2AV9_KSOL_SCALAR = prove
 (`!kappa top atlas (g:real->B->real^3^3) t x.
     p2b_kappa_solution kappa (top,atlas) g /\ t <= &0 /\ x IN topspace top
     ==> &0 <= mfd_scalar atlas (g t) x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  MATCH_MP_TAC P2BX_MFD_SCALAR_NONNEG THEN EXISTS_TAC `top:B topology` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2AV9_KSOL_VOL_BACK = prove
 (`!kappa top atlas (g:real->B->real^3^3) s S v0 vs.
     p2b_kappa_solution kappa (top,atlas) g /\ s <= &0 /\
     mfd_has_volume (top,atlas) (g(&0)) S v0 /\ mfd_has_volume (top,atlas) (g s) S vs
     ==> v0 <= vs`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `p2a_cbflow (top,atlas) (s - &1) (&0) (g:real->B->real^3^3)` MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2a_cbflow] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `s - &1`; `&0`; `g:real->B->real^3^3`; `s:real`; `S:B->bool`;
                 `v0:real`; `vs:real`] P2AV9_UPTO_VOL_MONO) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AV9_KSOL_SCALAR THEN
  MAP_EVERY EXISTS_TAC [`kappa:real`; `top:B topology`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2AV9_KSOL_DIST1 = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> ?B. &0 <= B /\
             !x y. x IN topspace top /\ y IN topspace top
                   ==> mfd_dist (top,atlas) (g(--(&1))) x y <=
                       exp B * mfd_dist (top,atlas) (g(&0)) x y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  SUBGOAL_THEN `p2a_cbflow (top,atlas) (--(&2)) (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AU_CBFLOW_CURV) THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "ric")))) THEN
  EXISTS_TAC `&2 * K` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `p2a_cbflow (top,atlas) (--(&2)) (&0) (g:real->B->real^3^3)` THEN
  REWRITE_TAC[p2a_cbflow] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `--(&2)`; `&0`;
                 `g:real->B->real^3^3`; `&2 * K`; `--(&1)`; `x:B`; `y:B`] P2AV9_UPTO_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`r:real`; `z:B`; `u:real^3`] THEN STRIP_TAC THEN
      USE_THEN "ric" (MP_TAC o SPECL [`r:real`; `z:B`; `u:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_ARITH `&0 - --(&1) = &1`; REAL_MUL_RID]]);;

let P2AV9_KSOL_DISTT = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) tb.
     P2C_REQ_DIST_DISTORTION_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     &1 <= tb
     ==> ?C. &0 <= C /\
             !x y. x IN topspace top /\ y IN topspace top
                   ==> mfd_dist (top,atlas) (g(--tb)) x y <=
                       mfd_dist (top,atlas) (g(--(&1))) x y + C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dd") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  SUBGOAL_THEN `p2a_cbflow (top,atlas) (--tb - &1) (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (--tb - &1) (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_cbflow (top,atlas) (--tb - &1) (&0) (g:real->B->real^3^3)` THEN
    SIMP_TAC[p2a_cbflow; ricci_flow_from];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AU_CBFLOW_CURV) THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "ric")))) THEN
  EXISTS_TAC `real_integral (real_interval[--tb,--(&1)]) (\s. &8 * sqrt(&2 * (K + &1) / &3))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_ARITH `&1 <= tb ==> --tb <= --(&1)`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC SQRT_POS_LE THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN STRIP_TAC THEN
  USE_THEN "dd" (MP_TAC o SPECL
    [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `--tb - &1`; `&0`;
     `g:real->B->real^3^3`; `\s:real. K + &1`; `--tb`; `--(&1)`; `x:B`; `y:B`] o
    REWRITE_RULE[P2C_REQ_DIST_DISTORTION_STATEMENT]) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `z:B`; `u:real^3`] THEN STRIP_TAC THEN
    USE_THEN "ric" (MP_TAC o SPECL [`s:real`; `z:B`; `u:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `z:B`; `u:real^3`] P2AP_QFORM_NONNEG) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC]);;

let P2AV9_KSOL_BALL_BACK = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p.
     P2C_REQ_DIST_DISTORTION_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top
     ==> ?B. &0 <= B /\
             !tb. &1 <= tb
                  ==> ?C. &0 <= C /\
                          !rho v0. mfd_has_volume (top,atlas) (g(&0))
                                     (mfd_ball (top,atlas) (g(&0)) p rho) v0
                                   ==> v0 <= mfd_volume (top,atlas) (g(--tb))
                                               (mfd_ball (top,atlas) (g(--tb)) p
                                                         (exp B * rho + C))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d1")) o
    MATCH_MP P2AV9_KSOL_DIST1) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `tb:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `tb:real`]
                P2AV9_KSOL_DISTT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dT"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`rho:real`; `v0:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3)(&0)) /\
                riemannian_metric atlas ((g:real->B->real^3^3)(--tb)) /\
                mfd_complete (top,atlas) ((g:real->B->real^3^3)(--tb))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `S = mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) p rho` THEN
  ABBREV_TAC `S' = mfd_ball (top,atlas) ((g:real->B->real^3^3)(--tb)) p (exp B * rho + C)` THEN
  SUBGOAL_THEN `(S:B->bool) SUBSET S'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S"; "S'"] THEN REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
    X_GEN_TAC `y:B` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    USE_THEN "d1" (MP_TAC o SPECL [`p:B`; `y:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "dT" (MP_TAC o SPECL [`p:B`; `y:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `exp B * mfd_dist (top,atlas) ((g:real->B->real^3^3)(&0)) p y < exp B * rho`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(--tb)`; `p:B`; `exp B * rho + C`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(--tb)`; `S:B->bool`; `S':B->bool`;
                 `mfd_volume (top,atlas) ((g:real->B->real^3^3)(--tb)) S'`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_volume (top,atlas) ((g:real->B->real^3^3)(--tb)) S` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AV9_KSOL_VOL_BACK THEN
  MAP_EVERY EXISTS_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                        `g:real->B->real^3^3`; `--tb`; `S:B->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Bishop-Gromov at time 0 (balls about p of every radius have volume >=    *)
(* eta rho^3 if arbitrarily large ones do) and at time -tb (every ball      *)
(* about every point has volume >= eta' rho^3 with                          *)
(* eta' = eta / (2 exp(B)^3), uniformly in tb >= 1).                        *)
(* ========================================================================= *)

let P2AV9_BG0 = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p eta.
     P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     p IN topspace top /\
     (!r0. ?r v. r0 <= r /\
                 mfd_has_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) p r) v /\
                 eta * r pow 3 < v)
     ==> !rho v0. &0 < rho /\
                  mfd_has_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) p rho) v0
                  ==> eta * rho pow 3 <= v0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bg") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "big")))) THEN
  MAP_EVERY X_GEN_TAC [`rho:real`; `v0:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  USE_THEN "big" (MP_TAC o SPEC `rho:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC)) THEN
  USE_THEN "bg" (MP_TAC o SPECL
    [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3)(&0)`;
     `p:B`; `rho:real`; `r:real`; `v0:real`; `v:real`] o
    REWRITE_RULE[P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < r pow 3 /\ &0 < rho pow 3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `eta < v / r pow 3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(v / r pow 3) * rho pow 3 <= v0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `eta * rho pow 3 <= (v / r pow 3) * rho pow 3` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let P2AV9_ARITH_BACK = prove
 (`!eta E R u X v rho.
     &0 < eta /\ &0 < E /\ &0 < rho /\ &0 < R /\ &4 / &5 * R <= u /\
     eta * (u / E) pow 3 <= X /\ X / R pow 3 <= v / rho pow 3
     ==> eta / (&2 * E pow 3) * rho pow 3 <= v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R pow 3 /\ &0 < rho pow 3 /\ &0 < E pow 3` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&4 / &5 * R) pow 3 <= u pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `eta / (&2 * E pow 3) * R pow 3 <= X` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eta * (u / E) pow 3` THEN
    ASM_REWRITE_TAC[REAL_POW_DIV] THEN
    SUBGOAL_THEN `eta / (&2 * E pow 3) * R pow 3 = (eta / E pow 3) * (R pow 3 / &2) /\
                  eta * u pow 3 / E pow 3 = (eta / E pow 3) * u pow 3`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN UNDISCH_TAC `&0 < E` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(&4 / &5 * R) pow 3 <= u pow 3` THEN
      REWRITE_TAC[REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      UNDISCH_TAC `&0 < R pow 3` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(X / R pow 3) * rho pow 3 <= v` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `eta / (&2 * E pow 3) <= X / R pow 3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `eta / (&2 * E pow 3) * rho pow 3 <= (X / R pow 3) * rho pow 3` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let P2AV9_BACK_LOWER = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p eta.
     P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT w /\ P2C_REQ_DIST_DISTORTION_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ &0 < eta /\
     (!rho v0. &0 < rho /\
               mfd_has_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) p rho) v0
               ==> eta * rho pow 3 <= v0)
     ==> ?eta'. &0 < eta' /\
                !tb q rho v. &1 <= tb /\ q IN topspace top /\ &0 < rho /\
                             mfd_has_volume (top,atlas) (g(--tb))
                               (mfd_ball (top,atlas) (g(--tb)) q rho) v
                             ==> eta' * rho pow 3 <= v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bg") (CONJUNCTS_THEN2 (LABEL_TAC "dd")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v0")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`]
                P2AV9_KSOL_BALL_BACK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "back"))) THEN
  EXISTS_TAC `eta / (&2 * exp B pow 3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_EXP_POS_LT]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`tb:real`; `q:B`; `rho:real`; `v:real`] THEN STRIP_TAC THEN
  USE_THEN "back" (MP_TAC o SPEC `tb:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C"))) THEN
  ABBREV_TAC `E = exp B` THEN
  SUBGOAL_THEN `&0 < E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (p:B) q` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3)(--tb)) /\
                mfd_complete (top,atlas) ((g:real->B->real^3^3)(--tb)) /\
                riemannian_metric atlas ((g:real->B->real^3^3)(&0)) /\
                mfd_complete (top,atlas) ((g:real->B->real^3^3)(&0))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `D = mfd_dist (top,atlas) ((g:real->B->real^3^3)(--tb)) p q` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `R = rho + &5 * (D + C) + &1` THEN
  ABBREV_TAC `rho' = (R - D - C) / E` THEN
  SUBGOAL_THEN `&0 < rho'` ASSUME_TAC THENL
   [EXPAND_TAC "rho'" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `E * rho' + C = R - D` ASSUME_TAC THENL
   [EXPAND_TAC "rho'" THEN UNDISCH_TAC `&0 < E` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(&0)`; `p:B`; `rho':real`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  USE_THEN "v0" (MP_TAC o SPECL [`rho':real`;
    `mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0)) (mfd_ball (top,atlas) (g(&0)) p rho')`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "C" (MP_TAC o SPECL [`rho':real`;
    `mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0)) (mfd_ball (top,atlas) (g(&0)) p rho')`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(--tb)`; `p:B`; `R - D`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3)(--tb)`; `q:B`; `R:real`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) ((g:real->B->real^3^3)(--tb)) p (R - D) SUBSET
                mfd_ball (top,atlas) (g(--tb)) q R` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (q:B) y /\
                  mfd_joinable (top,atlas) q p`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3)(--tb)`; `q:B`; `p:B`; `y:B`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3)(--tb)`; `q:B`; `p:B`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_volume (top,atlas) ((g:real->B->real^3^3)(--tb))
               (mfd_ball (top,atlas) (g(--tb)) p (R - D)) <=
    mfd_volume (top,atlas) (g(--tb)) (mfd_ball (top,atlas) (g(--tb)) q R)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3)(--tb)`;
                   `mfd_ball (top,atlas) ((g:real->B->real^3^3)(--tb)) p (R - D)`;
                   `mfd_ball (top,atlas) ((g:real->B->real^3^3)(--tb)) q R`;
                   `mfd_volume (top,atlas) ((g:real->B->real^3^3)(--tb))
                               (mfd_ball (top,atlas) (g(--tb)) p (R - D))`;
                   `mfd_volume (top,atlas) ((g:real->B->real^3^3)(--tb))
                               (mfd_ball (top,atlas) (g(--tb)) q R)`]
                  MFD_HAS_VOLUME_MONO) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "bg" (MP_TAC o SPECL
    [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3)(--tb)`;
     `q:B`; `rho:real`; `R:real`; `v:real`;
     `mfd_volume (top,atlas) ((g:real->B->real^3^3)(--tb)) (mfd_ball (top,atlas) (g(--tb)) q R)`] o
    REWRITE_RULE[P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC P2AV9_ARITH_BACK THEN
  MAP_EVERY EXISTS_TAC [`R:real`; `R - D - C`;
    `mfd_volume (top,atlas) ((g:real->B->real^3^3)(--tb)) (mfd_ball (top,atlas) (g(--tb)) q R)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The uniform lower bound at the times -tau k passes to the asymptotic     *)
(* soliton (LIM_VOL, the rescaling by 1/tau k keeps eta' rho^3): its balls  *)
(* B(xl,2r) at time 0 have volume >= eta' r^3 - 1; and a cubic beats every  *)
(* affine function.                                                         *)
(* ========================================================================= *)

let P2AV9_ARITH_LIM = prove
 (`!t r e vk v.
     &0 < t /\ e * (r * sqrt t) pow 3 <= vk /\ inv t * sqrt(inv t) * vk <= v + &1
     ==> e * r pow 3 - &1 <= v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt t /\ sqrt t pow 2 = t` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC `inv t * sqrt(inv t) * vk <= v + &1` THEN REWRITE_TAC[SQRT_INV] THEN
  SUBGOAL_THEN `(inv t * inv(sqrt t)) * (e * (r * sqrt t) pow 3) = e * r pow 3` ASSUME_TAC THENL
   [UNDISCH_TAC `sqrt t pow 2 = t` THEN UNDISCH_TAC `&0 < sqrt t` THEN UNDISCH_TAC `&0 < t` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(inv t * inv(sqrt t)) * (e * (r * sqrt t) pow 3) <= (inv t * inv(sqrt t)) * vk`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let P2AV9_LIM_LOWER = prove
 (`!kappa kappa' top atlas (h:real->B->real^3^3) tau q (top':B topology) atlas' g' xl eta'.
     p2b_kappa_solution kappa (top,atlas) h /\
     (!k. &0 < tau k) /\ (!M. ?N. !k. N <= k ==> M < tau k) /\ (!k. q k IN topspace top) /\
     p3_flow_limit_on (\k. p2b_kview (top,atlas) h) q (\k. --(tau k))
                      (\k. inv(tau k)) {s | s < &1} (top',atlas') g' xl /\
     p2b_kappa_solution kappa' (top',atlas') (\t. g'(t + &1 / &2)) /\
     (!tb y rho v. &1 <= tb /\ y IN topspace top /\ &0 < rho /\
                   mfd_has_volume (top,atlas) (h(--tb)) (mfd_ball (top,atlas) (h(--tb)) y rho) v
                   ==> eta' * rho pow 3 <= v)
     ==> !r v. &0 < r /\
               mfd_has_volume (top',atlas') (g'(&0))
                 (mfd_ball (top',atlas') (g'(&0)) xl (&2 * r)) v
               ==> eta' * r pow 3 - &1 <= v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "inf") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "low"))))))) THEN
  MAP_EVERY X_GEN_TAC [`r:real`; `v:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS o
    check (fun th -> can (find_term ((=) `h:real->B->real^3^3`)) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BX_KSOL_FACTS o
    check (fun th -> can (find_term ((=) `g':real->B->real^3^3`)) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hs'") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rm'") (K ALL_TAC))))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B_KSOL_BASIC o
    check (fun th -> can (find_term ((=) `g':real->B->real^3^3`)) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "cp'") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&0)) /\
                mfd_complete (top',atlas') (g'(&0))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "rm'" (MP_TAC o SPEC `--(&1 / &2)`);
      USE_THEN "cp'" (MP_TAC o SPEC `--(&1 / &2)`)] THEN
    BETA_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `p3_flow_limit_on (\k. p2b_kview (top,atlas) (h:real->B->real^3^3)) (q:num->B)
                 (\k. --(tau k)) (\k. inv(tau k)) {s | s < &1}
                 (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
                 (g':real->B->real^3^3) (xl:B)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(GEN_REWRITE_RULE I [P2C_FLOW_LIMIT_ON_WITH] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_TAC `phi:num->B->B`)) THEN
  SUBGOAL_THEN `(xl:B) IN topspace top' /\ (!k. (phi:num->B->B) k xl = q k)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_flow_limit_with (\k. p2b_kview (top,atlas) (h:real->B->real^3^3)) (q:num->B)
                   (\k. --(tau k)) (\k. inv(tau k)) {s | s < &1}
                   (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
                   (g':real->B->real^3^3) (xl:B) (W:num->B->bool) (phi:num->B->B)` THEN
    REWRITE_TAC[p2c_flow_limit_with] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&0)`; `xl:B`; `r:real`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`B:B->bool`; `B:B->bool`] LIM_VOL) THEN REWRITE_TAC[LIM_VOL_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`\k:num. p2b_kview (top,atlas) (h:real->B->real^3^3)`; `q:num->B`; `\k:num. --(tau k:real)`;
     `\k:num. inv(tau k:real)`; `{s:real | s < &1}`; `top':B topology`;
     `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
     `W:num->B->bool`; `phi:num->B->B`; `&0`; `xl:B`; `r:real`; `&2 * r`;
     `mfd_volume (top',atlas') ((g':real->B->real^3^3)(&0)) (mfd_ball (top',atlas') (g'(&0)) xl r)`;
     `v:real`; `&1`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2AK0_KVIEW_REG THEN
      EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN REWRITE_TAC[REAL_ARITH `!x:real. &0 / x = &0`; REAL_ADD_RID] THEN
      ASM_SIMP_TAC[P2AK0_KVIEW_SLICE; REAL_ARITH `&0 < x ==> --x <= &0`];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `!x:real. &0 / x = &0`; REAL_ADD_RID] THEN
  ASM_SIMP_TAC[P2AK0_KVIEW_SLICE; REAL_ARITH `&0 < x ==> --x <= &0`] THEN
  SUBGOAL_THEN `!k. r * inv(sqrt(inv(tau(k:num)))) = r * sqrt(tau k)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[SQRT_INV; REAL_INV_INV]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN
  USE_THEN "inf" (MP_TAC o SPEC `&1`) THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k0 + N:num` o check (fun th ->
    can (find_term ((=) `k0:num`)) (concl th))) THEN
  REWRITE_TAC[LE_ADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `vk1:real` (X_CHOOSE_THEN `vk2:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&1 < tau(k0 + N:num)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "low" (MP_TAC o SPECL [`tau(k0 + N:num):real`; `q(k0 + N:num):B`;
                                  `r * sqrt(tau(k0 + N:num))`; `vk1:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  MATCH_MP_TAC P2AV9_ARITH_LIM THEN
  MAP_EVERY EXISTS_TAC [`tau(k0 + N:num):real`; `vk1:real`] THEN
  ASM_REWRITE_TAC[]);;

let P2AV9_CUBIC = prove
 (`!e A B. &0 < e ==> ?r. &0 < r /\ A * r + B < e * r pow 3 - &1`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `&1 + (abs A + abs B + &2) / e` THEN
  ABBREV_TAC `M = abs A + abs B + &2` THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL [EXPAND_TAC "M" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = &1 + M / e` THEN
  SUBGOAL_THEN `&0 < M / e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= r` ASSUME_TAC THENL [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `M <= e * r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN
    SUBGOAL_THEN `e * M / e = M` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `r <= r pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `M * r <= e * r pow 3` ASSUME_TAC THENL
   [SUBGOAL_THEN `e * r pow 3 = (e * r) * r pow 2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * r pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `A * r <= abs A * r /\ &0 <= abs B * (r - &1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `M * r <= e * r pow 3` THEN EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The route theorem for MT Thm 9.59.  If the bound failed, balls of every  *)
(* radius about p at time 0 would have volume >= eta rho^3 (P2AV9_BG0),     *)
(* every ball at every time -tb <= -1 volume >= eta' rho^3                  *)
(* (P2AV9_BACK_LOWER), and the limit balls B(xl,2r) volume >= eta' r^3 - 1  *)
(* (P2AV9_LIM_LOWER); but they grow at most affinely in r: a compact limit  *)
(* has finite total volume, and the cylinder model has linear volume growth *)
(* (P2ACM_CYL_STD, P2ACM_STD_BALL_UPPER).                                   *)
(* ========================================================================= *)

let P2AV9_THM_9_59_ROUTE = prove
 (`!w:B->bool. P2B_THM_9_59_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_THM_9_59_ROUTE_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "asym")
    (CONJUNCTS_THEN2 (LABEL_TAC "bg") (LABEL_TAC "dd"))) THEN
  REWRITE_TAC[P2B_THM_9_59_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `p:B`; `eta:real`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o
    REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE; GSYM CONJ_ASSOC]) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `eta:real`] P2AV9_BG0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                 `eta:real`] P2AV9_BACK_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta':real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "low"))) THEN
  USE_THEN "asym" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                   `atlas:((B->bool)#(B->real^3))->bool`;
                                   `g:real->B->real^3^3`] o
                   REWRITE_RULE[P2B_ASYM_SOLITON_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:num->real` (X_CHOOSE_THEN `q:num->B`
    (X_CHOOSE_THEN `top':B topology` (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `xl:B`
    (X_CHOOSE_THEN `f:B->real` MP_TAC))))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "cases")))))))) THEN
  MP_TAC(ISPECL [`kappa:real`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `tau:num->real`;
                 `q:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `eta':real`] P2AV9_LIM_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "lim")] THEN
  (* facts about the limit at time 0 *)
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BX_KSOL_FACTS o
    check (fun th -> can (find_term ((=) `g':real->B->real^3^3`)) (concl th) &&
                     can (find_term (fun t -> is_const t &&
                                              fst(dest_const t) = "p2b_kappa_solution"))
                         (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rm'") (K ALL_TAC))))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B_KSOL_BASIC o
    check (fun th -> can (find_term ((=) `g':real->B->real^3^3`)) (concl th) &&
                     can (find_term (fun t -> is_const t &&
                                              fst(dest_const t) = "p2b_kappa_solution"))
                         (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "cp'") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&0)) /\
                mfd_complete (top',atlas') (g'(&0))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "rm'" (MP_TAC o SPEC `--(&1 / &2)`);
      USE_THEN "cp'" (MP_TAC o SPEC `--(&1 / &2)`)] THEN
    BETA_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xl:B) IN topspace top'` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_flow_limit_on (\k. p2b_kview (top,atlas) (g:real->B->real^3^3)) (q:num->B)
                   (\k. --(tau k)) (\k. inv(tau k)) {s | s < &1}
                   (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
                   (g':real->B->real^3^3) (xl:B)` THEN
    REWRITE_TAC[p3_flow_limit_on] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the limit balls grow at most affinely *)
  SUBGOAL_THEN
   `?A B0. !R v. &0 < R /\
                 mfd_has_volume (top',atlas') ((g':real->B->real^3^3)(&0))
                   (mfd_ball (top',atlas') (g'(&0)) xl R) v
                 ==> v <= A * R + B0`
  MP_TAC THENL
   [REMOVE_THEN "cases" (DISJ_CASES_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THENL
     [(* compact: finite total volume *)
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `(g':real->B->real^3^3)(&0)`; `topspace top':B->bool`]
                    MFD_HAS_VOLUME_COMPACT) THEN
      ASM_REWRITE_TAC[GSYM compact_space] THEN DISCH_THEN(X_CHOOSE_TAC `V:real`) THEN
      MAP_EVERY EXISTS_TAC [`&0`; `V:real`] THEN
      MAP_EVERY X_GEN_TAC [`R:real`; `v:real`] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `(g':real->B->real^3^3)(&0)`;
                     `mfd_ball (top',atlas') ((g':real->B->real^3^3)(&0)) xl R`;
                     `topspace top':B->bool`; `v:real`; `V:real`] MFD_HAS_VOLUME_MONO) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      (* the cylinder model in standard form at s = 0 *)
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[p2b_cyl_model] o
        check (fun th -> can (find_term (fun t -> is_const t &&
                                                  fst(dest_const t) = "p2b_cyl_model"))
                             (concl th))) THEN
      DISCH_THEN(X_CHOOSE_THEN `pm:real^3->B` (X_CHOOSE_THEN `lam:real`
        (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `(g':real->B->real^3^3)(&0)`; `pm:real^3->B`; `lam:real`; `--(&1 / &2)`]
                    P2ACM_CYL_STD) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`--(&1 / &2)`; `y:real^3`] o
          check (fun th -> can (find_term (fun t -> is_const t &&
                                                    fst(dest_const t) = "cylinder_flow"))
                               (concl th))) THEN
        BETA_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `qs:real^3->B`) THEN
      MATCH_MP_TAC P2ACM_STD_BALL_UPPER THEN
      MAP_EVERY EXISTS_TAC [`qs:real^3->B`; `lam - --(&1 / &2)`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real` (X_CHOOSE_THEN `B0:real` (LABEL_TAC "up"))) THEN
  MP_TAC(SPECL [`eta':real`; `&2 * A`; `B0:real`] P2AV9_CUBIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&0)`; `xl:B`; `&2 * r`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  USE_THEN "up" (MP_TAC o SPECL
    [`&2 * r`; `mfd_volume (top',atlas') ((g':real->B->real^3^3)(&0))
                           (mfd_ball (top',atlas') (g'(&0)) xl (&2 * r))`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "lim" (MP_TAC o SPECL
    [`r:real`; `mfd_volume (top',atlas') ((g':real->B->real^3^3)(&0))
                           (mfd_ball (top',atlas') (g'(&0)) xl (&2 * r))`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC);;

