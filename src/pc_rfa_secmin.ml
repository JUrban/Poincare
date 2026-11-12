(* ========================================================================= *)
(* Unit pc_rfa_secmin: the minimal sectional curvature lambda = mfd_sec_min  *)
(* on a 3-manifold: chart independence of the set of sectional curvatures,   *)
(* lambda as the first eigenvalue of P = (R/2) g - Ric in any chart, the     *)
(* Rayleigh bound lambda <= P(z,z) / g(z,z), and continuity of lambda along  *)
(* a family of metrics that extends smoothly past the initial time.          *)
(* ========================================================================= *)

needs "src/pc_rfa_p3alg.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Chart independence of the sectional set; lambda in a chart                *)
(* is P(f1,f1) for an ordered eigenframe; the Rayleigh bound.                *)
(* ========================================================================= *)

let RFA_NONCOLLINEAR_LINEAR_INJ = prove
 (`!(L:real^N->real^N) (M:real^N->real^N) u v.
     linear L /\ (!h. M (L h) = h) /\ ~collinear {vec 0,u,v}
     ==> ~collinear {vec 0,L u,L v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:real^N->real^N`; `{vec 0:real^N,u,v}`]
         COLLINEAR_LINEAR_IMAGE_EQ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES; MATCH_MP LINEAR_0 (ASSUME `linear (L:real^N->real^N)`)] THEN
  ASM_REWRITE_TAC[]);;

(* The set of sectional curvatures at x is the same in every chart.         *)

let RFA_SECSET_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     c IN atlas /\ x IN FST c
     ==> {mfd_sectional atlas g x u v | u,v | ~collinear {vec 0,u,v}} =
         {lsectional (metric_local atlas c g) (SND c x) u v | u,v |
          ~collinear {vec 0,u,v}}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  SUBGOAL_THEN
   `linear(chart_jac (c0:(A->bool)#(A->real^N)) c x) /\ linear(chart_jac c c0 x) /\
    (!h. chart_jac c0 c x (chart_jac c c0 x h) = h) /\
    (!h. chart_jac c c0 x (chart_jac c0 c x h) = h) /\
    (!u v. mfd_sectional atlas g x u v =
           lsectional (metric_local atlas c g) (SND c x)
                      (chart_jac c0 c x u) (chart_jac c0 c x v))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `x:A`] CHART_JAC_LINEAR) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `x:A`] CHART_JAC_LINEAR) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `x:A`] CHART_JAC_INVERSE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `x:A`] CHART_JAC_INVERSE) THEN
    REWRITE_TAC[PAIR; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `v:real^N`]
           LSECTIONAL_CHART_TRANS) THEN
    REWRITE_TAC[PAIR; IN_INTER] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `r:real` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`chart_jac (c0:(A->bool)#(A->real^N)) c x u`;
                          `chart_jac (c0:(A->bool)#(A->real^N)) c x v`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_NONCOLLINEAR_LINEAR_INJ THEN
    EXISTS_TAC `chart_jac (c:(A->bool)#(A->real^N)) c0 x` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`chart_jac (c:(A->bool)#(A->real^N)) c0 x u`;
                          `chart_jac (c:(A->bool)#(A->real^N)) c0 x v`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_NONCOLLINEAR_LINEAR_INJ THEN
    EXISTS_TAC `chart_jac (c0:(A->bool)#(A->real^N)) c x` THEN ASM_REWRITE_TAC[]]);;

(* In a chart, mfd_sec_min is the first value P(f1,f1) of an ordered       *)
(* eigenframe, a lower bound of all sectional curvatures, and a lower       *)
(* bound of every Rayleigh quotient P(z,z) / g(z,z).                        *)

let RFA_SECMIN_CHART_3D = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) c x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     c IN atlas /\ x IN FST c
     ==> ?S:real^3^3.
           invertible S /\
           matrix_inv(metric_local atlas c g (SND c x)) = transp S ** S /\
           (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
                  ==> lricci (metric_local atlas c g) (SND c x)
                        (transp S ** basis i) (transp S ** basis j) = &0) /\
           lpcurv (metric_local atlas c g) (SND c x) (\m. transp S ** basis 1) <=
           lpcurv (metric_local atlas c g) (SND c x) (\m. transp S ** basis 2) /\
           lpcurv (metric_local atlas c g) (SND c x) (\m. transp S ** basis 1) <=
           lpcurv (metric_local atlas c g) (SND c x) (\m. transp S ** basis 3) /\
           mfd_sec_min atlas g x =
           lpcurv (metric_local atlas c g) (SND c x) (\m. transp S ** basis 1) /\
           (!u v. ~collinear {vec 0,u,v}
                  ==> mfd_sec_min atlas g x <= mfd_sectional atlas g x u v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
                 (metric_local atlas c (g:A->real^3^3)) /\
    SND c x IN IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) g` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas c (g:A->real^3^3)`;
                 `SND (c:(A->bool)#(A->real^3)) x`] RFA_P3_EIGENFRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas c (g:A->real^3^3)`;
                 `SND (c:(A->bool)#(A->real^3)) x`; `S:real^3^3`] RFA_SECMIN_FRAME_3D) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `c:(A->bool)#(A->real^3)`; `x:A`] RFA_SECSET_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `S:real^3^3` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THENL
   [ASM_REWRITE_TAC[mfd_sec_min];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_sec_min] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `mfd_sectional (atlas:((A->bool)#(A->real^3))->bool) g x u v IN
    {lsectional (metric_local atlas c g) (SND (c:(A->bool)#(A->real^3)) x) u v | u,v |
     ~collinear {vec 0,u,v}}`
  MP_TAC THENL
   [FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let RFA_LPCURV_CMUL = prove
 (`!U (G:real^N->real^N^N) y k z.
     metric_field U G /\ y IN U
     ==> lpcurv G y (\m. k % z) = k pow 2 * lpcurv G y (\m. z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_LPCURV_DIAG] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l1") (LABEL_TAC "l2")) THEN
  SUBGOAL_THEN `lricci (G:real^N->real^N^N) y (k % z) (k % z) =
                k * k * lricci G y z z` SUBST1_TAC THENL
   [USE_THEN "l2" (MP_TAC o SPECL [`k:real`; `z:real^N`] o MATCH_MP LINEAR_CMUL o
      SPEC `k % z:real^N`) THEN
    USE_THEN "l1" (MP_TAC o SPECL [`k:real`; `z:real^N`] o MATCH_MP LINEAR_CMUL o
      SPEC `z:real^N`) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN REPEAT DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN REAL_ARITH_TAC);;

let RFA_SECMIN_RAYLEIGH = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) c x z.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     c IN atlas /\ x IN FST c /\ ~(z = vec 0)
     ==> mfd_sec_min atlas g x <=
         lpcurv (metric_local atlas c g) (SND c x) (\m. z) /
         (z dot (metric_local atlas c g (SND c x) ** z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
                 (metric_local atlas c (g:A->real^3^3)) /\
    SND c x IN IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) g` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `c:(A->bool)#(A->real^3)`; `x:A`]
         RFA_SECMIN_CHART_3D) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas c (g:A->real^3^3)`;
                 `SND (c:(A->bool)#(A->real^3)) x`; `S:real^3^3`] RFA_P3_MIN_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `D = (z:real^3) dot (metric_local atlas c (g:A->real^3^3)
                                    (SND (c:(A->bool)#(A->real^3)) x) ** z)` THEN
  SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(sqrt D) % (z:real^3)` o
    check (fun th -> can (term_match [] `!w:real^3. P w ==> Q w`) (concl th) &&
                     is_imp(snd(dest_forall(concl th))))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
    ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_LT_IMP_LE; REAL_MUL_LINV;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas c (g:A->real^3^3)`;
                 `SND (c:(A->bool)#(A->real^3)) x`; `inv(sqrt D)`; `z:real^3`]
         RFA_LPCURV_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Entries of g and P along smooth families, and the joint                   *)
(* continuity of the Rayleigh quotient on (time x chart) x sphere.           *)
(* ========================================================================= *)

(* Entries of g and P along smooth families of metrics: smoothness and    *)
(* locality (the hypotheses of RFA_EXT_LOCAL_CONTINUOUS).                    *)

let RFA_LMETRIC2_ENTRY_LSMOOTH = prove
 (`!U ta tb (G:real->real^N->real^N^N) p q.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(lmetric2 (G (drop(fstcart z))) (sndcart z)
                       (\m. if m = 1 then basis q else basis p)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REWRITE_TAC[lmetric2; ARITH] THEN
  MP_TAC(ISPECL [`interval(lift ta,lift tb) PCROSS (U:real^N->bool)`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))`;
                 `\m:real^(N,N)finite_prod.
                    lift(basis q dot ((matrify m:real^N^N) ** basis p))`]
         SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_DOT; o_DEF; MATRIFY_VECTORIZE]);;

let RFA_HALF_LSCALAR_LSMOOTH = prove
 (`!U ta tb (G:real->real^N->real^N^N).
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(lscalar (G (drop(fstcart z))) (sndcart z) / &2))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  SUBGOAL_THEN
   `(\z. lift(lscalar ((G:real->real^N->real^N^N) (drop(fstcart z))) (sndcart z) / &2)) =
    (\z. inv(&2) % lift(lscalar (G (drop(fstcart z))) (sndcart z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LRG_LSMOOTH_LSCALAR THEN ASM_REWRITE_TAC[]);;

let RFA_LPCURV_ENTRY_LSMOOTH = prove
 (`!U ta tb (G:real->real^N->real^N^N) p q.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(lpcurv (G (drop(fstcart z))) (sndcart z)
                       (\m. if m = 1 then basis q else basis p)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REWRITE_TAC[RFA_LPCURV_BIL; LIFT_SUB] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_SIMP_TAC[RFA_HALF_LSCALAR_LSMOOTH] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `G:real->real^N->real^N^N`;
                   `p:num`; `q:num`] RFA_LMETRIC2_ENTRY_LSMOOTH) THEN
    ASM_REWRITE_TAC[lmetric2; ARITH];
    MATCH_MP_TAC LRG_LSMOOTH_LRICCI THEN ASM_REWRITE_TAC[]]);;

let RFA_LPCURV_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 s y u.
     open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
     ==> lpcurv G1 y u = lpcurv G2 y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lpcurv; lmetric2; lric2] THEN
  MP_TAC(ISPECL [`G1:real^N->real^N^N`; `G2:real^N->real^N^N`; `s:real^N->bool`;
                 `y:real^N`] LSCALAR_LOCAL) THEN
  MP_TAC(ISPECL [`G1:real^N->real^N^N`; `G2:real^N->real^N^N`; `s:real^N->bool`;
                 `y:real^N`; `(u:num->real^N) 1`; `(u:num->real^N) 2`] LRICCI_LOCAL) THEN
  ASM_SIMP_TAC[]);;

let RFA_LMETRIC2_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 s y u.
     open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
     ==> lmetric2 G1 y u = lmetric2 G2 y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lmetric2] THEN ASM_SIMP_TAC[]);;

let RFA_CMAP_SND_COMPONENT = prove
 (`!(X:A topology) (K:real^N->bool) i.
     continuous_map (prod_topology X (subtopology euclidean K),euclideanreal)
                    (\pz. (SND pz)$i)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\pz:A#real^N. (SND pz)$i) = (\z:real^N. z$i) o SND`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (K:real^N->bool)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_SND] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EUCLIDEAN_COMPONENT THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  REWRITE_TAC[CONTINUOUS_MAP_ID]);;

let RFA_CMAP_FST_COMPOSE = prove
 (`!(X:A topology) (Y:B topology) (f:A->real).
     continuous_map (X,euclideanreal) f
     ==> continuous_map (prod_topology X Y,euclideanreal) (\pz. f (FST pz))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\pz:A#B. (f:A->real) (FST pz)) = f o FST` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `X:A topology` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_FST]);;

(* Joint continuity of the Rayleigh quotient (w,z) -> P_w(z,z) / g_w(z,z)  *)
(* on (chart times interval) x unit sphere, up to the initial time.          *)

let RFA_RQ_JOINT_CONTINUOUS = prove
 (`!V a b e (Gc:real->real^3->real^3^3)
    (FF:real^(1,3)finite_sum->real^(3,3)finite_prod).
     open V /\ &0 < e /\
     (!t. a <= t /\ t < b ==> metric_field V (Gc t)) /\
     smooth_map_on (interval(lift(a - e),lift b) PCROSS V) FF /\
     (!t y. a <= t /\ t < b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y))
     ==> continuous_map
           (prod_topology
              (subtopology euclidean
                 {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN V})
              (subtopology euclidean (sphere(vec 0:real^3,&1))),
            euclideanreal)
           (\pz. --(lpcurv (Gc (drop(fstcart(FST pz)))) (sndcart(FST pz)) (\m. SND pz) /
                    (SND pz dot (Gc (drop(fstcart(FST pz))) (sndcart(FST pz)) ** SND pz))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Sset = {w:real^(1,3)finite_sum |
                      a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN V}` THEN
  SUBGOAL_THEN
   `!p q. continuous_map (subtopology euclidean Sset,euclideanreal)
            (\w. lpcurv ((Gc:real->real^3->real^3^3) (drop(fstcart w))) (sndcart w)
                   (\m. if m = 1 then basis q else basis p)) /\
          continuous_map (subtopology euclidean Sset,euclideanreal)
            (\w. lmetric2 ((Gc:real->real^3->real^3^3) (drop(fstcart w))) (sndcart w)
                   (\m. if m = 1 then basis q else basis p))`
  (LABEL_TAC "ent") THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
    EXPAND_TAC "Sset" THEN CONJ_TAC THENL
     [MP_TAC(BETA_RULE(ISPECL
        [`\(G:real^3->real^3^3) y. lpcurv G y (\m. if m = 1 then basis q else basis p)`;
         `V:real^3->bool`; `a:real`; `b:real`; `e:real`; `Gc:real->real^3->real^3^3`;
         `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] RFA_EXT_LOCAL_CONTINUOUS)) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LPCURV_ENTRY_LSMOOTH THEN
        ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LPCURV_LOCAL THEN
        EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[]];
      MP_TAC(BETA_RULE(ISPECL
        [`\(G:real^3->real^3^3) y. lmetric2 G y (\m. if m = 1 then basis q else basis p)`;
         `V:real^3->bool`; `a:real`; `b:real`; `e:real`; `Gc:real->real^3->real^3^3`;
         `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] RFA_EXT_LOCAL_CONTINUOUS)) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LMETRIC2_ENTRY_LSMOOTH THEN
        ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LMETRIC2_LOCAL THEN
        EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w z. w IN Sset
          ==> lpcurv ((Gc:real->real^3->real^3^3) (drop(fstcart w))) (sndcart w) (\m. z) =
              sum(1..dimindex(:3)) (\p. sum(1..dimindex(:3)) (\q.
                 z$p * z$q * lpcurv (Gc (drop(fstcart w))) (sndcart w)
                               (\m. if m = 1 then basis q else basis p))) /\
              z dot (Gc (drop(fstcart w)) (sndcart w) ** z) =
              sum(1..dimindex(:3)) (\p. sum(1..dimindex(:3)) (\q.
                 z$p * z$q * lmetric2 (Gc (drop(fstcart w))) (sndcart w)
                               (\m. if m = 1 then basis q else basis p))) /\
              (~(z = vec 0) ==> &0 < z dot (Gc (drop(fstcart w)) (sndcart w) ** z))`
  (LABEL_TAC "exp") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "Sset" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `metric_field V ((Gc:real->real^3->real^3^3) (drop(fstcart(w:real^(1,3)finite_sum))))`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`V:real^3->bool`; `(Gc:real->real^3->real^3^3) (drop(fstcart(w:real^(1,3)finite_sum)))`]
             RFA_LPCURV_FIELD) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`V:real^3->bool`; `lpcurv ((Gc:real->real^3->real^3^3) (drop(fstcart(w:real^(1,3)finite_sum))))`;
                     `sndcart(w:real^(1,3)finite_sum)`; `z:real^3`; `z:real^3`]
             LRG_TENSOR2_EXPAND) THEN
      ASM_REWRITE_TAC[COND_ID];
      MP_TAC(ISPECL [`V:real^3->bool`; `(Gc:real->real^3->real^3^3) (drop(fstcart(w:real^(1,3)finite_sum)))`]
             LRG_LMETRIC2_FIELD) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`V:real^3->bool`; `lmetric2 ((Gc:real->real^3->real^3^3) (drop(fstcart(w:real^(1,3)finite_sum))))`;
                     `sndcart(w:real^(1,3)finite_sum)`; `z:real^3`; `z:real^3`]
             LRG_TENSOR2_EXPAND) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[lmetric2; COND_ID];
      DISCH_TAC THEN MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `V:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC
   `\pz:real^(1,3)finite_sum#real^3.
      --(sum(1..dimindex(:3)) (\p. sum(1..dimindex(:3)) (\q.
            (SND pz)$p * (SND pz)$q *
            lpcurv ((Gc:real->real^3->real^3^3) (drop(fstcart(FST pz)))) (sndcart(FST pz))
              (\m. if m = 1 then basis q else basis p))) /
         sum(1..dimindex(:3)) (\p. sum(1..dimindex(:3)) (\q.
            (SND pz)$p * (SND pz)$q *
            lmetric2 (Gc (drop(fstcart(FST pz)))) (sndcart(FST pz))
              (\m. if m = 1 then basis q else basis p))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN;
                INTER_UNIV; FORALL_PAIR_THM; IN_CROSS] THEN
    MAP_EVERY X_GEN_TAC [`w:real^(1,3)finite_sum`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "exp" (fun th -> MP_TAC(MP (SPECL [`w:real^(1,3)finite_sum`; `z:real^3`] th)
                                       (ASSUME `(w:real^(1,3)finite_sum) IN Sset`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_DIV THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[RFA_CMAP_SND_COMPONENT] THEN
    MATCH_MP_TAC RFA_CMAP_FST_COMPOSE THEN USE_THEN "ent" (fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC CONTINUOUS_MAP_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[RFA_CMAP_SND_COMPONENT] THEN
    MATCH_MP_TAC RFA_CMAP_FST_COMPOSE THEN USE_THEN "ent" (fun th -> REWRITE_TAC[th]);
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN;
                INTER_UNIV; FORALL_PAIR_THM; IN_CROSS] THEN
    MAP_EVERY X_GEN_TAC [`w:real^(1,3)finite_sum`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "exp" (fun th -> MP_TAC(MP (SPECL [`w:real^(1,3)finite_sum`; `z:real^3`] th)
                                       (ASSUME `(w:real^(1,3)finite_sum) IN Sset`))) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    DISCH_TAC THEN UNDISCH_TAC `(z:real^3) IN sphere(vec 0,&1)` THEN
    ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* lambda = -sup(-RQ) over the unit sphere, its continuity in                *)
(* charts, and continuity of lambda on [a,b) x M (pasting over the atlas).   *)
(* ========================================================================= *)

let RFA_LAM_CHART_CONTINUOUS = prove
 (`!V a b e (Gc:real->real^3->real^3^3)
    (FF:real^(1,3)finite_sum->real^(3,3)finite_prod).
     open V /\ &0 < e /\
     (!t. a <= t /\ t < b ==> metric_field V (Gc t)) /\
     smooth_map_on (interval(lift(a - e),lift b) PCROSS V) FF /\
     (!t y. a <= t /\ t < b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y))
     ==> continuous_map
           (subtopology euclidean
              {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN V},
            euclideanreal)
           (\w. sup(IMAGE (\z. --(lpcurv (Gc (drop(fstcart w))) (sndcart w) (\m. z) /
                                  (z dot (Gc (drop(fstcart w)) (sndcart w) ** z))))
                          (sphere(vec 0:real^3,&1))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`subtopology euclidean
       {w:real^(1,3)finite_sum | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
                                 sndcart w IN V}`;
    `euclidean:(real^3)topology`; `sphere(vec 0:real^3,&1)`;
    `\w:real^(1,3)finite_sum z:real^3.
       --(lpcurv ((Gc:real->real^3->real^3^3) (drop(fstcart w))) (sndcart w) (\m. z) /
          (z dot (Gc (drop(fstcart w)) (sndcart w) ** z)))`]
   RFA_SUP_COMPACT_CONTINUOUS)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE; SPHERE_EQ_EMPTY] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RFA_RQ_JOINT_CONTINUOUS THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
  ASM_REWRITE_TAC[]);;

let RFA_SECMIN_SUP = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) c x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     c IN atlas /\ x IN FST c
     ==> mfd_sec_min atlas g x =
         --(sup(IMAGE (\z. --(lpcurv (metric_local atlas c g) (SND c x) (\m. z) /
                               (z dot (metric_local atlas c g (SND c x) ** z))))
                      (sphere(vec 0:real^3,&1))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
                 (metric_local atlas c (g:A->real^3^3)) /\
    SND c x IN IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) g` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `c:(A->bool)#(A->real^3)`; `x:A`]
         RFA_SECMIN_CHART_3D) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas c (g:A->real^3^3)`;
                 `SND (c:(A->bool)#(A->real^3)) x`; `S:real^3^3`] RFA_P3_MIN_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `s = --l ==> l = --s`) THEN
  MATCH_MP_TAC REAL_SUP_UNIQUE THEN REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `l <= r ==> --r <= --l`) THEN
    MATCH_MP_TAC RFA_SECMIN_RAYLEIGH THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `norm(z:real^3) = &1` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `b':real` THEN DISCH_TAC THEN
  ABBREV_TAC `f1 = transp(S:real^3^3) ** basis 1` THEN
  SUBGOAL_THEN `~(f1:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(f1:real^3) dot (metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)
                                     (SND c x) ** f1) = &1` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `inv(norm(f1:real^3)) % f1` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas c (g:A->real^3^3)`;
                 `SND (c:(A->bool)#(A->real^3)) x`; `inv(norm(f1:real^3))`; `f1:real^3`]
         RFA_LPCURV_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL; REAL_MUL_RID] THEN
  SUBGOAL_THEN `~(inv(norm(f1:real^3)) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_INV_EQ_0; NORM_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `b' < --mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(inv(norm(f1:real^3)) pow 2 *
     lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)) (SND c x)
       (\m. f1)) / (inv(norm f1) * inv(norm f1)) =
    lpcurv (metric_local atlas c g) (SND c x) (\m. f1)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `~(norm(f1:real^3) = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[NORM_EQ_0]; CONV_TAC REAL_FIELD];
    ASM_REWRITE_TAC[]]);;

(* Generic chart-wise continuity on [a,b) x M: composition with a chart,  *)
(* and pasting over the atlas (the arguments of RFA_MQ_CHART_CONTINUOUS and *)
(* RFA_MQ_CONTINUOUS for an arbitrary chart-wise continuous function).      *)

let RFA_CHART_COMPOSE_CONTINUOUS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) a b (L:real^(1,N)finite_sum->real) c.
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     continuous_map
       (subtopology euclidean
          {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
               sndcart w IN IMAGE (SND c) (FST c)},
        euclideanreal) L
     ==> continuous_map
           (subtopology
             (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                            (subtopology top (topspace top)))
             {z | z IN topspace(prod_topology (subtopology euclideanreal
                                                 {t | a <= t /\ t < b})
                                               (subtopology top (topspace top))) /\
                  SND z IN FST c},
            euclideanreal)
           (\z. L (pastecart (lift(FST z)) (SND c (SND z))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z:real#A. (L:real^(1,N)finite_sum->real)
                  (pastecart (lift(FST z)) (SND(c:(A->bool)#(A->real^N)) (SND z)))) =
    L o (\z. pastecart (lift(FST z)) (SND c (SND z)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean
               {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
                    sndcart w IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)}` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY;
                IN_INTER; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS; FST; SND;
                TOPSPACE_EUCLIDEANREAL; IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `(\z:real#A. pastecart (lift(FST z)) (SND(c:(A->bool)#(A->real^N)) (SND z))) =
    (\(x,y). pastecart x y) o (\z. lift(FST z),SND c (SND z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM; FST; SND]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (euclidean:(real^1)topology) (euclidean:(real^N)topology)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_PASTECART; CONTINUOUS_MAP_PAIRED] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclideanreal` THEN
    REWRITE_TAC[CONTINUOUS_MAP_LIFT; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    MP_TAC(ISPECL [`subtopology euclideanreal {t | a <= t /\ t < b}`;
                   `subtopology (top:A topology) (topspace top)`] CONTINUOUS_MAP_FST) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology (top:A topology) (FST(c:(A->bool)#(A->real^N)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      MP_TAC(ISPECL [`subtopology euclideanreal {t | a <= t /\ t < b}`;
                     `subtopology (top:A topology) (topspace top)`] CONTINUOUS_MAP_SND) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY;
                  IN_INTER; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS; FST; SND] THEN
      SIMP_TAC[]];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
           SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP
                                 (last(CONJUNCTS th)))) THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX] THEN SIMP_TAC[]]);;

let RFA_CHART_PASTING = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) a b (ff:real->A->real).
     smooth_manifold_atlas top atlas /\
     (!c. c IN atlas
          ==> continuous_map
                (subtopology
                  (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                                 (subtopology top (topspace top)))
                  {z | z IN topspace(prod_topology (subtopology euclideanreal
                                                      {t | a <= t /\ t < b})
                                                    (subtopology top (topspace top))) /\
                       SND z IN FST c},
                 euclideanreal)
                (\z. ff (FST z) (SND z)))
     ==> continuous_map
           (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                          (subtopology top (topspace top)),
            euclideanreal)
           (\z. ff (FST z) (SND z))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:real#A`,`:A`; `:real`,`:B`;
                          `:(A->bool)#(A->real^N)`,`:K`] PASTING_LEMMA) THEN
  MAP_EVERY EXISTS_TAC
   [`\c:(A->bool)#(A->real^N). \z:real#A. (ff:real->A->real) (FST z) (SND z)`;
    `\c:(A->bool)#(A->real^N).
       {z:real#A | z IN topspace(prod_topology
                                   (subtopology euclideanreal {t | a <= t /\ t < b})
                                   (subtopology top (topspace top))) /\
                   SND z IN FST c}`;
    `atlas:((A->bool)#(A->real^N))->bool`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `subtopology (top:A topology) (topspace top)` THEN
      REWRITE_TAC[CONTINUOUS_MAP_SND; SUBTOPOLOGY_TOPSPACE] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_SUBTOPOLOGY; IN_CROSS; IN_INTER;
                IN_ELIM_THM] THEN
    STRIP_TAC THEN
    EXISTS_TAC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[IN_ELIM_THM; IN_CROSS; IN_INTER; TOPSPACE_PROD_TOPOLOGY;
             TOPSPACE_SUBTOPOLOGY; FST; SND] THEN
    ASM_REWRITE_TAC[]]);;

(* Continuity of lambda(t,x) = mfd_sec_min atlas (g t) x on [a,b) x M for a *)
(* family of metrics that extends smoothly past t = a in every chart.        *)

let RFA_SECMIN_CONTINUOUS_GEN = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3).
     smooth_manifold_atlas top atlas /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (g t)) /\
     (!c. c IN atlas
          ==> ?e FF. &0 < e /\
                     smooth_map_on
                       (interval(lift(a - e),lift b) PCROSS IMAGE (SND c) (FST c)) FF /\
                     !t y. a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                           ==> FF(pastecart (lift t) y) =
                               (vectorize:real^3^3->real^(3,3)finite_prod)
                               (metric_local atlas c (g t) y))
     ==> continuous_map
           (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                          (subtopology top (topspace top)),
            euclideanreal)
           (\z. mfd_sec_min atlas (g (FST z)) (SND z))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rm") (LABEL_TAC "Ext"))) THEN
  MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]
                      RFA_CHART_PASTING) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "Ext" (MP_TAC o C MATCH_MP (ASSUME `(c:(A->bool)#(A->real^3)) IN atlas`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
   (X_CHOOSE_THEN `FF:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC
   `\z:real#A. --(sup(IMAGE
      (\v. --(lpcurv (metric_local atlas (c:(A->bool)#(A->real^3))
                        ((g:real->A->real^3^3) (FST z))) (SND c (SND z)) (\m. v) /
              (v dot (metric_local atlas c (g (FST z)) (SND c (SND z)) ** v))))
      (sphere(vec 0:real^3,&1))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY; IN_INTER; IN_ELIM_THM;
                FORALL_PAIR_THM; IN_CROSS; TOPSPACE_EUCLIDEANREAL; IN_UNIV; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFA_SECMIN_SUP THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
     `\w:real^(1,3)finite_sum.
        sup(IMAGE (\v. --(lpcurv (metric_local atlas (c:(A->bool)#(A->real^3))
                                    ((g:real->A->real^3^3) (drop(fstcart w))))
                                 (sndcart w) (\m. v) /
                          (v dot (metric_local atlas c (g (drop(fstcart w)))
                                    (sndcart w) ** v))))
                  (sphere(vec 0:real^3,&1)))`;
     `c:(A->bool)#(A->real^3)`] RFA_CHART_COMPOSE_CONTINUOUS) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(BETA_RULE(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`; `a:real`; `b:real`;
                 `e:real`; `\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
                 `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`]
         RFA_LAM_CHART_CONTINUOUS)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  USE_THEN "rm" (MP_TAC o C MATCH_MP (CONJ (ASSUME `a <= t:real`) (ASSUME `t < b:real`))) THEN
  REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

