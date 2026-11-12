(* ========================================================================= *)
(* Unit pc_rfa_null: null points of lambda along a 3D Ricci flow with        *)
(* lambda >= 0.  At a zero of lambda that is minimal in space and on the     *)
(* left in time, P is positive semidefinite of rank at most one, and the     *)
(* Rayleigh barrier of any unit null vector has Laplacian 0; the local       *)
(* parallel unit field where R > 0 (RFA_PARALLEL_CHART).                     *)
(* ========================================================================= *)

needs "src/pc_rfa_smaxv.ml";;
needs "src/pc_rfa_secpres.ml";;
needs "src/pc_rfa_pinch.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The Rayleigh barrier for a given ordered eigenframe, and the              *)
(* null point lemmas (RFA_NULL_POINT, RFA_RANK1_POINT).                     *)
(* ========================================================================= *)

(* The Rayleigh barrier for lambda in a chart c built from a given ordered  *)
(* Ricci eigenframe S at (t0, x0) (its first vector minimizing P), with the *)
(* explicit barrier and the Laplacian identity at every point.            *)

let RFA_SECMIN_BARRIER_FRAME = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) U c t0 x0
    (S:real^3^3).
     ricci_flow_on (top,atlas) a b g /\ open_in top U /\ c IN atlas /\
     a < t0 /\ t0 < b /\ x0 IN FST c /\ x0 IN U /\
     invertible S /\
     matrix_inv(metric_local atlas c (g t0) (SND c x0)) = transp S ** S /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
            ==> lricci (metric_local atlas c (g t0)) (SND c x0)
                  (transp S ** basis i) (transp S ** basis j) = &0) /\
     lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 1) <=
     lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 2) /\
     lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 1) <=
     lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 3) /\
     mfd_sec_min atlas (g t0) x0 =
     lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 1)
     ==> ?d W (phi:real->real^3->real) D.
           &0 < d /\ open W /\ SND c x0 IN W /\
           W SUBSET IMAGE (SND c) (FST c INTER U) /\
           (!y. y IN W ==> mfd_sec_min atlas (g t0) (chart_inv c y) <= phi t0 y) /\
           phi t0 (SND c x0) = mfd_sec_min atlas (g t0) x0 /\
           (!t. t0 - d < t /\ t <= t0 ==> mfd_sec_min atlas (g t) x0 <= phi t (SND c x0)) /\
           smooth_map_on W (\y. lift(phi t0 y)) /\
           ((\t. phi t (SND c x0)) has_real_derivative D)
             (atreal t0 within {s | t0 - d <= s /\ s <= t0}) /\
           llap (metric_local atlas c (g t0)) (phi t0) (SND c x0) +
           &2 * (mfd_sec_min atlas (g t0) x0 pow 2 +
                 lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 2) *
                 lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 3)) = D /\
           (!t y. phi t y =
                  lpcurv (metric_local atlas c (g t)) y
                    (\m. transp S ** basis 1 -
                         christoffel (metric_local atlas c (g t0)) (SND c x0)
                           (y - SND c x0) (transp S ** basis 1)) /
                  ((transp S ** basis 1 -
                    christoffel (metric_local atlas c (g t0)) (SND c x0)
                      (y - SND c x0) (transp S ** basis 1)) dot
                   (metric_local atlas c (g t) y **
                    (transp S ** basis 1 -
                     christoffel (metric_local atlas c (g t0)) (SND c x0)
                       (y - SND c x0) (transp S ** basis 1)))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U)) /\
                (!y. y IN IMAGE (SND c) (FST c INTER U) ==> chart_inv c y IN U)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `y0 = SND (c:(A->bool)#(A->real^3)) x0` THEN
  ABBREV_TAC `V = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`]
         LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `metric_field V (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) /\
    (y0:real^3) IN V`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ASSUME `lricci_flow V a b
        (\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t))`) THEN
      REWRITE_TAC[lricci_flow] THEN
      DISCH_THEN(MP_TAC o SPEC `t0:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXPAND_TAC ["y0"; "V"] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^3->bool`;
                 `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`;
                 `y0:real^3`; `S:real^3^3`] RFA_P3_MIN_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `f1 = transp(S:real^3^3) ** basis 1` THEN
  ABBREV_TAC `f2 = transp(S:real^3^3) ** basis 2` THEN
  ABBREV_TAC `f3 = transp(S:real^3^3) ** basis 3` THEN
  SUBGOAL_THEN
   `f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y0 - y0) f1 = f1` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_EXT_AT THEN EXISTS_TAC `V:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f1:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `f1 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f1) = &1` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U)
        ==> y IN V /\ chart_inv c y IN FST c /\ SND c (chart_inv c y) = y`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN V` ASSUME_TAC THENL
     [EXPAND_TAC "V" THEN UNDISCH_TAC
       `(y:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U)` THEN
      SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                     ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `{y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                  ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)} =
      IMAGE (SND c) (FST c INTER U) INTER
      {y | (\y. f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1) y IN (:real^3) DIFF {vec 0}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN X_GEN_TAC `z:real^3` THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\h. --(christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 h f1)` THEN
    MATCH_MP_TAC RFA_EXT_HAS_DERIVATIVE THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN {y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                     ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "y0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `{y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                     ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)} SUBSET V` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP LRG_METRIC_INVERTIBLE
    (CONJ (ASSUME `metric_field V (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))`) (ASSUME `(y0:real^3) IN V`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> (transp(S:real^3^3) ** basis i) dot
              (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** (transp S ** basis j)) = if i = j then &1 else &0`
  (LABEL_TAC "orth") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_GFRAME_ORTHO THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `f2 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f2) = &1 /\ f3 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f3) = &1 /\
    f1 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f2) = &0 /\ f1 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f3) = &0 /\
    f2 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f3) = &0 /\ f3 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f2) = &0`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "orth" (fun th ->
      MAP_EVERY (fun (i,j) -> MP_TAC(SPECL [mk_small_numeral i; mk_small_numeral j] th))
        [2,2; 3,3; 1,2; 1,3; 2,3; 3,2]) THEN
    REWRITE_TAC[ARITH; ASSUME `transp(S:real^3^3) ** basis 1 = f1`;
                ASSUME `transp(S:real^3^3) ** basis 2 = f2`;
                ASSUME `transp(S:real^3^3) ** basis 3 = f3`] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `t0 - a:real` THEN
  EXISTS_TAC
   `{y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)}` THEN
  EXISTS_TAC
   `\t y. lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)) y
            (\m. f1 - christoffel (metric_local atlas c (g t0)) y0 (y - y0) f1) /
          ((f1 - christoffel (metric_local atlas c (g t0)) y0 (y - y0) f1) dot
           (metric_local atlas c (g t) y **
            (f1 - christoffel (metric_local atlas c (g t0)) y0 (y - y0) f1)))` THEN
  EXISTS_TAC
   `ltlap 2 (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) (lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))) y0 (\m. f1) +
    &2 * (lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f1) pow 2 +
          lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f2) * lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f3))` THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* d > 0 *)
    ASM_REAL_ARITH_TAC;
    (* W SUBSET IMAGE *)
    SET_TAC[];
    (* spatial barrier *)
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `(y:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U)`)) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t0`; `c:(A->bool)#(A->real^3)`;
                   `chart_inv (c:(A->bool)#(A->real^3)) y`;
                   `f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1`] RFA_SECMIN_RAYLEIGH) THEN
    ASM_SIMP_TAC[];
    (* value at y0 *)
    REWRITE_TAC[REAL_DIV_1];
    (* time barrier *)
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `c:(A->bool)#(A->real^3)`; `x0:A`;
                   `f1:real^3`] RFA_SECMIN_RAYLEIGH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    (* smoothness *)
    MATCH_MP_TAC RFA_RQ_EXT_SMOOTH THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_ELIM_THM];
    (* derivative *)
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MP_TAC(BETA_RULE(ISPECL [`V:real^3->bool`; `a:real`; `b:real`;
       `\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
       `t0:real`; `y0:real^3`; `S:real^3^3`] RFA_BARRIER_REACTION)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    (* llap *)
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x + z = y + z:real`) THEN
    MATCH_MP_TAC RFA_BARRIER_LAP2 THEN
    MAP_EVERY EXISTS_TAC
     [`V:real^3->bool`;
      `{y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                   ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)}`;
      `lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f1)`] THEN
    ASM_REWRITE_TAC[lmetric2] THEN SIMP_TAC[IN_ELIM_THM]]);;

(* At a zero of lambda that is a minimum in space and on the left in time, *)
(* the other two eigenvalues have product 0 and the Rayleigh barrier of the *)
(* minimizing frame vector has Laplacian 0.                                  *)

let RFA_NULL_POINT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) c t0 x0
    (S:real^3^3) d0.
     ricci_flow_on (top,atlas) a b g /\ c IN atlas /\
     a < t0 /\ t0 < b /\ x0 IN FST c /\
     invertible S /\
     matrix_inv(metric_local atlas c (g t0) (SND c x0)) = transp S ** S /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
            ==> lricci (metric_local atlas c (g t0)) (SND c x0)
                  (transp S ** basis i) (transp S ** basis j) = &0) /\
     lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 1) <=
     lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 2) /\
     lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 1) <=
     lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 3) /\
     mfd_sec_min atlas (g t0) x0 =
     lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 1) /\
     (!x. x IN topspace top ==> &0 <= mfd_sec_min atlas (g t0) x) /\
     &0 < d0 /\ (!t. t0 - d0 < t /\ t <= t0 ==> &0 <= mfd_sec_min atlas (g t) x0) /\
     mfd_sec_min atlas (g t0) x0 = &0
     ==> lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 2) *
         lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp S ** basis 3) = &0 /\
         llap (metric_local atlas c (g t0))
              (\y. lpcurv (metric_local atlas c (g t0)) y
                     (\m. transp S ** basis 1 -
                          christoffel (metric_local atlas c (g t0)) (SND c x0)
                            (y - SND c x0) (transp S ** basis 1)) /
                   ((transp S ** basis 1 -
                     christoffel (metric_local atlas c (g t0)) (SND c x0)
                       (y - SND c x0) (transp S ** basis 1)) dot
                    (metric_local atlas c (g t0) y **
                     (transp S ** basis 1 -
                      christoffel (metric_local atlas c (g t0)) (SND c x0)
                        (y - SND c x0) (transp S ** basis 1)))))
              (SND c x0) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `topspace(top:A topology)`;
                 `c:(A->bool)#(A->real^3)`; `t0:real`; `x0:A`; `S:real^3^3`]
         RFA_SECMIN_BARRIER_FRAME) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `W:real^3->bool`
    (X_CHOOSE_THEN `phi:real->real^3->real` (X_CHOOSE_THEN `D:real`
      STRIP_ASSUME_TAC)))) THEN
  POP_ASSUM MP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
                 (metric_local atlas c ((g:real->A->real^3^3) t0)) /\
    SND c x0 IN IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t0)` MP_TAC THENL
       [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
           (SND c x0) (\m. transp(S:real^3^3) ** basis 1) = &0`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_sec_min atlas ((g:real->A->real^3^3) t0) x0 =
       lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) (g t0)) (SND c x0)
              (\m. transp(S:real^3^3) ** basis 1)` THEN
    UNDISCH_TAC `mfd_sec_min atlas ((g:real->A->real^3^3) t0) x0 = &0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_sec_min atlas ((g:real->A->real^3^3) t0) x0 =
     lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) (g t0)) (SND c x0)
            (\m. transp(S:real^3^3) ** basis 1)` THEN
  DISCH_THEN(K ALL_TAC) THEN
  UNDISCH_TAC `mfd_sec_min atlas ((g:real->A->real^3^3) t0) x0 = &0` THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `!y. y IN W ==> &0 <= (phi:real->real^3->real) t0 y` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_sec_min atlas ((g:real->A->real^3^3) t0)
                  (chart_inv (c:(A->bool)#(A->real^3)) y)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) y IN FST c` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= llap (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
               ((phi:real->real^3->real) t0) (SND c x0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LLAP_LOCAL_MIN THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                          `W:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `D <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LEFT_MIN_DERIV_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`\t. (phi:real->real^3->real) t (SND(c:(A->bool)#(A->real^3)) x0)`;
                          `t0:real`; `d:real`; `min d d0`] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_sec_min atlas ((g:real->A->real^3^3) s) x0` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
            (SND c x0) (\m. transp(S:real^3^3) ** basis 2) *
          lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. transp(S:real^3^3) ** basis 3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun pf ->
  SUBGOAL_THEN
   `(phi:real->real^3->real) t0 =
    (\y. lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y
           (\m. transp(S:real^3^3) ** basis 1 -
                christoffel (metric_local atlas c (g t0)) (SND c x0)
                  (y - SND c x0) (transp(S:real^3^3) ** basis 1)) /
         ((transp(S:real^3^3) ** basis 1 -
           christoffel (metric_local atlas c (g t0)) (SND c x0)
             (y - SND c x0) (transp(S:real^3^3) ** basis 1)) dot
          (metric_local atlas c (g t0) y **
           (transp(S:real^3^3) ** basis 1 -
            christoffel (metric_local atlas c (g t0)) (SND c x0)
              (y - SND c x0) (transp(S:real^3^3) ** basis 1)))))`
  (SUBST_ALL_TAC o SYM) THENL
   [REWRITE_TAC[FUN_EQ_THM; pf]; ALL_TAC]) THEN
  UNDISCH_TAC `mfd_sec_min atlas ((g:real->A->real^3^3) t0) x0 = &0` THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
           (SND c x0) (\m. transp(S:real^3^3) ** basis 1) pow 2 = &0`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* At such a null point P is positive semidefinite of rank at most one:    *)
(* P(u,u) P(w,w) = P(u,w)^2 and P(w,w) >= 0, in any chart.                  *)

let RFA_RANK1_POINT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) c t0 x0 d0.
     ricci_flow_on (top,atlas) a b g /\ c IN atlas /\
     a < t0 /\ t0 < b /\ x0 IN FST c /\
     (!x. x IN topspace top ==> &0 <= mfd_sec_min atlas (g t0) x) /\
     &0 < d0 /\ (!t. t0 - d0 < t /\ t <= t0 ==> &0 <= mfd_sec_min atlas (g t) x0) /\
     mfd_sec_min atlas (g t0) x0 = &0
     ==> (!u w. lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. u) *
                lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. w) =
                lpcurv (metric_local atlas c (g t0)) (SND c x0)
                       (\m. if m = 1 then u else w) pow 2) /\
         (!w. &0 <= lpcurv (metric_local atlas c (g t0)) (SND c x0) (\m. w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                riemannian_metric atlas ((g:real->A->real^3^3) t0)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t0`; `c:(A->bool)#(A->real^3)`; `x0:A`]
         RFA_SECMIN_CHART_3D) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `t0:real`;
                 `x0:A`; `S:real^3^3`; `d0:real`] RFA_NULL_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
                 (metric_local atlas c ((g:real->A->real^3^3) t0)) /\
    SND c x0 IN IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^3^3) t0)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)` THEN
  ABBREV_TAC `y0 = SND (c:(A->bool)#(A->real^3)) x0` THEN
  ABBREV_TAC `p1 = lpcurv (G:real^3->real^3^3) y0 (\m. transp(S:real^3^3) ** basis 1)` THEN
  ABBREV_TAC `p2 = lpcurv (G:real^3->real^3^3) y0 (\m. transp(S:real^3^3) ** basis 2)` THEN
  ABBREV_TAC `p3 = lpcurv (G:real^3->real^3^3) y0 (\m. transp(S:real^3^3) ** basis 3)` THEN
  SUBGOAL_THEN `p1 = &0` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u w. lpcurv (G:real^3->real^3^3) y0 (\m. if m = 1 then u else w) =
          ((transp(S:real^3^3) ** basis 1) dot (G y0 ** u)) *
          ((transp S ** basis 1) dot (G y0 ** w)) * p1 +
          ((transp S ** basis 2) dot (G y0 ** u)) *
          ((transp S ** basis 2) dot (G y0 ** w)) * p2 +
          ((transp S ** basis 3) dot (G y0 ** u)) *
          ((transp S ** basis 3) dot (G y0 ** w)) * p3`
  (LABEL_TAC "e1") THENL
   [REPEAT GEN_TAC THEN MAP_EVERY EXPAND_TAC ["p1"; "p2"; "p3"] THEN
    MATCH_MP_TAC RFA_FRAME3_P THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. lpcurv (G:real^3->real^3^3) y0 (\m. w) =
        ((transp(S:real^3^3) ** basis 1) dot (G y0 ** w)) *
        ((transp S ** basis 1) dot (G y0 ** w)) * p1 +
        ((transp S ** basis 2) dot (G y0 ** w)) *
        ((transp S ** basis 2) dot (G y0 ** w)) * p2 +
        ((transp S ** basis 3) dot (G y0 ** w)) *
        ((transp S ** basis 3) dot (G y0 ** w)) * p3`
  (LABEL_TAC "e2") THENL
   [GEN_TAC THEN USE_THEN "e1" (MP_TAC o SPECL [`w:real^3`; `w:real^3`]) THEN
    REWRITE_TAC[COND_ID];
    ALL_TAC] THEN
  USE_THEN "e1" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "e2" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ASSUME `p1 = &0`] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    UNDISCH_TAC `p2 * p3 = &0` THEN CONV_TAC REAL_RING;
    GEN_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_2] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Pointwise algebra of P: bilinear expansions, unit vectors,                *)
(* null vectors and frames of a rank-one P (RFA_RANK1_NULL_FRAME).          *)
(* ========================================================================= *)

(* Algebra of P at a point: bilinear expansions, null vectors of a          *)
(* rank-one P, unit vectors orthogonal to a unit vector, and an ordered     *)
(* Ricci eigenframe with a prescribed unit null first vector.              *)

let RFA_LRICCI_LCOMB = prove
 (`!U (G:real^N->real^N^N) y p q r s w.
     metric_field U G /\ y IN U
     ==> lricci G y (p % q + r % s) w = p * lricci G y q w + r * lricci G y s w /\
         lricci G y w (p % q + r % s) = p * lricci G y w q + r * lricci G y w s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SPEC `w:real^N`)
                             (ASSUME_TAC o SPEC `w:real^N`)) THEN
  REWRITE_TAC[GSYM LIFT_EQ; LIFT_ADD; LIFT_CMUL] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\a. lift(lricci (G:real^N->real^N^N) y a w)`;
                   `p % q:real^N`; `r % s:real^N`] LINEAR_ADD) THEN
    MP_TAC(ISPECL [`\a. lift(lricci (G:real^N->real^N^N) y a w)`;
                   `p:real`; `q:real^N`] LINEAR_CMUL) THEN
    MP_TAC(ISPECL [`\a. lift(lricci (G:real^N->real^N^N) y a w)`;
                   `r:real`; `s:real^N`] LINEAR_CMUL);
    MP_TAC(ISPECL [`\b. lift(lricci (G:real^N->real^N^N) y w b)`;
                   `p % q:real^N`; `r % s:real^N`] LINEAR_ADD) THEN
    MP_TAC(ISPECL [`\b. lift(lricci (G:real^N->real^N^N) y w b)`;
                   `p:real`; `q:real^N`] LINEAR_CMUL) THEN
    MP_TAC(ISPECL [`\b. lift(lricci (G:real^N->real^N^N) y w b)`;
                   `r:real`; `s:real^N`] LINEAR_CMUL)] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

let RFA_LPCURV_QUAD = prove
 (`!U (G:real^N->real^N^N) y a b u w.
     metric_field U G /\ y IN U
     ==> lpcurv G y (\m. a % u + b % w) =
         a pow 2 * lpcurv G y (\m. u) +
         &2 * a * b * lpcurv G y (\m. if m = 1 then u else w) +
         b pow 2 * lpcurv G y (\m. w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_LPCURV_DIAG; RFA_LPCURV_BIL] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] RFA_LRICCI_LCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `u:real^N`;
                 `w:real^N`] LRICCI_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `u:real^N`;
                 `w:real^N`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                  DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  REAL_ARITH_TAC);;

(* Normalization and a unit vector g-orthogonal to a given unit vector.    *)

let RFA_GNORM_UNIT = prove
 (`!U (G:real^N->real^N^N) y v.
     metric_field U G /\ y IN U /\ ~(v = vec 0)
     ==> (inv(sqrt(v dot (G y ** v))) % v) dot
         (G y ** (inv(sqrt(v dot (G y ** v))) % v)) = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < v dot ((G:real^N->real^N^N) y ** v)` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_LT_IMP_LE; REAL_MUL_LINV;
               REAL_LT_IMP_NZ]);;

let RFA_UNIT_PERP3 = prove
 (`!U (G:real^3->real^3^3) y e.
     metric_field U G /\ y IN U /\ e dot (G y ** e) = &1
     ==> ?u. u dot (G y ** u) = &1 /\ e dot (G y ** u) = &0`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a = (G:real^3->real^3^3) y ** e` THEN
  SUBGOAL_THEN `~(a:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(e:real^3) dot a = &1` THEN
    ASM_REWRITE_TAC[DOT_RZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `v = if (a:real^3)$2 = &0 /\ a$3 = &0 then vector[--(a$3); &0; a$1]:real^3
                  else vector[&0; a$3; --(a$2)]` THEN
  SUBGOAL_THEN `(a:real^3) dot v = &0 /\ ~(v:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN COND_CASES_TAC THEN
    REWRITE_TAC[DOT_3; VECTOR_3; CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THENL
     [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~(a:real^3 = vec 0)` THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~((a:real^3)$2 = &0 /\ a$3 = &0)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `inv(sqrt(v dot ((G:real^3->real^3^3) y ** v))) % (v:real^3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_GNORM_UNIT THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `e:real^3`;
                 `v:real^3`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

(* A unit null vector g-orthogonal to a given unit null vector, and an     *)
(* ordered Ricci eigenframe starting with a given unit null vector, for a  *)
(* positive semidefinite P of rank at most one.                            *)

let RFA_RANK1_NULL_VANISH = prove
 (`!(G:real^N->real^N^N) y v w.
     (!u w. lpcurv G y (\m. u) * lpcurv G y (\m. w) =
            lpcurv G y (\m. if m = 1 then u else w) pow 2) /\
     lpcurv G y (\m. v) = &0
     ==> lpcurv G y (\m. if m = 1 then v else w) = &0 /\
         lpcurv G y (\m. if m = 1 then w else v) = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "r1") ASSUME_TAC) THEN
  USE_THEN "r1" (MP_TAC o SPECL [`v:real^N`; `w:real^N`]) THEN
  USE_THEN "r1" (MP_TAC o SPECL [`w:real^N`; `v:real^N`]) THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_EQ_0; ARITH]) THEN ASM_REWRITE_TAC[]);;

let RFA_RANK1_NULL_PERP = prove
 (`!U (G:real^3->real^3^3) y e.
     metric_field U G /\ y IN U /\
     (!u w. lpcurv G y (\m. u) * lpcurv G y (\m. w) =
            lpcurv G y (\m. if m = 1 then u else w) pow 2) /\
     e dot (G y ** e) = &1 /\ lpcurv G y (\m. e) = &0
     ==> ?e2. e2 dot (G y ** e2) = &1 /\ e dot (G y ** e2) = &0 /\
              lpcurv G y (\m. e2) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `e:real^3`]
         RFA_UNIT_PERP3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n1:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `e:real^3`;
                 `n1:real^3`] RFA_NORMAL3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n2:real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `A = lpcurv (G:real^3->real^3^3) y (\m. n1)` THEN
  ASM_CASES_TAC `A = &0` THENL
   [EXISTS_TAC `n1:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `B = lpcurv (G:real^3->real^3^3) y (\m. if m = 1 then n1 else n2)` THEN
  ABBREV_TAC `v = B % n1 + --A % (n2:real^3)` THEN
  SUBGOAL_THEN `lpcurv (G:real^3->real^3^3) y (\m. v) = &0` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `B:real`;
                   `--A:real`; `n1:real^3`; `n2:real^3`] RFA_LPCURV_QUAD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n1:real^3`; `n2:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3) dot ((G:real^3->real^3^3) y ** v) = &0 /\
                n2 dot (G y ** v) = --A` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RADD;
                DOT_RMUL] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `n2:real^3`;
                   `n1:real^3`] LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `n2 dot ((G:real^3->real^3^3) y ** v) = --A` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `inv(sqrt(v dot ((G:real^3->real^3^3) y ** v))) % (v:real^3)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RFA_GNORM_UNIT THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; REAL_MUL_RZERO];
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                   `inv(sqrt(v dot ((G:real^3->real^3^3) y ** v)))`; `v:real^3`]
           RFA_LPCURV_CMUL) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO]]);;

let RFA_RANK1_NULL_FRAME = prove
 (`!U (G:real^3->real^3^3) y e.
     metric_field U G /\ y IN U /\
     (!u w. lpcurv G y (\m. u) * lpcurv G y (\m. w) =
            lpcurv G y (\m. if m = 1 then u else w) pow 2) /\
     (!w. &0 <= lpcurv G y (\m. w)) /\
     e dot (G y ** e) = &1 /\ lpcurv G y (\m. e) = &0
     ==> ?S:real^3^3.
           invertible S /\ matrix_inv(G y) = transp S ** S /\
           (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
                  ==> lricci G y (transp S ** basis i) (transp S ** basis j) = &0) /\
           lpcurv G y (\m. transp S ** basis 1) <= lpcurv G y (\m. transp S ** basis 2) /\
           lpcurv G y (\m. transp S ** basis 1) <= lpcurv G y (\m. transp S ** basis 3) /\
           transp S ** basis 1 = e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "r1") (CONJUNCTS_THEN2 (LABEL_TAC "psd")
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `e:real^3`]
         RFA_RANK1_NULL_PERP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e2:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `e:real^3`;
                 `e2:real^3`] RFA_NORMAL3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e3:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!a b. a dot ((G:real^3->real^3^3) y ** b) = b dot (G y ** a)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_SYM THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `e:real^3`; `e2:real^3`; `e3:real^3`]
         RFA_ORTHO3_MATRIX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!u w. lricci (G:real^3->real^3^3) y u w =
          lscalar G y / &2 * (u dot (G y ** w)) - lpcurv G y (\m. if m = 1 then u else w)`
  ASSUME_TAC THENL
   [REWRITE_TAC[RFA_LPCURV_BIL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. lpcurv (G:real^3->real^3^3) y (\m. if m = 1 then e else w) = &0 /\
        lpcurv G y (\m. if m = 1 then w else e) = &0 /\
        lpcurv G y (\m. if m = 1 then e2 else w) = &0 /\
        lpcurv G y (\m. if m = 1 then w else e2) = &0`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`G:real^3->real^3^3`; `y:real^3`; `e:real^3`; `w:real^3`]
           RFA_RANK1_NULL_VANISH) THEN
    MP_TAC(ISPECL [`G:real^3->real^3^3`; `y:real^3`; `e2:real^3`; `w:real^3`]
           RFA_RANK1_NULL_VANISH) THEN
    USE_THEN "r1" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
          ==> lricci (G:real^3->real^3^3) y (transp(S:real^3^3) ** basis i)
                     (transp S ** basis j) = &0`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(i = 1 \/ i = 2 \/ i = 3) /\ (j = 1 \/ j = 2 \/ j = 3)` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IMP_CONJ] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH]) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `F`))) THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
    TRY(MP_TAC(ISPECL [`e3:real^3`; `e:real^3`] (ASSUME
      `!a b. a dot ((G:real^3->real^3^3) y ** b) = b dot (G y ** a)`))) THEN
    TRY(MP_TAC(ISPECL [`e3:real^3`; `e2:real^3`] (ASSUME
      `!a b. a dot ((G:real^3->real^3^3) y ** b) = b dot (G y ** a)`))) THEN
    TRY(MP_TAC(ISPECL [`e2:real^3`; `e:real^3`] (ASSUME
      `!a b. a dot ((G:real^3->real^3^3) y ** b) = b dot (G y ** a)`))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `S:real^3^3` THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* ========================================================================= *)
(* Local vector calculus for the parallel field: gradient zero,              *)
(* llap of h^2 k, the field Y = G^-1 P(b,.), the orthogonality of nabla Y   *)
(* to null vectors, nabla Y parallel to Y, and nabla (Y/|Y|) = 0.          *)
(* ========================================================================= *)

(* A function with vanishing gradient norm has vanishing derivative.       *)

let RFA_LGRAD2_ZERO = prove
 (`!U (G:real^N->real^N^N) f y.
     metric_field U G /\ y IN U /\ (\z. lift(f z)) differentiable (at y) /\
     lgrad2 G f y = &0
     ==> !v. rfa_d1 f y v = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(lambda i. rfa_d1 (f:real^N->real) y (basis i)):real^N = vec 0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
           LRG_METRIC_INV_POSDEF) THEN
    ASM_REWRITE_TAC[positive_definite] THEN STRIP_TAC THEN
    UNDISCH_TAC `lgrad2 (G:real^N->real^N^N) f y = &0` THEN
    REWRITE_TAC[RFA_LGRAD2_D1; rfa_lginner; LRG_QUADFORM_SUM] THEN
    ASM_MESON_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN
  SUBGOAL_THEN `linear (\h. lift(rfa_d1 (f:real^N->real) y h))` ASSUME_TAC THENL
   [REWRITE_TAC[rfa_d1; LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:N) ==> rfa_d1 (f:real^N->real) y (basis i) = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `(lambda i. rfa_d1 (f:real^N->real) y (basis i)):real^N = vec 0` THEN
    REWRITE_TAC[CART_EQ; VEC_COMPONENT] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[LAMBDA_BETA];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  REWRITE_TAC[GSYM LIFT_EQ; LIFT_NUM] THEN
  MP_TAC(ISPECL [`\h. lift(rfa_d1 (f:real^N->real) y h)`;
                 `\i. (v:real^N)$i % basis i:real^N`; `1..dimindex(:N)`] LINEAR_VSUM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[IN_NUMSEG; o_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_CMUL th)]) THEN
  ASM_SIMP_TAC[LIFT_NUM; VECTOR_MUL_RZERO]);;

(* The Laplacian of h^2 k at a zero of h.                                  *)

let RFA_LLAP_SQ_MUL = prove
 (`!U (G:real^N->real^N^N) h k y.
     metric_field U G /\ smooth_map_on U (\z. lift(h z)) /\
     smooth_map_on U (\z. lift(k z)) /\ y IN U /\ h y = &0
     ==> llap G (\z. (h z * h z) * k z) y = &2 * k y * lgrad2 G h y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift((h:real^N->real) z * h z))` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `\z. (h:real^N->real) z * h z`;
                 `k:real^N->real`; `y:real^N`] RFA_LLAP_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `h:real^N->real`;
                 `h:real^N->real`; `y:real^N`] RFA_LLAP_MUL) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `!v. rfa_d1 (\z. (h:real^N->real) z * h z) y v = &0` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`h:real^N->real`; `h:real^N->real`; `y:real^N`; `v:real^N`]
           RFA_D1_MUL_AT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[RFA_LGRAD2_D1] THEN
  ASM_REWRITE_TAC[rfa_lginner; REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0] THEN
  REAL_ARITH_TAC);;

(* The covector P(b,.) and the vector field Y = G^-1 P(b,.):               *)
(* g(Y,w) = P(b,w), and Y is smooth.                                         *)

let RFA_PCOV_DOT = prove
 (`!U (G:real^N->real^N^N) y b w.
     metric_field U G /\ y IN U
     ==> ((lambda k. lpcurv G y (\m. if m = 1 then b else basis k)):real^N) dot w =
         lpcurv G y (\m. if m = 1 then b else w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear (\w. lift(lpcurv (G:real^N->real^N^N) y (\m. if m = 1 then b else w)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[RFA_LPCURV_BIL; LIFT_SUB; LIFT_CMUL] THEN
    MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[RFA_LIFT_DOT_GMUL_LINEAR];
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
             LRG_LRICCI_LINEAR) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o ABS_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `lpcurv (G:real^N->real^N^N) y
      (\m. if m = 1 then b else vsum(1..dimindex(:N)) (\i. (w:real^N)$i % basis i)) =
    drop(lift(lpcurv G y (\m. if m = 1 then b
                                else vsum(1..dimindex(:N)) (\i. w$i % basis i))))`
  SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\w. lift(lpcurv (G:real^N->real^N^N) y (\m. if m = 1 then b else w))`;
                 `\i. (w:real^N)$i % basis i:real^N`; `1..dimindex(:N)`] LINEAR_VSUM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DROP_VSUM; FINITE_NUMSEG; o_DEF; dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_CMUL th)]) THEN
  ASM_SIMP_TAC[LAMBDA_BETA; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

let RFA_PFIELD_DOT = prove
 (`!U (G:real^N->real^N^N) y b w.
     metric_field U G /\ y IN U
     ==> (matrix_inv(G y) ** ((lambda k. lpcurv G y (\m. if m = 1 then b else basis k)):real^N))
         dot (G y ** w) =
         lpcurv G y (\m. if m = 1 then b else w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP LRG_METRIC_INVERTIBLE
    (CONJ (ASSUME `metric_field U (G:real^N->real^N^N)`) (ASSUME `(y:real^N) IN U`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [SYM(ASSUME
    `transp((G:real^N->real^N^N) y) = G y`)] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN MATCH_MP_TAC RFA_PCOV_DOT THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let RFA_PFIELD_SMOOTH = prove
 (`!U (G:real^N->real^N^N) b.
     metric_field U G
     ==> smooth_map_on U
           (\y. matrix_inv(G y) **
                ((lambda k. lpcurv G y (\m. if m = 1 then b else basis k)):real^N))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]
           LRG_METRIC_INVERTIBLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
                 `\k y. lift(lpcurv (G:real^N->real^N^N) y
                               (\m. if m = 1 then b else basis k))`]
         (INST_TYPE [`:N`,`:M`] SMOOTH_MAP_ON_LAMBDA)) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_LPCURV_FIELD) THEN
  ASM_SIMP_TAC[]);;

(* Symmetry of P in its two slots.                                         *)

let RFA_LPCURV_SYM2 = prove
 (`!U (G:real^N->real^N^N) y u w.
     metric_field U G /\ y IN U
     ==> lpcurv G y (\m. if m = 1 then u else w) = lpcurv G y (\m. if m = 1 then w else u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_LPCURV_BIL] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `u:real^N`;
                 `w:real^N`] LRICCI_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `u:real^N`;
                 `w:real^N`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

(* The key orthogonality at a point where P is PSD of rank one nearby: for  *)
(* a unit null vector e whose Rayleigh barrier has Laplacian 0, the        *)
(* covariant derivative of Y = G^-1 P(b,.) is g-orthogonal to e.            *)

let RFA_PARALLEL_ORTHO = prove
 (`!U (G:real^N->real^N^N) N b y0 e z.
     metric_field U G /\ open N /\ N SUBSET U /\ y0 IN N /\
     (!y u w. y IN N
              ==> lpcurv G y (\m. u) * lpcurv G y (\m. w) =
                  lpcurv G y (\m. if m = 1 then u else w) pow 2) /\
     (!y. y IN N ==> &0 < lpcurv G y (\m. b)) /\
     e dot (G y0 ** e) = &1 /\ lpcurv G y0 (\m. e) = &0 /\
     llap G (\y. lpcurv G y (\m. e - christoffel G y0 (y - y0) e) /
                 ((e - christoffel G y0 (y - y0) e) dot
                  (G y ** (e - christoffel G y0 (y - y0) e)))) y0 = &0
     ==> lcovd G (\y. z)
           (\y. matrix_inv(G y) **
                ((lambda k. lpcurv G y (\m. if m = 1 then b else basis k)):real^N))
           y0 dot (G y0 ** e) = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "r1") (CONJUNCTS_THEN2 (LABEL_TAC "pb")
      STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\ (y0:real^N) IN U` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC
   `Y = \y. matrix_inv((G:real^N->real^N^N) y) **
            ((lambda k. lpcurv G y (\m. if m = 1 then b else basis k)):real^N)` THEN
  ABBREV_TAC `E = \y:real^N. e - christoffel (G:real^N->real^N^N) y0 (y - y0) e` THEN
  SUBGOAL_THEN `(E:real^N->real^N) y0 = e` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[] THEN MATCH_MP_TAC RFA_EXT_AT THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (Y:real^N->real^N) /\ smooth_map_on U (E:real^N->real^N)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Y"; "E"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_PFIELD_SMOOTH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_EXT_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y w. y IN U ==> (Y:real^N->real^N) y dot ((G:real^N->real^N^N) y ** w) =
                     lpcurv G y (\m. if m = 1 then b else w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Y" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_PFIELD_DOT THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `W = {y:real^N | y IN N /\ ~((E:real^N->real^N) y = vec 0)}` THEN
  SUBGOAL_THEN `open(W:real^N->bool) /\ (y0:real^N) IN W /\ W SUBSET U` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN
    MATCH_MP_TAC(TAUT `a /\ b /\ c ==> a /\ b /\ c`) THEN
    CONJ_TAC THENL [ALL_TAC; CONJ_TAC] THENL
     [SUBGOAL_THEN
       `{y:real^N | y IN N /\ ~((E:real^N->real^N) y = vec 0)} =
        N INTER {y | E y IN (:real^N) DIFF {vec 0}}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING];
        ALL_TAC] THEN
      MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
      SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN X_GEN_TAC `x:real^N` THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\h. --(christoffel (G:real^N->real^N^N) y0 h e)` THEN
      EXPAND_TAC "E" THEN MATCH_MP_TAC RFA_EXT_HAS_DERIVATIVE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `e dot ((G:real^N->real^N^N) y0 ** e) = &1` THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(N:real^N->bool) SUBSET U` THEN REWRITE_TAC[SUBSET] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field W (G:real^N->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `h = \y. (Y:real^N->real^N) y dot ((G:real^N->real^N^N) y ** E y)` THEN
  ABBREV_TAC
   `k = \y. inv(lpcurv (G:real^N->real^N^N) y (\m. b) *
               ((E:real^N->real^N) y dot (G y ** E y)))` THEN
  SUBGOAL_THEN `(h:real^N->real) y0 = &0` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`G:real^N->real^N^N`; `y0:real^N`; `e:real^N`; `b:real^N`]
           RFA_RANK1_NULL_VANISH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN USE_THEN "r1" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (E:real^N->real^N) y = e - christoffel (G:real^N->real^N^N) y0 (y - y0) e`
  (LABEL_TAC "Edef") THENL [EXPAND_TAC "E" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN W
        ==> lpcurv (G:real^N->real^N^N) y (\m. e - christoffel G y0 (y - y0) e) /
            ((e - christoffel G y0 (y - y0) e) dot (G y ** (e - christoffel G y0 (y - y0) e))) =
            ((h:real^N->real) y * h y) * (k:real^N->real) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN N /\ ~((E:real^N->real^N) y = vec 0)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN W` THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM(ASSUME `!y. (E:real^N->real^N) y =
                                e - christoffel (G:real^N->real^N^N) y0 (y - y0) e`)] THEN
    MAP_EVERY EXPAND_TAC ["h"; "k"] THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `&0 < lpcurv (G:real^N->real^N^N) y (\m. b) /\
                  &0 < (E:real^N->real^N) y dot (G y ** E y)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "pb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < lpcurv (G:real^N->real^N^N) y (\m. b) /\
                  &0 < (e - christoffel G y0 (y - y0) e) dot
                       (G y ** (e - christoffel G y0 (y - y0) e))`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "r1" (fun th -> MP_TAC(MP (SPECL [`y:real^N`;
      `e - christoffel (G:real^N->real^N^N) y0 (y - y0) e`; `b:real^N`] th)
      (ASSUME `(y:real^N) IN N`))) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `e - christoffel (G:real^N->real^N^N) y0 (y - y0) e`; `b:real^N`]
           RFA_LPCURV_SYM2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ABBREV_TAC `pE = lpcurv (G:real^N->real^N^N) y (\m. e - christoffel G y0 (y - y0) e)` THEN
    ABBREV_TAC `pb = lpcurv (G:real^N->real^N^N) y (\m. b)` THEN
    ABBREV_TAC `pbE = lpcurv (G:real^N->real^N^N) y
                        (\m. if m = 1 then b else e - christoffel G y0 (y - y0) e)` THEN
    ABBREV_TAC `gE = (e - christoffel (G:real^N->real^N^N) y0 (y - y0) e) dot
                     (G y ** (e - christoffel G y0 (y - y0) e))` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `~(pb = &0) /\ ~(gE = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `pE * pb = pbE pow 2` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REMOVE_THEN "Edef" (K ALL_TAC) THEN
  (* smoothness of h and k on W *)
  SUBGOAL_THEN `smooth_map_on W (\y. lift((h:real^N->real) y)) /\
                smooth_map_on W (\y. lift((k:real^N->real) y))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `smooth_map_on W (Y:real^N->real^N) /\ smooth_map_on W (E:real^N->real^N) /\
                  smooth_map_on W (\y. (G:real^N->real^N^N) y ** E y)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `smooth_map_on W (Y:real^N->real^N) /\ smooth_map_on W (E:real^N->real^N)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        ASM_MESON_TAC[metric_field];
        REWRITE_TAC[ETA_AX] THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["h"; "k"] THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`W:real^N->bool`;
      `\y. lift(lpcurv (G:real^N->real^N^N) y (\m. b) *
                ((E:real^N->real^N) y dot (G y ** E y)))`] SMOOTH_MAP_ON_LIFT_INV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_LPCURV_FIELD) THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^N) IN N /\ ~((E:real^N->real^N) y = vec 0)` STRIP_ASSUME_TAC
      THENL
       [UNDISCH_TAC `(y:real^N) IN W` THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [USE_THEN "pb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  (* the Laplacian of q = h^2 k and the vanishing of dh at y0 *)
  SUBGOAL_THEN `lgrad2 (G:real^N->real^N^N) h y0 = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`W:real^N->bool`; `G:real^N->real^N^N`; `h:real^N->real`;
                   `k:real^N->real`; `y0:real^N`] RFA_LLAP_SQ_MUL) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `llap (G:real^N->real^N^N) (\z. ((h:real^N->real) z * h z) * (k:real^N->real) z) y0 =
      llap G (\y. lpcurv G y (\m. e - christoffel G y0 (y - y0) e) /
                  ((e - christoffel G y0 (y - y0) e) dot
                   (G y ** (e - christoffel G y0 (y - y0) e)))) y0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RFA_LLAP_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (k:real^N->real) y0` ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_INV THEN USE_THEN "pb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. rfa_d1 (h:real^N->real) y0 v = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LGRAD2_ZERO THEN
    MAP_EVERY EXISTS_TAC [`W:real^N->bool`; `G:real^N->real^N^N`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* metric compatibility: dh = g(nabla Y, E) + g(Y, nabla E), nabla E(y0) = 0 *)
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `\y:real^N. (z:real^N)`;
                 `Y:real^N->real^N`; `E:real^N->real^N`; `y0:real^N`] LCOVD_METRIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `lcovd (G:real^N->real^N^N) (\y:real^N. (z:real^N)) E y0 = vec 0`
  SUBST1_TAC THENL
   [REWRITE_TAC[lcovd] THEN
    SUBGOAL_THEN `frechet_derivative (E:real^N->real^N) (at y0) =
                  (\h. --(christoffel (G:real^N->real^N^N) y0 h e))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN EXPAND_TAC "E" THEN
      MATCH_MP_TAC RFA_EXT_HAS_DERIVATIVE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_ADD_RID] THEN
  SUBGOAL_THEN
   `frechet_derivative (\y. lift((Y:real^N->real^N) y dot ((G:real^N->real^N^N) y ** E y)))
                       (at y0) z = vec 0`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `z:real^N` (ASSUME `!v. rfa_d1 (h:real^N->real) y0 v = &0`)) THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[rfa_d1] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_VEC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN MESON_TAC[]);;

(* A vector g-orthogonal to all unit null vectors of a rank-one PSD P is a  *)
(* multiple of Y = G^-1 P(b,.) (P(b,b) > 0).                                *)

let RFA_PARALLEL_YPAR = prove
 (`!U (G:real^N->real^N^N) y0 b X Y.
     metric_field U G /\ y0 IN U /\
     (!u w. lpcurv G y0 (\m. u) * lpcurv G y0 (\m. w) =
            lpcurv G y0 (\m. if m = 1 then u else w) pow 2) /\
     &0 < lpcurv G y0 (\m. b) /\
     (!e. e dot (G y0 ** e) = &1 /\ lpcurv G y0 (\m. e) = &0
          ==> X dot (G y0 ** e) = &0) /\
     Y = matrix_inv(G y0) **
         ((lambda k. lpcurv G y0 (\m. if m = 1 then b else basis k)):real^N)
     ==> X = ((X dot (G y0 ** Y)) / (Y dot (G y0 ** Y))) % Y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "r1") (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "orth") ASSUME_TAC))))) THEN
  SUBGOAL_THEN `!w. (Y:real^N) dot ((G:real^N->real^N^N) y0 ** w) =
                    lpcurv G y0 (\m. if m = 1 then b else w)`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_PFIELD_DOT THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a c. a dot ((G:real^N->real^N^N) y0 ** c) = c dot (G y0 ** a)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (Y:real^N) dot ((G:real^N->real^N^N) y0 ** Y)` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `!w. (Y:real^N) dot ((G:real^N->real^N^N) y0 ** w) =
                     lpcurv G y0 (\m. if m = 1 then b else w)` THEN
    DISCH_THEN(MP_TAC o SPEC `b:real^N`) THEN ASM_REWRITE_TAC[DOT_LZERO] THEN
    REWRITE_TAC[COND_ID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `mu = ((X:real^N) dot ((G:real^N->real^N^N) y0 ** Y)) / (Y dot (G y0 ** Y))` THEN
  ABBREV_TAC `Z = (X:real^N) - mu % Y` THEN
  SUBGOAL_THEN `(Y:real^N) dot ((G:real^N->real^N^N) y0 ** Z) = &0` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Z"; "mu"] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RSUB;
                DOT_RMUL] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THEN
    UNDISCH_TAC `&0 < (Y:real^N) dot ((G:real^N->real^N^N) y0 ** Y)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `lpcurv (G:real^N->real^N^N) y0 (\m. if m = 1 then b else Z) = &0`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(Y:real^N) dot ((G:real^N->real^N^N) y0 ** Z) = &0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lpcurv (G:real^N->real^N^N) y0 (\m. Z) = &0` ASSUME_TAC THENL
   [USE_THEN "r1" (MP_TAC o SPECL [`Z:real^N`; `b:real^N`]) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `Z:real^N`;
                   `b:real^N`] RFA_LPCURV_SYM2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[ASSUME `lpcurv (G:real^N->real^N^N) y0 (\m. if m = 1 then b else Z) = &0`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `Z:real^N = vec 0` THENL
   [UNDISCH_TAC `(X:real^N) - mu % Y = Z` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(X:real^N) dot ((G:real^N->real^N^N) y0 ** Z) = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt((Z:real^N) dot ((G:real^N->real^N^N) y0 ** Z))` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC LRG_METRIC_POS THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `Z:real^N`]
           RFA_GNORM_UNIT) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`;
                   `inv(sqrt((Z:real^N) dot ((G:real^N->real^N^N) y0 ** Z)))`; `Z:real^N`]
           RFA_LPCURV_CMUL) THEN
    ABBREV_TAC `c = inv(sqrt((Z:real^N) dot ((G:real^N->real^N^N) y0 ** Z)))` THEN
    SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REPEAT DISCH_TAC THEN
    USE_THEN "orth" (MP_TAC o SPEC `c % (Z:real^N)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; REAL_ENTIRE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Z:real^N) dot ((G:real^N->real^N^N) y0 ** Z) = &0` MP_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM(ASSUME `(X:real^N) - mu % Y = Z`)] THEN
    REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN
    ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `Z:real^N`]
         LRG_METRIC_POS) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* If the covariant derivative of a nonvanishing field Y is a multiple of Y, *)
(* then its normalization Y/|Y| has covariant derivative 0.                 *)

let RFA_PARALLEL_NORM = prove
 (`!U (G:real^N->real^N^N) (Y:real^N->real^N) y0 z mu.
     metric_field U G /\ smooth_map_on U Y /\ y0 IN U /\
     (!y. y IN U ==> ~(Y y = vec 0)) /\
     lcovd G (\y. z) Y y0 = mu % Y y0
     ==> lcovd G (\y. z) (\y. inv(sqrt(Y y dot (G y ** Y y))) % Y y) y0 = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U ==> &0 < (Y:real^N->real^N) y dot ((G:real^N->real^N^N) y ** Y y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s = \y. inv(sqrt((Y:real^N->real^N) y dot ((G:real^N->real^N^N) y ** Y y)))` THEN
  SUBGOAL_THEN `!y. y IN U ==> &0 < (s:real^N->real) y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "s" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\y. lift((s:real^N->real) y))` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
      `\y. lift(sqrt((Y:real^N->real^N) y dot ((G:real^N->real^N^N) y ** Y y)))`]
      SMOOTH_MAP_ON_LIFT_INV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`;
        `\y. lift((Y:real^N->real^N) y dot ((G:real^N->real^N^N) y ** Y y))`]
        SMOOTH_MAP_ON_LIFT_SQRT) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[ETA_AX] THEN
      ASM_MESON_TAC[metric_field];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `V = \y. (s:real^N->real) y % (Y:real^N->real^N) y` THEN
  SUBGOAL_THEN `(\y. inv(sqrt((Y:real^N->real^N) y dot ((G:real^N->real^N^N) y ** Y y))) % Y y) =
                (V:real^N->real^N)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["V"; "s"] THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (V:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\y. lift((s:real^N->real) y)`; `Y:real^N->real^N`]
           SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    ASM_REWRITE_TAC[LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  (* lcovd V = kappa Y *)
  SUBGOAL_THEN `?kappa. lcovd (G:real^N->real^N^N) (\y. z) (V:real^N->real^N) y0 =
                        kappa % (Y:real^N->real^N) y0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. lift((s:real^N->real) y)) differentiable (at y0) /\
                  (Y:real^N->real^N) differentiable (at y0)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->real`;
                   `\h. drop(frechet_derivative (\y. lift((s:real^N->real) y)) (at y0) h)`;
                   `Y:real^N->real^N`; `frechet_derivative (Y:real^N->real^N) (at y0)`;
                   `y0:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    SUBGOAL_THEN `(\x. (s:real^N->real) x % (Y:real^N->real^N) x) = V` SUBST1_TAC THENL
     [EXPAND_TAC "V" THEN REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    EXISTS_TAC `(s:real^N->real) y0 * mu +
                drop(frechet_derivative (\y. lift((s:real^N->real) y)) (at y0) z)` THEN
    UNDISCH_TAC `lcovd (G:real^N->real^N^N) (\y. z) (Y:real^N->real^N) y0 = mu % Y y0` THEN
    REWRITE_TAC[lcovd] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN
    SUBGOAL_THEN `(V:real^N->real^N) y0 = (s:real^N->real) y0 % (Y:real^N->real^N) y0`
    SUBST1_TAC THENL [EXPAND_TAC "V" THEN REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`]
           CHRISTOFFEL_BILINEAR) THEN
    ASM_REWRITE_TAC[bilinear] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^N` o CONJUNCT1) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_CMUL th)]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `frechet_derivative (Y:real^N->real^N) (at y0) z =
                  mu % Y y0 - christoffel (G:real^N->real^N^N) y0 z (Y y0)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `frechet_derivative (Y:real^N->real^N) (at y0) z +
                   christoffel (G:real^N->real^N^N) y0 z (Y y0) = mu % Y y0` THEN
      VECTOR_ARITH_TAC;
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  (* |V| = 1 near y0, hence g(lcovd V, V) = 0 at y0 *)
  SUBGOAL_THEN `!y. y IN U ==> (V:real^N->real^N) y dot ((G:real^N->real^N^N) y ** V y) = &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["V"; "s"] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_GNORM_UNIT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `\y:real^N. (z:real^N)`;
                 `V:real^N->real^N`; `V:real^N->real^N`; `y0:real^N`] LCOVD_METRIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `frechet_derivative (\y. lift((V:real^N->real^N) y dot ((G:real^N->real^N^N) y ** V y)))
                       (at y0) z = vec 0`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `frechet_derivative (\y. lift((V:real^N->real^N) y dot ((G:real^N->real^N^N) y ** V y)))
                         (at y0) =
      frechet_derivative (\y:real^N. lift(&1)) (at y0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `frechet_derivative (\y:real^N. lift(&1)) (at y0) = (\h. vec 0)`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(V:real^N->real^N) y0 = (s:real^N->real) y0 % (Y:real^N->real^N) y0`
  SUBST1_TAC THENL [EXPAND_TAC "V" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
  SUBGOAL_THEN `&0 < (s:real^N->real) y0 /\
                &0 < (Y:real^N->real^N) y0 dot ((G:real^N->real^N^N) y0 ** Y y0)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `kappa = &0` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
  UNDISCH_TAC `&0 = kappa * (s:real^N->real) y0 *
                    ((Y:real^N->real^N) y0 dot ((G:real^N->real^N^N) y0 ** Y y0)) +
                    s y0 * kappa * (Y y0 dot (G y0 ** Y y0))` THEN
  REWRITE_TAC[REAL_ARITH `k * s * n + s * k * n = &2 * k * (s * n)`] THEN
  DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[REAL_ENTIRE] THEN
  SUBGOAL_THEN `&0 < (s:real^N->real) y0 *
                ((Y:real^N->real^N) y0 dot ((G:real^N->real^N^N) y0 ** Y y0))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* The parallel unit field in a chart at an interior time                    *)
(* (RFA_PARALLEL_CHART).                                                     *)
(* ========================================================================= *)

(* The parallel unit field in a chart at an interior time where lambda = 0  *)
(* everywhere (lambda >= 0 before): on an open set N of the chart where     *)
(* P(b0,b0) > 0, Y/|Y| with Y = G^-1 P(b0,.) is parallel.                   *)

let RFA_PARALLEL_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) c t0 N b0 y z.
     ricci_flow_on (top,atlas) a b g /\ c IN atlas /\ a < t0 /\ t0 < b /\
     (!t x. a < t /\ t <= t0 /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     (!x. x IN topspace top ==> mfd_sec_min atlas (g t0) x = &0) /\
     open N /\ N SUBSET IMAGE (SND c) (FST c) /\
     (!y. y IN N ==> &0 < lpcurv (metric_local atlas c (g t0)) y (\m. b0)) /\
     y IN N
     ==> lcovd (metric_local atlas c (g t0)) (\w. z)
           (\w. inv(sqrt((matrix_inv(metric_local atlas c (g t0) w) **
                          ((lambda k. lpcurv (metric_local atlas c (g t0)) w
                                        (\m. if m = 1 then b0 else basis k)):real^3)) dot
                         (metric_local atlas c (g t0) w **
                          (matrix_inv(metric_local atlas c (g t0) w) **
                           ((lambda k. lpcurv (metric_local atlas c (g t0)) w
                                         (\m. if m = 1 then b0 else basis k)):real^3))))) %
                (matrix_inv(metric_local atlas c (g t0) w) **
                 ((lambda k. lpcurv (metric_local atlas c (g t0)) w
                               (\m. if m = 1 then b0 else basis k)):real^3)))
           y = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                riemannian_metric atlas ((g:real->A->real^3^3) t0)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `V = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)` THEN
  SUBGOAL_THEN `metric_field V (G:real^3->real^3^3)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["V"; "G"] THEN
    UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^3^3) t0)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* rank one and PSD at every point of V *)
  SUBGOAL_THEN
   `!w. w IN V
        ==> (!u v. lpcurv (G:real^3->real^3^3) w (\m. u) * lpcurv G w (\m. v) =
                   lpcurv G w (\m. if m = 1 then u else v) pow 2) /\
            (!v. &0 <= lpcurv G w (\m. v))`
  (LABEL_TAC "rk") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) w IN FST c /\ SND c (chart_inv c w) = w`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) w IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `t0:real`;
                   `chart_inv (c:(A->bool)#(A->real^3)) w`; `t0 - a:real`]
           RFA_RANK1_POINT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_REFL]; ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N:real^3->bool) SUBSET V /\ metric_field N (G:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `Yf = \w. matrix_inv((G:real^3->real^3^3) w) **
             ((lambda k. lpcurv G w (\m. if m = 1 then b0 else basis k)):real^3)` THEN
  SUBGOAL_THEN `smooth_map_on N (Yf:real^3->real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Yf" THEN MATCH_MP_TAC RFA_PFIELD_SMOOTH THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN N ==> ~((Yf:real^3->real^3) w = vec 0)` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `w:real^3`; `b0:real^3`;
                   `b0:real^3`] RFA_PFIELD_DOT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `(Yf:real^3->real^3) w = vec 0` THEN EXPAND_TAC "Yf" THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_LZERO; COND_ID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&0 = x)`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN V` ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  (* every unit null vector at y gives a barrier with Laplacian 0 *)
  SUBGOAL_THEN
   `!e. e dot ((G:real^3->real^3^3) y ** e) = &1 /\ lpcurv G y (\m. e) = &0
        ==> lcovd G (\w. z) (Yf:real^3->real^3) y dot (G y ** e) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^3` THEN STRIP_TAC THEN
    USE_THEN "rk" (fun th -> MP_TAC(MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN V`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "r1y") (LABEL_TAC "psdy")) THEN
    MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `e:real^3`]
           RFA_RANK1_NULL_FRAME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "r1y" ACCEPT_TAC; USE_THEN "psdy" ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) y IN FST c /\ SND c (chart_inv c y) = y`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) y IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `t0:real`;
                   `chart_inv (c:(A->bool)#(A->real^3)) y`; `S:real^3^3`; `t0 - a:real`]
           RFA_NULL_POINT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        ASM_SIMP_TAC[REAL_LE_REFL];
        ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_TAC THEN
    EXPAND_TAC "Yf" THEN MATCH_MP_TAC RFA_PARALLEL_ORTHO THEN
    MAP_EVERY EXISTS_TAC [`V:real^3->bool`; `N:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`w:real^3`; `u:real^3`; `w':real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN V` ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    USE_THEN "rk" (fun th -> MP_TAC(MP (SPEC `w:real^3` th) (ASSUME `(w:real^3) IN V`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = lcovd (G:real^3->real^3^3) (\w. z) (Yf:real^3->real^3) y` THEN
  SUBGOAL_THEN
   `(X:real^3) = ((X dot ((G:real^3->real^3^3) y ** (Yf:real^3->real^3) y)) /
                  (Yf y dot (G y ** Yf y))) % Yf y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_PARALLEL_YPAR THEN
    MAP_EVERY EXISTS_TAC [`V:real^3->bool`; `b0:real^3`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "rk" (fun th -> MP_TAC(MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN V`))) THEN
      SIMP_TAC[];
      ASM_SIMP_TAC[];
      EXPAND_TAC "Yf" THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`N:real^3->bool`; `G:real^3->real^3^3`; `Yf:real^3->real^3`; `y:real^3`;
                 `z:real^3`;
                 `((X:real^3) dot ((G:real^3->real^3^3) y ** (Yf:real^3->real^3) y)) /
                  (Yf y dot (G y ** Yf y))`] RFA_PARALLEL_NORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN REFL_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "Yf" THEN REWRITE_TAC[]);;

