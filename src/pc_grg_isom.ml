(* ========================================================================= *)
(* pc_grg_isom: Riemannian isometries (mfd_isometry of pc_grg_dist, built on *)
(* mfd_diffeo of pc_mfd_maps): the identity and the inverse are isometries, *)
(* isometries preserve lengths, joinability and distances, and the teeth    *)
(* tests on flat real^N (translations are isometries, the dilation by 2 is  *)
(* not).  Built on pc_grg_dist2 (C^1 curves pushed forward).               *)
(* ========================================================================= *)

needs "src/pc_grg_dist2.ml";;

prioritize_real();;
type_invention_error := true;;

let GRGD_ISOMETRY_FACTS = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f'.
        mfd_isometry (top,atlas) g (top',atlas') g' f f'
        ==> continuous_map (subtopology top (topspace top),top') f /\
            continuous_map (subtopology top' (topspace top'),top) f' /\
            mfd_smooth_map atlas atlas' (topspace top) f /\
            mfd_smooth_map atlas' atlas (topspace top') f' /\
            IMAGE f (topspace top) SUBSET topspace top' /\
            IMAGE f' (topspace top') SUBSET topspace top /\
            (!x. x IN topspace top ==> f'(f x) = x) /\
            (!y. y IN topspace top' ==> f(f' y) = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_isometry] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  ASM_REWRITE_TAC[]);;

let GRGD_ISOMETRY_C1 = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f'
    (gamma:real->A) a b.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        mfd_c1_curve (top,atlas) gamma a b /\ a < b
        ==> mfd_c1_curve (top',atlas') (f o gamma) a b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  MATCH_MP_TAC GRGD_C1_CURVE_PUSH THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `topspace top:A->bool`] THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
  ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]);;

let GRGD_ISOMETRY_SPEED = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f'
    (gamma:real->A) a b t.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        mfd_c1_curve (top,atlas) gamma a b /\ a < b /\ t IN real_interval[a,b]
        ==> mfd_speed atlas' g' (f o gamma) a b t = mfd_speed atlas g gamma a b t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_isometry]) THEN
  DISCH_THEN(LABEL_TAC "ISO") THEN
  SUBGOAL_THEN
   `mfd_c1_curve (top',atlas':((B->bool)#(B->real^N))->bool)
                 ((f:A->B) o (gamma:real->A)) a b`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_ISOMETRY_C1 THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `g:A->real^N^N`; `g':B->real^N^N`; `f':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B)((gamma:real->A) t) IN topspace top'` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:A->B) (topspace top) SUBSET topspace top'` THEN
    UNDISCH_TAC `(gamma:real->A) t IN topspace top` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?U (phi:A->real^N). (U,phi) IN (atlas:((A->bool)#(A->real^N))->bool) /\
                        (gamma:real->A) t IN U`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(gamma:real->A) t`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)`,
             `k:(A->bool)#(A->real^N)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?V (psi:B->real^N). (V,psi) IN (atlas':((B->bool)#(B->real^N))->bool) /\
                        (f:A->B)((gamma:real->A) t) IN V`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `(f:A->B)((gamma:real->A) t)`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`chart_at (atlas':((B->bool)#(B->real^N))->bool)
                       ((f:A->B)((gamma:real->A) t))`,
             `k:(B->bool)#(B->real^N)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `(f:A->B) o (gamma:real->A)`; `a:real`; `b:real`;
                 `t:real`; `V:B->bool`; `psi:B->real^N`] MFD_SPEED_CHART) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`;
                 `t:real`; `U:A->bool`; `phi:A->real^N`] MFD_SPEED_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `vector_derivative (\s. (psi:B->real^N)((f:A->B)((gamma:real->A)(drop s))))
      (at (lift t) within interval[lift a,lift b]) =
    frechet_derivative (psi o f o chart_inv (U:A->bool,phi:A->real^N))
      (at (phi(gamma t)))
      (vector_derivative (\s. phi(gamma(drop s)))
         (at (lift t) within interval[lift a,lift b]))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `topspace top:A->bool`; `f:A->B`; `gamma:real->A`;
                   `a:real`; `b:real`;
                   `(U:A->bool,phi:A->real^N)`; `(V:B->bool,psi:B->real^N)`;
                   `lift t`] GRGD_PUSH_VD) THEN
    ASM_REWRITE_TAC[FST; SND; LIFT_DROP; GRGD_IN_INTERVAL_LIFT; OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_local atlas (U:A->bool,phi:A->real^N) (g:A->real^N^N)
                 (phi((gamma:real->A) t)) =
    mpullback ((psi:B->real^N) o (f:A->B) o chart_inv (U,phi))
              (metric_local atlas' (V:B->bool,psi) (g':B->real^N^N)) (phi(gamma t))`
  SUBST1_TAC THENL
   [REMOVE_THEN "ISO" (MP_TAC o SPECL
     [`(U:A->bool,phi:A->real^N)`; `(V:B->bool,psi:B->real^N)`]) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative ((psi:B->real^N) o (f:A->B) o
                               chart_inv (U:A->bool,phi:A->real^N))
                              (at (phi((gamma:real->A) t))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `topspace top:A->bool`; `f:A->B`; `(U:A->bool,phi:A->real^N)`;
                   `(V:B->bool,psi:B->real^N)`; `(gamma:real->A) t`]
                  GRGD_CHART_MAP_DIFF) THEN
    ASM_REWRITE_TAC[FST; SND; OPEN_IN_TOPSPACE] THEN SIMP_TAC[has_derivative];
    ALL_TAC] THEN
  REWRITE_TAC[mpullback; o_THM] THEN
  SUBGOAL_THEN `chart_inv (U:A->bool,phi:A->real^N) (phi((gamma:real->A) t)) = gamma t`
  SUBST1_TAC THENL [ASM_MESON_TAC[CHART_INV]; ALL_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC GRGD_QUAD_CONGR THEN ASM_REWRITE_TAC[]);;

let GRGD_ISOMETRY_LENGTH = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f'
    (gamma:real->A) a b.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        mfd_c1_curve (top,atlas) gamma a b /\ a < b
        ==> mfd_length atlas' g' (f o gamma) a b = mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_length] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC GRGD_ISOMETRY_SPEED THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `f':B->A`] THEN
  ASM_REWRITE_TAC[]);;

let MFD_ISOMETRY_ID = prove
 (`!top atlas (g:A->real^N^N).
        smooth_manifold_atlas top atlas
        ==> mfd_isometry (top,atlas) g (top,atlas) g (\x. x) (\x. x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_isometry] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_ID THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`] THEN
  STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS
   `mpullback (chart_trans (U:A->bool,phi:A->real^N) (V,psi))
              (metric_local atlas (V,psi) (g:A->real^N^N)) (phi(x:A))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[IN_INTER];
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; chart_trans; SND]]);;

(* Inverse Jacobians, and the pullback by inverse matrices. *)

let GRGD_JAC_INVERSE = prove
 (`!(h:real^N->real^N) (k:real^N->real^N) s z y.
        open s /\ z IN s /\ (!w. w IN s ==> h(k w) = w) /\ k z = y /\
        k differentiable (at z) /\ h differentiable (at y)
        ==> matrix(frechet_derivative h (at y)) **
            matrix(frechet_derivative k (at z)) = mat 1`,
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FRECHET_DERIVATIVE_WORKS]) THEN
  SUBGOAL_THEN
   `((h:real^N->real^N) o (k:real^N->real^N) has_derivative
     (frechet_derivative h (at y) o frechet_derivative k (at z))) (at z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((h:real^N->real^N) o (k:real^N->real^N) has_derivative (\x. x)) (at z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`\x:real^N. x`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (h:real^N->real^N) (at y) o
    frechet_derivative (k:real^N->real^N) (at z) = (\x. x)`
  ASSUME_TAC THENL [ASM_MESON_TAC[FRECHET_DERIVATIVE_UNIQUE_AT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (h:real^N->real^N) (at y)) /\
    linear(frechet_derivative (k:real^N->real^N) (at z))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM MATRIX_COMPOSE; MATRIX_ID]);;

let GRGD_PULLBACK_INVERSE_MAT = prove
 (`!(A:real^N^N) (B:real^N^N) (G:real^N^N).
        A ** B = mat 1 ==> transp B ** (transp A ** G ** A) ** B = G`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `transp(B:real^N^N) ** (transp(A:real^N^N) ** (G:real^N^N) ** A) ** B =
    transp(A ** B) ** G ** (A ** B)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC];
    ASM_REWRITE_TAC[TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]]);;

let MFD_ISOMETRY_INVERSE = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f'.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f'
        ==> mfd_isometry (top',atlas') g' (top,atlas) g f' f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_isometry]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ISO")) THEN
  REWRITE_TAC[mfd_isometry] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:B->bool`; `psi:B->real^N`; `U:A->bool`; `phi:A->real^N`] THEN
  STRIP_TAC THEN X_GEN_TAC `z:real^N` THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:B` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u:B) IN topspace top'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `(V:B->bool,psi:B->real^N)`] GRGD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
    UNDISCH_TAC `(u:B) IN V` THEN UNDISCH_TAC `(V:B->bool) SUBSET topspace top'` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f':B->A) u IN topspace top /\ (f:A->B)(f' u) = u`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f':B->A) (topspace top') SUBSET topspace top` THEN
      UNDISCH_TAC `(u:B) IN topspace top'` THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `V:B->bool`; `psi:B->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `metric_local atlas (U:A->bool,phi:A->real^N) (g:A->real^N^N)
                 (phi((f':B->A) u)) =
    mpullback ((psi:B->real^N) o (f:A->B) o chart_inv (U,phi))
              (metric_local atlas' (V:B->bool,psi) (g':B->real^N^N)) (phi(f' u))`
  ASSUME_TAC THENL
   [REMOVE_THEN "ISO" (MP_TAC o SPECL
     [`(U:A->bool,phi:A->real^N)`; `(V:B->bool,psi:B->real^N)`]) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `matrix(frechet_derivative ((psi:B->real^N) o (f:A->B) o
                               chart_inv (U:A->bool,phi:A->real^N))
                              (at (phi((f':B->A) u)))) **
    matrix(frechet_derivative (phi o f' o chart_inv (V:B->bool,psi))
                              (at (psi u))) = mat 1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_JAC_INVERSE THEN
    EXISTS_TAC
     `IMAGE (psi:B->real^N) {v | v IN V INTER topspace top' /\ (f':B->A) v IN U}` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                     `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(V:B->bool,psi:B->real^N)`; `(U:A->bool,phi:A->real^N)`;
                     `topspace top':B->bool`; `f':B->A`] MFDM_CHART_DOMAIN_OPEN) THEN
      ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; FST; SND] THEN SIMP_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
      X_GEN_TAC `v:B` THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[o_THM];
      REWRITE_TAC[differentiable] THEN
      EXISTS_TAC
       `frechet_derivative ((phi:A->real^N) o (f':B->A) o
                            chart_inv (V:B->bool,psi:B->real^N)) (at (psi(u:B)))` THEN
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                     `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `topspace top':B->bool`; `f':B->A`;
                     `(V:B->bool,psi:B->real^N)`; `(U:A->bool,phi:A->real^N)`;
                     `u:B`] GRGD_CHART_MAP_DIFF) THEN
      ASM_REWRITE_TAC[FST; SND; OPEN_IN_TOPSPACE];
      REWRITE_TAC[differentiable] THEN
      EXISTS_TAC
       `frechet_derivative ((psi:B->real^N) o (f:A->B) o
                            chart_inv (U:A->bool,phi:A->real^N))
                           (at (phi((f':B->A) u)))` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                     `topspace top:A->bool`; `f:A->B`;
                     `(U:A->bool,phi:A->real^N)`; `(V:B->bool,psi:B->real^N)`;
                     `(f':B->A) u`] GRGD_CHART_MAP_DIFF) THEN
      ASM_REWRITE_TAC[FST; SND; OPEN_IN_TOPSPACE]];
    ALL_TAC] THEN
  REWRITE_TAC[mpullback; o_THM] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[mpullback; o_THM] THEN ASM_SIMP_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC GRGD_PULLBACK_INVERSE_MAT THEN
  ASM_REWRITE_TAC[]);;

(* Isometries preserve joinability and distance. *)

let GRGD_JOINABLE_LENGTHS = prove
 (`!top atlas (g:A->real^N^N) x y.
        mfd_joinable (top,atlas) x y <=>
        ~({mfd_length atlas g gamma (&0) (&1) | gamma |
           mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
           gamma(&0) = x /\ gamma(&1) = y} = {})`,
  REWRITE_TAC[mfd_joinable; GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
  MESON_TAC[]);;

let MFD_DIST_ISOMETRY = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f'.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f'
        ==> !x y. x IN topspace top /\ y IN topspace top
                  ==> (mfd_joinable (top',atlas') (f x) (f y) <=>
                       mfd_joinable (top,atlas) x y) /\
                      mfd_dist (top',atlas') g' (f x) (f y) =
                      mfd_dist (top,atlas) g x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  SUBGOAL_THEN
   `mfd_isometry (top',atlas') (g':B->real^N^N) (top,atlas) (g:A->real^N^N) f' f`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_ISOMETRY_INVERSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{mfd_length atlas' (g':B->real^N^N) beta (&0) (&1) | beta |
     mfd_c1_curve (top',atlas') beta (&0) (&1) /\
     beta(&0) = (f:A->B) x /\ beta(&1) = f y} =
    {mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) | gamma |
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     gamma(&0) = x /\ gamma(&1) = y}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; GRGD_IN_LENGTHS] THEN X_GEN_TAC `L:real` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `beta:real->B` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(f':B->A) o (beta:real->B)` THEN
      SUBGOAL_THEN
       `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool)
                     ((f':B->A) o (beta:real->B)) (&0) (&1)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC GRGD_ISOMETRY_C1 THEN
        MAP_EVERY EXISTS_TAC
         [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
          `g':B->real^N^N`; `g:A->real^N^N`; `f:A->B`] THEN
        ASM_REWRITE_TAC[REAL_LT_01];
        ALL_TAC] THEN
      ASM_SIMP_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC GRGD_ISOMETRY_LENGTH THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `top:A topology`; `f:A->B`] THEN
      ASM_REWRITE_TAC[REAL_LT_01];
      DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(f:A->B) o (gamma:real->A)` THEN ASM_REWRITE_TAC[o_THM] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC GRGD_ISOMETRY_C1 THEN
        MAP_EVERY EXISTS_TAC
         [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
          `g:A->real^N^N`; `g':B->real^N^N`; `f':B->A`] THEN
        ASM_REWRITE_TAC[REAL_LT_01];
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC GRGD_ISOMETRY_LENGTH THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `f':B->A`] THEN
        ASM_REWRITE_TAC[REAL_LT_01]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `g':B->real^N^N`; `(f:A->B) x`; `(f:A->B) y`]
                  GRGD_JOINABLE_LENGTHS) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `y:A`] GRGD_JOINABLE_LENGTHS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REWRITE_TAC[mfd_dist] THEN ASM_REWRITE_TAC[]]);;

(* Teeth: translations of flat real^N are isometries, the dilation by 2 is   *)
(* not.                                                                      *)

let MFD_ISOMETRY_EUCLIDEAN_TRANSLATION = prove
 (`!a:real^N.
        mfd_isometry (euclidean,{((:real^N),\x:real^N. x)}) (\x. mat 1)
                     (euclidean,{((:real^N),\x:real^N. x)}) (\x. mat 1)
                     (\x. x + a) (\x. x - a)`,
  GEN_TAC THEN REWRITE_TAC[mfd_isometry] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM open_set_atlas; MFD_DIFFEO_EUCLIDEAN; TOPSPACE_EUCLIDEAN] THEN
    REWRITE_TAC[diffeomorphism_on; OPEN_UNIV; IN_UNIV] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
      X_GEN_TAC `y:real^N` THEN EXISTS_TAC `(y:real^N) - a` THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
      X_GEN_TAC `y:real^N` THEN EXISTS_TAC `(y:real^N) + a` THEN VECTOR_ARITH_TAC;
      VECTOR_ARITH_TAC;
      VECTOR_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SING] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN REWRITE_TAC[FST; SND] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x:real^N. x) o (\x:real^N. x + (a:real^N)) o
    chart_inv ((:real^N),\x:real^N. x) =
    (\x:real^N. x + a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\x:real^N. x + (a:real^N)) (at y) = (\x. x)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MP_TAC(ISPECL [`\x:real^N. x`; `\h:real^N. h`; `\x:real^N. (a:real^N)`;
                   `\h:real^N. vec 0:real^N`; `at (y:real^N)`] HAS_DERIVATIVE_ADD) THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST; VECTOR_ADD_RID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[mpullback; GRGD_EUCLID_METRIC_LOCAL; OPEN_UNIV; IN_UNIV; MATRIX_ID;
               TRANSP_MAT; MATRIX_MUL_LID]);;

let MFD_NOT_ISOMETRY_EUCLIDEAN_DILATION = prove
 (`~mfd_isometry (euclidean,{((:real^N),\x:real^N. x)}) (\x. mat 1)
                 (euclidean,{((:real^N),\x:real^N. x)}) (\x. mat 1)
                 (\x. &2 % x) (\x. inv(&2) % x)`,
  DISCH_TAC THEN
  MP_TAC(ISPEC `(:real^N)` MFD_EUCLIDEAN_OPEN) THEN
  REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x y:real^N. mfd_dist (euclidean,{((:real^N),\z:real^N. z)}) (\z. mat 1) x y =
                 dist(x,y)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`(:real^N)`; `x:real^N`; `y:real^N`] MFD_DIST_EUCLIDEAN) THEN
    REWRITE_TAC[OPEN_UNIV; CONVEX_UNIV; IN_UNIV; SUBTOPOLOGY_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`euclidean:(real^N)topology`; `{((:real^N),\x:real^N. x)}`;
    `\x:real^N. mat 1:real^N^N`;
    `euclidean:(real^N)topology`; `{((:real^N),\x:real^N. x)}`;
    `\x:real^N. mat 1:real^N^N`;
    `\x:real^N. &2 % x`; `\x:real^N. inv(&2) % x`] MFD_DIST_ISOMETRY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^N`; `basis 1:real^N`]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; DIST_0; NORM_MUL; NORM_BASIS_1] THEN
  REAL_ARITH_TAC);;

