(* ========================================================================= *)
(* Harmonic spheres (part of the harmonic map regularity layer               *)
(* pc_hm_regularity).  The ambient covariant derivative along a planar map,  *)
(* metric compatibility, torsion freeness and the G-orthogonality of the     *)
(* tension to the tangent vectors give the Cauchy-Riemann equations of the   *)
(* Hopf differential; the sphere-to-plane bridge (cap charts of              *)
(* pc_cmr_ball), the decay at infinity and Liouville give CM_HOPF; the       *)
(* epsilon-regularity on large discs gives CM_SPHERE_GAP; a                  *)
(* log-subharmonicity argument gives CM_CRITICAL_ISOLATED.                   *)
(* ========================================================================= *)

needs "src/pc_hm_reg_eps.ml";;
needs "src/pc_cmr_ball.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The ambient covariant derivative along a planar map u, its compatibility  *)
(* with G, torsion freeness, and the G-orthogonality of the tension of a     *)
(* harmonic map to the tangent vectors.                                      *)
(* ========================================================================= *)

let hmr_cd = new_definition
 `hmr_cd (G:real^K->real^K^K) (u:real^2->real^K) (X:real^2->real^K) (j:num) (z:real^2) =
    partial_derivative j X z + christoffel G (u z) (partial_derivative j u z) (X z)`;;

(* The Christoffel identity behind metric compatibility. *)

let HMR_CHRISTOFFEL_COMPAT = prove
 (`!(G:real^K->real^K^K) y a x w.
     metric_field (:real^K) G
     ==> christoffel G y a x dot (G y ** w) + x dot (G y ** christoffel G y a w) =
         x dot (mderiv G y a ** w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `transp((G:real^K->real^K^K) y) = G y` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `christoffel G y a x dot ((G:real^K->real^K^K) y ** w) =
                w dot (G y ** christoffel G y a x)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [DOT_SYM] THEN ASM_SIMP_TAC[HMR_SYM_DOT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^K)`; `G:real^K->real^K^K`; `y:real^K`; `a:real^K`; `x:real^K`;
                 `w:real^K`] LRG_CHRISTOFFEL_DOT) THEN
  MP_TAC(ISPECL [`(:real^K)`; `G:real^K->real^K^K`; `y:real^K`; `a:real^K`; `w:real^K`;
                 `x:real^K`] LRG_CHRISTOFFEL_DOT) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`(:real^K)`; `G:real^K->real^K^K`; `y:real^K`] LRG_MDERIV_SYM) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPECL [`a:real^K`; `w:real^K`; `x:real^K`] th) THEN
                        MP_TAC(SPECL [`x:real^K`; `a:real^K`; `w:real^K`] th) THEN
                        MP_TAC(SPECL [`w:real^K`; `x:real^K`; `a:real^K`] th)) THEN
  REAL_ARITH_TAC);;

(* Metric compatibility along u. *)

let HMR_CD_DOT = prove
 (`!(G:real^K->real^K^K) s (u:real^2->real^K) X Y j z.
     metric_field (:real^K) G /\ open s /\ smooth_map_on s u /\ smooth_map_on s X /\
     smooth_map_on s Y /\ z IN s
     ==> cml_d j (\x. X x dot (G(u x) ** Y x)) z =
         hmr_cd G u X j z dot (G(u z) ** Y z) + X z dot (G(u z) ** hmr_cd G u Y j z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G)`
  ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s (\x. (G:real^K->real^K^K)((u:real^2->real^K) x) ** Y x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMR_MATVEC_SMOOTH THEN EXISTS_TAC `(:real^K)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `X:real^2->real^K`;
                 `\x. (G:real^K->real^K^K)((u:real^2->real^K) x) ** Y x`; `z:real^2`; `j:num`]
    HMR_D_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`(:real^K)`; `s:real^2->bool`; `G:real^K->real^K^K`; `u:real^2->real^K`;
                 `Y:real^2->real^K`; `z:real^2`; `j:num`] HMR_PD_MATVEC) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[hmr_cd; DOT_LADD; MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_RADD] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `(u:real^2->real^K) z`;
                 `partial_derivative j (u:real^2->real^K) z`; `(X:real^2->real^K) z`;
                 `(Y:real^2->real^K) z`] HMR_CHRISTOFFEL_COMPAT) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Torsion freeness. *)

let HMR_CD_TORSION = prove
 (`!(G:real^K->real^K^K) s (u:real^2->real^K) z.
     metric_field (:real^K) G /\ open s /\ smooth_map_on s u /\ z IN s
     ==> hmr_cd G u (partial_derivative 2 u) 1 z = hmr_cd G u (partial_derivative 1 u) 2 z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_cd] THEN BINOP_TAC THENL
   [MATCH_MP_TAC HMR_SCHWARZ_ALL THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MATCH_MP_TAC CHRISTOFFEL_SYM THEN EXISTS_TAC `(:real^K)` THEN
    ASM_REWRITE_TAC[IN_UNIV]]);;

(* The tension of a harmonic map is G-orthogonal to the tangent vectors. *)

let HMR_TENSION_ORTH = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) z i.
     cm_target S G d /\ open s /\ cm_harmonic S G s u /\ z IN s
     ==> (hmr_cd G u (partial_derivative 1 u) 1 z + hmr_cd G u (partial_derivative 2 u) 2 z)
         dot (G(u z) ** partial_derivative i u z) = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN
   `hmr_cd G u (partial_derivative 1 u) 1 z + hmr_cd G u (partial_derivative 2 u) 2 z =
    hmr_vlap (u:real^2->real^K) z +
    vsum(1..2) (\i. christoffel (G:real^K->real^K^K) (u z) (partial_derivative i u z)
                                                         (partial_derivative i u z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[hmr_cd; hmr_vlap; VSUM_2] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`;
                 `hmr_vlap (u:real^2->real^K) z +
                  vsum(1..2) (\i. christoffel (G:real^K->real^K^K) (u z)
                                    (partial_derivative i u z) (partial_derivative i u z))`;
                 `i:num`; `z:real^2`] HMR_TANGENT_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `z:real^2`] HMR_EL_STRONG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_LZERO]);;

(* ========================================================================= *)
(* The Cauchy-Riemann equations of the Hopf differential (|u_1|^2 - |u_2|^2) *)
(* - 2i <u_1, u_2> (lengths and inner product of G) of a planar harmonic     *)
(* map.                                                                      *)
(* ========================================================================= *)

let HMR_GPAIR_SMOOTH = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) a b.
     cm_target S G d /\ open s /\ smooth_map_on s u
     ==> smooth_map_on s
           (\x. lift(partial_derivative a u x dot (G(u x) ** partial_derivative b u x)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMR_METRIC_FIELD) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX] THEN
  MATCH_MP_TAC HMR_MATVEC_SMOOTH THEN EXISTS_TAC `(:real^K)` THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX] THEN
  ASM_MESON_TAC[metric_field]);;

let HMR_HOPF_CR = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) z.
     cm_target S G d /\ open s /\ cm_harmonic S G s u /\ z IN s
     ==> cml_d 1 (\x. partial_derivative 1 u x dot (G(u x) ** partial_derivative 1 u x) -
                      partial_derivative 2 u x dot (G(u x) ** partial_derivative 2 u x)) z =
         -- &2 * cml_d 2 (\x. partial_derivative 1 u x dot
                              (G(u x) ** partial_derivative 2 u x)) z /\
         cml_d 2 (\x. partial_derivative 1 u x dot (G(u x) ** partial_derivative 1 u x) -
                      partial_derivative 2 u x dot (G(u x) ** partial_derivative 2 u x)) z =
         &2 * cml_d 1 (\x. partial_derivative 1 u x dot
                           (G(u x) ** partial_derivative 2 u x)) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMR_METRIC_FIELD) THEN
  SUBGOAL_THEN `!y. transp((G:real^K->real^K^K) y) = G y` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. smooth_map_on s (partial_derivative i (u:real^2->real^K))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`] HMR_GPAIR_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. cml_d j (\x. partial_derivative 1 (u:real^2->real^K) x dot
                      (G(u x) ** partial_derivative 1 u x) -
                     partial_derivative 2 u x dot (G(u x) ** partial_derivative 2 u x)) z =
        cml_d j (\x. partial_derivative 1 u x dot (G(u x) ** partial_derivative 1 u x)) z -
        cml_d j (\x. partial_derivative 2 u x dot (G(u x) ** partial_derivative 2 u x)) z`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`;
      `\x. partial_derivative 1 (u:real^2->real^K) x dot
           ((G:real^K->real^K^K)(u x) ** partial_derivative 1 u x)`;
      `\x. partial_derivative 2 (u:real^2->real^K) x dot
           ((G:real^K->real^K^K)(u x) ** partial_derivative 2 u x)`; `z:real^2`; `j:num`]
      CML_D_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j a b. cml_d j (\x. partial_derivative a (u:real^2->real^K) x dot
                          (G(u x) ** partial_derivative b u x)) z =
            hmr_cd G u (partial_derivative a u) j z dot (G(u z) ** partial_derivative b u z) +
            partial_derivative a u z dot (G(u z) ** hmr_cd G u (partial_derivative b u) j z)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC HMR_CD_DOT THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `M = (G:real^K->real^K^K)((u:real^2->real^K) z)` THEN
  ABBREV_TAC `X1 = partial_derivative 1 (u:real^2->real^K) z` THEN
  ABBREV_TAC `X2 = partial_derivative 2 (u:real^2->real^K) z` THEN
  ABBREV_TAC `N11 = hmr_cd (G:real^K->real^K^K) u (partial_derivative 1 u) 1 z` THEN
  ABBREV_TAC `N22 = hmr_cd (G:real^K->real^K^K) u (partial_derivative 2 u) 2 z` THEN
  ABBREV_TAC `N21 = hmr_cd (G:real^K->real^K^K) u (partial_derivative 1 u) 2 z` THEN
  SUBGOAL_THEN `hmr_cd (G:real^K->real^K^K) u (partial_derivative 2 u) 1 z = N21`
  SUBST1_TAC THENL
   [EXPAND_TAC "N21" THEN MATCH_MP_TAC HMR_CD_TORSION THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^K. x dot (M ** y) = y dot (M ** x)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [DOT_SYM] THEN
    EXPAND_TAC "M" THEN ASM_SIMP_TAC[HMR_SYM_DOT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `z:real^2`; `1`] HMR_TENSION_ORTH) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `z:real^2`; `2`] HMR_TENSION_ORTH) THEN
  ASM_REWRITE_TAC[DOT_LADD] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC(map (fun (a,b) -> SPECL [a;b] th)
    [`X1:real^K`,`N11:real^K`; `X1:real^K`,`N21:real^K`; `X1:real^K`,`N22:real^K`;
     `X2:real^K`,`N11:real^K`; `X2:real^K`,`N21:real^K`; `X2:real^K`,`N22:real^K`])) THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Maps of the sphere in a cap chart.  The normalisation is smooth; a smooth *)
(* sphere map read in the chart cm_capmap Q is smooth on the plane; a planar *)
(* test map phi with compact support gives the sphere test map hmr_ctest Q   *)
(* phi (phi of the chart, zero at the pole) with smooth radial extension.    *)
(* ========================================================================= *)

let HMR_OPEN_NONZERO3 = prove
 (`open {z:real^3 | ~(z = vec 0)}`,
  REWRITE_TAC[SET_RULE `{x | ~(x = a)} = (:real^3) DELETE a`] THEN
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV]);;

let HMR_NORMALIZE_SMOOTH = prove
 (`smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. inv(norm z) % z)`,
  SUBGOAL_THEN `(\z:real^3. inv(norm z) % z) = (\z. drop(lift(inv(drop(lift(norm z))))) % z)`
  SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
  REWRITE_TAC[HMR_OPEN_NONZERO3; SMOOTH_MAP_ON_ID] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_INV THEN REWRITE_TAC[HMR_OPEN_NONZERO3; LIFT_DROP] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_NORM THEN
    REWRITE_TAC[HMR_OPEN_NONZERO3; SMOOTH_MAP_ON_ID; IN_ELIM_THM] THEN MESON_TAC[];
    REWRITE_TAC[IN_ELIM_THM; NORM_EQ_0]]);;

let HMR_CAPMAP_SMOOTH = prove
 (`!Q:real^3^3. smooth_map_on (:real^2) (cm_capmap Q)`,
  GEN_TAC THEN
  SUBGOAL_THEN `cm_capmap (Q:real^3^3) = (\x. Q ** x) o stereo2_n_inv` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; cm_capmap]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  REWRITE_TAC[OPEN_UNIV; MATRIX_VECTOR_MUL_LINEAR; CML_XN_PROPS]);;

let HMR_ORTH_FACTS = prove
 (`!Q:real^3^3.
     orthogonal_matrix Q
     ==> (!x. transp Q ** (Q ** x) = x) /\ (!x. Q ** (transp Q ** x) = x) /\
         (!x. norm(Q ** x) = norm x) /\ (!x. norm(transp Q ** x) = norm x)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!A:real^3^3. orthogonal_matrix A ==> !x. norm(A ** x) = norm x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `\x:real^3. (A:real^3^3) ** x` ORTHOGONAL_TRANSFORMATION_MATRIX) THEN
    REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; MATRIX_VECTOR_MUL_LINEAR] THEN
    ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ORTHOGONAL_MATRIX_TRANSP] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [orthogonal_matrix]) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]);;

let HMR_CAP_COMPOSE_SMOOTH = prove
 (`!Q (u:real^3->real^K).
     orthogonal_matrix Q /\ smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u)
     ==> smooth_map_on (:real^2) (\y. u(cm_capmap Q y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
  SUBGOAL_THEN `(\y. (u:real^3->real^K)(cm_capmap Q y)) = wan_rext u o cm_capmap Q`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CM_REXT_SPHERE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; HMR_OPEN_NONZERO3; HMR_CAPMAP_SMOOTH] THEN
  REWRITE_TAC[SUBSET; IN_DELETE; IN_SPHERE_0; IN_ELIM_THM] THEN
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* The sphere test map of a planar test map. *)

let hmr_ctest = new_definition
 `hmr_ctest (Q:real^3^3) (phi:real^2->real^K) (y:real^3) =
    if y = Q ** basis 3 then vec 0 else phi(cmr_chart Q y)`;;

let HMR_CTEST_CAP = prove
 (`!Q (phi:real^2->real^K) y.
     orthogonal_matrix Q ==> hmr_ctest Q phi (cm_capmap Q y) = phi y`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
  ASM_REWRITE_TAC[hmr_ctest]);;

let HMR_CTEST_BOUND = prove
 (`!Q (phi:real^2->real^K) B y.
     (!x. norm(phi x) <= B) /\ &0 <= B ==> norm(hmr_ctest Q phi y) <= B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_ctest] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[NORM_0]);;

let HMR_CTEST_SMOOTH = prove
 (`!Q (phi:real^2->real^K) k.
     orthogonal_matrix Q /\ smooth_map_on (:real^2) phi /\ compact k /\
     (!y. ~(y IN k) ==> phi y = vec 0)
     ==> smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (hmr_ctest Q phi))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_ORTH_FACTS) THEN
  SUBGOAL_THEN `(\z:real^3. inv(norm z) % z) continuous_on {z:real^3 | ~(z = vec 0)}`
  ASSUME_TAC THENL [REWRITE_TAC[CMT_NORMALIZE_CONTINUOUS]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. ~(z = vec 0) ==> inv(norm z) % z IN sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[HMR_OPEN_NONZERO3; IN_ELIM_THM] THEN
  X_GEN_TAC `z0:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `inv(norm(z0:real^3)) % z0 = (Q:real^3^3) ** basis 3` THENL
   [(* near the pole the test map vanishes *)
    EXISTS_TAC `{z:real^3 | z IN {z | ~(z = vec 0)} /\
                            inv(norm z) % z IN (:real^3) DIFF IMAGE (cm_capmap Q) k}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_REWRITE_TAC[HMR_OPEN_NONZERO3; GSYM closed] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; HMR_CAPMAP_SMOOTH] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON; HMR_CAPMAP_SMOOTH];
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_IMAGE] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\z:real^3. vec 0:real^K` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
        ASM_REWRITE_TAC[HMR_OPEN_NONZERO3; GSYM closed] THEN
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(:real^2)` THEN
        SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON; HMR_CAPMAP_SMOOTH];
        ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_IMAGE; wan_rext; hmr_ctest] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `~(?x. inv(norm z) % z = cm_capmap Q x /\ (x:real^2) IN k)` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `cmr_chart Q (inv(norm(z:real^3)) % z)` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[IN_DELETE]];
    (* away from the pole the test map is a composition of smooth maps *)
    EXISTS_TAC `{z:real^3 | z IN {z | ~(z = vec 0)} /\
                            inv(norm z) % z IN (:real^3) DELETE ((Q:real^3^3) ** basis 3)}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[HMR_OPEN_NONZERO3; OPEN_DELETE; OPEN_UNIV];
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_DELETE; IN_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z:real^3. (phi:real^2->real^K)(stereo2_n(transp Q ** (inv(norm z) % z)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[HMR_OPEN_NONZERO3; OPEN_DELETE; OPEN_UNIV];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; IN_DELETE; IN_UNIV; wan_rext; hmr_ctest; cmr_chart] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\z:real^3. (phi:real^2->real^K)(stereo2_n(transp Q ** (inv(norm z) % z)))) =
      phi o (stereo2_n o ((\x. transp Q ** x) o (\z. inv(norm z) % z)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    ABBREV_TAC `WA = {z:real^3 | z IN {z | ~(z = vec 0)} /\
                                 inv(norm z) % z IN (:real^3) DELETE ((Q:real^3^3) ** basis 3)}` THEN
    SUBGOAL_THEN `open (WA:real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "WA" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[HMR_OPEN_NONZERO3; OPEN_DELETE; OPEN_UNIV];
      ALL_TAC] THEN
    SUBGOAL_THEN `WA SUBSET {z:real^3 | ~(z = vec 0)}` ASSUME_TAC THENL
     [EXPAND_TAC "WA" THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `{x:real^3 | x$3 < &1}` THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; STEX_STEREO2_N_SMOOTH] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `z:real^3` THEN
      EXPAND_TAC "WA" THEN REWRITE_TAC[IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN STRIP_TAC THEN
      MP_TAC STEX_STEREO2_N_DOMAIN THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `transp (Q:real^3^3) ** inv(norm(z:real^3)) % z`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
          can (find_term (fun t -> t = `sphere(vec 0:real^3,&1)`)) (concl th) &&
          is_forall (concl th) && is_imp(snd(dest_forall(concl th))))) THEN
        ASM_REWRITE_TAC[IN_SPHERE_0];
        DISCH_TAC THEN
        UNDISCH_TAC `~(inv(norm(z:real^3)) % z = (Q:real^3^3) ** basis 3)` THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      ASM_REWRITE_TAC[HMR_NORMALIZE_SMOOTH]]]);;

(* ========================================================================= *)
(* Energy bookkeeping for the bridge.  Continuous maps are absolutely        *)
(* integrable on bounded measurable sets; for smooth planar maps agreeing    *)
(* off a compact set k inside s', the energy of a ball containing s' minus   *)
(* the energy of s' is the same.                                             *)
(* ========================================================================= *)

let HMR_CONT_ABSINT_BOUNDED = prove
 (`!(f:real^N->real^M) s.
     f continuous_on (:real^N) /\ bounded s /\ lebesgue_measurable s
     ==> f absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_TAC `b:real^N`) o
    MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `interval[a:real^N,b]` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let HMR_W12_SMOOTH_BOUNDED = prove
 (`!s (h:real^2->real^N).
     open s /\ bounded s /\ smooth_map_on (:real^2) h ==> wan_w12 s h`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,R + &1)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`; `h:real^2->real^N`; `vec 0:real^2`; `R + &1`]
      HMR_W12_SMOOTH_BALL) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN SIMP_TAC[];
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN ASM_MESON_TAC[REAL_ARITH `x <= R ==> x < R + &1`]]);;

(* The classical energy density of a smooth map. *)

let HMR_GDIR_SMOOTH_BOUNDED = prove
 (`!(G:real^K->real^K^K) s (W:real^2->real^K).
     open s /\ bounded s /\ smooth_map_on (:real^2) W
     ==> wan_gdir s G W =
         sum(1..2) (\i. drop(integral s
                      (\x. lift(partial_derivative i W x dot (G(W x) ** partial_derivative i W x)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `G:real^K->real^K^K`; `W:real^2->real^K`]
    HMC_GDIR_CLASSICAL) THEN
  REWRITE_TAC[DIMINDEX_2] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `smooth_map_on s (W:real^2->real^K)` MP_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MAP_ON_SUBSET; SUBSET_UNIV]; SIMP_TAC[smooth_map_on]];
    MATCH_MP_TAC HMR_W12_SMOOTH_BOUNDED THEN ASM_REWRITE_TAC[]]);;

let HMR_GDIR_SPLIT_LOCAL = prove
 (`!S (G:real^K->real^K^K) d s c R k (W:real^2->real^K) W'.
     cm_target S G d /\ open s /\ s SUBSET ball(c,R) /\ compact k /\ k SUBSET s /\
     smooth_map_on (:real^2) W /\ smooth_map_on (:real^2) W' /\
     (!x. ~(x IN k) ==> W x = W' x)
     ==> wan_gdir (ball(c,R)) G W - wan_gdir s G W =
         wan_gdir (ball(c,R)) G W' - wan_gdir s G W'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bounded (s:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET; BOUNDED_BALL]; ALL_TAC] THEN
  ASM_SIMP_TAC[HMR_GDIR_SMOOTH_BOUNDED; OPEN_BALL; BOUNDED_BALL] THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `vectorize o (G:real^K->real^K^K) continuous_on (:real^K)` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!V:real^2->real^K. smooth_map_on (:real^2) V
        ==> (\x. lift(partial_derivative i V x dot ((G:real^K->real^K^K)(V x) **
                                                    partial_derivative i V x)))
            continuous_on (:real^2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX] THEN
    MATCH_MP_TAC HMR_MATVEC_SMOOTH THEN EXISTS_TAC `(:real^K)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!V:real^2->real^K. smooth_map_on (:real^2) V
        ==> drop(integral (ball(c,R))
                  (\x. lift(partial_derivative i V x dot ((G:real^K->real^K^K)(V x) **
                                                          partial_derivative i V x)))) =
            drop(integral s
                  (\x. lift(partial_derivative i V x dot (G(V x) ** partial_derivative i V x)))) +
            drop(integral (ball(c,R) DIFF s)
                  (\x. lift(partial_derivative i V x dot (G(V x) ** partial_derivative i V x))))`
  (fun th -> ASM_SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DROP_ADD] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `ball(c:real^2,R) = s UNION (ball(c,R) DIFF s)` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [th]) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_UNION THEN
    REWRITE_TAC[SET_RULE `(s:real^2->bool) INTER (t DIFF s) = {}`; NEGLIGIBLE_EMPTY] THEN
    CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC HMR_CONT_ABSINT_BOUNDED THEN ASM_SIMP_TAC[] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; LEBESGUE_MEASURABLE_DIFF; OPEN_BALL] THEN
    ASM_MESON_TAC[BOUNDED_SUBSET; BOUNDED_BALL; SUBSET_DIFF];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> (a + x) - a = (b + y) - b`) THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((x:real^2) IN k)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `partial_derivative i (W:real^2->real^K) x = partial_derivative i W' x`
  (fun th -> ASM_SIMP_TAC[th]) THEN
  MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `(:real^2) DIFF k` THEN
  ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV]);;

(* ========================================================================= *)
(* The sphere-to-plane bridge.  A harmonic sphere read in a cap chart is a   *)
(* smooth harmonic map on the whole plane: a planar test map phi on s gives  *)
(* the sphere test map hmr_ctest Q phi; the energy of the varied sphere map  *)
(* (CMR_SEN_SPLIT) differs from the planar energy on s of the varied planar  *)
(* map by a constant.                                                        *)
(* ========================================================================= *)

let HMR_GCOND = prove
 (`!S (G:real^K->real^K^K) d. cm_target S G d ==> ?Lam. CMR_GCOND G Lam`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  EXISTS_TAC `Lam:real` THEN REWRITE_TAC[CMR_GCOND] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]);;

let HMR_SPH_PLANE_HARMONIC = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) Q.
     cm_target S G d /\ cm_sharmonic S G u /\ orthogonal_matrix Q
     ==> cm_harmonic S G (:real^2) (\y. u(cm_capmap Q y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_sharmonic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `Lam:real` o MATCH_MP HMR_GCOND) THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\y. (u:real^3->real^K)(cm_capmap Q y))`
  ASSUME_TAC THENL [MATCH_MP_TAC HMR_CAP_COMPOSE_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `v = \y. (u:real^3->real^K)(cm_capmap Q y)` THEN
  SUBGOAL_THEN `!y. (v:real^2->real^K) y IN S` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN GEN_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[cm_harmonic] THEN ASM_REWRITE_TAC[IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`phi:real^2->real^K`; `s:real^2->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC) o
    GEN_REWRITE_RULE I [wan_vtest]) THEN
  (* a bound for phi *)
  SUBGOAL_THEN `?B. &0 < B /\ !x. norm((phi:real^2->real^K) x) <= B` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (phi:real^2->real^K) k` COMPACT_IMP_BOUNDED) THEN ANTS_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `B:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN
    ASM_CASES_TAC `(x:real^2) IN k` THEN ASM_SIMP_TAC[NORM_0; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* the radius of a ball containing s *)
  SUBGOAL_THEN `?R. &0 < R /\ (s:real^2->bool) SUBSET ball(vec 0,R)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS] o
      check (fun th -> concl th = `bounded (s:real^2->bool)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `R0:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `R0 + &1` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN ASM_MESON_TAC[REAL_ARITH `x <= R ==> x < R + &1`];
    ALL_TAC] THEN
  (* the sphere test map *)
  ABBREV_TAC `psi = hmr_ctest Q (phi:real^2->real^K)` THEN
  SUBGOAL_THEN `smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (psi:real^3->real^K))`
  ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN MATCH_MP_TAC HMR_CTEST_SMOOTH THEN EXISTS_TAC `k:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (psi:real^3->real^K)(cm_capmap Q y) = phi y` ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN ASM_SIMP_TAC[HMR_CTEST_CAP]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. norm((psi:real^3->real^K) y) <= B` ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN GEN_TAC THEN MATCH_MP_TAC HMR_CTEST_BOUND THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* small variations stay in the tube *)
  ABBREV_TAC `e0 = d / (B + &1)` THEN
  SUBGOAL_THEN `&0 < e0` ASSUME_TAC THENL
   [EXPAND_TAC "e0" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!e p (q:real^K). abs e < e0 /\ p IN S /\ norm q <= B ==> p + e % q IN cm_tube S d`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[cm_tube; IN_ELIM_THM] THEN EXISTS_TAC `p:real^K` THEN
    ASM_REWRITE_TAC[dist; VECTOR_ARITH `(p + e % q) - p:real^K = e % q`; NORM_MUL] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e0 * B` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE; REAL_ABS_POS] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "e0" THEN REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < B ==> &0 < B + &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the planar varied maps are smooth *)
  SUBGOAL_THEN `!e. abs e < e0
                    ==> smooth_map_on (:real^2)
                          (\x. closest_point S ((v:real^2->real^K) x + e % phi x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\x. closest_point S ((v:real^2->real^K) x + e % phi x)) =
                  closest_point S o (\x. v x + e % phi x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN CONJ_TAC THENL
     [GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV]];
    ALL_TAC] THEN
  (* the varied sphere maps are W^{1,2} *)
  SUBGOAL_THEN `!e. abs e < e0
                    ==> wan_s2_w12 (\y. closest_point S ((u:real^3->real^K) y + e % psi y))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[wan_s2_w12] THEN
    SUBGOAL_THEN
     `smooth_map_on {z:real^3 | ~(z = vec 0)}
        (wan_rext (\y. closest_point S ((u:real^3->real^K) y + e % psi y)))`
     (fun th -> MESON_TAC[th; smooth_map_on; CMT_REXT_WD_AE]) THEN
    SUBGOAL_THEN
     `wan_rext (\y. closest_point S ((u:real^3->real^K) y + e % psi y)) =
      closest_point S o (\z. wan_rext u z + e % wan_rext psi z)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; wan_rext]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
    ASM_REWRITE_TAC[HMR_OPEN_NONZERO3; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[wan_rext] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[HMR_OPEN_NONZERO3; ETA_AX] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[HMR_OPEN_NONZERO3; ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (u:real^3->real^K)(cm_capmap Q y) = v y` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN REWRITE_TAC[]; ALL_TAC] THEN
  (* the energy identity *)
  SUBGOAL_THEN
   `!e. abs e < e0
        ==> cm_sen G (\y. closest_point S ((u:real^3->real^K) y + e % psi y)) -
            cm_gen G s (\x. closest_point S ((v:real^2->real^K) x + e % phi x)) =
            cm_sen G (\y. closest_point S (u y + &0 % psi y)) -
            cm_gen G s (\x. closest_point S (v x + &0 % phi x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs(&0) < e0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`;
                   `\y. closest_point S ((u:real^3->real^K) y + e % psi y)`;
                   `Q:real^3^3`; `Lam:real`; `vec 0:real^2`; `R:real`] CMR_SEN_SPLIT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`;
                   `\y. closest_point S ((u:real^3->real^K) y + &0 % psi y)`;
                   `Q:real^3^3`; `Lam:real`; `vec 0:real^2`; `R:real`] CMR_SEN_SPLIT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[cm_gen; ETA_AX] THEN
    SUBGOAL_THEN
     `wan_gdir ((:real^2) DIFF cball(vec 0,R)) G
        (\x. closest_point S ((v:real^2->real^K) x + e % phi x)) =
      wan_gdir ((:real^2) DIFF cball(vec 0,R)) G (\x. closest_point S (v x + &0 % phi x))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CMT_WAN_GDIR_EQ THEN X_GEN_TAC `x:real^2` THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; IN_CBALL_0; REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(phi:real^2->real^K) x = vec 0`
       (fun th -> REWRITE_TAC[th; VECTOR_MUL_RZERO]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN ball(vec 0,R)` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                   `vec 0:real^2`; `R:real`; `k:real^2->bool`;
                   `\x. closest_point S ((v:real^2->real^K) x + e % phi x)`;
                   `\x. closest_point S ((v:real^2->real^K) x + &0 % phi x)`]
      HMR_GDIR_SPLIT_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(phi:real^2->real^K) x = vec 0` (fun th -> REWRITE_TAC[th; VECTOR_MUL_RZERO]) THEN
      ASM_SIMP_TAC[];
      DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a - b = c - d ==> (a / &2 + w / &2) - b / &2 =
                                                (c / &2 + w / &2) - d / &2`) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* the derivative *)
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\e. cm_sen G (\y. closest_point S ((u:real^3->real^K) y + e % psi y)) -
                  (cm_sen G (\y. closest_point S (u y + &0 % psi y)) -
                   cm_gen G s (\x. closest_point S ((v:real^2->real^K) x + &0 % phi x)))` THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `e:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cm_sen")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cm_gen")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 = &0 - &0` (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* A harmonic sphere is conformal in every cap chart.  The Hopf components A *)
(* = |u_1|^2 - |u_2|^2 and B = -2 <u_1,u_2> (G-lengths) of the planar map    *)
(* satisfy the Cauchy-Riemann equations on the plane and decay like |z|^-4   *)
(* (the map is a smooth map composed with the inversion), so they vanish by  *)
(* Liouville (CML_LIOUVILLE_ZERO).                                           *)
(* ========================================================================= *)

let HMR_SPHERE_COMPOSE_SMOOTH = prove
 (`!Q (u:real^3->real^K) (X:real^2->real^3).
     orthogonal_matrix Q /\ smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
     smooth_map_on (:real^2) X /\ (!y. norm(X y) = &1)
     ==> smooth_map_on (:real^2) (\y. u(Q ** X y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_ORTH_FACTS) THEN
  SUBGOAL_THEN `(\y. (u:real^3->real^K)((Q:real^3^3) ** (X:real^2->real^3) y)) =
                wan_rext u o ((\x. Q ** x) o X)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CM_REXT_SPHERE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; HMR_OPEN_NONZERO3] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM; o_THM] THEN
    GEN_TAC THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[OPEN_UNIV; MATRIX_VECTOR_MUL_LINEAR]]);;

(* Partial derivatives through the inversion. *)

let HMR_INV_PD = prove
 (`!(w:real^2->real^N) z a.
     smooth_map_on (:real^2) w /\ ~(z = vec 0)
     ==> partial_derivative a (\y. w(cml_inv y)) z =
         frechet_derivative w (at (cml_inv z)) (bel_dT z (basis a))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_FRECHET) THEN
  MP_TAC(ISPECL [`cml_inv`; `w:real^2->real^N`; `z:real^2`; `basis a:real^2`]
    LRG_FRECHET_DERIVATIVE_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let HMR_INV_PD_BOUND = prove
 (`!(w:real^2->real^N) z a.
     smooth_map_on (:real^2) w /\ ~(z = vec 0) /\ 1 <= a /\ a <= 2
     ==> norm(partial_derivative a (\y. w(cml_inv y)) z) <=
         (norm(partial_derivative 1 w (cml_inv z)) + norm(partial_derivative 2 w (cml_inv z))) *
         inv(norm z pow 2)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HMR_INV_PD] THEN
  MP_TAC(ISPECL [`w:real^2->real^N`; `cml_inv z`; `bel_dT z (basis a)`] CML_FRECHET_BASIS2) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`z:real^2`; `a:num`; `1`] CML_DT_COMPONENT) THEN
  MP_TAC(ISPECL [`z:real^2`; `a:num`; `2`] CML_DT_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((bel_dT z (basis a))$1) * norm(partial_derivative 1 (w:real^2->real^N) (cml_inv z)) +
              abs((bel_dT z (basis a))$2) * norm(partial_derivative 2 w (cml_inv z))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH `norm(a:real^N) <= x /\ norm(b:real^N) <= y ==> norm(a + b) <= x + y`) THEN
    REWRITE_TAC[NORM_MUL; REAL_LE_REFL];
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[NORM_POS_LE]]);;

(* A polarisation bound for the G-inner product. *)

let HMR_GPAIR_BOUND = prove
 (`!(M:real^K^K) Lam x y.
     transp M = M /\ (!v. &0 <= v dot (M ** v) /\ v dot (M ** v) <= Lam * norm v pow 2)
     ==> abs(x dot (M ** y)) <= Lam * (norm x pow 2 + norm y pow 2) / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `y dot ((M:real^K^K) ** x) = x dot (M ** y)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [DOT_SYM] THEN ASM_SIMP_TAC[HMR_SYM_DOT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(x + y) dot ((M:real^K^K) ** (x + y)) =
    x dot (M ** x) + &2 * (x dot (M ** y)) + y dot (M ** y) /\
    (x - y) dot ((M:real^K^K) ** (x - y)) =
    x dot (M ** x) - &2 * (x dot (M ** y)) + y dot (M ** y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_LADD;
                DOT_LSUB; DOT_RADD; DOT_RSUB] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Lam` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `basis 1:real^K` o check (is_forall o concl)) THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(x + y:real^K) pow 2 + norm(x - y) pow 2 = &2 * norm x pow 2 + &2 * norm y pow 2`
  ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_LSUB; DOT_RADD; DOT_RSUB] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Lam * norm(x + y:real^K) pow 2 + Lam * norm(x - y) pow 2 =
                &2 * Lam * norm x pow 2 + &2 * Lam * norm y pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Lam * norm(x + y:real^K) pow 2 /\ &0 <= Lam * norm(x - y:real^K) pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  FIRST_ASSUM((fun th -> MP_TAC(SPEC `x + y:real^K` th) THEN MP_TAC(SPEC `x - y:real^K` th)) o
    check (is_forall o concl)) THEN
  ASM_REAL_ARITH_TAC);;

(* The planar conformality of harmonic spheres. *)

let HMR_DECAY_ALG = prove
 (`!Lam D0 n1 n2 r.
     &0 <= Lam /\ &0 <= n1 /\ &0 <= n2 /\ &0 < r /\
     n1 <= D0 * inv(r pow 2) /\ n2 <= D0 * inv(r pow 2)
     ==> Lam * (n1 pow 2 + n2 pow 2) <= (&2 * Lam * D0 pow 2) / r pow 4`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(D0 * inv(r pow 2)) pow 2 = D0 pow 2 / r pow 4` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `n1 pow 2 <= D0 pow 2 / r pow 4 /\ n2 pow 2 <= D0 pow 2 / r pow 4`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM) THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * Lam * D0 pow 2) / r pow 4 = Lam * (D0 pow 2 / r pow 4 + D0 pow 2 / r pow 4)`
  SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_ADD2]);;

let HMR_PLANE_CONFORMAL = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) Q v.
     cm_target S G d /\ cm_sharmonic S G u /\ orthogonal_matrix Q /\
     v = (\y. u(cm_capmap Q y))
     ==> !z. partial_derivative 1 v z dot (G(v z) ** partial_derivative 1 v z) =
             partial_derivative 2 v z dot (G(v z) ** partial_derivative 2 v z) /\
             partial_derivative 1 v z dot (G(v z) ** partial_derivative 2 v z) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^3->real^K`;
                 `Q:real^3^3`] HMR_SPH_PLANE_HARMONIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_sharmonic]) THEN
  (* the picture in the opposite chart through the inversion *)
  ABBREV_TAC `w = \y. (u:real^3->real^K)(Q ** stereo2_s_inv y)` THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (w:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC HMR_SPHERE_COMPOSE_SMOOTH THEN
    ASM_REWRITE_TAC[CML_XS_PROPS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. ~(z = vec 0) ==> (v:real^2->real^K) z = w(cml_inv z)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ASSUME `v = (\y. (u:real^3->real^K)(cm_capmap Q y))`; cm_capmap] THEN
    SIMP_TAC[CML_XN_XS];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
                                             lhs(concl th) = `v:real^2->real^K`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  SUBGOAL_THEN `!p. transp((G:real^K->real^K^K) p) = G p` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_target]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `(:real^2)`;
                 `v:real^2->real^K`] HMR_GPAIR_SMOOTH) THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `(:real^2)`;
                 `v:real^2->real^K`] HMR_HOPF_CR) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\x. partial_derivative 1 (v:real^2->real^K) x dot
         ((G:real^K->real^K^K)(v x) ** partial_derivative 1 v x) -
         partial_derivative 2 v x dot (G(v x) ** partial_derivative 2 v x)`;
    `\x. --(&2) * (partial_derivative 1 (v:real^2->real^K) x dot
                   ((G:real^K->real^K^K)(v x) ** partial_derivative 2 v x))`]
    CML_LIOUVILLE_ZERO) THEN
  REWRITE_TAC[] THEN
  (* the decay at infinity *)
  SUBGOAL_THEN
   `?C. !z. &1 <= norm z
            ==> abs(partial_derivative 1 (v:real^2->real^K) z dot
                    ((G:real^K->real^K^K)(v z) ** partial_derivative 1 v z) -
                    partial_derivative 2 v z dot (G(v z) ** partial_derivative 2 v z))
                <= C / norm z pow 4 /\
                abs(--(&2) * (partial_derivative 1 v z dot (G(v z) ** partial_derivative 2 v z)))
                <= C / norm z pow 4`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`;
                   `\y. lift(norm(partial_derivative 1 (w:real^2->real^K) y) +
                             norm(partial_derivative 2 w y))`] HMC_CONT_BOUND) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL; LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV; ETA_AX] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[NORM_LIFT] THEN
    DISCH_THEN(X_CHOOSE_THEN `D0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `&2 * Lam * D0 pow 2` THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(z = vec 0:real^2)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(z:real^2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `!a. 1 <= a /\ a <= 2
          ==> norm(partial_derivative a (v:real^2->real^K) z) <= D0 * inv(norm z pow 2)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `partial_derivative a (v:real^2->real^K) z =
                    partial_derivative a (\y. w(cml_inv y)) z` SUBST1_TAC THENL
       [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `(:real^2) DELETE vec 0` THEN
        SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(norm(partial_derivative 1 (w:real^2->real^K) (cml_inv z)) +
                   norm(partial_derivative 2 w (cml_inv z))) * inv(norm(z:real^2) pow 2)` THEN
      ASM_SIMP_TAC[HMR_INV_PD_BOUND] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; NORM_POS_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `abs x <= d ==> x <= d`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_CBALL_0] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_NORM) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) o
      check (fun th -> can (find_term (fun t -> t = `D0:real`)) (concl th) &&
                       is_forall (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT DISCH_TAC THEN
    ABBREV_TAC `x1 = partial_derivative 1 (v:real^2->real^K) z` THEN
    ABBREV_TAC `x2 = partial_derivative 2 (v:real^2->real^K) z` THEN
    ABBREV_TAC `M = (G:real^K->real^K^K)((v:real^2->real^K) z)` THEN
    SUBGOAL_THEN `Lam * (norm(x1:real^K) pow 2 + norm(x2:real^K) pow 2) <=
                  (&2 * Lam * D0 pow 2) / norm(z:real^2) pow 4` ASSUME_TAC THENL
     [MATCH_MP_TAC HMR_DECAY_ALG THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^K`; `basis 1:real^K`] o check (fun th ->
        can (find_term (fun t -> t = `Lam:real`)) (concl th) && is_forall (concl th))) THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`M:real^K^K`; `Lam:real`; `x1:real^K`; `x2:real^K`] HMR_GPAIR_BOUND) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "M" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(v:real^2->real^K) z`; `x1:real^K`] (ASSUME
      `!z xi. &0 <= xi dot ((G:real^K->real^K^K) z ** xi) /\
              xi dot (G z ** xi) <= Lam * norm xi pow 2`)) THEN
    MP_TAC(ISPECL [`(v:real^2->real^K) z`; `x2:real^K`] (ASSUME
      `!z xi. &0 <= xi dot ((G:real^K->real^K^K) z ** xi) /\
              xi dot (G z ** xi) <= Lam * norm xi pow 2`)) THEN
    REWRITE_TAC[ASSUME `(G:real^K->real^K^K)((v:real^2->real^K) z) = M`] THEN
    REPEAT DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `C:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CML_SM_SUB THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC CML_SM_CMUL THEN ASM_REWRITE_TAC[OPEN_UNIV];
      X_GEN_TAC `z:real^2` THEN
      MP_TAC(ISPECL [`(:real^2)`; `--(&2)`;
                     `\x. partial_derivative 1 (v:real^2->real^K) x dot
                          ((G:real^K->real^K^K)(v x) ** partial_derivative 2 v x)`;
                     `z:real^2`] CML_D_CMUL) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cml_d")) (concl th) &&
        is_forall (concl th) &&
        not (can (find_term (fun t -> t = `--(&2):real`)) (snd(strip_forall(concl th))) &&
             can (find_term (fun t -> is_const t && fst(dest_const t) = "lift")) (concl th)))) THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[REAL_ARITH `--(&2) * x = &0 <=> x = &0`; REAL_SUB_0]]);;

(* ========================================================================= *)
(* CM_HOPF.  Every point y of the sphere is a regular point of some cap      *)
(* chart; the differential of the chart is conformal with orthonormal frame  *)
(* cml_frame, so the planar conformality (HMR_PLANE_CONFORMAL) transfers to  *)
(* the tangent plane of y.                                                   *)
(* ========================================================================= *)

let HMR_PLANE_EXPAND = prove
 (`!(Fr:real^3^3) x. Fr ** transp Fr = mat 1 /\ x dot Fr$1 = &0
     ==> x = (x dot Fr$2) % Fr$2 + (x dot Fr$3) % Fr$3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `transp Fr ** (Fr:real^3^3) = mat 1` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_MATRIX; ORTHOGONAL_MATRIX_ALT]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MATRIX_VECTOR_MUL_LID] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[MATRIX_VECTOR_COLUMN] THEN
  REWRITE_TAC[TRANSP_TRANSP; DIMINDEX_3; VSUM_3] THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
  MESON_TAC[DOT_SYM]);;

let HMR_CONF_LINALG = prove
 (`!(Fr:real^3^3) (Q:real^3^3) (J:real^3^K) (M:real^K^K) v w.
     Fr ** transp Fr = mat 1 /\ orthogonal_matrix Q /\ transp M = M /\
     (J ** (Q ** Fr$2)) dot (M ** (J ** (Q ** Fr$2))) =
     (J ** (Q ** Fr$3)) dot (M ** (J ** (Q ** Fr$3))) /\
     (J ** (Q ** Fr$2)) dot (M ** (J ** (Q ** Fr$3))) = &0 /\
     v dot (Q ** Fr$1) = &0 /\ w dot (Q ** Fr$1) = &0
     ==> (J ** v) dot (M ** (J ** v)) =
         (v dot v) * ((J ** (Q ** Fr$2)) dot (M ** (J ** (Q ** Fr$2)))) /\
         (J ** v) dot (M ** (J ** w)) =
         (v dot w) * ((J ** (Q ** Fr$2)) dot (M ** (J ** (Q ** Fr$2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_ORTH_FACTS) THEN
  SUBGOAL_THEN
   `!x:real^3. x dot (Q ** Fr$1) = &0
               ==> x = ((transp Q ** x) dot (Fr:real^3^3)$2) % (Q ** Fr$2) +
                       ((transp Q ** x) dot Fr$3) % (Q ** Fr$3)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`Fr:real^3^3`; `transp (Q:real^3^3) ** (x:real^3)`] HMR_PLANE_EXPAND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\y:real^3. (Q:real^3^3) ** y`) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((Q:real^3^3) ** (Fr:real^3^3)$2) dot (Q ** Fr$2) = &1 /\ (Q ** Fr$3) dot (Q ** Fr$3) = &1 /\
    (Q ** Fr$2) dot (Q ** Fr$3) = &0 /\ (Q ** Fr$3) dot (Q ** Fr$2) = &0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!x y:real^3. ((Q:real^3^3) ** x) dot (Q ** y) = x dot y` (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Fr:real^3^3`] (INST_TYPE [`:3`,`:N`] CML_MMT_ENTRY)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MP_TAC(SPECL [`2`; `2`] th) THEN MP_TAC(SPECL [`3`; `3`] th) THEN
                         MP_TAC(SPECL [`2`; `3`] th) THEN MP_TAC(SPECL [`3`; `2`] th)) THEN
    SIMP_TAC[MAT_COMPONENT; DIMINDEX_3; ARITH] THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^K. x dot (M ** y) = y dot (M ** x)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [DOT_SYM] THEN ASM_SIMP_TAC[HMR_SYM_DOT];
    ALL_TAC] THEN
  ABBREV_TAC `p2 = (Q:real^3^3) ** (Fr:real^3^3)$2` THEN
  ABBREV_TAC `p3 = (Q:real^3^3) ** (Fr:real^3^3)$3` THEN
  FIRST_X_ASSUM((fun th -> ONCE_REWRITE_TAC[MATCH_MP th (ASSUME `v dot ((Q:real^3^3) ** (Fr:real^3^3)$1) = &0`)] THEN
                           ONCE_REWRITE_TAC[MATCH_MP th (ASSUME `w dot ((Q:real^3^3) ** (Fr:real^3^3)$1) = &0`)]) o
    check (fun th -> can (find_term (fun t -> t = `transp (Q:real^3^3)`)) (concl th))) THEN
  ABBREV_TAC `c2 = (transp (Q:real^3^3) ** (v:real^3)) dot (Fr:real^3^3)$2` THEN
  ABBREV_TAC `c3 = (transp (Q:real^3^3) ** (v:real^3)) dot (Fr:real^3^3)$3` THEN
  ABBREV_TAC `d2 = (transp (Q:real^3^3) ** (w:real^3)) dot (Fr:real^3^3)$2` THEN
  ABBREV_TAC `d3 = (transp (Q:real^3^3) ** (w:real^3)) dot (Fr:real^3^3)$3` THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_LADD; DOT_RADD;
              DOT_LMUL; DOT_RMUL] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPECL [`(J:real^3^K) ** p3`; `(J:real^3^K) ** p2`] th)) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The partial derivatives of a sphere map in a cap chart. *)

let HMR_CAP_PD = prove
 (`!Q (u:real^3->real^K) z a.
     orthogonal_matrix Q /\ smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext u)
     ==> partial_derivative a (\z. u(cm_capmap Q z)) z =
         jacobian (wan_rext u) (at (cm_capmap Q z)) ** (Q ** bel_dP z (basis a))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
  SUBGOAL_THEN `(\z. (u:real^3->real^K)(cm_capmap Q z)) = (\z. wan_rext u (cm_capmap Q z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CM_REXT_SPHERE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(cm_capmap Q z = vec 0:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
      can (find_term (fun t -> t = `sphere(vec 0:real^3,&1)`)) (concl th) &&
      is_forall (concl th) && not(is_imp(snd(dest_forall(concl th)))))) THEN
    SIMP_TAC[IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((cm_capmap Q) has_derivative (\h. (Q:real^3^3) ** bel_dP z h)) (at z)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `cm_capmap (Q:real^3^3) = (\x. Q ** x) o stereo2_n_inv` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; cm_capmap]; ALL_TAC] THEN
    SUBGOAL_THEN `(\h. (Q:real^3^3) ** bel_dP z h) = (\x. Q ** x) o bel_dP z` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[BEL_P_HAS_DERIVATIVE] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_rext (u:real^3->real^K) differentiable at (cm_capmap Q z)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[HMR_OPEN_NONZERO3; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[partial_derivative] THEN
  MP_TAC(ISPECL [`cm_capmap Q`; `wan_rext (u:real^3->real^K)`; `z:real^2`; `basis a:real^2`]
    LRG_FRECHET_DERIVATIVE_CHAIN) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[differentiable]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "bel_dP")) (concl th))) THEN
  REWRITE_TAC[jacobian] THEN ASM_SIMP_TAC[MATRIX_WORKS; LINEAR_FRECHET_DERIVATIVE]);;

(* CM_HOPF. *)

let HMR_POLE_AVOID = prove
 (`!y:real^3. ?Q:real^3^3. orthogonal_matrix Q /\ ~(y = Q ** basis 3)`,
  GEN_TAC THEN ASM_CASES_TAC `y:real^3 = basis 3` THENL
   [EXISTS_TAC `--(mat 1):real^3^3` THEN
    REWRITE_TAC[orthogonal_matrix; TRANSP_MATRIX_NEG; TRANSP_MAT; MATRIX_MUL_LNEG;
                MATRIX_MUL_RNEG; MATRIX_NEG_NEG; MATRIX_MUL_LID] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG; MATRIX_VECTOR_MUL_LID] THEN
    REWRITE_TAC[VECTOR_ARITH `(x:real^3) = --x <=> x = vec 0`] THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH];
    EXISTS_TAC `mat 1:real^3^3` THEN ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID; MATRIX_VECTOR_MUL_LID]]);;

let CM_HOPF = prove
 (`!kk:K->bool. CM_HOPF_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CM_HOPF_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:real^3->real^K`; `y:real^3`; `v:real^3`; `w:real^3`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_sharmonic]) THEN
  SUBGOAL_THEN `transp((G:real^K->real^K^K)((u:real^3->real^K) y)) = G(u y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_target]; ALL_TAC] THEN
  X_CHOOSE_THEN `Q:real^3^3` STRIP_ASSUME_TAC (SPEC `y:real^3` HMR_POLE_AVOID) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
  ABBREV_TAC `z0 = cmr_chart Q (y:real^3)` THEN
  SUBGOAL_THEN `cm_capmap Q z0 = (y:real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^3->real^K`;
                 `Q:real^3^3`; `\z. (u:real^3->real^K)(cm_capmap Q z)`] HMR_PLANE_CONFORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z0:real^2`) THEN
  ASM_SIMP_TAC[HMR_CAP_PD] THEN STRIP_TAC THEN
  ABBREV_TAC `J = jacobian (wan_rext (u:real^3->real^K)) (at y)` THEN
  ABBREV_TAC `M = (G:real^K->real^K^K)((u:real^3->real^K) y)` THEN
  SUBGOAL_THEN
   `!v' w'. v' dot y = &0 /\ w' dot y = &0
            ==> ((J:real^3^K) ** v') dot ((M:real^K^K) ** (J ** v')) =
                (v' dot v') * ((J ** ((Q:real^3^3) ** inv(sqrt(cml_rho z0)) % bel_dP z0 (basis 1)))
                               dot (M ** (J ** (Q ** inv(sqrt(cml_rho z0)) % bel_dP z0 (basis 1))))) /\
                (J ** v') dot (M ** (J ** w')) =
                (v' dot w') * ((J ** (Q ** inv(sqrt(cml_rho z0)) % bel_dP z0 (basis 1)))
                               dot (M ** (J ** (Q ** inv(sqrt(cml_rho z0)) % bel_dP z0 (basis 1)))))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`cml_frame z0`; `Q:real^3^3`; `J:real^3^K`; `M:real^K^K`; `v':real^3`;
                   `w':real^3`] HMR_CONF_LINALG) THEN
    REWRITE_TAC[cml_frame; VECTOR_3; CML_FRAME_ORTH] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM cm_capmap] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`v:real^3`; `w:real^3`] th) THEN
                          MP_TAC(SPECL [`w:real^3`; `v:real^3`] th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  ASM_REWRITE_TAC[DOT_SQUARE_NORM]);;

(* ========================================================================= *)
(* CM_SPHERE_GAP.  The planar energy of a cap chart reading on any open set  *)
(* is at most twice the sphere energy; if the sphere energy is below half    *)
(* the epsilon of HMR_EPS_E, the first derivatives of the chart readings     *)
(* vanish (large balls), so the map is constant, which a harmonic sphere is  *)
(* not.                                                                      *)
(* ========================================================================= *)

let HMR_CAP_ENERGY_LE = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K) Q D.
     cm_target S G d /\ wan_s2_w12 u /\ orthogonal_matrix Q /\ open D
     ==> wan_gdir D G (\y. u(cm_capmap Q y)) <= &2 * cm_sen G u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `Lam:real` o MATCH_MP HMR_GCOND) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [CMR_GCOND]) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Q:real^3^3`; `Lam:real`; `D:real^2->bool`]
    CMR_CAP_EN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o
    MATCH_MP (REAL_ARITH `x = y / &2 ==> y = &2 * x`)) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_DENS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  REWRITE_TAC[cmr_sen_on; real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `cmr_cone (sphere(vec 0:real^3,&1)) = wan_shell` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; cmr_cone; IN_ELIM_THM; IN_SPHERE_0; wan_shell] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[cmr_cone; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`;
                   `cmr_cone (IMAGE (cm_capmap Q) D)`] CMR_DENS_FACTS) THEN
    ASM_SIMP_TAC[CMR_CAPMAP_CONE] THEN ANTS_TAC THENL
     [REWRITE_TAC[cmr_cone; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]; SIMP_TAC[]];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`; `wan_shell`]
      CMR_DENS_FACTS) THEN
    ASM_SIMP_TAC[SUBSET_REFL; LEBESGUE_MEASURABLE_OPEN; CMT_SHELL_OPEN];
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`; `wan_shell`]
      CMR_DENS_FACTS) THEN
    ASM_SIMP_TAC[SUBSET_REFL; LEBESGUE_MEASURABLE_OPEN; CMT_SHELL_OPEN]]);;

let HMR_SHARMONIC_W12 = prove
 (`!S (G:real^K->real^K^K) u. cm_sharmonic S G u ==> wan_s2_w12 u`,
  REWRITE_TAC[cm_sharmonic; wan_s2_w12] THEN MESON_TAC[CMT_REXT_WD_AE; smooth_map_on]);;

let HMR_PLANE_CONST = prove
 (`!(v:real^2->real^K).
     smooth_map_on (:real^2) v /\
     (!z i. 1 <= i /\ i <= 2 ==> partial_derivative i v z = vec 0)
     ==> !z. v z = v (vec 0)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^2->real^K`; `(:real^2)`; `vec 0:real^2`; `(v:real^2->real^K)(vec 0)`]
    HAS_DERIVATIVE_ZERO_UNIQUE) THEN
  REWRITE_TAC[CONVEX_UNIV; IN_UNIV; WITHIN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:real^2` THEN
  SUBGOAL_THEN `(v:real^2->real^K) differentiable at x` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (v:real^2->real^K) (at x) = (\h. vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    ASM_SIMP_TAC[CML_FRECHET_BASIS2; ARITH; VECTOR_MUL_RZERO; VECTOR_ADD_LID];
    ALL_TAC] THEN
  ASM_MESON_TAC[FRECHET_DERIVATIVE_WORKS]);;

let HMR_SPHERE_CONST_CHARTS = prove
 (`!u:real^3->real^K.
     (!Q. orthogonal_matrix Q ==> !z. u(cm_capmap Q z) = u(cm_capmap Q (vec 0)))
     ==> ?c. !y. y IN sphere(vec 0,&1) ==> u y = c`,
  GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `(u:real^3->real^K)(cm_capmap (mat 1:real^3^3) (vec 0))` THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `orthogonal_matrix(--(mat 1):real^3^3)` ASSUME_TAC THENL
   [REWRITE_TAC[orthogonal_matrix; TRANSP_MATRIX_NEG; TRANSP_MAT; MATRIX_MUL_LNEG;
                MATRIX_MUL_RNEG; MATRIX_NEG_NEG; MATRIX_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Q x. orthogonal_matrix Q /\ x IN sphere(vec 0,&1) /\ ~(x = Q ** basis 3)
          ==> (u:real^3->real^K) x = u(cm_capmap Q (vec 0))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cmr_chart")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Q:real^3^3` o check (fun th ->
      can (find_term (fun t -> t = `vec 0:real^2`)) (concl th) && is_forall (concl th))) THEN
    DISCH_THEN(fun th -> ACCEPT_TAC(SPEC `cmr_chart Q (x:real^3)`
                                     (MP th (ASSUME `orthogonal_matrix(Q:real^3^3)`))));
    ALL_TAC] THEN
  SUBGOAL_THEN `(basis 1:real^3) IN sphere(vec 0,&1) /\ ~(basis 1 = (mat 1:real^3^3) ** basis 3) /\
                ~(basis 1 = (--(mat 1):real^3^3) ** basis 3)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; MATRIX_VECTOR_MUL_LID; MATRIX_VECTOR_MUL_LNEG] THEN
    SIMP_TAC[NORM_BASIS; BASIS_INJ_EQ; DIMINDEX_3; ARITH] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. x$1`) THEN
    SIMP_TAC[VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `y:real^3 = (mat 1:real^3^3) ** basis 3` THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(u:real^3->real^K)(cm_capmap (--(mat 1):real^3^3) (vec 0))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG; MATRIX_VECTOR_MUL_LID] THEN
      REWRITE_TAC[VECTOR_ARITH `(x:real^3) = --x <=> x = vec 0`] THEN
      SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH];
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(u:real^3->real^K)(basis 1)` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID]]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ORTHOGONAL_MATRIX_ID]]);;

let CM_SPHERE_GAP = prove
 (`!kk:K->bool. CM_SPHERE_GAP_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CM_SPHERE_GAP_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMR_EPS_E) THEN
  EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `u:real^3->real^K` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMR_SHARMONIC_W12) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_sharmonic]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th))) THEN REWRITE_TAC[] THEN
  (* each chart reading is constant *)
  MATCH_MP_TAC HMR_SPHERE_CONST_CHARTS THEN
  X_GEN_TAC `Q:real^3^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^3->real^K`;
                   `Q:real^3^3`] HMR_SPH_PLANE_HARMONIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `\y. (u:real^3->real^K)(cm_capmap Q y)` HMR_PLANE_CONST) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`z:real^2`; `i:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `hmr_e (\y. (u:real^3->real^K)(cm_capmap Q y)) z <= &0` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      ABBREV_TAC `h = hmr_e (\y. (u:real^3->real^K)(cm_capmap Q y)) z` THEN
      ABBREV_TAC `R = &2 * norm(z:real^2) + &2 + &2 * C * e / h` THEN
      SUBGOAL_THEN `&0 <= &2 * C * e / h` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_DIV];
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= R /\ (z:real^2) IN ball(vec 0,R / &2)` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "R" THEN REWRITE_TAC[IN_BALL_0] THEN
        MP_TAC(ISPEC `z:real^2` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `wan_gdir (ball(vec 0,R)) G (\y. (u:real^3->real^K)(cm_capmap Q y)) <= &2 * cm_sen G u`
      ASSUME_TAC THENL
       [MATCH_MP_TAC HMR_CAP_ENERGY_LE THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
        ASM_REWRITE_TAC[OPEN_BALL];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^2`; `R:real`;
                                    `\y. (u:real^3->real^K)(cm_capmap Q y)`] o
        check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "hmr_e"))
                             (concl th) && is_forall (concl th))) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC HMC_HARMONIC_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
          ASM_REWRITE_TAC[SUBSET_UNIV];
          MP_TAC(ISPECL [`(:real^2)`; `\y. (u:real^3->real^K)(cm_capmap Q y)`; `vec 0:real^2`;
                         `R:real`] HMR_W12_SMOOTH_BALL) THEN
          ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN SIMP_TAC[];
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&2 * C * e <= R pow 2 * h` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `R * h` THEN CONJ_TAC THENL
         [SUBGOAL_THEN `&2 * C * e = (&2 * C * e / h) * h` SUBST1_TAC THENL
           [UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          EXPAND_TAC "R" THEN MP_TAC(ISPEC `z:real^2` NORM_POS_LE) THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          REWRITE_TAC[REAL_POW_2] THEN
          GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `C * wan_gdir (ball(vec 0,R)) G (\y. (u:real^3->real^K)(cm_capmap Q y)) <=
                    C * e` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < C * e` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
      UNDISCH_TAC `R pow 2 * h <= C * wan_gdir (ball(vec 0,R)) G (\y. (u:real^3->real^K)(cm_capmap Q y))` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[hmr_e] THEN
    MP_TAC(ISPEC `partial_derivative 1 (\y. (u:real^3->real^K)(cm_capmap Q y)) z` DOT_POS_LE) THEN
    MP_TAC(ISPEC `partial_derivative 2 (\y. (u:real^3->real^K)(cm_capmap Q y)) z` DOT_POS_LE) THEN
    SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[GSYM DOT_EQ_0] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The log-Laplacian inequality for the energy density of a planar harmonic  *)
(* map.  With E = |d1 v|^2 + |d2 v|^2, the refined Kato inequality (complex  *)
(* Cauchy-Schwarz for d_z v) and the Bochner formula give, for every dl > 0  *)
(* and pointwise bounds E <= M and |D^2 v| <= S2,                            *)
(*   Lap log(E + dl) >= -(16 B0 S2 + 2 B1 M)                                 *)
(* with B0, B1 depending only on the target (HMR_LOGLAP); the bound does not *)
(* depend on dl, which is what the unique continuation argument below needs. *)
(* ========================================================================= *)

let HMR_KATO_VEC = prove
 (`!a b p q:real^N.
     (a dot p + b dot q) pow 2 + (a dot q - b dot p) pow 2 <=
     (a dot a + b dot b) * (p dot p + q dot q)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(p:real^N) dot p + (q:real^N) dot q = &0` THENL
   [SUBGOAL_THEN `p:real^N = vec 0 /\ q:real^N = vec 0` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM DOT_EQ_0] THEN
      MP_TAC(ISPEC `p:real^N` DOT_POS_LE) THEN MP_TAC(ISPEC `q:real^N` DOT_POS_LE) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[DOT_RZERO; DOT_LZERO] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (p:real^N) dot p + (q:real^N) dot q` ASSUME_TAC THENL
   [MP_TAC(ISPEC `p:real^N` DOT_POS_LE) THEN MP_TAC(ISPEC `q:real^N` DOT_POS_LE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
  EXISTS_TAC `(p:real^N) dot p + (q:real^N) dot q` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `(p dot p + q dot q) % a - (a dot p + b dot q) % p -
                (a dot q - b dot p) % q:real^N` DOT_POS_LE) THEN
  MP_TAC(ISPEC `(p dot p + q dot q) % b - (a dot p + b dot q) % q +
                (a dot q - b dot p) % p:real^N` DOT_POS_LE) THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
  REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

let HMR_DOT_SQ_LE = prove
 (`!x y:real^N. (x dot y) pow 2 <= (x dot x) * (y dot y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL; GSYM REAL_LE_SQUARE_ABS] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM; NORM_CAUCHY_SCHWARZ_ABS]);;

let HMR_LOGLAP_ALG = prove
 (`!a b v11 v12 v22 L1 L2:real^N dl K1 K2.
     &0 < dl /\ &0 <= K1 /\ &0 <= K2 /\
     abs(a dot L1 + b dot L2) <= K1 * (a dot a + b dot b) /\
     abs((a dot (v11 - v22) + &2 * (b dot v12)) * (a dot (v11 + v22)) +
         (&2 * (a dot v12) - b dot (v11 - v22)) * (b dot (v11 + v22)))
     <= K2 * (a dot a + b dot b) pow 2
     ==> --((&2 * K1 + &2 * K2) * ((a dot a + b dot b) + dl) pow 2) <=
         ((a dot a + b dot b) + dl) *
         (&2 * ((v11 dot v11 + v12 dot v12) + (v12 dot v12 + v22 dot v22)) +
          &2 * (a dot L1 + b dot L2)) -
         ((&2 * (a dot v11) + &2 * (b dot v12)) pow 2 +
          (&2 * (a dot v12) + &2 * (b dot v22)) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `&2 * (((v11:real^N) dot v11 + (v12:real^N) dot v12) + (v12 dot v12 + (v22:real^N) dot v22)) =
    ((v11 - v22) dot (v11 - v22) + &2 * &2 * (v12 dot v12)) +
    (v11 + v22) dot (v11 + v22)`
  SUBST1_TAC THENL
   [REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB] THEN REWRITE_TAC[DOT_SYM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * ((a:real^N) dot (v11:real^N)) + &2 * ((b:real^N) dot (v12:real^N)) =
    (a dot (v11 - (v22:real^N)) + &2 * (b dot v12)) + a dot (v11 + v22)`
  SUBST1_TAC THENL [REWRITE_TAC[DOT_RADD; DOT_RSUB] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * ((a:real^N) dot (v12:real^N)) + &2 * ((b:real^N) dot (v22:real^N)) =
    (&2 * (a dot v12) - b dot ((v11:real^N) - v22)) + b dot (v11 + v22)`
  SUBST1_TAC THENL [REWRITE_TAC[DOT_RADD; DOT_RSUB] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `v11 - v22:real^N`; `&2 % v12:real^N`]
    HMR_KATO_VEC) THEN
  REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `v11 + v22:real^N`] HMR_DOT_SQ_LE) THEN
  MP_TAC(ISPECL [`b:real^N`; `v11 + v22:real^N`] HMR_DOT_SQ_LE) THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPEC `a:real^N` DOT_POS_LE) THEN MP_TAC(ISPEC `b:real^N` DOT_POS_LE) THEN
  MP_TAC(ISPEC `v11 - v22:real^N` DOT_POS_LE) THEN MP_TAC(ISPEC `v12:real^N` DOT_POS_LE) THEN
  MP_TAC(ISPEC `v11 + v22:real^N` DOT_POS_LE) THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= dl * (((v11:real^N) - v22) dot (v11 - v22) + &2 * &2 * ((v12:real^N) dot v12)) /\
    &0 <= dl * (((v11:real^N) + v22) dot (v11 + v22)) /\
    &0 <= (((a:real^N) dot a + (b:real^N) dot b) + dl) *
          ((a dot (L1:real^N) + b dot (L2:real^N)) + K1 * (a dot a + b dot b)) /\
    &0 <= K1 * (((a:real^N) dot a + (b:real^N) dot b) + dl) * dl /\
    &0 <= K2 * ((a:real^N) dot a + (b:real^N) dot b) * dl /\ &0 <= K2 * dl * dl`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

let HMR_D_E = prove
 (`!s (v:real^2->real^K) y j.
     open s /\ smooth_map_on s v /\ y IN s
     ==> cml_d j (hmr_e v) y =
         &2 * (partial_derivative 1 v y dot partial_derivative j (partial_derivative 1 v) y) +
         &2 * (partial_derivative 2 v y dot partial_derivative j (partial_derivative 2 v) y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a. smooth_map_on s (partial_derivative a (v:real^2->real^K))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `hmr_e (v:real^2->real^K) =
                (\y. partial_derivative 1 v y dot partial_derivative 1 v y +
                     partial_derivative 2 v y dot partial_derivative 2 v y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; hmr_e]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`;
                 `\y. partial_derivative 1 (v:real^2->real^K) y dot partial_derivative 1 v y`;
                 `\y. partial_derivative 2 (v:real^2->real^K) y dot partial_derivative 2 v y`;
                 `y:real^2`; `j:num`] CML_D_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `partial_derivative 1 (v:real^2->real^K)`; `y:real^2`;
                 `j:num`] HMR_D_SQ) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `partial_derivative 2 (v:real^2->real^K)`; `y:real^2`;
                 `j:num`] HMR_D_SQ) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

let HMR_LAP_SHIFT = prove
 (`!s (f:real^2->real) c z.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ z IN s
     ==> cml_lap (\x. f x + c) z = cml_lap f z /\
         cml_grad2 (\x. f x + c) z = cml_grad2 f z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i y. y IN s ==> cml_d i (\x. (f:real^2->real) x + c) y = cml_d i f y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `f:real^2->real`; `\x:real^2. c:real`; `y:real^2`;
                   `i:num`] CML_D_ADD) THEN
    ASM_REWRITE_TAC[CML_SM_CONST; CML_D_CONST; REAL_ADD_RID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[cml_grad2; cml_lap] THEN
  BINOP_TAC THEN MATCH_MP_TAC CML_D_LOCAL THEN EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[]);;

let HMR_VLAP_BOUNDS = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?B0 B1. &0 <= B0 /\ &0 <= B1 /\
                 !s (v:real^2->real^K) x.
                    open s /\ cm_harmonic S G s v /\ x IN s
                    ==> norm(hmr_vlap v x) <= B0 * hmr_e v x /\
                        !i. norm(partial_derivative i (\y. hmr_vlap v y) x) <=
                            &2 * B0 * (norm(partial_derivative i (partial_derivative 1 v) x) *
                                       norm(partial_derivative 1 v x) +
                                       norm(partial_derivative i (partial_derivative 2 v) x) *
                                       norm(partial_derivative 2 v x)) +
                            B1 * hmr_e v x * norm(partial_derivative i v x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_BQ_FAMILY) THEN
  MP_TAC(ISPECL [`cm_tube (S:real^K->bool) d`; `S:real^K->bool`;
                 `hmr_bq (S:real^K->bool) (G:real^K->real^K^K)`] HMR_BILFAM_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B0:real` (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`B0:real`; `B1:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `v:real^2->real^K`; `x:real^2`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `!a. smooth_map_on s (partial_derivative a (v:real^2->real^K))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^2->real^K) x IN S` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                   `v:real^2->real^K`; `x:real^2`] HMR_PDE) THEN
    ASM_REWRITE_TAC[VSUM_2] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B0 * norm(partial_derivative 1 (v:real^2->real^K) x) *
                     norm(partial_derivative 1 v x) +
                B0 * norm(partial_derivative 2 v x) * norm(partial_derivative 2 v x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `norm(a:real^N) <= x /\ norm b <= y ==> norm(a + b) <= x + y`) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[hmr_e; GSYM NORM_POW_2] THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. partial_derivative i (\y. hmr_vlap (v:real^2->real^K) y) x =
        (hmr_bq S G (v x) (partial_derivative i (partial_derivative 1 v) x)
                          (partial_derivative 1 v x) +
         hmr_bq S G (v x) (partial_derivative 1 v x)
                          (partial_derivative i (partial_derivative 1 v) x) +
         frechet_derivative (\q. hmr_bq S G q (partial_derivative 1 v x)
                                               (partial_derivative 1 v x))
                            (at (v x)) (partial_derivative i v x)) +
        (hmr_bq S G (v x) (partial_derivative i (partial_derivative 2 v) x)
                          (partial_derivative 2 v x) +
         hmr_bq S G (v x) (partial_derivative 2 v x)
                          (partial_derivative i (partial_derivative 2 v) x) +
         frechet_derivative (\q. hmr_bq S G q (partial_derivative 2 v x)
                                               (partial_derivative 2 v x))
                            (at (v x)) (partial_derivative i v x))`
  (LABEL_TAC "DF") THENL
   [GEN_TAC THEN
    TRANS_TAC EQ_TRANS
     `partial_derivative i
        (\y. hmr_bq S G ((v:real^2->real^K) y) (partial_derivative 1 v y)
                                               (partial_derivative 1 v y) +
             hmr_bq S G (v y) (partial_derivative 2 v y) (partial_derivative 2 v y)) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN BETA_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                     `v:real^2->real^K`; `y:real^2`] HMR_PDE) THEN
      ASM_REWRITE_TAC[VSUM_2];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`i:num`;
      `\y. hmr_bq S G ((v:real^2->real^K) y) (partial_derivative 1 v y) (partial_derivative 1 v y)`;
      `\y. hmr_bq S G ((v:real^2->real^K) y) (partial_derivative 2 v y) (partial_derivative 2 v y)`;
      `x:real^2`] PARTIAL_DERIVATIVE_ADD) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC HMR_BQ_DIFF THEN
      MAP_EVERY EXISTS_TAC [`d:real`; `s:real^2->bool`] THEN ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
    BINOP_TAC THEN MATCH_MP_TAC HMR_BQ_DERIV THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `s:real^2->bool`] THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  GEN_TAC THEN USE_THEN "DF" (fun th -> REWRITE_TAC[th]) THEN
  ABBREV_TAC `t1 = partial_derivative 1 (v:real^2->real^K) x` THEN
  ABBREV_TAC `t2 = partial_derivative 2 (v:real^2->real^K) x` THEN
  REWRITE_TAC[hmr_e; GSYM NORM_POW_2] THEN
  MATCH_MP_TAC(GEN_ALL(NORM_ARITH
   `norm(a1:real^N) <= x1 /\ norm a2 <= x2 /\ norm a3 <= x3 /\
    norm b1 <= y1 /\ norm b2 <= y2 /\ norm b3 <= y3 /\
    x1 + x2 + x3 + y1 + y2 + y3 <= z
    ==> norm((a1 + a2 + a3) + (b1 + b2 + b3)) <= z`)) THEN
  MAP_EVERY EXISTS_TAC
   [`B0 * norm(partial_derivative i (partial_derivative 1 (v:real^2->real^K)) x) * norm(t1:real^K)`;
    `B0 * norm(t1:real^K) * norm(partial_derivative i (partial_derivative 1 (v:real^2->real^K)) x)`;
    `B1 * norm(t1:real^K) * norm(t1:real^K) * norm(partial_derivative i (v:real^2->real^K) x)`;
    `B0 * norm(partial_derivative i (partial_derivative 2 (v:real^2->real^K)) x) * norm(t2:real^K)`;
    `B0 * norm(t2:real^K) * norm(partial_derivative i (partial_derivative 2 (v:real^2->real^K)) x)`;
    `B1 * norm(t2:real^K) * norm(t2:real^K) * norm(partial_derivative i (v:real^2->real^K) x)`] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let HMR_K1_ALG = prove
 (`!na nb n1 n2 m11 m12 m21 m22 B0 B1 S2 M z1 z2.
     &0 <= na /\ &0 <= nb /\ &0 <= B0 /\ &0 <= B1 /\ &0 <= S2 /\
     na pow 2 + nb pow 2 <= M /\
     m11 <= S2 /\ m12 <= S2 /\ m21 <= S2 /\ m22 <= S2 /\
     abs z1 <= na * n1 /\ abs z2 <= nb * n2 /\
     n1 <= &2 * B0 * (m11 * na + m12 * nb) + B1 * (na pow 2 + nb pow 2) * na /\
     n2 <= &2 * B0 * (m21 * na + m22 * nb) + B1 * (na pow 2 + nb pow 2) * nb
     ==> abs(z1 + z2) <= (&4 * B0 * S2 + B1 * M) * (na pow 2 + nb pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `na:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `nb:real` REAL_LE_POW_2) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `na * n1 <= na * (&2 * B0 * (m11 * na + m12 * nb) + B1 * (na pow 2 + nb pow 2) * na) /\
    nb * n2 <= nb * (&2 * B0 * (m21 * na + m22 * nb) + B1 * (na pow 2 + nb pow 2) * nb)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= B0 * (S2 - m11) * na * na /\ &0 <= B0 * (S2 - m12) * nb * na /\
    &0 <= B0 * (S2 - m21) * na * nb /\ &0 <= B0 * (S2 - m22) * nb * nb /\
    &0 <= B0 * S2 * (na - nb) pow 2 /\
    &0 <= B1 * (M - (na pow 2 + nb pow 2)) * (na pow 2 + nb pow 2)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let HMR_K2_ALG = prove
 (`!na nb x y al bl S2 B0 nL.
     &0 <= na /\ &0 <= nb /\ &0 <= S2 /\ &0 <= B0 /\
     abs x <= &2 * S2 * (na + nb) /\ abs y <= &2 * S2 * (na + nb) /\
     abs al <= na * nL /\ abs bl <= nb * nL /\ nL <= B0 * (na pow 2 + nb pow 2)
     ==> abs(x * al + y * bl) <= (&4 * S2 * B0) * (na pow 2 + nb pow 2) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `abs x * abs al <= (&2 * S2 * (na + nb)) * (na * (B0 * (na pow 2 + nb pow 2))) /\
    abs y * abs bl <= (&2 * S2 * (na + nb)) * (nb * (B0 * (na pow 2 + nb pow 2)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `na * nL`; EXISTS_TAC `nb * nL`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= S2 * B0 * (na pow 2 + nb pow 2) * (na - nb) pow 2` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x * al:real`; `y * bl:real`] REAL_ABS_TRIANGLE) THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN ASM_REAL_ARITH_TAC);;

let HMR_XY_BOUND = prove
 (`!a b v11 v12 v22:real^N S2.
     norm v11 <= S2 /\ norm v12 <= S2 /\ norm v22 <= S2
     ==> abs(a dot (v11 - v22) + &2 * (b dot v12)) <= &2 * S2 * (norm a + norm b) /\
         abs(&2 * (a dot v12) - b dot (v11 - v22)) <= &2 * S2 * (norm a + norm b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(v11 - v22:real^N) <= &2 * S2` ASSUME_TAC THENL
   [MP_TAC(NORM_ARITH `norm(v11 - v22:real^N) <= norm v11 + norm v22`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((a:real^N) dot (v11 - v22)) <= norm a * (&2 * S2) /\
    abs((b:real^N) dot (v11 - v22)) <= norm b * (&2 * S2) /\
    abs((a:real^N) dot v12) <= norm a * S2 /\ abs((b:real^N) dot v12) <= norm b * S2`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `norm(a:real^N) * norm(v11 - v22:real^N)`;
      EXISTS_TAC `norm(b:real^N) * norm(v11 - v22:real^N)`;
      EXISTS_TAC `norm(a:real^N) * norm(v12:real^N)`;
      EXISTS_TAC `norm(b:real^N) * norm(v12:real^N)`] THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let HMR_LOGLAP = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?B0 B1. &0 <= B0 /\ &0 <= B1 /\
                 !s (v:real^2->real^K) x dl M S2.
                    open s /\ cm_harmonic S G s v /\ x IN s /\ &0 < dl /\
                    hmr_e v x <= M /\
                    (!i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
                           ==> norm(partial_derivative i (partial_derivative j v) x) <= S2)
                    ==> --(&16 * B0 * S2 + &2 * B1 * M) <=
                        cml_lap (\y. log(hmr_e v y + dl)) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B0:real` (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMR_VLAP_BOUNDS) THEN
  MAP_EVERY EXISTS_TAC [`B0:real`; `B1:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `v:real^2->real^K`; `x:real^2`; `dl:real`; `M:real`;
                       `S2:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^2->bool`; `v:real^2->real^K`; `x:real^2`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dL")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `&0 <= S2 /\ &0 <= M` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) x)` THEN
      REWRITE_TAC[NORM_POS_LE] THEN FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      MP_TAC(ISPECL [`v:real^2->real^K`; `x:real^2`] HMR_E_POS) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s (\y. lift(hmr_e (v:real^2->real^K) y))` ASSUME_TAC THENL
   [MATCH_MP_TAC HMR_E_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `\y. hmr_e (v:real^2->real^K) y + dl`; `x:real^2`]
    CML_LAP_LOG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CML_SM_ADD THEN ASM_REWRITE_TAC[CML_SM_CONST];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`v:real^2->real^K`; `y:real^2`] HMR_E_POS) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `hmr_e (v:real^2->real^K)`; `dl:real`; `x:real^2`]
    HMR_LAP_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `&0 < (hmr_e (v:real^2->real^K) x + dl) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(ISPECL [`v:real^2->real^K`; `x:real^2`] HMR_E_POS) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; ASSUME `&0 < (hmr_e (v:real^2->real^K) x + dl) pow 2`] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:real^2->real^K`; `x:real^2`] HMR_LAP_E) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[cml_grad2] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:real^2->real^K`; `x:real^2`; `1`] HMR_D_E) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:real^2->real^K`; `x:real^2`; `2`] HMR_D_E) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[SUM_2] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:real^2->real^K`; `x:real^2`; `1`; `2`] HMR_SCHWARZ_ALL) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[hmr_e] THEN
  SUBGOAL_THEN `norm(partial_derivative 1 (v:real^2->real^K) x) pow 2 +
                norm(partial_derivative 2 v x) pow 2 <= M` ASSUME_TAC THENL
   [UNDISCH_TAC `hmr_e (v:real^2->real^K) x <= M` THEN REWRITE_TAC[hmr_e; NORM_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) x) <= S2 /\
    norm(partial_derivative 1 (partial_derivative 2 (v:real^2->real^K)) x) <= S2 /\
    norm(partial_derivative 2 (partial_derivative 1 (v:real^2->real^K)) x) <= S2 /\
    norm(partial_derivative 2 (partial_derivative 2 (v:real^2->real^K)) x) <= S2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "dL" (fun th ->
    ASSUME_TAC(REWRITE_RULE[hmr_e; GSYM NORM_POW_2] (SPEC `1` th)) THEN
    ASSUME_TAC(REWRITE_RULE[hmr_e; GSYM NORM_POW_2] (SPEC `2` th))) THEN
  SUBGOAL_THEN
   `norm(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) x +
         partial_derivative 2 (partial_derivative 2 v) x) <=
    B0 * (norm(partial_derivative 1 v x) pow 2 + norm(partial_derivative 2 v x) pow 2)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `norm(hmr_vlap (v:real^2->real^K) x) <= B0 * hmr_e v x` THEN
    REWRITE_TAC[hmr_vlap; VSUM_2; hmr_e; NORM_POW_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`partial_derivative 1 (v:real^2->real^K) x`;
                 `partial_derivative 2 (v:real^2->real^K) x`;
                 `partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) x`;
                 `partial_derivative 2 (partial_derivative 1 (v:real^2->real^K)) x`;
                 `partial_derivative 2 (partial_derivative 2 (v:real^2->real^K)) x`;
                 `S2:real`] HMR_XY_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`partial_derivative 1 (v:real^2->real^K) x`;
                 `partial_derivative 2 (v:real^2->real^K) x`;
                 `partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) x`;
                 `partial_derivative 2 (partial_derivative 1 (v:real^2->real^K)) x`;
                 `partial_derivative 2 (partial_derivative 2 (v:real^2->real^K)) x`;
                 `partial_derivative 1 (\y. hmr_vlap (v:real^2->real^K) y) x`;
                 `partial_derivative 2 (\y. hmr_vlap (v:real^2->real^K) y) x`;
                 `dl:real`; `&4 * B0 * S2 + B1 * M`; `&4 * S2 * B0`] HMR_LOGLAP_ALG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM NORM_POW_2] THEN MATCH_MP_TAC HMR_K1_ALG THEN
      MAP_EVERY EXISTS_TAC
       [`norm(partial_derivative 1 (\y. hmr_vlap (v:real^2->real^K) y) x)`;
        `norm(partial_derivative 2 (\y. hmr_vlap (v:real^2->real^K) y) x)`;
        `norm(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) x)`;
        `norm(partial_derivative 1 (partial_derivative 2 (v:real^2->real^K)) x)`;
        `norm(partial_derivative 2 (partial_derivative 1 (v:real^2->real^K)) x)`;
        `norm(partial_derivative 2 (partial_derivative 2 (v:real^2->real^K)) x)`] THEN
      ASM_REWRITE_TAC[NORM_POS_LE; NORM_CAUCHY_SCHWARZ_ABS];
      REWRITE_TAC[GSYM NORM_POW_2] THEN MATCH_MP_TAC HMR_K2_ALG THEN
      EXISTS_TAC `norm(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) x +
                       partial_derivative 2 (partial_derivative 2 v) x)` THEN
      ASM_REWRITE_TAC[NORM_POS_LE; NORM_CAUCHY_SCHWARZ_ABS]];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Unique continuation for planar harmonic maps.  If the energy density      *)
(* vanishes on a nonempty open set, it vanishes everywhere: for a point p    *)
(* with E(p) > 0 take a disc around p containing a disc of the zero set;     *)
(* log(E + dl) + K |y - p|^2 / 4 is subharmonic there (HMR_LOGLAP, K         *)
(* independent of dl), and its sub-mean value inequality forces log(E(p)) to *)
(* be below any bound as dl -> 0.                                            *)
(* ========================================================================= *)

let HMR_DJ_CONT_CONST = prove
 (`!s (u:real^2->real^K) m r.
     open s /\ smooth_map_on s u
     ==> (\y. lift(hmr_dj m r u y)) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_dj; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]);;

(* The sub-mean value inequality for log(f + dl) with a quadratic           *)
(* correction.                                                               *)

let HMR_LOG_SUBMEAN = prove
 (`!s (f:real^2->real) p rho K dl.
     open s /\ &0 < rho /\ cball(p,rho) SUBSET s /\ &0 < dl /\ &0 <= K /\
     smooth_map_on s (\x. lift(f x)) /\ (!x. &0 <= f x) /\
     (!x. x IN s ==> --K <= cml_lap (\y. log(f y + dl)) x)
     ==> log(f p + dl) <=
         inv(pi * rho pow 2) * drop(integral (ball(p,rho)) (\x. lift(log(f x + dl)))) +
         K * rho pow 2 / &4`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on s (\x. lift(log((f:real^2->real) x + dl)))` ASSUME_TAC THENL
   [MATCH_MP_TAC CML_SM_LOG THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CML_SM_ADD THEN ASM_REWRITE_TAC[CML_SM_CONST];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MP_TAC(SPEC `x:real^2` (ASSUME `!x:real^2. &0 <= (f:real^2->real) x`)) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `h = \y:real^2. &1 * log((f:real^2->real) y + dl) + (K / &4) * norm(y - p) pow 2` THEN
  SUBGOAL_THEN `smooth_map_on s (\y. lift(norm(y - p:real^2) pow 2))` ASSUME_TAC THENL
   [MESON_TAC[SMOOTH_MAP_ON_SUBSET; SUBSET_UNIV; HMR_SQ_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s (\y. lift((h:real^2->real) y))` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC CML_SM_ADD THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC CML_SM_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. y IN s ==> &0 <= llap (\z:real^2. mat 1) (h:real^2->real) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `\y. log((f:real^2->real) y + dl)`;
                   `\y:real^2. norm(y - p) pow 2`; `&1`; `K / &4`; `y:real^2`]
      WANL_LLAP_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `\y. log((f:real^2->real) y + dl)`; `y:real^2`]
      HMR_LLAP_CML) THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `\y:real^2. norm(y - p) pow 2`; `y:real^2`]
      HMR_LLAP_CML) THEN
    ASM_REWRITE_TAC[HMR_LAP_SQ] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `cml_lap`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`s:real^2->bool`; `h:real^2->real`; `p:real^2`; `rho:real`]
               (REWRITE_RULE[WAN_SUBMEAN_2D_STATEMENT] WAN_SUBMEAN_2D)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `(h:real^2->real) p = log((f:real^2->real) p + dl)` SUBST1_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift(log((f:real^2->real) x + dl))) integrable_on ball(p,rho) /\
                (\x. lift(norm(x - p:real^2) pow 2)) integrable_on ball(p,rho)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(MESON[WANL_CONT_CBALL_INTEGRABLE]
      `!f:real^2->real^1 a r. f continuous_on cball(a,r) ==> f integrable_on ball(a,r)`) THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (ball(p,rho)) (\x. lift((h:real^2->real) x))) =
    drop(integral (ball(p,rho)) (\x. lift(log((f:real^2->real) x + dl)))) +
    K / &4 * drop(integral (ball(p,rho)) (\x. lift(norm(x - p:real^2) pow 2)))`
  SUBST1_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[REAL_MUL_LID; LIFT_ADD; LIFT_CMUL] THEN
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_CMUL; INTEGRABLE_CMUL; DROP_ADD; DROP_CMUL;
                 REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop(integral (ball(p,rho)) (\x. lift(norm(x - p:real^2) pow 2))) <=
                rho pow 2 * (pi * rho pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (ball(p:real^2,rho)) (\y. lift(rho pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_REWRITE_TAC[INTEGRABLE_CONST; LIFT_DROP] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(MESON[WANL_CONT_CBALL_INTEGRABLE]
      `!f:real^2->real^1 a r. f continuous_on cball(a,r) ==> f integrable_on ball(a,r)`) THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST];
        X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
        ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_MESON_TAC[dist; REAL_LT_IMP_LE]];
      SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP] THEN
      ASM_SIMP_TAC[AREA_BALL; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < pi * rho pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[PI_POS; REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(pi * rho pow 2) *
    (K / &4 * drop(integral (ball(p,rho)) (\x. lift(norm(x - p:real^2) pow 2)))) <=
    K * rho pow 2 / &4`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(pi * rho pow 2) * (K / &4 * (rho pow 2 * (pi * rho pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < pi * rho pow 2` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* The integral of log(f + dl) over a disc containing a disc of zeros.      *)

let HMR_LOG_INT_BOUND = prove
 (`!s (f:real^2->real) p rho z0 r0 dl M.
     open s /\ cball(p,rho) SUBSET s /\ smooth_map_on s (\x. lift(f x)) /\
     &0 < r0 /\ &0 <= rho /\ cball(z0,r0) SUBSET cball(p,rho) /\
     ball(z0,r0) SUBSET ball(p,rho) /\ &0 < dl /\ dl <= &1 /\ (!x. &0 <= f x) /\
     (!x. x IN ball(p,rho) ==> f x <= M) /\ (!x. x IN ball(z0,r0) ==> f x = &0)
     ==> drop(integral (ball(p,rho)) (\x. lift(log(f x + dl)))) <=
         pi * r0 pow 2 * (log dl - log(M + &1)) + pi * rho pow 2 * log(M + &1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `LM = log(M + &1)` THEN
  SUBGOAL_THEN `smooth_map_on s (\x. lift(log((f:real^2->real) x + dl)))` ASSUME_TAC THENL
   [MATCH_MP_TAC CML_SM_LOG THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CML_SM_ADD THEN ASM_REWRITE_TAC[CML_SM_CONST];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MP_TAC(SPEC `x:real^2` (ASSUME `!x:real^2. &0 <= (f:real^2->real) x`)) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift(log((f:real^2->real) x + dl))) continuous_on cball(p,rho)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(LM - log((f:real^2->real) x + dl))) integrable_on ball(p,rho) /\
    (\x. lift(LM - log((f:real^2->real) x + dl))) integrable_on ball(z0,r0) /\
    (\x. lift(log((f:real^2->real) x + dl))) integrable_on ball(p,rho) /\
    (\x:real^2. lift LM) integrable_on ball(p,rho)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC(MESON[WANL_CONT_CBALL_INTEGRABLE]
      `!f:real^2->real^1 a r. f continuous_on cball(a,r) ==> f integrable_on ball(a,r)`) THEN
    REWRITE_TAC[LIFT_SUB; CONTINUOUS_ON_CONST] THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST]) THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(LM - log((f:real^2->real) x + dl))`; `ball(z0:real^2,r0)`;
                 `ball(p:real^2,rho)`] INTEGRAL_SUBSET_DROP_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> &0 <= b - a`) THEN EXPAND_TAC "LM" THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    MP_TAC(SPEC `x:real^2` (ASSUME `!x:real^2. &0 <= (f:real^2->real) x`)) THEN
    SUBGOAL_THEN `(f:real^2->real) x <= M` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < dl` THEN UNDISCH_TAC `dl <= &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (ball(z0,r0)) (\x. lift(LM - log((f:real^2->real) x + dl)))) =
    pi * r0 pow 2 * (LM - log dl)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `drop(integral (ball(z0:real^2,r0)) (\x. lift(LM - log dl)))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[REAL_ADD_LID];
      SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP] THEN
      ASM_SIMP_TAC[AREA_BALL; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (ball(p,rho)) (\x. lift(LM - log((f:real^2->real) x + dl)))) =
    pi * rho pow 2 * LM - drop(integral (ball(p,rho)) (\x. lift(log(f x + dl))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN
    MP_TAC(ISPECL [`\x:real^2. lift LM`; `\x. lift(log((f:real^2->real) x + dl))`;
                   `ball(p:real^2,rho)`] INTEGRAL_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[DROP_SUB; INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP] THEN
    ASM_SIMP_TAC[AREA_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Unique continuation on the plane. *)

let HMR_UC_PLANE = prove
 (`!S (G:real^K->real^K^K) d (v:real^2->real^K) W.
     cm_target S G d /\ cm_harmonic S G (:real^2) v /\ open W /\ ~(W = {}) /\
     (!z. z IN W ==> hmr_e v z = &0)
     ==> !p. hmr_e v p = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `p:real^2` THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B0:real` (X_CHOOSE_THEN `B1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LL")))) o
    MATCH_MP HMR_LOGLAP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `?z0 r0. &0 < r0 /\ ball(z0:real^2,r0) SUBSET W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY; OPEN_CONTAINS_BALL]; ALL_TAC] THEN
  ASM_CASES_TAC `hmr_e (v:real^2->real^K) p = &0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < hmr_e (v:real^2->real^K) p` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`v:real^2->real^K`; `p:real^2`] HMR_E_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the discs *)
  ABBREV_TAC `rho = norm(p - z0:real^2) + r0` THEN
  SUBGOAL_THEN `&0 < rho /\ ball(z0:real^2,r0) SUBSET ball(p,rho) /\
                cball(z0:real^2,r0) SUBSET cball(p,rho)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL; dist] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `p - z0:real^2` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN
      MP_TAC(NORM_ARITH `norm(p - x:real^2) <= norm(p - z0) + norm(z0 - x)`) THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN
      MP_TAC(NORM_ARITH `norm(p - x:real^2) <= norm(p - z0) + norm(z0 - x)`) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `R1 = rho + &1` THEN
  SUBGOAL_THEN `cball(p:real^2,rho) SUBSET ball(p,R1) /\ ball(p:real^2,R1) SUBSET cball(p,R1) /\
                ball(p:real^2,rho) SUBSET cball(p,R1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R1" THEN REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN REPEAT CONJ_TAC THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* bounds on the closed disc of radius R1 *)
  SUBGOAL_THEN `?D. &0 <= D /\
                    !y. y IN cball(p:real^2,R1) ==> hmr_dj 1 (&1) (v:real^2->real^K) y <= D`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\y:real^2. hmr_dj 1 (&1) (v:real^2->real^K) y`; `cball(p:real^2,R1)`]
      CONTINUOUS_ATTAINS_SUP) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL; CBALL_EQ_EMPTY; o_DEF] THEN CONJ_TAC THENL
       [EXPAND_TAC "R1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[HMR_DJ_CONT_CONST; OPEN_UNIV; SUBSET_UNIV];
      REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y1:real^2` STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC `hmr_dj 1 (&1) (v:real^2->real^K) y1` THEN ASM_SIMP_TAC[HMR_DJ_POS; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN cball(p:real^2,R1)
        ==> (!i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
                   ==> norm(partial_derivative i (partial_derivative j (v:real^2->real^K)) y)
                       <= D) /\
            hmr_e v y <= &2 * D pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `hmr_dj 1 (&1) (v:real^2->real^K) y <= D` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`1`; `&1`; `v:real^2->real^K`; `y:real^2`; `j:num`; `[i:num]`]
        HMR_DJ_TERM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[LENGTH; ALL; REAL_POS] THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[iterated_partial; LENGTH; REAL_POW_ONE; REAL_MUL_LID; ETA_AX] THEN
      ASM_MESON_TAC[REAL_LE_TRANS];
      ALL_TAC] THEN
    SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                      ==> norm(partial_derivative i (v:real^2->real^K) y) <= D`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`1`; `&1`; `v:real^2->real^K`; `y:real^2`; `i:num`; `[]:num list`]
        HMR_DJ_TERM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[LENGTH; ALL; REAL_POS] THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[iterated_partial; LENGTH; REAL_POW_ONE; REAL_MUL_LID; ETA_AX] THEN
      ASM_MESON_TAC[REAL_LE_TRANS];
      ALL_TAC] THEN
    REWRITE_TAC[hmr_e; GSYM NORM_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= d /\ b <= d ==> a + b <= &2 * d`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  (* the log-Laplacian bound on the open disc of radius R1 *)
  ABBREV_TAC `K = &16 * B0 * D + &2 * B1 * (&2 * D pow 2)` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!dl y. &0 < dl /\ y IN ball(p:real^2,R1)
           ==> --K <= cml_lap (\y. log(hmr_e (v:real^2->real^K) y + dl)) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN cball(p,R1)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
      can (find_term (fun t -> t = `&2 * D pow 2`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXPAND_TAC "K" THEN USE_THEN "LL" MATCH_MP_TAC THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  (* the choice of dl *)
  ABBREV_TAC `th = r0 pow 2 / rho pow 2` THEN
  ABBREV_TAC `LM = log(&2 * D pow 2 + &1)` THEN
  ABBREV_TAC `Z = LM + K * rho pow 2 / &4 - log(hmr_e (v:real^2->real^K) p)` THEN
  ABBREV_TAC `dl = exp(--((abs Z + LM + &1) / th))` THEN
  SUBGOAL_THEN `&0 < th` ASSUME_TAC THENL
   [EXPAND_TAC "th" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= LM` ASSUME_TAC THENL
   [EXPAND_TAC "LM" THEN MATCH_MP_TAC LOG_POS THEN MP_TAC(SPEC `D:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dl /\ dl <= &1 /\ th * log dl = --(abs Z + LM + &1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN REWRITE_TAC[REAL_EXP_POS_LT; LOG_EXP] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --x <= &0`) THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < th` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  (* the sub-mean value inequality and the integral bound *)
  SUBGOAL_THEN `smooth_map_on (ball(p:real^2,R1)) (\x. lift(hmr_e (v:real^2->real^K) x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[HMR_E_SMOOTH; OPEN_UNIV; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!x. x IN ball(p:real^2,rho) ==> hmr_e (v:real^2->real^K) x <= &2 * D pow 2) /\
                (!x. x IN ball(z0:real^2,r0) ==> hmr_e (v:real^2->real^K) x = &0) /\
                &0 <= rho`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
        can (find_term (fun t -> t = `&2 * D pow 2`)) (concl th) && is_forall(concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(p:real^2,R1)`; `hmr_e (v:real^2->real^K)`; `p:real^2`; `rho:real`;
                 `K:real`; `dl:real`] HMR_LOG_SUBMEAN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; HMR_E_POS] THEN ASM_SIMP_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`ball(p:real^2,R1)`; `hmr_e (v:real^2->real^K)`; `p:real^2`; `rho:real`;
                 `z0:real^2`; `r0:real`; `dl:real`; `&2 * D pow 2`] HMR_LOG_INT_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL; HMR_E_POS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `inv(pi * rho pow 2) *
    drop(integral (ball(p,rho)) (\x. lift(log(hmr_e (v:real^2->real^K) x + dl)))) <=
    th * (log dl - LM) + LM`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(pi * rho pow 2) * (pi * r0 pow 2 * (log dl - LM) + pi * rho pow 2 * LM)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV THEN
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[PI_POS_LE; REAL_LE_POW_2];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "th" THEN
      MP_TAC PI_POS THEN UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hmr_e (v:real^2->real^K) p`; `hmr_e (v:real^2->real^K) p + dl`]
    LOG_MONO_LE_IMP) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= th * LM` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* CM_CRITICAL_ISOLATED.  If the differential of a harmonic sphere vanished  *)
(* on a nonempty open subset of the sphere, every cap chart reading would    *)
(* have zero energy density on a nonempty open subset of the plane, hence    *)
(* everywhere (HMR_UC_PLANE), so every chart reading and then the map itself *)
(* would be constant.                                                        *)
(* ========================================================================= *)

let HMR_OPEN_SPHERE_AVOID = prove
 (`!O (P:real^3).
     open_in (subtopology euclidean (sphere(vec 0,&1))) O /\ ~(O = {})
     ==> ?y. y IN O /\ ~(y = P)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `y0:real^3` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_CASES_TAC `y0:real^3 = P` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[OPEN_IN_OPEN] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y0:real^3) IN sphere(vec 0,&1) /\ y0 IN t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `y0:real^3` o REWRITE_RULE[OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `y0:real^3`] LIMIT_POINT_OF_SPHERE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH; REAL_LT_01] THEN
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y1:real^3` THEN
  SUBGOAL_THEN `(y1:real^3) IN ball(y0,e)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
  ASM SET_TAC[]);;

let CM_CRITICAL_ISOLATED = prove
 (`!kk:K->bool. CM_CRITICAL_ISOLATED_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CM_CRITICAL_ISOLATED_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:real^3->real^K`; `O:real^3->bool`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_sharmonic]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) && is_exists(rand(concl th)))) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC HMR_SPHERE_CONST_CHARTS THEN
  X_GEN_TAC `Q:real^3^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^3->real^K`;
                 `Q:real^3^3`] HMR_SPH_PLANE_HARMONIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the energy density of the chart reading vanishes on the plane *)
  SUBGOAL_THEN `!z. hmr_e (\y. (u:real^3->real^K)(cm_capmap Q y)) z = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC HMR_UC_PLANE THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                          `{z:real^2 | cm_capmap Q z IN O}`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o REWRITE_RULE[OPEN_IN_OPEN] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `{z:real^2 | cm_capmap Q z IN O} = {z | cm_capmap Q z IN t}`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
        MP_TAC(MATCH_MP CMR_CAPMAP_FACTS (ASSUME `orthogonal_matrix(Q:real^3^3)`)) THEN
        SIMP_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN REWRITE_TAC[ETA_AX] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `Q:real^3^3` HMR_CAPMAP_SMOOTH) THEN
      DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
      SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`O:real^3->bool`; `(Q:real^3^3) ** basis 3`] HMR_OPEN_SPHERE_AVOID) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `cmr_chart Q (y:real^3)` THEN
      SUBGOAL_THEN `(y:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
      MP_TAC(MATCH_MP CMR_CAPMAP_FACTS (ASSUME `orthogonal_matrix(Q:real^3^3)`)) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      REWRITE_TAC[hmr_e] THEN
      MP_TAC(ISPECL [`Q:real^3^3`; `u:real^3->real^K`; `z:real^2`; `1`] HMR_CAP_PD) THEN
      MP_TAC(ISPECL [`Q:real^3^3`; `u:real^3->real^K`; `z:real^2`; `2`] HMR_CAP_PD) THEN
      ASM_SIMP_TAC[MATRIX_VECTOR_MUL_LZERO; DOT_LZERO; REAL_ADD_LID]];
    ALL_TAC] THEN
  (* hence the chart reading is constant *)
  MP_TAC(ISPEC `\y. (u:real^3->real^K)(cm_capmap Q y)` HMR_PLANE_CONST) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "cm_harmonic")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`z:real^2`; `i:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "hmr_e")) (concl th))) THEN
  REWRITE_TAC[hmr_e] THEN
  MP_TAC(ISPEC `partial_derivative 1 (\y. (u:real^3->real^K)(cm_capmap Q y)) z` DOT_POS_LE) THEN
  MP_TAC(ISPEC `partial_derivative 2 (\y. (u:real^3->real^K)(cm_capmap Q y)) z` DOT_POS_LE) THEN
  SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[GSYM DOT_EQ_0] THEN REAL_ARITH_TAC);;

