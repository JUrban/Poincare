(* ========================================================================= *)
(* Unit pc_cmp_ltpg (comparison-geometry layer CMP):                         *)
(* CMP_R8_LOCAL_TOPONOGOV_STATEMENT, Toponogov's angle comparison in a       *)
(* compact convex region D of a possibly incomplete manifold with sec >= 0,  *)
(* the form needed where MT Lemmas 10.21-10.22 apply Toponogov's Thm 2.4 in  *)
(* the incomplete U_inf.  The proof of the complete case (pc_cmp_tpg) goes   *)
(* through with the incomplete Calabi barrier of pc_cmp_lhup and with the    *)
(* minimizing segments that the convexity of D provides: a shortest curve in *)
(* D is a minimizing geodesic segment (CMPRG_SHORTEST of pc_cmp_reg).        *)
(* ========================================================================= *)

needs "src/pc_cmp_lhup.ml";;
needs "src/pc_cmp_tpg.ml";;
needs "src/pc_apx_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Continuity and barriers of h(t) = d(q,sigma t)^2 - t^2 along              *)
(* a geodesic sigma = geo(p,u) on a part of its maximal interval, given a    *)
(* minimizing direction from sigma(t0) to q (CMPA_HCONT, CMPAN_HBARRIER_J    *)
(* without completeness).                                                    *)
(* ========================================================================= *)

let CMPLT_HCONT = prove
 (`!top atlas (g:A->real^N^N) (p:A) u (q:A) a c.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ p IN topspace top /\
        real_interval[a,c] SUBSET mfd_geo_maxint (top,atlas) g p u
        ==> (\t. mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g p u t) pow 2 - t pow 2)
            real_continuous_on real_interval[a,c]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) p u`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) p u`] GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\t. mfd_dist (top,atlas) (g:A->real^N^N) q (mfd_geo (top,atlas) g p u t))
                real_continuous_on real_interval[a,c]` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM GRGD_CONTINUOUS_MAP_REAL] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `mfd_geo_maxint (top,atlas) (g:A->real^N^N) p u` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\t. mfd_dist (top,atlas) (g:A->real^N^N) q (mfd_geo (top,atlas) g p u t)) =
                  (\y. mfd_dist (top,atlas) g q y) o mfd_geo (top,atlas) g p u`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID]]);;

let CMPLT_HBARRIER = prove
 (`!top atlas (g:A->real^N^N) (p:A) u (q:A) t0 e.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p IN topspace top /\ mfd_tnorm g p u = &1 /\ q IN topspace top /\ &0 < e /\
        t0 IN mfd_geo_maxint (top,atlas) g p u /\
        mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p u t0) q /\
        (?w. w IN mfd_exp_dom (top,atlas) g (mfd_geo (top,atlas) g p u t0) /\
             mfd_exp (top,atlas) g (mfd_geo (top,atlas) g p u t0) w = q /\
             mfd_tnorm g (mfd_geo (top,atlas) g p u t0) w =
             mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) q)
        ==> ?d bf bf' bf2.
              &0 < d /\
              (!s. abs(s - t0) < d ==> (bf has_real_derivative bf'(s)) (atreal s)) /\
              (bf' has_real_derivative bf2) (atreal t0) /\ bf2 <= e /\
              bf t0 = mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g p u t0) pow 2 -
                      t0 pow 2 /\
              (!s. abs(s - t0) < d
                   ==> mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g p u s) pow 2 -
                       s pow 2 <= bf s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) p u` THEN
  ABBREV_TAC `M = mfd_geo_maxint (top,atlas) (g:A->real^N^N) p u` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!s. s IN M ==> (sigma:real->A) s IN topspace top` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `M:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN M
                    ==> mfd_tnorm (g:A->real^N^N) ((sigma:real->A) s) (mfd_vel atlas sigma s) = &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `sigma:real->A`; `M:real->bool`; `s:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?d0. &0 < d0 /\ !s. abs(s - t0) < d0 ==> s IN (M:real->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `real_open(M:real->bool)` THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN(MP_TAC o SPEC `t0:real`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(sigma:real->A) t0 = q` THENL
   [EXISTS_TAC `d0:real` THEN
    EXISTS_TAC `\s. t0 pow 2 - &2 * s * t0` THEN
    EXISTS_TAC `\s:real. --(&2 * t0)` THEN EXISTS_TAC `&0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `q:A`] MFD_DIST_REFL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(s:real) IN M` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `sigma:real->A`; `M:real->bool`; `t0:real`; `s:real`]
        GEOH_GEO_SEG_DIST) THEN
      ASM_SIMP_TAC[REAL_MUL_RID] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `q:A`; `(sigma:real->A) s`] MFD_DIST_POS_LE) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
      SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) q ((sigma:real->A) s) pow 2 <=
                    (s - t0) pow 2` MP_TAC THENL
       [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_MESON_TAC[REAL_ABS_REFL; REAL_LE_TRANS;
          REAL_ABS_POS];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `z = (sigma:real->A) t0` THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^N^N) z q` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`; `q:A`] MFD_DIST_EQ_0) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`; `q:A`] MFD_DIST_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `delta = min (L / &2) (e * L / &4)` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= L / &2 /\ delta <= e * L / &4` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < e * L / &4` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "delta" THEN REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`; `t0:real`; `z:A`; `w:real^N`; `q:A`;
                 `delta:real`] CMPLH_BARRIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `bf2 <= &2 * delta / (mfd_tnorm (g:A->real^N^N) z w - delta)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * delta / (L - delta)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < L - delta` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `!x y. &2 * x / y = (&2 * x) / y`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `e * L / &2 <= e * (L - delta)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `z:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                               with Failure _ -> false)) (concl th) &&
      can (find_term ((=) `bf:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* Monotonicity of the comparison cosine in one variable on an               *)
(* incomplete manifold (CMPAN_MONO1 with the side geo(p,v) defined on        *)
(* [0,s2'] and minimizing directions from its interior points to q).         *)
(* ========================================================================= *)

let CMPLT_MONO1 = prove
 (`!top atlas (g:A->real^N^N) (p:A) v (q:A) s1 s2 s2'.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p IN topspace top /\ mfd_tnorm g p v = &1 /\ q IN topspace top /\
        mfd_joinable (top,atlas) p q /\
        mfd_dist (top,atlas) g p q = s1 /\ &0 < s1 /\ &0 < s2 /\ s2 <= s2' /\
        real_interval[&0,s2'] SUBSET mfd_geo_maxint (top,atlas) g p v /\
        (!t. &0 < t /\ t < s2'
             ==> mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p v t) q /\
                 ?w. w IN mfd_exp_dom (top,atlas) g (mfd_geo (top,atlas) g p v t) /\
                     mfd_exp (top,atlas) g (mfd_geo (top,atlas) g p v t) w = q /\
                     mfd_tnorm g (mfd_geo (top,atlas) g p v t) w =
                     mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p v t) q)
        ==> (s1 pow 2 + s2 pow 2 -
             mfd_dist (top,atlas) g q (mfd_exp (top,atlas) g p (s2 % v)) pow 2) /
            (&2 * s1 * s2) <=
            (s1 pow 2 + s2' pow 2 -
             mfd_dist (top,atlas) g q (mfd_exp (top,atlas) g p (s2' % v)) pow 2) /
            (&2 * s1 * s2')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s2:real = s2'` THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `s2 < s2'` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= s2'
                    ==> mfd_exp (top,atlas) (g:A->real^N^N) p (t % v) =
                        mfd_geo (top,atlas) g p v t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `v:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `real_interval[&0,s2'] SUBSET mfd_geo_maxint (top,atlas) (g:A->real^N^N) p v` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) p (s2 % v) = mfd_geo (top,atlas) g p v s2 /\
                mfd_exp (top,atlas) g p (s2' % v) = mfd_geo (top,atlas) g p v s2'`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. mfd_dist (top,atlas) (g:A->real^N^N) q
                        (mfd_geo (top,atlas) g p v t) pow 2 - t pow 2`;
                 `&0`; `s2':real`] CMPA_CALABI) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CMPLT_HCONT THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t0:real`; `e:real`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p:A`; `v:real^N`; `q:A`; `t0:real`; `e:real`]
        CMPLT_HBARRIER) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `real_interval[&0,s2'] SUBSET
                       mfd_geo_maxint (top,atlas) (g:A->real^N^N) p v` THEN
          REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                                     with Failure _ -> false)) (concl th))) THEN
          ASM_REWRITE_TAC[]];
        SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s2:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `p:A`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_POW_ZERO; ARITH_EQ] THEN DISCH_TAC THEN
  MATCH_MP_TAC CMPAN_ALG THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN ABBREV_TAC `Da = mfd_dist (top,atlas) (g:A->real^N^N) q
                                          (mfd_geo (top,atlas) g p v s2) pow 2` THEN
  ABBREV_TAC `Dc = mfd_dist (top,atlas) (g:A->real^N^N) q
                     (mfd_geo (top,atlas) g p v s2') pow 2` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The local Toponogov theorem in dimension n.  The convexity of D gives,    *)
(* through CMPRG_SHORTEST, a minimizing segment from any point of D to any   *)
(* other (CMPLT_CONVEX_SEG); the sides exp_p(s v_i), 0 <= s <= L_i, lie in D *)
(* and their initial segments are minimizing (CMPS_RAY_DIST); then           *)
(* CMPLT_MONO1 is applied in each variable as in CMPAN_TOPONOGOV_GEN.        *)
(* ========================================================================= *)

let CMPLT_CONVEX_SEG = prove
 (`!top atlas (g:A->real^N^N) D.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        (!y z. y IN D /\ z IN D
               ==> ?gamma. (mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                            !s t. &0 <= s /\ s <= t /\ t <= &1
                                  ==> mfd_length atlas g gamma s t =
                                      mfd_dist (top,atlas) g (gamma s) (gamma t)) /\
                           gamma (&0) = y /\ gamma (&1) = z /\
                           !s. &0 <= s /\ s <= &1 ==> gamma s IN D)
        ==> !y z. y IN D /\ z IN D
                  ==> mfd_joinable (top,atlas) y z /\
                      ?w. w IN mfd_exp_dom (top,atlas) g y /\
                          mfd_exp (top,atlas) g y w = z /\
                          mfd_tnorm g y w = mfd_dist (top,atlas) g y z`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv")))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "conv" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `(y:A) IN D`) (ASSUME `(z:A) IN D`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(gamma:real->A)(&0) = y`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(gamma:real->A)(&1) = z`)) THEN
    MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`] CMPRG_SHORTEST) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let CMPLT_TOPONOGOV_GEN = prove
 (`!top atlas (g:A->real^N^N) D p v1 v2 L1 L2.
       hausdorff_space top /\ smooth_manifold_atlas top atlas /\
       riemannian_metric atlas g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v) /\
       D SUBSET topspace top /\
       (!y z. y IN D /\ z IN D
              ==> ?gamma. (mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                           !s t. &0 <= s /\ s <= t /\ t <= &1
                                 ==> mfd_length atlas g gamma s t =
                                     mfd_dist (top,atlas) g (gamma s) (gamma t)) /\
                          gamma (&0) = y /\ gamma (&1) = z /\
                          !s. &0 <= s /\ s <= &1 ==> gamma s IN D) /\
       p IN D /\ mfd_tnorm g p v1 = &1 /\ mfd_tnorm g p v2 = &1 /\ &0 < L1 /\ &0 < L2 /\
       (!s. &0 <= s /\ s <= L1
            ==> s % v1 IN mfd_exp_dom (top,atlas) g p /\
                mfd_exp (top,atlas) g p (s % v1) IN D) /\
       (!s. &0 <= s /\ s <= L2
            ==> s % v2 IN mfd_exp_dom (top,atlas) g p /\
                mfd_exp (top,atlas) g p (s % v2) IN D) /\
       mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L1 % v1)) = L1 /\
       mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L2 % v2)) = L2
       ==> !s1 s1' s2 s2'. &0 < s1 /\ s1 <= s1' /\ s1' <= L1 /\
                           &0 < s2 /\ s2 <= s2' /\ s2' <= L2
           ==> (s1 pow 2 + s2 pow 2 -
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s1 % v1))
                                       (mfd_exp (top,atlas) g p (s2 % v2)) pow 2) /
               (&2 * s1 * s2) <=
               (s1' pow 2 + s2' pow 2 -
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s1' % v1))
                                       (mfd_exp (top,atlas) g p (s2' % v2)) pow 2) /
               (&2 * s1' * s2')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `D:A->bool`] CMPLT_CONVEX_SEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "seg2")] THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v L s. mfd_tnorm (g:A->real^N^N) p v = &1 /\ &0 < L /\
            (!s. &0 <= s /\ s <= L
                 ==> s % v IN mfd_exp_dom (top,atlas) g p /\
                     mfd_exp (top,atlas) g p (s % v) IN D) /\
            mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L % v)) = L /\
            &0 <= s /\ s <= L
            ==> mfd_exp (top,atlas) g p (s % v) IN topspace top /\
                mfd_joinable (top,atlas) p (mfd_exp (top,atlas) g p (s % v)) /\
                mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (s % v)) = s`
  (LABEL_TAC "seg") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(L:real) % (v:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) p`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `L:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `L:real`)) (concl th) &&
        can (find_term ((=) `v:real^N`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_exp_dom"
                                 with Failure _ -> false)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p (L % v) = L` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `L % (v:real^N)`; `&0`; `s / L`] CMPS_RAY_DIST) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; REAL_SUB_RZERO; VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `s / L * L = s` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] MFD_EXP_DOM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `L:real`)) (concl th) &&
      can (find_term ((=) `v:real^N`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_exp_dom"
                               with Failure _ -> false)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v L. (!s. &0 <= s /\ s <= L
               ==> s % v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) p /\
                   mfd_exp (top,atlas) g p (s % v) IN D)
          ==> real_interval[&0,L] SUBSET mfd_geo_maxint (top,atlas) g p v /\
              !s. &0 <= s /\ s <= L
                  ==> mfd_exp (top,atlas) g p (s % v) = mfd_geo (top,atlas) g p v s`
  (LABEL_TAC "max") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `!s. &0 <= s /\ s <= L
                      ==> s IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) p v`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p:A`; `v:real^N`; `s:real`] MFD_EXP_RADIAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `v:real^N`; `s:real`] MFD_EXP_RADIAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v L (q:A) s1 s s'.
        mfd_tnorm (g:A->real^N^N) p v = &1 /\ &0 < L /\
        (!s. &0 <= s /\ s <= L
             ==> s % v IN mfd_exp_dom (top,atlas) g p /\
                 mfd_exp (top,atlas) g p (s % v) IN D) /\
        q IN D /\ mfd_joinable (top,atlas) p q /\ mfd_dist (top,atlas) g p q = s1 /\
        &0 < s1 /\ &0 < s /\ s <= s' /\ s' <= L
        ==> (s1 pow 2 + s pow 2 -
             mfd_dist (top,atlas) g q (mfd_exp (top,atlas) g p (s % v)) pow 2) /
            (&2 * s1 * s) <=
            (s1 pow 2 + s' pow 2 -
             mfd_dist (top,atlas) g q (mfd_exp (top,atlas) g p (s' % v)) pow 2) /
            (&2 * s1 * s')`
  (LABEL_TAC "mono") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "max" (MP_TAC o SPECL [`v:real^N`; `L:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC CMPLT_MONO1 THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval[&0,L]` THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_geo"
                                 with Failure _ -> false)) (concl th) &&
        not(can (find_term (fun t -> try fst(dest_const t) = "mfd_geo_maxint"
                                     with Failure _ -> false)) (concl th)))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      USE_THEN "seg2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `L:real`)) (concl th) &&
        can (find_term ((=) `v:real^N`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_exp_dom"
                                 with Failure _ -> false)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `(s1 pow 2 + s2' pow 2 -
     mfd_dist (top,atlas) (g:A->real^N^N) (mfd_exp (top,atlas) g p (s1 % v1))
                            (mfd_exp (top,atlas) g p (s2' % v2)) pow 2) /
    (&2 * s1 * s2')` THEN
  CONJ_TAC THENL
   [USE_THEN "seg" (MP_TAC o SPECL [`v1:real^N`; `L1:real`; `s1:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "mono" MATCH_MP_TAC THEN EXISTS_TAC `L2:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `L1:real`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_exp_dom"
                               with Failure _ -> false)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "seg" (MP_TAC o SPECL [`v2:real^N`; `L2:real`; `s2':real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "mono" (MP_TAC o SPECL
   [`v1:real^N`; `L1:real`; `mfd_exp (top,atlas) (g:A->real^N^N) p (s2' % v2)`;
    `s2':real`; `s1:real`; `s1':real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `s2':real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `L2:real`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_exp_dom"
                                 with Failure _ -> false)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= L1
        ==> mfd_dist (top,atlas) (g:A->real^N^N) (mfd_exp (top,atlas) g p (s2' % v2))
              (mfd_exp (top,atlas) g p (s % v1)) =
            mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s % v1))
              (mfd_exp (top,atlas) g p (s2' % v2))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s1 /\ s1 <= L1 /\ &0 <= s1' /\ s1' <= L1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[ASSUME
   `!s. &0 <= s /\ s <= L1
        ==> mfd_dist (top,atlas) (g:A->real^N^N) (mfd_exp (top,atlas) g p (s2' % v2))
              (mfd_exp (top,atlas) g p (s % v1)) =
            mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s % v1))
              (mfd_exp (top,atlas) g p (s2' % v2))`;
    ASSUME `&0 <= s1`; ASSUME `s1 <= L1`; ASSUME `&0 <= s1'`; ASSUME `s1' <= L1`] THEN
  MATCH_MP_TAC(REAL_ARITH `a = c /\ b = d ==> a <= b ==> c <= d`) THEN
  CONJ_TAC THEN BINOP_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The local Toponogov theorem.  The statement constant has the body of the  *)
(* statement P2B_REQ_CMP_LOCAL_TOPONOGOV_STATEMENT of pc_p2b_defs verbatim;  *)
(* apx_shortest is from pc_apx_defs.                                         *)
(* ========================================================================= *)

let CMP_R8_LOCAL_TOPONOGOV_STATEMENT = new_definition
 `CMP_R8_LOCAL_TOPONOGOV_STATEMENT (w:B->bool) <=>
    !top atlas g D p v1 v2 L1 L2.
       hausdorff_space top /\ smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
       riemannian_metric atlas g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v) /\
       compact_in top D /\
       (!y z. y IN D /\ z IN D
              ==> ?gamma. apx_shortest (top,atlas) g gamma (&0) (&1) /\
                          gamma (&0) = y /\ gamma (&1) = z /\
                          !s. &0 <= s /\ s <= &1 ==> gamma s IN D) /\
       p IN D /\ mfd_tnorm g p v1 = &1 /\ mfd_tnorm g p v2 = &1 /\ &0 < L1 /\ &0 < L2 /\
       (!s. &0 <= s /\ s <= L1
            ==> s % v1 IN mfd_exp_dom (top,atlas) g p /\
                mfd_exp (top,atlas) g p (s % v1) IN D) /\
       (!s. &0 <= s /\ s <= L2
            ==> s % v2 IN mfd_exp_dom (top,atlas) g p /\
                mfd_exp (top,atlas) g p (s % v2) IN D) /\
       mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L1 % v1)) = L1 /\
       mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (L2 % v2)) = L2
       ==> !s1 s1' s2 s2'. &0 < s1 /\ s1 <= s1' /\ s1' <= L1 /\
                           &0 < s2 /\ s2 <= s2' /\ s2' <= L2
           ==> (s1 pow 2 + s2 pow 2 -
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s1 % v1))
                                       (mfd_exp (top,atlas) g p (s2 % v2)) pow 2) /
               (&2 * s1 * s2) <=
               (s1' pow 2 + s2' pow 2 -
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s1' % v1))
                                       (mfd_exp (top,atlas) g p (s2' % v2)) pow 2) /
               (&2 * s1' * s2')`;;

let CMP_R8_LOCAL_TOPONOGOV = prove
 (`!w:B->bool. CMP_R8_LOCAL_TOPONOGOV_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[CMP_R8_LOCAL_TOPONOGOV_STATEMENT; apx_shortest] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMPLT_TOPONOGOV_GEN THEN
  EXISTS_TAC `D:B->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]);;

