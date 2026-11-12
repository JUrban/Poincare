(* ========================================================================= *)
(* Unit pc_cmp_affine (comparison-geometry layer CMP): step (E) of the       *)
(* splitting theorem CMP_R3_SPLIT_STATEMENT (pc_cmp_split), with no          *)
(* reference to lines.  Let f be a function on a complete Riemannian         *)
(* manifold that is 1-Lipschitz (on joinable pairs), affine along every      *)
(* geodesic from every point, and has through every point x a unit geodesic  *)
(* c with f(c s) = f(x) + s for abs s <= r (some r > 0 depending on x).      *)
(* Then f(exp_x w) = f(x) + <w, X(x)>_g for a unit field X, f is smooth in   *)
(* every chart, its Hessian vanishes, and X is parallel (p2b_parallel_on).   *)
(* Proof: the first-variation barrier of d(c(-r), .) at x (CMPFV_BARRIER)    *)
(* bounds the directional rate of f by <w, c'(0)>; homogeneity along the     *)
(* geodesics gives equality.  Smoothness comes from the local inverse of exp *)
(* (CMPH_EXP_CHART_NBHD).  Along chart curves of geodesics F'' = 0, so D2 F  *)
(* = dF(Gamma); with metric compatibility the representatives G^-1 grad F    *)
(* are parallel.                                                             *)
(* ========================================================================= *)

needs "src/pc_cmp_fvar.ml";;
needs "src/pc_cmp_busemann.ml";;
needs "src/pc_p2b_splitreq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The linear formula at a point.  If f is 1-Lipschitz, affine along the     *)
(* geodesics from x, and f(exp_x(-r u)) = f(x) - r for a unit u, then        *)
(* f(exp_x w) = f(x) + <w,u>_g for every w.                                  *)
(* ========================================================================= *)

let CMPAF_DERIV_RIGHT = prove
 (`!D D' u s.
        (D has_real_derivative D') (atreal u within s)
        ==> !e. &0 < e
                ==> ?d. &0 < d /\
                        !h. &0 < h /\ h < d /\ (u + h) IN s
                            ==> D(u + h) <= D u + (D' + e) * h`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL; REALLIM_WITHINREAL] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u + h:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = ((D:real->real)(u + h) - D u) / ((u + h) - u)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(D:real->real)(u + h) = D u + q * h` SUBST1_TAC THENL
   [EXPAND_TAC "q" THEN UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `q < D' + e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q * h < (D' + e) * h` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

(* The geodesics from a point of a complete manifold. *)

let CMPAF_GEO_ALL = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ x IN topspace top
        ==> mfd_exp_dom (top,atlas) g x = (:real^N) /\
            mfd_geo_maxint (top,atlas) g x v = (:real) /\
            mfd_geodesic (top,atlas) g (mfd_geo (top,atlas) g x v) (:real) /\
            mfd_geo (top,atlas) g x v (&0) = x /\
            mfd_vel atlas (mfd_geo (top,atlas) g x v) (&0) = v /\
            (!t. mfd_exp (top,atlas) g x (t % v) = mfd_geo (top,atlas) g x v t) /\
            (!t. mfd_geo (top,atlas) g x v t IN topspace top) /\
            (!s t. mfd_joinable (top,atlas) (mfd_geo (top,atlas) g x v s)
                                            (mfd_geo (top,atlas) g x v t) /\
                   mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x v s)
                            (mfd_geo (top,atlas) g x v t) <= abs(t - s) * mfd_tnorm g x v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `!v. mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v = (:real)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) x = (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOH_GEO_COMPLETE_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!s. mfd_tnorm (g:A->real^N^N) ((sigma:real->A) s) (mfd_vel atlas sigma s) =
                    mfd_tnorm g x v` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `sigma:real->A`; `(:real)`; `s:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN MESON_TAC[];
    GEN_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `(:real)`] THEN ASM_REWRITE_TAC[IN_UNIV];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `sigma:real->A`; `(:real)`; `s:real`; `t:real`]
      GEOH_GEO_SEG_DIST) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN MESON_TAC[]]);;

(* One half of the linear formula: the first-variation barrier of           *)
(* d(q, .), q = exp_x(-r u) at distance r, bounds the rate of f along        *)
(* exp_x(t w) at t = 0 by <w,u>.                                            *)

let CMPAF_ONE_SIDE = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) (x:A) u r w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y z. mfd_joinable (top,atlas) y z
               ==> abs(f y - f z) <= mfd_dist (top,atlas) g y z) /\
        (!v t. f(mfd_exp (top,atlas) g x (t % v)) =
               f x + t * (f(mfd_exp (top,atlas) g x v) - f x)) /\
        x IN topspace top /\ &0 < r /\ mfd_tnorm g x u = &1 /\
        f(mfd_exp (top,atlas) g x ((--r) % u)) = f x - r
        ==> f(mfd_exp (top,atlas) g x w) - f x <= w dot (g x ** u)`,
  INTRO_TAC "!top atlas g f x u r w; haus smooth riem comp lip aff xtop rpos unit fq" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] CMPAF_GEO_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `c = mfd_geo (top,atlas) (g:A->real^N^N) x u` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dom") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "c0")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cexp")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cseg")))))))) THEN
  ABBREV_TAC `q = mfd_exp (top,atlas) (g:A->real^N^N) x ((--r) % u)` THEN
  SUBGOAL_THEN `(c:real->A)(--r) = q` (LABEL_TAC "cq") THENL
   [EXPAND_TAC "q" THEN USE_THEN "cexp" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x q /\
                mfd_dist (top,atlas) (g:A->real^N^N) x q <= r` STRIP_ASSUME_TAC THENL
   [USE_THEN "cseg" (MP_TAC o SPECL [`&0`; `--r:real`]) THEN
    USE_THEN "c0" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "cq" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "unit" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_SUB_RZERO; REAL_ABS_NEG] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x q = r` (LABEL_TAC "dxq") THENL
   [USE_THEN "lip" (MP_TAC o SPECL [`x:A`; `q:A`]) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "fq" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^N^N) x q <= r` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) x ((--r) % u) = r` (LABEL_TAC "tn") THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 th))]) THEN
    USE_THEN "unit" (fun th -> REWRITE_TAC[th; REAL_ABS_NEG; REAL_MUL_RID]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `w:real^N`] CMPAF_GEO_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x w` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ggeo") (CONJUNCTS_THEN2 (LABEL_TAC "g0")
    (CONJUNCTS_THEN2 (LABEL_TAC "gvel") (CONJUNCTS_THEN2 (LABEL_TAC "gexp")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gseg")))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `(:real)`; `&0`; `&1`]
    MFD_GEODESIC_C1_CURVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_UNIV; REAL_POS]; ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "velw")
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `mfd_velocity atlas (gam:real->A) (&0) (&1) (&0) = w:real^N` (LABEL_TAC "v0") THENL
   [USE_THEN "velw" (MP_TAC o SPEC `&0`) THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_POS] THEN
    DISCH_THEN SUBST1_TAC THEN USE_THEN "gvel" ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `q:A`; `gam:real->A`; `&0`; `&1`; `&0`; `(--r) % u:real^N`]
    CMPFV_BARRIER) THEN
  USE_THEN "g0" (fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL
   [USE_THEN "tn" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "dxq" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_POS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `phi:A->real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `--(mfd_velocity atlas (gam:real->A) (&0) (&1) (&0) dot
       ((g:A->real^N^N) x ** ((--r) % u))) / mfd_tnorm g x ((--r) % u) =
    w dot (g x ** u)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [USE_THEN "v0" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "tn" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN
    UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC CMPB_LE_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CMPAF_DERIV_RIGHT) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d2"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `gam:real->A`; `(:real)`; `W:A->bool`; `&0`]
    GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL
   [USE_THEN "ggeo" (MP_TAC o MATCH_MP GEOL_GEODESIC_BASIC) THEN
    USE_THEN "g0" (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[REAL_OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d1"))) THEN
  ABBREV_TAC `h = min (min d1 d2) (&1) / &2` THEN
  SUBGOAL_THEN `&0 < h /\ h < d1 /\ h < d2 /\ h <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "d1" (MP_TAC o SPEC `h:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "d2" (MP_TAC o SPEC `h:real`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL; REAL_ADD_LID] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LID] THEN USE_THEN "g0" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x ((gam:real->A) h)`
  ASSUME_TAC THENL
   [USE_THEN "gseg" (MP_TAC o SPECL [`&0`; `h:real`]) THEN
    USE_THEN "g0" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (q:A) ((gam:real->A) h)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `x:A` THEN
    ASM_MESON_TAC[MFD_JOINABLE_SYM];
    ALL_TAC] THEN
  USE_THEN "lip" (MP_TAC o SPECL [`q:A`; `(gam:real->A) h`]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) q x = r` ASSUME_TAC THENL
   [USE_THEN "dxq" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC MFD_DIST_SYM THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->real)((gam:real->A) h) =
                f x + h * (f(mfd_exp (top,atlas) (g:A->real^N^N) x w) - f x)` ASSUME_TAC THENL
   [USE_THEN "gexp" (fun th -> REWRITE_TAC[GSYM th]) THEN USE_THEN "aff" MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) q ((gam:real->A) h) <= phi(gam h)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f(mfd_exp (top,atlas) (g:A->real^N^N) x w) - (f:A->real) x) * h <=
                (w dot (g x ** u) + e) * h` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ]);;

let CMPAF_LINEAR = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) (x:A) u r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y z. mfd_joinable (top,atlas) y z
               ==> abs(f y - f z) <= mfd_dist (top,atlas) g y z) /\
        (!v t. f(mfd_exp (top,atlas) g x (t % v)) =
               f x + t * (f(mfd_exp (top,atlas) g x v) - f x)) /\
        x IN topspace top /\ &0 < r /\ mfd_tnorm g x u = &1 /\
        f(mfd_exp (top,atlas) g x ((--r) % u)) = f x - r
        ==> !w. f(mfd_exp (top,atlas) g x w) = f x + w dot (g x ** u)`,
  INTRO_TAC "!top atlas g f x u r; haus smooth riem comp lip aff xtop rpos unit fq" THEN
  X_GEN_TAC `w:real^N` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `x:A`; `u:real^N`; `r:real`; `w:real^N`]
    CMPAF_ONE_SIDE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `x:A`; `u:real^N`; `r:real`; `--w:real^N`]
    CMPAF_ONE_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f:A->real)(mfd_exp (top,atlas) (g:A->real^N^N) x (--w)) =
                f x - (f(mfd_exp (top,atlas) g x w) - f x)` SUBST1_TAC THENL
   [USE_THEN "aff" (MP_TAC o SPECL [`w:real^N`; `--(&1)`]) THEN
    REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DOT_LNEG] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The field X.  Under the hypotheses of (E), every point x has a unit       *)
(* vector X(x) with f(exp_x w) = f(x) + <w, X(x)>_g for all w.               *)
(* ========================================================================= *)

let CMPAF_FIELD = prove
 (`!top atlas (g:A->real^N^N) (f:A->real).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y z. mfd_joinable (top,atlas) y z
               ==> abs(f y - f z) <= mfd_dist (top,atlas) g y z) /\
        (!x v t. x IN topspace top
                 ==> f(mfd_exp (top,atlas) g x (t % v)) =
                     f x + t * (f(mfd_exp (top,atlas) g x v) - f x)) /\
        (!x. x IN topspace top
             ==> ?u r. &0 < r /\ mfd_tnorm g x u = &1 /\
                       !s. abs s <= r ==> f(mfd_geo (top,atlas) g x u s) = f x + s)
        ==> ?X. !x. x IN topspace top
                    ==> mfd_tnorm g x (X x) = &1 /\
                        !w. f(mfd_exp (top,atlas) g x w) = f x + w dot (g x ** X x)`,
  INTRO_TAC "!top atlas g f; haus smooth riem comp lip aff line" THEN
  REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  USE_THEN "line" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN topspace top`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPAF_LINEAR THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN USE_THEN "aff" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] CMPAF_GEO_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(funpow 5 CONJUNCT2 th)]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--r:real` o check (fun th ->
    can (find_term ((=) `r:real`)) (concl th) && is_forall (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_sub]);;

(* ========================================================================= *)
(* Smoothness.  If f(exp_q w) = f(q) + w.b for all w, then f is smooth near  *)
(* q in the preferred chart (f = f(q) + (E Fi).b with the local inverse Fi   *)
(* of exp_q; CMPH_EXP_CHART_NBHD); if this holds at every point, f is smooth *)
(* in every chart.                                                           *)
(* ========================================================================= *)

let CMPAF_LOCAL_REP = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) (q:A) b.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ q IN topspace top /\
        (!w. f(mfd_exp (top,atlas) g q w) = f q + w dot b)
        ==> ?V. open V /\ SND(chart_at atlas q) q IN V /\
                V SUBSET IMAGE (SND(chart_at atlas q)) (FST(chart_at atlas q)) /\
                smooth_map_on V (\z. lift(f(chart_inv (chart_at atlas q) z)))`,
  INTRO_TAC "!top atlas g f q b; haus smooth riem comp qtop form" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[GSYM mfd_orthonormal_frame] THEN
  DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) q = (:real^N)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `vec 0:real^N`] CMPAF_GEO_ALL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `E:real^N^N`; `vec 0:real^N`; `(:real^N)`; `q:A`]
    CMPH_EXP_CHART_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; OPEN_UNIV; IN_UNIV] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`] MFD_EXP_DIFFERENTIAL_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`] MFD_EXP_DOM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (q:A)` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `Fi:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "c" THEN ASM_MESON_TAC[CHART_AT]; ALL_TAC] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(\z. lift((f:A->real) q) + (\v. lift(((E:real^N^N) ** v) dot b)) ((Fi:real^N->real^N) z))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z IN FST c /\
                  SND c (chart_inv c z) = (z:real^N)` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `chart_inv (c:(A->bool)#(A->real^N)) z` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Fi:real^N->real^N`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) =
                  f q + ((E:real^N^N) ** (Fi:real^N->real^N) z) dot b`
    (fun th -> REWRITE_TAC[th; LIFT_ADD]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  SUBGOAL_THEN
   `(\z. lift(((E:real^N^N) ** (Fi:real^N->real^N) z) dot b)) =
    (\v. lift((E ** v) dot b)) o Fi`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[linear; MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
              DOT_LADD; DOT_LMUL; LIFT_ADD; LIFT_CMUL]);;

let CMPAF_CHART_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) (X:A->real^N) c.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!x w. x IN topspace top
               ==> f(mfd_exp (top,atlas) g x w) = f x + w dot (g x ** X x)) /\
        c IN atlas
        ==> smooth_map_on (IMAGE (SND c) (FST c)) (\y. lift(f(chart_inv c y)))`,
  INTRO_TAC "!top atlas g f X c; haus smooth riem comp form cat" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "copen") (CONJUNCTS_THEN2 (LABEL_TAC "iopen")
    (CONJUNCTS_THEN2 (LABEL_TAC "inv1") (LABEL_TAC "inv2")))) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  ABBREV_TAC `P = chart_inv (c:(A->bool)#(A->real^N)) y0` THEN
  SUBGOAL_THEN `(P:A) IN FST (c:(A->bool)#(A->real^N)) /\ SND c P = (y0:real^N)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN USE_THEN "inv2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(P:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `P:A`; `(g:A->real^N^N) P ** (X:A->real^N) P`]
    CMPAF_LOCAL_REP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `P:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c' = chart_at (atlas:((A->bool)#(A->real^N))->bool) (P:A)` THEN
  STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "copen'") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inv1'") (LABEL_TAC "inv2'")))) THEN
  SUBGOAL_THEN
   `open (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST c')) /\
    smooth_map_on (IMAGE (SND c) (FST c INTER FST c')) (chart_trans c c')`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`]
        CHART_TRANS_SMOOTH) THEN
      ASM_REWRITE_TAC[PAIR]];
    ALL_TAC] THEN
  EXISTS_TAC `{y | y IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST c') /\
                   chart_trans c c' y IN (V:real^N->bool)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `P:A` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[chart_trans] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(\z. lift((f:A->real)(chart_inv (c':(A->bool)#(A->real^N)) z))) o
              chart_trans (c:(A->bool)#(A->real^N)) c'` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM; chart_trans; IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x':A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N)))
                  (FST c INTER FST (c':(A->bool)#(A->real^N)))` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Geodesic chart curves.  In a chart c at P, the geodesic from P whose      *)
(* chart velocity is z gives a chart curve sigma with sigma' = v, v' =       *)
(* -Gamma(v,v), v(0) = z.  Along it F = f o chart_inv c is affine, so dF(y)  *)
(* z = <w, X(P)>_g (w the preferred-chart form of z) and D2 F(y)(z,z) =      *)
(* dF(y)(Gamma(y)(z,z)).                                                     *)
(* ========================================================================= *)

let CMPAF_VCHAIN = prove
 (`!(Fc:real^N->real^M) Fc' (sig:real^1->real^N) v t.
        (sig has_vector_derivative v) (at t) /\ (Fc has_derivative Fc') (at (sig t))
        ==> ((\s. Fc(sig s)) has_vector_derivative Fc' v) (at t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sig:real^1->real^N`; `Fc:real^N->real^M`; `\x:real^1. drop x % (v:real^N)`;
                 `Fc':real^N->real^M`; `t:real^1`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  SUBGOAL_THEN `linear (Fc':real^N->real^M)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_CMUL]);;

let CMPAF_GEO_CHART = prove
 (`!top atlas (g:A->real^N^N) c (P:A) z.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        c IN atlas /\ P IN FST c
        ==> ?v d. &0 < d /\ v(&0) = z /\
                  !t. abs t < d
                      ==> mfd_geo (top,atlas) g P (chart_jac c (chart_at atlas P) P z) t
                            IN FST c /\
                          ((\s. SND c (mfd_geo (top,atlas) g P
                                         (chart_jac c (chart_at atlas P) P z) (drop s)))
                           has_vector_derivative v t) (at (lift t)) /\
                          ((\s. v(drop s)) has_vector_derivative
                           --(christoffel (metric_local atlas c g)
                                (SND c (mfd_geo (top,atlas) g P
                                          (chart_jac c (chart_at atlas P) P z) t))
                                (v t) (v t))) (at (lift t))`,
  INTRO_TAC "!top atlas g c P z; haus smooth riem comp cat Pc" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(P:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `P:A`;
                 `chart_jac (c:(A->bool)#(A->real^N)) (chart_at atlas (P:A)) P z`]
    CMPAF_GEO_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `w = chart_jac (c:(A->bool)#(A->real^N)) (chart_at atlas (P:A)) P z` THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) P w` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `(:real)`; `c:(A->bool)#(A->real^N)`]
    GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real->real^N` (LABEL_TAC "vv")) THEN
  MP_TAC(ISPECL [`top:A topology`; `gam:real->A`; `(:real)`;
                 `FST(c:(A->bool)#(A->real^N))`; `&0`] GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GEOL_GEODESIC_BASIC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "mfd_geodesic"
      with Failure _ -> false)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV; REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`v:real->real^N`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gam:real->A`; `(:real)`; `c:(A->bool)#(A->real^N)`;
                   `(v:real->real^N)(&0)`; `&0`] GEOL_CHART_VEL_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_UNIV] THEN
      USE_THEN "vv" (MP_TAC o SPEC `&0`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "w" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (P:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (P:A))`; `P:A`]
      CHART_JAC_INVERSE) THEN
    REWRITE_TAC[PAIR] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `P:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o C AP_THM `z:real^N`) THEN REWRITE_TAC[o_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gam:real->A) t IN FST (c:(A->bool)#(A->real^N))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "vv" (fun th -> ACCEPT_TAC(MATCH_MP th
    (ASSUME `(gam:real->A) t IN FST (c:(A->bool)#(A->real^N))`))));;

let CMPAF_DF_HESS = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) (X:A->real^N) c y z.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!x w. x IN topspace top
               ==> f(mfd_exp (top,atlas) g x w) = f x + w dot (g x ** X x)) /\
        c IN atlas /\ y IN IMAGE (SND c) (FST c)
        ==> frechet_derivative (\y. lift(f(chart_inv c y))) (at y) z =
            lift(chart_jac c (chart_at atlas (chart_inv c y)) (chart_inv c y) z dot
                 (g(chart_inv c y) ** X(chart_inv c y))) /\
            frechet_derivative
              (\y'. frechet_derivative (\y. lift(f(chart_inv c y))) (at y') z) (at y) z =
            frechet_derivative (\y. lift(f(chart_inv c y))) (at y)
              (christoffel (metric_local atlas c g) y z z)`,
  INTRO_TAC "!top atlas g f X c y z; haus smooth riem comp form cat yim" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inv1") (LABEL_TAC "inv2")))) THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                  (\y. lift((f:A->real)(chart_inv c y)))` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPAF_CHART_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `X:A->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Fc = \y:real^N. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))` THEN
  ABBREV_TAC `U = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  ABBREV_TAC `P = chart_inv (c:(A->bool)#(A->real^N)) y` THEN
  SUBGOAL_THEN `(P:A) IN FST (c:(A->bool)#(A->real^N)) /\ SND c P = (y:real^N)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN USE_THEN "inv2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(P:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `P:A`; `z:real^N`]
    CMPAF_GEO_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `P:A`;
                 `chart_jac (c:(A->bool)#(A->real^N)) (chart_at atlas (P:A)) P z`]
    CMPAF_GEO_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `w = chart_jac (c:(A->bool)#(A->real^N)) (chart_at atlas (P:A)) P z` THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) P w` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "g0")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gexp")
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real->real^N` (X_CHOOSE_THEN `d:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "v0") (LABEL_TAC "loc"))))) THEN
  ABBREV_TAC `alpha = (w:real^N) dot ((g:A->real^N^N) P ** (X:A->real^N) P)` THEN
  SUBGOAL_THEN `!t. abs t < d
                    ==> (Fc:real^N->real^1)(SND (c:(A->bool)#(A->real^N)) ((gam:real->A) t)) =
                        lift((f:A->real) P + t * alpha)`
  (LABEL_TAC "aff") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXPAND_TAC "Fc" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c ((gam:real->A) t)) = gam t`
    SUBST1_TAC THENL
     [USE_THEN "inv1" MATCH_MP_TAC THEN
      USE_THEN "loc" (fun th -> ACCEPT_TAC(CONJUNCT1(MATCH_MP (SPEC `t:real` th)
        (ASSUME `abs t < d`))));
      ALL_TAC] THEN
    USE_THEN "gexp" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "form" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(P:A) IN topspace top`)]) THEN
    EXPAND_TAC "alpha" THEN REWRITE_TAC[DOT_LMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. abs t < d
                    ==> frechet_derivative (Fc:real^N->real^1)
                          (at (SND (c:(A->bool)#(A->real^N)) ((gam:real->A) t)))
                          ((v:real->real^N) t) = lift alpha`
  (LABEL_TAC "dconst") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> STRIP_ASSUME_TAC(MATCH_MP (SPEC `t:real` th)
      (ASSUME `abs t < d`))) THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\s. (Fc:real^N->real^1)(SND (c:(A->bool)#(A->real^N)) ((gam:real->A)(drop s)))` THEN
    EXISTS_TAC `lift t` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`Fc:real^N->real^1`;
                     `frechet_derivative (Fc:real^N->real^1)
                        (at (SND (c:(A->bool)#(A->real^N)) ((gam:real->A) t)))`;
                     `\s. SND (c:(A->bool)#(A->real^N)) ((gam:real->A)(drop s))`;
                     `(v:real->real^N) t`; `lift t`] CMPAF_VCHAIN) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `Fc:real^N->real^1`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "U" THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `lift o (\t. (f:A->real) P + t * alpha) o drop` THEN
    EXISTS_TAC `d - abs t` THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN DISCH_TAC THEN
      REWRITE_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN USE_THEN "aff" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
      MP_TAC(ISPECL [`\t:real. (f:A->real) P`; `&0`; `\t:real. t * alpha`; `alpha:real`;
                     `atreal t`] HAS_REAL_DERIVATIVE_ADD) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`\x:real. x`; `&1`; `alpha:real`; `t:real`]
        HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "loc" (MP_TAC o SPEC `&0`) THEN REWRITE_TAC[REAL_ABS_0] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "g0" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "v0" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [USE_THEN "dconst" (MP_TAC o SPEC `&0`) THEN
    USE_THEN "g0" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "v0" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[REAL_ABS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\r. frechet_derivative (Fc:real^N->real^1)
            (at (SND (c:(A->bool)#(A->real^N)) ((gam:real->A)(drop r))))
            ((v:real->real^N)(drop r))) has_vector_derivative vec 0) (at (lift(&0)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `(\r:real^1. lift alpha)` THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
    X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP; REAL_SUB_RZERO] THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "dconst" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `Fc:real^N->real^1`;
                 `\s. SND (c:(A->bool)#(A->real^N)) ((gam:real->A)(drop s))`;
                 `\s. (v:real->real^N)(drop s)`; `z:real^N`;
                 `--(christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                       y z z)`;
                 `lift(&0)`] GEOL_FRECHET_ALONG) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  USE_THEN "g0" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "v0" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (Fc:real^N->real^1) (at y))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP VECTOR_DERIVATIVE_UNIQUE_AT o CONJ
    (ASSUME `((\r. frechet_derivative (Fc:real^N->real^1)
            (at (SND (c:(A->bool)#(A->real^N)) ((gam:real->A)(drop r))))
            ((v:real->real^N)(drop r))) has_vector_derivative vec 0) (at (lift(&0)))`)) THEN
  ASM_SIMP_TAC[LINEAR_NEG] THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC(VECTOR_ARITH `vec 0 = a + --b ==> a:real^1 = b`) THEN
                       ACCEPT_TAC th));;

(* ========================================================================= *)
(* The chart identities.  In every chart c, with F = f o chart_inv c, G the  *)
(* local metric and X_c = mfd_vrep atlas X c: dF(y) z = <z, G(y) X_c(y)> and *)
(* D2 F(y)(w,z) = dF(y)(Gamma(y)(w,z)).                                      *)
(* ========================================================================= *)

let CMPAF_DF_METRIC = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) (X:A->real^N) c y z.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!x w. x IN topspace top
               ==> f(mfd_exp (top,atlas) g x w) = f x + w dot (g x ** X x)) /\
        c IN atlas /\ y IN IMAGE (SND c) (FST c)
        ==> frechet_derivative (\y. lift(f(chart_inv c y))) (at y) z =
            lift(z dot (metric_local atlas c g y ** mfd_vrep atlas X c y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `X:A->real^N`; `c:(A->bool)#(A->real^N)`;
                 `y:real^N`; `z:real^N`] CMPAF_DF_HESS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN AP_TERM_TAC THEN
  REWRITE_TAC[metric_local; mfd_vrep] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `P = chart_inv (c:(A->bool)#(A->real^N)) y` THEN
  SUBGOAL_THEN `(P:A) IN FST (c:(A->bool)#(A->real^N))` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(P:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `P:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `linear (chart_jac (c:(A->bool)#(A->real^N)) (chart_at atlas (P:A)) P) /\
    !v. chart_jac c (chart_at atlas P) P (chart_jac (chart_at atlas P) c P v) = v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (P:A))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (P:A))`; `P:A`]
        CHART_JAC_LINEAR) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (P:A))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (P:A))`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `P:A`]
        CHART_JAC_INVERSE) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

(* Second derivatives of smooth maps are bilinear (the first half of the   *)
(* proof of LRG_SECOND_DERIVATIVE_SYM, which does not export it).          *)

let CMPAF_D2_BILINEAR = prove
 (`!s (f:real^M->real^P) y.
        open s /\ smooth_map_on s f /\ y IN s
        ==> bilinear (\u v. frechet_derivative
                              (\z. frechet_derivative f (at z) v) (at y) u)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bilinear] THEN CONJ_TAC THEN X_GEN_TAC `w:real^M` THENL
   [SUBGOAL_THEN
     `!c. frechet_derivative (\z. frechet_derivative (f:real^M->real^P) (at z) c)
                             (at y) =
          (\u. vsum (1..dimindex(:M))
                 (\i. c$i % frechet_derivative
                              (\z. frechet_derivative f (at z) (basis i))
                              (at y) u))`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MP_TAC(ISPECL [`\z. frechet_derivative (f:real^M->real^P) (at z)`;
                     `s:real^M->bool`; `y:real^M`; `c:real^M`]
             LRG_HAS_DERIVATIVE_LINFAM_CONST) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
        MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
        MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real^P`; `z:real^M`;
                       `c:real^M`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
        ASM_SIMP_TAC[];
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real^P`; `y:real^M`;
                       `basis i:real^M`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
        ASM_SIMP_TAC[]];
      BETA_TAC THEN REWRITE_TAC[LRG_LINEAR_VSUM_COMPONENTS]];
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real^P`; `y:real^M`;
                   `w:real^M`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[]]);;

(* Polarization: a symmetric bilinear B agreeing with L(h(u,u)) on the     *)
(* diagonal (h symmetric bilinear, L linear) agrees everywhere.            *)

let CMPAF_POLAR = prove
 (`!(B:real^N->real^N->real^M) (L:real^N->real^M) (h:real^N->real^N->real^N).
        bilinear B /\ (!u v. B u v = B v u) /\ linear L /\ bilinear h /\
        (!u v. h u v = h v u) /\ (!u. B u u = L(h u u))
        ==> !u v. B u v = L(h u v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `u + v:real^N` (ASSUME `!u. (B:real^N->real^N->real^M) u u =
                                          (L:real^N->real^M)(h u u)`)) THEN
  MP_TAC(SPEC `u:real^N` (ASSUME `!u. (B:real^N->real^N->real^M) u u =
                                      (L:real^N->real^M)(h u u)`)) THEN
  MP_TAC(SPEC `v:real^N` (ASSUME `!u. (B:real^N->real^N->real^M) u u =
                                      (L:real^N->real^M)(h u u)`)) THEN
  MP_TAC(SPECL [`u:real^N`; `v:real^N`]
    (ASSUME `!u v. (B:real^N->real^N->real^M) u v = B v u`)) THEN
  MP_TAC(AP_TERM `L:real^N->real^M` (SPECL [`v:real^N`; `u:real^N`]
    (ASSUME `!u v. (h:real^N->real^N->real^N) u v = h v u`))) THEN
  SIMP_TAC[ASSUME `bilinear (B:real^N->real^N->real^M)`;
           ASSUME `bilinear (h:real^N->real^N->real^N)`; BILINEAR_LADD; BILINEAR_RADD] THEN
  SIMP_TAC[ASSUME `linear (L:real^N->real^M)`; LINEAR_ADD] THEN
  VECTOR_ARITH_TAC);;

let CMPAF_HESS = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) (X:A->real^N) c y.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!x w. x IN topspace top
               ==> f(mfd_exp (top,atlas) g x w) = f x + w dot (g x ** X x)) /\
        c IN atlas /\ y IN IMAGE (SND c) (FST c)
        ==> !u v. frechet_derivative
                    (\y'. frechet_derivative (\y. lift(f(chart_inv c y))) (at y') v)
                    (at y) u =
                  frechet_derivative (\y. lift(f(chart_inv c y))) (at y)
                    (christoffel (metric_local atlas c g) y u v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                  (\y. lift((f:A->real)(chart_inv c y)))` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPAF_CHART_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `X:A->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                  (metric_local atlas c (g:A->real^N^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\u v. frechet_derivative
             (\y'. frechet_derivative
                     (\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))) (at y') v)
             (at (y:real^N)) u`;
    `frechet_derivative (\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)))
       (at (y:real^N))`;
    `christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)) (y:real^N)`]
    CMPAF_POLAR) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMPAF_D2_BILINEAR THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_SECOND_DERIVATIVE_SYM THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN MATCH_MP_TAC CHRISTOFFEL_SYM THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `X:A->real^N`; `c:(A->bool)#(A->real^N)`;
                   `y:real^N`; `u:real^N`] CMPAF_DF_HESS) THEN
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Local calculus in one chart.  For a metric field G on U and a smooth F    *)
(* with dF(y) z = <z, G(y) V(y)> and D2 F = dF(Gamma), the field V is smooth *)
(* and parallel: DV(y) z + Gamma(y)(z, V(y)) = 0 (metric compatibility       *)
(* through LRG_CHRISTOFFEL_DOT and LRG_MDERIV_SYM).                          *)
(* ========================================================================= *)

let CMPAF_HAS_DERIVATIVE_GDOTV = prove
 (`!(G:real^N->real^N^N) (V:real^N->real^N) y a.
        (vectorize o G) differentiable at y /\ V differentiable at y
        ==> ((\z. lift(a dot (G z ** V z))) has_derivative
             (\w. lift(a dot (mderiv G y w ** V y +
                              G y ** frechet_derivative V (at y) w)))) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`;
                 `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                      (G:real^N->real^N^N)) (at y)`;
                 `(\z. a):real^N->real^N`; `(\w. vec 0):real^N->real^N`;
                 `V:real^N->real^N`; `frechet_derivative (V:real^N->real^N) (at y)`;
                 `y:real^N`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST; GSYM FRECHET_DERIVATIVE_WORKS] THEN
  REWRITE_TAC[mderiv; DOT_LZERO; REAL_ADD_LID]);;

let CMPAF_PARALLEL_LOCAL = prove
 (`!U (G:real^N->real^N^N) (Fc:real^N->real^1) (V:real^N->real^N).
        metric_field U G /\ smooth_map_on U Fc /\ smooth_map_on U V /\
        (!y z. y IN U ==> frechet_derivative Fc (at y) z = lift(z dot (G y ** V y))) /\
        (!y u v. y IN U
                 ==> frechet_derivative (\y'. frechet_derivative Fc (at y') v) (at y) u =
                     frechet_derivative Fc (at y) (christoffel G y u v))
        ==> !y z. y IN U
                  ==> frechet_derivative V (at y) z + christoffel G y z (V y) = vec 0`,
  REPEAT GEN_TAC THEN INTRO_TAC "mf sF sV dF hess" THEN
  X_GEN_TAC `y:real^N` THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `(vectorize o (G:real^N->real^N^N)) differentiable at y` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
  SUBGOAL_THEN `(V:real^N->real^N) differentiable at y` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE]; ALL_TAC] THEN
  ABBREV_TAC `W = frechet_derivative (V:real^N->real^N) (at y) z +
                  christoffel (G:real^N->real^N^N) y z (V y)` THEN
  SUBGOAL_THEN `!a:real^N. a dot ((G:real^N->real^N^N) y ** W) = &0` ASSUME_TAC THENL
   [X_GEN_TAC `a:real^N` THEN
    SUBGOAL_THEN
     `lift(christoffel (G:real^N->real^N^N) y z a dot (G y ** (V:real^N->real^N) y)) =
      lift(a dot (mderiv G y z ** V y + G y ** frechet_derivative V (at y) z))`
    MP_TAC THENL
     [TRANS_TAC EQ_TRANS
       `frechet_derivative (\y'. frechet_derivative (Fc:real^N->real^1) (at y') a) (at y) z` THEN
      CONJ_TAC THENL
       [USE_THEN "hess" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^N) IN U`)]) THEN
        USE_THEN "dF" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^N) IN U`)]);
        ALL_TAC] THEN
      SUBGOAL_THEN
       `frechet_derivative (\y'. frechet_derivative (Fc:real^N->real^1) (at y') a) (at y) =
        frechet_derivative (\y'. lift(a dot ((G:real^N->real^N^N) y' ** (V:real^N->real^N) y')))
          (at y)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN X_GEN_TAC `y':real^N` THEN DISCH_TAC THEN
        USE_THEN "dF" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y':real^N) IN U`)]);
        ALL_TAC] THEN
      MP_TAC(ISPECL [`G:real^N->real^N^N`; `V:real^N->real^N`; `y:real^N`; `a:real^N`]
        CMPAF_HAS_DERIVATIVE_GDOTV) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_EQ; DOT_RADD] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `z:real^N`;
                   `(V:real^N->real^N) y`; `a:real^N`] LRG_CHRISTOFFEL_DOT) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `z:real^N`;
                   `a:real^N`; `(V:real^N->real^N) y`] LRG_CHRISTOFFEL_DOT) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `christoffel (G:real^N->real^N^N) y z a`; `(V:real^N->real^N) y`]
      LRG_METRIC_SYM) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `z:real^N`;
                   `a:real^N`; `(V:real^N->real^N) y`] LRG_MDERIV_SYM) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                   `z:real^N`; `(V:real^N->real^N) y`] LRG_MDERIV_SYM) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `(V:real^N->real^N) y`; `z:real^N`; `a:real^N`] LRG_MDERIV_SYM) THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "W" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_RADD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `W:real^N = vec 0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < W dot ((G:real^N->real^N^N) y ** W)` MP_TAC THENL
   [UNDISCH_TAC `metric_field U (G:real^N->real^N^N)` THEN REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2 o CONJUNCT2) THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[REAL_LT_REFL]]);;

let CMPAF_VREP_SMOOTH = prove
 (`!U (G:real^N->real^N^N) (Fc:real^N->real^1) (V:real^N->real^N).
        metric_field U G /\ smooth_map_on U Fc /\
        (!y z. y IN U ==> frechet_derivative Fc (at y) z = lift(z dot (G y ** V y)))
        ==> smooth_map_on U V`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\y. matrix_inv((G:real^N->real^N^N) y) **
                  vsum(1..dimindex(:N))
                    (\i. drop(frechet_derivative (Fc:real^N->real^1) (at y) (basis i)) %
                         basis i)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `vsum(1..dimindex(:N))
        (\i. drop(frechet_derivative (Fc:real^N->real^1) (at y) (basis i)) % basis i) =
      (G:real^N->real^N^N) y ** (V:real^N->real^N) y`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM BASIS_EXPANSION] THEN
      MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[LIFT_DROP; DOT_BASIS];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
      LRG_METRIC_INVERTIBLE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field];
      ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]];
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\y. drop(frechet_derivative (Fc:real^N->real^1) (at y) (basis i)) %
           (basis i:real^N)) =
      (\x:real^1. drop x % (basis i:real^N)) o (\y. frechet_derivative Fc (at y) (basis i))`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC]]);;

(* ========================================================================= *)
(* The theorem (E).  f 1-Lipschitz on joinable pairs, affine along the       *)
(* geodesics from every point, and with a unit-rate geodesic through every   *)
(* point on an explicit interval [-r,r]: then there is a unit parallel field *)
(* X (p2b_parallel_on) with f(exp_x w) = f(x) + <w, X(x)>_g, f is smooth in  *)
(* every chart and its Hessian D2 F - dF(Gamma) vanishes.                    *)
(* ========================================================================= *)

let CMP_AFFINE_PARALLEL = prove
 (`!top atlas (g:A->real^N^N) (f:A->real).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y z. mfd_joinable (top,atlas) y z
               ==> abs(f y - f z) <= mfd_dist (top,atlas) g y z) /\
        (!x v t. x IN topspace top
                 ==> f(mfd_exp (top,atlas) g x (t % v)) =
                     f x + t * (f(mfd_exp (top,atlas) g x v) - f x)) /\
        (!x. x IN topspace top
             ==> ?u r. &0 < r /\ mfd_tnorm g x u = &1 /\
                       !s. abs s <= r ==> f(mfd_geo (top,atlas) g x u s) = f x + s)
        ==> ?X. p2b_parallel_on atlas g (topspace top) X /\
                (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
                (!x w. x IN topspace top
                       ==> f(mfd_exp (top,atlas) g x w) = f x + w dot (g x ** X x)) /\
                (!c. c IN atlas
                     ==> smooth_map_on (IMAGE (SND c) (FST c))
                           (\y. lift(f(chart_inv c y))) /\
                         !y u v. y IN IMAGE (SND c) (FST c)
                                 ==> frechet_derivative
                                       (\y'. frechet_derivative
                                               (\y. lift(f(chart_inv c y))) (at y') v)
                                       (at y) u =
                                     frechet_derivative (\y. lift(f(chart_inv c y))) (at y)
                                       (christoffel (metric_local atlas c g) y u v))`,
  INTRO_TAC "!top atlas g f; haus smooth riem comp lip aff line" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`] CMPAF_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:A->real^N` (LABEL_TAC "X")) THEN
  EXISTS_TAC `X:A->real^N` THEN
  SUBGOAL_THEN `!x w. x IN topspace top
                      ==> (f:A->real)(mfd_exp (top,atlas) (g:A->real^N^N) x w) =
                          f x + w dot (g x ** (X:A->real^N) x)`
  (LABEL_TAC "form") THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN atlas
        ==> metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c (g:A->real^N^N)) /\
            smooth_map_on (IMAGE (SND c) (FST c)) (\y. lift((f:A->real)(chart_inv c y))) /\
            (!y z. y IN IMAGE (SND c) (FST c)
                   ==> frechet_derivative (\y. lift(f(chart_inv c y))) (at y) z =
                       lift(z dot (metric_local atlas c g y **
                                   mfd_vrep atlas (X:A->real^N) c y))) /\
            (!y u v. y IN IMAGE (SND c) (FST c)
                     ==> frechet_derivative
                           (\y'. frechet_derivative (\y. lift(f(chart_inv c y))) (at y') v)
                           (at y) u =
                         frechet_derivative (\y. lift(f(chart_inv c y))) (at y)
                           (christoffel (metric_local atlas c g) y u v))`
  (LABEL_TAC "chart") THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[riemannian_metric];
      MATCH_MP_TAC CMPAF_CHART_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `g:A->real^N^N`; `X:A->real^N`] THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPAF_DF_METRIC THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `f:A->real`; `X:A->real^N`;
                     `c:(A->bool)#(A->real^N)`; `y:real^N`] CMPAF_HESS) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. c IN atlas ==> FST c INTER topspace top = FST (c:(A->bool)#(A->real^N))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p2b_parallel_on] THEN CONJ_TAC THENL
     [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      USE_THEN "chart" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`))) THEN
      MATCH_MP_TAC CMPAF_VREP_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                            `\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `y:real^N`; `z:real^N`] THEN
      STRIP_TAC THEN RULE_ASSUM_TAC(fun th -> try MATCH_MP (ASSUME
        `!c. c IN atlas ==> FST c INTER topspace top = FST (c:(A->bool)#(A->real^N))`) th
        with Failure _ -> th) THEN
      UNDISCH_TAC `(y:real^N) IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER topspace top)` THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN
      USE_THEN "chart" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`))) THEN
      MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                     `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                     `\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))`;
                     `mfd_vrep atlas (X:A->real^N) (c:(A->bool)#(A->real^N))`]
        CMPAF_PARALLEL_LOCAL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMPAF_VREP_SMOOTH THEN
        MAP_EVERY EXISTS_TAC [`metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                              `\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    USE_THEN "X" (MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(y:A) IN topspace top`)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`] GEOD_TNORM_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `(X:A->real^N) y` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    USE_THEN "form" ACCEPT_TAC;
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    USE_THEN "chart" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`))) THEN
    ASM_REWRITE_TAC[]]);;

