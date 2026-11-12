(* ========================================================================= *)
(* Unit pc_cmp_split (comparison-geometry layer CMP): the splitting theorem  *)
(* CMP_R3_SPLIT in the sec >= 0 form (Toponogov): a complete connected       *)
(* manifold with sec >= 0 containing a line is locally split, with the       *)
(* parallel unit field tangent to the line.  Route: the Busemann functions   *)
(* b1, b2 of the two halves of the line are convex (CMPB_CONVEX), b1 + b2    *)
(* <= 0 vanishes at lam(0), hence everywhere (convexity along the geodesics  *)
(* from lam(0)); so b1 is affine along every geodesic, 1-Lipschitz, and has  *)
(* unit-rate asymptotic geodesics through every point; step (E)              *)
(* (CMP_AFFINE_PARALLEL) gives the parallel field X, and lam is the geodesic *)
(* of X (CMPRG_CORE).                                                        *)
(* ========================================================================= *)

needs "src/pc_cmp_affine.ml";;
needs "src/pc_cmp_reg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Real and linear-algebra helpers.                                          *)
(* ========================================================================= *)

(* A function equal to its chords on every interval is affine. *)

let CMPSP_AFFINE_REAL = prove
 (`!phi:real->real.
        (!a c x. a < c /\ a <= x /\ x <= c
                 ==> phi x = phi a + (x - a) / (c - a) * (phi c - phi a))
        ==> !s. phi s = phi(&0) + s * (phi(&1) - phi(&0))`,
  GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `s:real` THEN
  ASM_CASES_TAC `&0 <= s /\ s <= &1` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `&1`; `s:real`]) THEN
    ASM_REWRITE_TAC[REAL_LT_01; REAL_SUB_RZERO; REAL_DIV_1];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 < s` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `s:real`; `&1`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `&1`; `&0`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s < &0` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* The convexity step of f = b1 + b2 <= 0 with f(0) = 0: the chord on       *)
(* [-1, L] through 0 forces f(L) >= 0.                                      *)

let CMPSP_CONVEX_ZERO_REAL = prove
 (`!A B L. &0 < L /\ A <= &0 /\ B <= &0 /\
           &0 <= A + (&0 - --(&1)) / (L - --(&1)) * (B - A)
           ==> B = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&0 - --(&1)) / (L - --(&1)) * (B - A) = (B - A) / (L + &1)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A * (L + &1) + (B - A)` MP_TAC THENL
   [SUBGOAL_THEN `A * (L + &1) + (B - A) = (A + (B - A) / (L + &1)) * (L + &1)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `A * L <= &0` MP_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC);;

(* Two unit vectors with inner product 1 are equal. *)

let CMPSP_UNIT_EQ = prove
 (`!top atlas (g:A->real^N^N) (x:A) u v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
        mfd_tnorm g x u = &1 /\ mfd_tnorm g x v = &1 /\ u dot (g x ** v) = &1
        ==> u = v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOG_G_SYM_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u - v:real^N`] GEOD_TNORM_EQ_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) x (u - v) pow 2 = &0` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_LSUB; DOT_RSUB] THEN
    MP_TAC(SPEC `u:real^N` (ASSUME `!v. mfd_tnorm (g:A->real^N^N) x v pow 2 =
                                        v dot (g x ** v)`)) THEN
    MP_TAC(SPEC `v:real^N` (ASSUME `!v. mfd_tnorm (g:A->real^N^N) x v pow 2 =
                                        v dot (g x ** v)`)) THEN
    MP_TAC(SPECL [`v:real^N`; `u:real^N`] (ASSUME `!a b. a dot ((g:A->real^N^N) x ** b) =
                                                        b dot (g x ** a)`)) THEN
    REWRITE_TAC[ASSUME `mfd_tnorm (g:A->real^N^N) x u = &1`;
                ASSUME `mfd_tnorm (g:A->real^N^N) x v = &1`;
                ASSUME `u dot ((g:A->real^N^N) x ** v) = &1`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ]]);;

(* ========================================================================= *)
(* A line gives two opposite rays; their Busemann functions                  *)
(* b1, b2 satisfy b1 + b2 = 0 (sec >= 0: convex, <= 0, = 0 at lam(0)), so   *)
(* b1 is affine along every geodesic, 1-Lipschitz, b1(lam t) = t, and every  *)
(* point has a unit-rate geodesic for b1: the hypotheses of step (E).        *)
(* ========================================================================= *)

let CMPSP_LINE_RAYS = prove
 (`!top atlas (g:A->real^N^N) (lam:real->A).
        connected_space top /\ smooth_manifold_atlas top atlas /\
        (!s t. lam s IN topspace top /\ mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s))
        ==> (!x y. x IN topspace top /\ y IN topspace top ==> mfd_joinable (top,atlas) x y) /\
            cmp_ray (top,atlas) g lam /\ cmp_ray (top,atlas) g (\t. lam(--t)) /\
            (!s t. &0 <= s /\ &0 <= t
                   ==> s + t <= mfd_dist (top,atlas) g (lam s) ((\t. lam(--t)) t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN topspace top /\ y IN topspace top
                      ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cmp_ray] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* A function <= 0 on a complete manifold, = 0 at p and convex along the  *)
(* unit geodesics from p vanishes everywhere.                              *)

let CMPSP_CONVEX_ZERO = prove
 (`!top atlas (g:A->real^N^N) (Fn:A->real) (p:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
        (!y. y IN topspace top ==> mfd_joinable (top,atlas) p y) /\
        (!y. y IN topspace top ==> Fn y <= &0) /\ Fn p = &0 /\
        (!u a c x. mfd_tnorm g p u = &1 /\ a < c /\ a <= x /\ x <= c
                   ==> Fn(mfd_geo (top,atlas) g p u x) <=
                       Fn(mfd_geo (top,atlas) g p u a) +
                       (x - a) / (c - a) *
                       (Fn(mfd_geo (top,atlas) g p u c) - Fn(mfd_geo (top,atlas) g p u a)))
        ==> !y. y IN topspace top ==> Fn y = &0`,
  INTRO_TAC "!top atlas g Fn p; haus smooth riem comp ptop join le zero cvx" THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `y:A = p` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `y:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "vy") (K ALL_TAC)))) THEN
  ABBREV_TAC `L = mfd_tnorm (g:A->real^N^N) p v` THEN
  SUBGOAL_THEN `~(v:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(y:A = p)` THEN REWRITE_TAC[] THEN
    USE_THEN "vy" (SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] MFD_EXP_DOM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOD_TNORM_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `v:real^N`] GEOD_TNORM_EQ_0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `v:real^N` (ASSUME `!v. &0 <= mfd_tnorm (g:A->real^N^N) p v`)) THEN
    REWRITE_TAC[ASSUME `mfd_tnorm (g:A->real^N^N) p v = L`;
                ASSUME `~(v:real^N = vec 0)`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u = inv L % (v:real^N)` THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p u = &1 /\ L % u = (v:real^N)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < L ==> abs L = L`; REAL_MUL_LINV; REAL_MUL_RINV;
                 REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) p u` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s0") (CONJUNCTS_THEN2 (LABEL_TAC "stop")
    (CONJUNCTS_THEN2 (LABEL_TAC "sexp") ASSUME_TAC))) THEN
  SUBGOAL_THEN `(sigma:real->A) L = y` ASSUME_TAC THENL
   [USE_THEN "sexp" (SUBST1_TAC o SYM o SPEC `L:real`) THEN
    REWRITE_TAC[ASSUME `L % u = (v:real^N)`] THEN USE_THEN "vy" ACCEPT_TAC;
    ALL_TAC] THEN
  USE_THEN "cvx" (MP_TAC o SPECL [`u:real^N`; `--(&1)`; `L:real`; `&0`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC CMPSP_CONVEX_ZERO_REAL THEN
  MAP_EVERY EXISTS_TAC [`(Fn:A->real)((sigma:real->A)(--(&1)))`; `L:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "le" MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let CMPSP_LINE_BUSEMANN = prove
 (`!top atlas (g:A->real^N^N) (lam:real->A).
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g x u v) /\
        (!s t. lam s IN topspace top /\ mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s))
        ==> (!x. x IN topspace top
                 ==> cmp_busemann (top,atlas) g lam x +
                     cmp_busemann (top,atlas) g (\t. lam(--t)) x = &0) /\
            (!t. cmp_busemann (top,atlas) g lam (lam t) = t)`,
  INTRO_TAC "!top atlas g lam; haus conn smooth riem comp sec line" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `lam:real->A`] CMPSP_LINE_RAYS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "join") (CONJUNCTS_THEN2 (LABEL_TAC "r1")
    (CONJUNCTS_THEN2 (LABEL_TAC "r2") (LABEL_TAC "opp")))) THEN
  ABBREV_TAC `B1 = cmp_busemann (top,atlas) (g:A->real^N^N) lam` THEN
  ABBREV_TAC `B2 = cmp_busemann (top,atlas) (g:A->real^N^N) (\t. (lam:real->A)(--t))` THEN
  ABBREV_TAC `p = (lam:real->A)(&0)` THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN topspace top ==> (B1:A->real) y + (B2:A->real) y <= &0`
  (LABEL_TAC "le") THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["B1"; "B2"] THEN
    MATCH_MP_TAC CMPB_OPPOSITE_SUM THEN ASM_REWRITE_TAC[REAL_NEG_0] THEN
    USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B1:A->real) p = &0 /\ (B2:A->real) p = &0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["B1"; "B2"; "p"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPB_ON_RAY THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `\t. (lam:real->A)(--t)`; `&0`] CMPB_ON_RAY) THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; REAL_NEG_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN topspace top ==> (B1:A->real) y + (B2:A->real) y = &0`
  (LABEL_TAC "zero") THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `\y. (B1:A->real) y + (B2:A->real) y`; `p:A`]
      CMPSP_CONVEX_ZERO) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `a:real`; `c:real`; `x:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `lam:real->A`; `p:A`; `u:real^N`;
                   `a:real`; `c:real`; `x:real`] CMPB_CONVEX) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `\t. (lam:real->A)(--t)`; `p:A`; `u:real^N`;
                   `a:real`; `c:real`; `x:real`] CMPB_CONVEX) THEN
    ASM_REWRITE_TAC[REAL_NEG_0] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) p p` ASSUME_TAC THENL
     [USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN
  ASM_CASES_TAC `&0 <= t` THENL
   [EXPAND_TAC "B1" THEN MATCH_MP_TAC CMPB_ON_RAY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(B2:A->real)((lam:real->A) t) = --t` ASSUME_TAC THENL
   [EXPAND_TAC "B2" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `\t. (lam:real->A)(--t)`; `--t`] CMPB_ON_RAY) THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(lam:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "zero" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(lam:real->A) t IN topspace top`))) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* b1 is affine along every unit geodesic. *)

let CMPSP_LINE_GEO_AFFINE = prove
 (`!top atlas (g:A->real^N^N) (lam:real->A).
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g x u v) /\
        (!s t. lam s IN topspace top /\ mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s))
        ==> !p u. p IN topspace top /\ mfd_tnorm g p u = &1
                  ==> !s. cmp_busemann (top,atlas) g lam (mfd_geo (top,atlas) g p u s) =
                          cmp_busemann (top,atlas) g lam p +
                          s * (cmp_busemann (top,atlas) g lam (mfd_geo (top,atlas) g p u (&1)) -
                               cmp_busemann (top,atlas) g lam p)`,
  INTRO_TAC "!top atlas g lam; haus conn smooth riem comp sec line" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `lam:real->A`] CMPSP_LINE_RAYS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "join") (CONJUNCTS_THEN2 (LABEL_TAC "r1")
    (CONJUNCTS_THEN2 (LABEL_TAC "r2") ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `lam:real->A`] CMPSP_LINE_BUSEMANN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "zero") ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`p:A`; `u:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) p ((lam:real->A)(&0))`
  ASSUME_TAC THENL [USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) p u` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s0") (CONJUNCTS_THEN2 (LABEL_TAC "stop")
    ASSUME_TAC)) THEN
  ABBREV_TAC `B1 = cmp_busemann (top,atlas) (g:A->real^N^N) lam` THEN
  ABBREV_TAC `B2 = cmp_busemann (top,atlas) (g:A->real^N^N) (\t. (lam:real->A)(--t))` THEN
  SUBGOAL_THEN `!s. (B2:A->real)((sigma:real->A) s) = --((B1:A->real)(sigma s))`
  (LABEL_TAC "neg") THENL
   [GEN_TAC THEN
    USE_THEN "stop" (fun st -> USE_THEN "zero" (fun z ->
      MP_TAC(MATCH_MP z (SPEC `s:real` st)))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `\s. (B1:A->real)((sigma:real->A) s)` CMPSP_AFFINE_REAL) THEN
  REWRITE_TAC[] THEN USE_THEN "s0" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `c:real`; `x:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `lam:real->A`; `p:A`; `u:real^N`;
                 `a:real`; `c:real`; `x:real`] CMPB_CONVEX) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\t. (lam:real->A)(--t)`; `p:A`; `u:real^N`;
                 `a:real`; `c:real`; `x:real`] CMPB_CONVEX) THEN
  ASM_REWRITE_TAC[REAL_NEG_0] THEN REAL_ARITH_TAC);;

(* The hypotheses of step (E) for f = b1. *)

let CMPSP_LINE_E_HYPS = prove
 (`!top atlas (g:A->real^N^N) (lam:real->A).
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g x u v) /\
        (!s t. lam s IN topspace top /\ mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s))
        ==> (!y z. mfd_joinable (top,atlas) y z
                   ==> abs(cmp_busemann (top,atlas) g lam y -
                           cmp_busemann (top,atlas) g lam z) <=
                       mfd_dist (top,atlas) g y z) /\
            (!x v t. x IN topspace top
                     ==> cmp_busemann (top,atlas) g lam (mfd_exp (top,atlas) g x (t % v)) =
                         cmp_busemann (top,atlas) g lam x +
                         t * (cmp_busemann (top,atlas) g lam (mfd_exp (top,atlas) g x v) -
                              cmp_busemann (top,atlas) g lam x)) /\
            (!x. x IN topspace top
                 ==> ?u r. &0 < r /\ mfd_tnorm g x u = &1 /\
                           !s. abs s <= r
                               ==> cmp_busemann (top,atlas) g lam
                                     (mfd_geo (top,atlas) g x u s) =
                                   cmp_busemann (top,atlas) g lam x + s)`,
  INTRO_TAC "!top atlas g lam; haus conn smooth riem comp sec line" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `lam:real->A`] CMPSP_LINE_RAYS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "join") (CONJUNCTS_THEN2 (LABEL_TAC "r1")
    (CONJUNCTS_THEN2 (LABEL_TAC "r2") ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `lam:real->A`] CMPSP_LINE_GEO_AFFINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_THEN(LABEL_TAC "aff") THEN
  ABBREV_TAC `B1 = cmp_busemann (top,atlas) (g:A->real^N^N) lam` THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "B1" THEN MATCH_MP_TAC CMPB_LIPSCHITZ THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "join" MATCH_MP_TAC THEN
    ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `v:real^N`; `t:real`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    ASM_CASES_TAC `v:real^N = vec 0` THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    ABBREV_TAC `L = mfd_tnorm (g:A->real^N^N) x v` THEN
    SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `v:real^N`] GEOD_TNORM_EQ_0) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `v:real^N` (ASSUME `!v. &0 <= mfd_tnorm (g:A->real^N^N) x v`)) THEN
      REWRITE_TAC[ASSUME `mfd_tnorm (g:A->real^N^N) x v = L`;
                  ASSUME `~(v:real^N = vec 0)`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `u = inv L % (v:real^N)` THEN
    SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) x u = &1 /\ L % u = (v:real^N)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < L ==> abs L = L`; REAL_MUL_LINV; REAL_MUL_RINV;
                   REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) x u` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s0") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "sexp") ASSUME_TAC))) THEN
    SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) x (t % v) = (sigma:real->A) (t * L) /\
                  mfd_exp (top,atlas) g x v = sigma L`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "sexp" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN REWRITE_TAC[ASSUME `L % u = (v:real^N)`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "aff" (fun th -> MP_TAC(SPEC `t * L:real` (MATCH_MP th
      (CONJ (ASSUME `(x:A) IN topspace top`) (ASSUME `mfd_tnorm (g:A->real^N^N) x u = &1`))))) THEN
    USE_THEN "aff" (fun th -> MP_TAC(SPEC `L:real` (MATCH_MP th
      (CONJ (ASSUME `(x:A) IN topspace top`) (ASSUME `mfd_tnorm (g:A->real^N^N) x u = &1`))))) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `lam:real->A`; `x:A`] CMPB_ASYMPTOTE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`u:real^N`; `&1`] THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "aff" (fun th -> MP_TAC(SPEC `s:real` (MATCH_MP th
      (CONJ (ASSUME `(x:A) IN topspace top`) (ASSUME `mfd_tnorm (g:A->real^N^N) x u = &1`))))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `u:real^N`)) (concl th))) THEN
    REWRITE_TAC[REAL_POS] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The line is the geodesic of X.  A unit vector along which f               *)
(* grows with unit rate is X (CMPSP_DIR_UNIQUE); by CMPRG_CORE the line is   *)
(* a geodesic from lam(0) in both directions, hence lam = geo(lam 0, X).     *)
(* ========================================================================= *)

let CMPSP_DIR_UNIQUE = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) (X:A->real^N) (q:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
        (!x w. x IN topspace top
               ==> f(mfd_exp (top,atlas) g x w) = f x + w dot (g x ** X x)) /\
        q IN topspace top /\ mfd_tnorm g q v = &1 /\
        f(mfd_geo (top,atlas) g q v (&1)) = f q + &1
        ==> v = X q`,
  INTRO_TAC "!top atlas g f X q v; haus smooth riem comp unit form qtop vunit fv" THEN
  MATCH_MP_TAC CMPSP_UNIT_EQ THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:A->real^N^N`; `q:A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_tnorm] THEN
    USE_THEN "unit" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(q:A) IN topspace top`)]) THEN
    REWRITE_TAC[SQRT_1];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `v:real^N`] CMPAF_GEO_ALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `&1` o CONJUNCT1 o funpow 5 CONJUNCT2) THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_TAC THEN
    USE_THEN "form" (MP_TAC o SPEC `v:real^N` o C MATCH_MP (ASSUME `(q:A) IN topspace top`)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let CMPSP_LINE_IS_GEO = prove
 (`!top atlas (g:A->real^N^N) (lam:real->A) (f:A->real) (X:A->real^N).
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!s t. lam s IN topspace top /\ mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s)) /\
        (!t. f(lam t) = t) /\
        (!p u. p IN topspace top /\ mfd_tnorm g p u = &1
               ==> !s. f(mfd_geo (top,atlas) g p u s) =
                       f p + s * (f(mfd_geo (top,atlas) g p u (&1)) - f p)) /\
        (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
        (!x w. x IN topspace top
               ==> f(mfd_exp (top,atlas) g x w) = f x + w dot (g x ** X x))
        ==> !r. lam r = mfd_geo (top,atlas) g (lam(&0)) (X(lam(&0))) r`,
  INTRO_TAC "!top atlas g lam f X; haus conn smooth riem comp line fl aff unit form" THEN
  ABBREV_TAC `p = (lam:real->A)(&0)` THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->real) p = &0` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN topspace top /\ y IN topspace top
                      ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x y`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `(X:A->real^N) p`] CMPAF_GEO_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "xexp" o CONJUNCT1 o funpow 5 CONJUNCT2) THEN
  X_GEN_TAC `r:real` THEN ASM_CASES_TAC `&0 <= r` THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `lam:real->A`; `r + &1`] CMPRG_CORE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `u = (X:A->real^N) p` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC CMPSP_DIR_UNIQUE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `g:A->real^N^N`; `f:A->real`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p u (&1) = (lam:real->A)(&1)`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_ADD_LID];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\t. (lam:real->A)(--t)`; `--r + &1`] CMPRG_CORE) THEN
  REWRITE_TAC[REAL_NEG_0] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOD_TNORM_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] CMPAF_GEO_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "uexp" o CONJUNCT1 o funpow 5 CONJUNCT2) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `--u:real^N`] CMPAF_GEO_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "nexp" o CONJUNCT1 o funpow 5 CONJUNCT2) THEN
  SUBGOAL_THEN `--u = (X:A->real^N) p` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPSP_DIR_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `f:A->real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p (--u) (&1) =
                  mfd_geo (top,atlas) g p u (--(&1))` SUBST1_TAC THENL
     [USE_THEN "nexp" (fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "uexp" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LNEG];
      ALL_TAC] THEN
    USE_THEN "aff" (fun th -> MP_TAC(SPEC `--(&1)` (MATCH_MP th
      (CONJ (ASSUME `(p:A) IN topspace top`) (ASSUME `mfd_tnorm (g:A->real^N^N) p u = &1`))))) THEN
    SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p u (&1) = (lam:real->A)(--(&1))`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `&1` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `u:real^N`)) (concl th) &&
        can (find_term ((=) `lam:real->A`)) (concl th))) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(lam:real->A) r = mfd_geo (top,atlas) (g:A->real^N^N) p u (--r)` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `--r:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `u:real^N`)) (concl th) &&
      can (find_term ((=) `lam:real->A`)) (concl th))) THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "uexp" (fun th -> REWRITE_TAC[GSYM th]) THEN
  USE_THEN "xexp" (fun th -> REWRITE_TAC[GSYM th]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `--u = (X:A->real^N) p`)) THEN
  REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_RNEG; VECTOR_NEG_NEG]);;

(* ========================================================================= *)
(* The velocity of the geodesic of X is X, and the general                   *)
(* splitting theorem.                                                        *)
(* ========================================================================= *)

let CMPSP_GEO_VELOCITY = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) (X:A->real^N) (p:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
        (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
        (!x w. x IN topspace top
               ==> f(mfd_exp (top,atlas) g x w) = f x + w dot (g x ** X x)) /\
        (!t. f(mfd_geo (top,atlas) g p (X p) t) = f p + t)
        ==> !s. mfd_velocity atlas (mfd_geo (top,atlas) g p (X p)) (s - &1) (s + &1) s =
                X(mfd_geo (top,atlas) g p (X p) s)`,
  INTRO_TAC "!top atlas g f X p; haus smooth riem comp ptop unit form rate" THEN
  X_GEN_TAC `s:real` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `(X:A->real^N) p`] CMPAF_GEO_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) p ((X:A->real^N) p)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `(:real)`; `s - &1`; `s + &1`; `s:real`]
    GEOM_VELOCITY_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_UNIV; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC CMPSP_DIR_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:A->real^N^N`; `f:A->real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gam:real->A`; `(:real)`; `s:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[mfd_tnorm] THEN
    USE_THEN "unit" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(p:A) IN topspace top`)]) THEN
    REWRITE_TAC[SQRT_1];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `(X:A->real^N) p`; `s:real`] MFD_GEO_SHIFT) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "rate" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

let CMPSP_SPLIT_GEN = prove
 (`!top atlas (g:A->real^N^N) (lam:real->A).
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g x u v) /\
        (!s t. lam s IN topspace top /\ mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s))
        ==> p2b_locally_split (top,atlas) g /\
            ?X. p2b_parallel_on atlas g (topspace top) X /\
                (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
                !s. mfd_velocity atlas lam (s - &1) (s + &1) s = X(lam s)`,
  INTRO_TAC "!top atlas g lam; haus conn smooth riem comp sec line" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `lam:real->A`] CMPSP_LINE_E_HYPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `lam:real->A`] CMPSP_LINE_GEO_AFFINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `lam:real->A`] CMPSP_LINE_BUSEMANN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `B1 = cmp_busemann (top,atlas) (g:A->real^N^N) lam` THEN
  DISCH_THEN(LABEL_TAC "fl" o CONJUNCT2) THEN
  DISCH_THEN(LABEL_TAC "aff") THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lip")
    (CONJUNCTS_THEN2 (LABEL_TAC "eaff") (LABEL_TAC "asym"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `B1:A->real`] CMP_AFFINE_PARALLEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:A->real^N` (CONJUNCTS_THEN2 (LABEL_TAC "par")
    (CONJUNCTS_THEN2 (LABEL_TAC "unit") (CONJUNCTS_THEN2 (LABEL_TAC "form") (K ALL_TAC))))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2b_locally_split] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`topspace top:A->bool`; `X:A->real^N`] THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  EXISTS_TAC `X:A->real^N` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `lam:real->A`; `B1:A->real`; `X:A->real^N`]
    CMPSP_LINE_IS_GEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `p = (lam:real->A)(&0)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(lam:real->A) = mfd_geo (top,atlas) (g:A->real^N^N) p ((X:A->real^N) p)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CMPSP_GEO_VELOCITY THEN EXISTS_TAC `B1:A->real` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "p" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `t:real` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "mfd_geo" with Failure _ -> false))
        (concl th) &&
    can (find_term ((=) `lam:real->A`)) (concl th))) THEN
  USE_THEN "fl" (fun th -> REWRITE_TAC[th]) THEN
  EXPAND_TAC "p" THEN USE_THEN "fl" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The splitting theorem: the statement constant CMP_R3_SPLIT_STATEMENT and  *)
(* its proof CMP_R3_SPLIT.                                                   *)
(* ========================================================================= *)

let CMP_R3_SPLIT_STATEMENT = new_definition
 `CMP_R3_SPLIT_STATEMENT (w:B->bool) <=>
    !top atlas g lam.
       hausdorff_space top /\ connected_space top /\
       smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v) /\
       (!s t. lam s IN topspace top /\
              mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s))
       ==> p2b_locally_split (top,atlas) g /\
           ?X. p2b_parallel_on atlas g (topspace top) X /\
               (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
               !s. mfd_velocity atlas lam (s - &1) (s + &1) s = X(lam s)`;;

let CMP_R3_SPLIT = prove
 (`!w:B->bool. CMP_R3_SPLIT_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[CMP_R3_SPLIT_STATEMENT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMPSP_SPLIT_GEN THEN
  ASM_REWRITE_TAC[]);;

