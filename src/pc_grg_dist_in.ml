(* ========================================================================= *)
(* pc_grg_dist_in: the Riemannian distance through curves inside a set S    *)
(* (distances and diameters measured inside a region, e.g. necks and caps). *)
(* Built on pc_grg_dist.                                                     *)
(* ========================================================================= *)

needs "src/pc_grg_dist.ml";;

prioritize_real();;
type_invention_error := true;;

let mfd_dist_in = new_definition
 `mfd_dist_in (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
              (g:A->real^N^N) (S:A->bool) (x:A) (y:A) =
    inf {mfd_length atlas g gamma (&0) (&1) | gamma |
         mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
         gamma(&0) = x /\ gamma(&1) = y /\
         (!t. &0 <= t /\ t <= &1 ==> gamma t IN S)}`;;

(* Points joined by a C^1 curve on [0,1] staying inside S. *)

let mfd_joinable_in = new_definition
 `mfd_joinable_in (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                  (S:A->bool) (x:A) (y:A) <=>
    ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
            gamma(&0) = x /\ gamma(&1) = y /\
            (!t. &0 <= t /\ t <= &1 ==> gamma t IN S)`;;

(* ------------------------------------------------------------------------- *)
(* The set of lengths of curves inside S.                                    *)
(* ------------------------------------------------------------------------- *)

let GRGD_IN_LENGTHS_IN = prove
 (`!top atlas (g:A->real^N^N) S x y L.
        L IN {mfd_length atlas g gamma (&0) (&1) | gamma |
              mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
              gamma(&0) = x /\ gamma(&1) = y /\
              (!t. &0 <= t /\ t <= &1 ==> gamma t IN S)} <=>
        ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                gamma(&0) = x /\ gamma(&1) = y /\
                (!t. &0 <= t /\ t <= &1 ==> gamma t IN S) /\
                L = mfd_length atlas g gamma (&0) (&1)`,
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let GRGD_LENGTHS_IN_POS_LE = prove
 (`!top atlas (g:A->real^N^N) S x y L.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        L IN {mfd_length atlas g gamma (&0) (&1) | gamma |
              mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
              gamma(&0) = x /\ gamma(&1) = y /\
              (!t. &0 <= t /\ t <= &1 ==> gamma t IN S)}
        ==> &0 <= L`,
  REWRITE_TAC[GRGD_IN_LENGTHS_IN] THEN MESON_TAC[MFD_LENGTH_POS_LE]);;

(* The concatenation of two curves inside S stays inside S. *)

let GRGD_CONCAT_IN = prove
 (`!(gamma1:real->A) gamma2 S.
        (!t. &0 <= t /\ t <= &1 ==> gamma1 t IN S) /\
        (!t. &0 <= t /\ t <= &1 ==> gamma2 t IN S)
        ==> !t. &0 <= t /\ t <= &1 ==> grgd_concat gamma1 gamma2 t IN S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REWRITE_TAC[grgd_concat; grgd_ss] THEN COND_CASES_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THENL
   [MP_TAC(SPEC `&2 * t - &0` GRGD_SMOOTHSTEP_RANGE);
    MP_TAC(SPEC `&2 * t - &1` GRGD_SMOOTHSTEP_RANGE)] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]));;

(* ------------------------------------------------------------------------- *)
(* Joinability inside S.                                                     *)
(* ------------------------------------------------------------------------- *)

let MFD_JOINABLE_IN_IMP = prove
 (`!top atlas (S:A->bool) x y.
        mfd_joinable_in (top,atlas:((A->bool)#(A->real^N))->bool) S x y
        ==> mfd_joinable (top,atlas) x y`,
  REWRITE_TAC[mfd_joinable_in; mfd_joinable] THEN MESON_TAC[]);;

let MFD_JOINABLE_IN_TOPSPACE_EQ = prove
 (`!top atlas (x:A) y.
        mfd_joinable_in (top,atlas:((A->bool)#(A->real^N))->bool)
                        (topspace top) x y <=>
        mfd_joinable (top,atlas) x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_joinable_in; mfd_joinable] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> r) ==> (p /\ q1 /\ q2 /\ r <=> p /\ q1 /\ q2)`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `&0`; `&1`] THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL]);;

let MFD_JOINABLE_IN_MONO = prove
 (`!top atlas (S:A->bool) S' x y.
        S SUBSET S' /\
        mfd_joinable_in (top,atlas:((A->bool)#(A->real^N))->bool) S x y
        ==> mfd_joinable_in (top,atlas) S' x y`,
  REWRITE_TAC[mfd_joinable_in; SUBSET] THEN MESON_TAC[]);;

let MFD_JOINABLE_IN_REFL = prove
 (`!top atlas (S:A->bool) x.
        x IN topspace top /\ x IN S
        ==> mfd_joinable_in (top,atlas:((A->bool)#(A->real^N))->bool) S x x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_joinable_in] THEN
  EXISTS_TAC `\t:real. (x:A)` THEN BETA_TAC THEN
  ASM_SIMP_TAC[MFD_C1_CURVE_CONST; REAL_POS]);;

let MFD_JOINABLE_IN_SYM = prove
 (`!top atlas (S:A->bool) x y.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)
        ==> (mfd_joinable_in (top,atlas) S x y <=>
             mfd_joinable_in (top,atlas) S y x)`,
  SUBGOAL_THEN
   `!top atlas (S:A->bool) x y.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_joinable_in (top,atlas) S x y
        ==> mfd_joinable_in (top,atlas) S y x`
   (fun th -> MESON_TAC[th]) THEN
  REWRITE_TAC[mfd_joinable_in] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `\t. (gamma:real->A)(&0 + &1 - t)` THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> (gamma:real->A)(&0 + &1 - t) IN S`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(\x. mat 1):A->real^N^N`; `gamma:real->A`] GRGD_REVERSE_01) THEN
  ASM_SIMP_TAC[]);;

let MFD_JOINABLE_IN_TRANS = prove
 (`!top atlas (S:A->bool) x y z.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_joinable_in (top,atlas) S x y /\ mfd_joinable_in (top,atlas) S y z
        ==> mfd_joinable_in (top,atlas) S x z`,
  REWRITE_TAC[mfd_joinable_in] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `grgd_concat (gamma:real->A) gamma'` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `gamma':real->A`] GRGD_CONCAT_C1) THEN
  MP_TAC(ISPECL [`gamma:real->A`; `gamma':real->A`; `S:A->bool`]
                GRGD_CONCAT_IN) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The distance inside S.                                                    *)
(* ------------------------------------------------------------------------- *)

let MFD_DIST_IN_POS_LE = prove
 (`!top atlas (g:A->real^N^N) S x y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_joinable_in (top,atlas) S x y
        ==> &0 <= mfd_dist_in (top,atlas) g S x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_dist_in] THEN MATCH_MP_TAC REAL_LE_INF THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS_IN] THEN
    ASM_MESON_TAC[mfd_joinable_in];
    ASM_MESON_TAC[GRGD_LENGTHS_IN_POS_LE]]);;

let MFD_DIST_IN_LE_LENGTH = prove
 (`!top atlas (g:A->real^N^N) S (gamma:real->A) a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b /\
        (!t. t IN real_interval[a,b] ==> gamma t IN S)
        ==> mfd_dist_in (top,atlas) g S (gamma a) (gamma b) <=
            mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_dist_in] THEN MATCH_MP_TAC REAL_INF_LE THEN
  MAP_EVERY EXISTS_TAC
   [`&0`; `mfd_length atlas (g:A->real^N^N) (gamma:real->A) a b`] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
   [REWRITE_TAC[GRGD_IN_LENGTHS_IN] THEN
    EXISTS_TAC `(gamma:real->A) o (\x. a + (b - a) * x)` THEN
    SUBGOAL_THEN `a:real <= b` ASSUME_TAC THENL
     [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `gamma:real->A`; `a:real`; `b:real`] GRGD_AFFINE_CURVE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(SPECL [`a:real`; `b:real`] GRGD_AFFINE_FACTS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN SIMP_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC GRGD_AFFINE_LENGTH THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `L:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `S:A->bool`; `(gamma:real->A) a`;
                   `(gamma:real->A) b`; `L:real`] GRGD_LENGTHS_IN_POS_LE) THEN
    ASM_REWRITE_TAC[]]);;

let MFD_DIST_IN_REFL = prove
 (`!top atlas (g:A->real^N^N) S x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top /\ x IN S
        ==> mfd_dist_in (top,atlas) g S x x = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (\t:real. (x:A)) (&0) (&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_C1_CURVE_CONST THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `S:A->bool`; `\t:real. (x:A)`; `&0`; `&1`]
                  MFD_DIST_IN_LE_LENGTH) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[GRGD_LENGTH_CONST];
    MATCH_MP_TAC MFD_DIST_IN_POS_LE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_JOINABLE_IN_REFL THEN ASM_REWRITE_TAC[]]);;

let MFD_DIST_IN_TOPSPACE = prove
 (`!top atlas (g:A->real^N^N) x y.
        mfd_dist_in (top,atlas) g (topspace top) x y =
        mfd_dist (top,atlas) g x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_dist_in; mfd_dist] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; GRGD_IN_LENGTHS_IN; GRGD_IN_LENGTHS] THEN
  X_GEN_TAC `L:real` THEN AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT
   `(p ==> r) ==> (p /\ q1 /\ q2 /\ r /\ s <=> p /\ q1 /\ q2 /\ s)`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `&0`; `&1`] THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL]);;

let MFD_DIST_LE_DIST_IN = prove
 (`!top atlas (g:A->real^N^N) S x y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_joinable_in (top,atlas) S x y
        ==> mfd_dist (top,atlas) g x y <= mfd_dist_in (top,atlas) g S x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_dist; mfd_dist_in] THEN
  MATCH_MP_TAC REAL_LE_INF_SUBSET THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS_IN] THEN
    ASM_MESON_TAC[mfd_joinable_in];
    REWRITE_TAC[SUBSET; GRGD_IN_LENGTHS_IN; GRGD_IN_LENGTHS] THEN MESON_TAC[];
    EXISTS_TAC `&0` THEN ASM_MESON_TAC[GRGD_LENGTHS_POS_LE]]);;

let MFD_DIST_IN_MONO = prove
 (`!top atlas (g:A->real^N^N) S S' x y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        S SUBSET S' /\ mfd_joinable_in (top,atlas) S x y
        ==> mfd_dist_in (top,atlas) g S' x y <= mfd_dist_in (top,atlas) g S x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_dist_in] THEN
  MATCH_MP_TAC REAL_LE_INF_SUBSET THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS_IN] THEN
    ASM_MESON_TAC[mfd_joinable_in];
    REWRITE_TAC[SUBSET; GRGD_IN_LENGTHS_IN] THEN
    UNDISCH_TAC `(S:A->bool) SUBSET S'` THEN REWRITE_TAC[SUBSET] THEN MESON_TAC[];
    EXISTS_TAC `&0` THEN ASM_MESON_TAC[GRGD_LENGTHS_IN_POS_LE]]);;

let GRGD_LENGTHS_IN_SYM = prove
 (`!top atlas (g:A->real^N^N) S x y.
        smooth_manifold_atlas top atlas
        ==> {mfd_length atlas g gamma (&0) (&1) | gamma |
             mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
             gamma(&0) = x /\ gamma(&1) = y /\
             (!t. &0 <= t /\ t <= &1 ==> gamma t IN S)} =
            {mfd_length atlas g gamma (&0) (&1) | gamma |
             mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
             gamma(&0) = y /\ gamma(&1) = x /\
             (!t. &0 <= t /\ t <= &1 ==> gamma t IN S)}`,
  SUBGOAL_THEN
   `!top atlas (g:A->real^N^N) S x y L.
        smooth_manifold_atlas top atlas /\
        L IN {mfd_length atlas g gamma (&0) (&1) | gamma |
              mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
              gamma(&0) = x /\ gamma(&1) = y /\
              (!t. &0 <= t /\ t <= &1 ==> gamma t IN S)}
        ==> L IN {mfd_length atlas g gamma (&0) (&1) | gamma |
                  mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                  gamma(&0) = y /\ gamma(&1) = x /\
                  (!t. &0 <= t /\ t <= &1 ==> gamma t IN S)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[GRGD_IN_LENGTHS_IN] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `\t. (gamma:real->A)(&0 + &1 - t)` THEN
    SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> (gamma:real->A)(&0 + &1 - t) IN S`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`] GRGD_REVERSE_01) THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN ASM_MESON_TAC[]]);;

let MFD_DIST_IN_SYM = prove
 (`!top atlas (g:A->real^N^N) S x y.
        smooth_manifold_atlas top atlas
        ==> mfd_dist_in (top,atlas) g S x y = mfd_dist_in (top,atlas) g S y x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_dist_in] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC GRGD_LENGTHS_IN_SYM THEN ASM_REWRITE_TAC[]);;

let MFD_DIST_IN_TRIANGLE = prove
 (`!top atlas (g:A->real^N^N) S x y z.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_joinable_in (top,atlas) S x y /\ mfd_joinable_in (top,atlas) S y z
        ==> mfd_dist_in (top,atlas) g S x z <=
            mfd_dist_in (top,atlas) g S x y + mfd_dist_in (top,atlas) g S y z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!L1 L2. L1 IN {mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) | gamma |
                   mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                   gamma(&0) = (x:A) /\ gamma(&1) = y /\
                   (!t. &0 <= t /\ t <= &1 ==> gamma t IN S)} /\
            L2 IN {mfd_length atlas g gamma (&0) (&1) | gamma |
                   mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                   gamma(&0) = y /\ gamma(&1) = z /\
                   (!t. &0 <= t /\ t <= &1 ==> gamma t IN S)}
            ==> mfd_dist_in (top,atlas) g S x z <= L1 + L2`
  ASSUME_TAC THENL
   [REWRITE_TAC[GRGD_IN_LENGTHS_IN] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[mfd_dist_in] THEN MATCH_MP_TAC REAL_INF_LE THEN
    MAP_EVERY EXISTS_TAC [`&0`; `L1 + L2:real`] THEN REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GRGD_IN_LENGTHS_IN] THEN
      EXISTS_TAC `grgd_concat (gamma:real->A) gamma'` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `gamma:real->A`; `gamma':real->A`] GRGD_CONCAT_C1) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma:real->A`; `gamma':real->A`]
                    GRGD_CONCAT_LENGTH) THEN
      MP_TAC(ISPECL [`gamma:real->A`; `gamma':real->A`; `S:A->bool`]
                    GRGD_CONCAT_IN) THEN
      ASM_SIMP_TAC[];
      ASM_MESON_TAC[GRGD_LENGTHS_IN_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!L2. L2 IN {mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) | gamma |
                mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                gamma(&0) = (y:A) /\ gamma(&1) = z /\
                (!t. &0 <= t /\ t <= &1 ==> gamma t IN S)}
         ==> mfd_dist_in (top,atlas) g S x z - L2 <=
             mfd_dist_in (top,atlas) g S x y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC (RAND_CONV) [mfd_dist_in] THEN
    MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS_IN] THEN
      ASM_MESON_TAC[mfd_joinable_in];
      ASM_MESON_TAC[REAL_ARITH `d <= l1 + l2 ==> d - l2 <= l1`]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `d <= a + b <=> d - a <= b`] THEN
  GEN_REWRITE_TAC (RAND_CONV) [mfd_dist_in] THEN
  MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS_IN] THEN
    ASM_MESON_TAC[mfd_joinable_in];
    ASM_MESON_TAC[REAL_ARITH `d - l2 <= l1 ==> d - l1 <= l2`]]);;

