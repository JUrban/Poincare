(* ========================================================================= *)
(* Unit pc_p2c_fl515 (Part 2C, flowlim route): MT Thm 5.15 in the corrected  *)
(* form P2C_THM_5_15_STATEMENT, i.e. P2C_THM_5_15_ROUTE_STATEMENT u (from    *)
(* Thm 5.11, Prop 5.14, Thms 3.28/3.29 and HISTORY_REGULAR).  The slice      *)
(* limit at the base time (Thm 5.11, or Cheeger-Gromov compactness           *)
(* P2CK_CG_COMPACT when 0 is the least element of J) is restricted to the    *)
(* joinable class of the base point (pc_p2c_lrestrict: the limit need not be *)
(* connected), the images phi n (W m) lie in rescaled balls about x n        *)
(* (P2BC_BALL_IMAGE_IN), so the ball hypotheses of 5.15 give the region      *)
(* hypotheses of 5.14; completeness passes along a uniform curvature bound.  *)
(* The statement assumes that the least element of J, if any, is 0.          *)
(* ========================================================================= *)

needs "src/pc_p2c_lrestrict.ml";;
needs "src/pc_p2c_flloc.ml";;
needs "src/pc_p2c_fl511.ml";;
needs "src/pc_p2c_fl514.ml";;
needs "src/pc_rfa_hbar.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Distances are bounded on compact sets, short curves stay in               *)
(* balls, the time-0 quadratic forms of a slice limit, and the images of    *)
(* the exhaustion lie in rescaled balls about the base points.              *)
(* ------------------------------------------------------------------------- *)

let P2CO_DIST_BOUNDED = prove
 (`!top (atlas:((B->bool)#(B->real^N))->bool) (g:B->real^N^N) x0 K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ compact_in top K
     ==> ?R. &0 < R /\ !y. y IN K ==> mfd_dist (top,atlas) g x0 y < R`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `euclideanreal`;
                 `\y. mfd_dist (top,atlas:((B->bool)#(B->real^N))->bool) (g:B->real^N^N) x0 y`;
                 `K:B->bool`] IMAGE_COMPACT_IN) THEN
  ASM_SIMP_TAC[MFD_DIST_CONTINUOUS_RIGHT] THEN
  REWRITE_TAC[GSYM real_compact_def] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `abs B + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:B`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2CO_CURVE_IN_BALL = prove
 (`!top (atlas:((B->bool)#(B->real^N))->bool) (g:B->real^N^N) (gamma:real->B) y0 r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = y0 /\
     mfd_length atlas g gamma (&0) (&1) < r
     ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN mfd_ball (top,atlas) g y0 r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g:B->real^N^N`;
                 `gamma:real->B`; `&0`; `s:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g:B->real^N^N`;
                 `gamma:real->B`; `s:real`; `&1`] MFD_LENGTH_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(gamma:real->B)(&0) = y0`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g:B->real^N^N) (gamma:real->B) (&0) s` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]]);;

let P2CO_PULLBACK_CMUL = prove
 (`!(atlas:((B->bool)#(B->real^N))->bool) (atlas':((A->bool)#(A->real^N))->bool)
    (f:B->A) (g:A->real^N^N) c x.
     mfd_pullback_metric atlas atlas' f (\z. c %% g z) x =
     c %% mfd_pullback_metric atlas atlas' f g x`,
  REWRITE_TAC[mfd_pullback_metric; METRIC_LOCAL_CMUL; mpullback] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

(* The time-0 quadratic forms of a slice limit (no region hypotheses). *)

let P2CO_SL_QF0 = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g0 xl W phi K.
     (!n s. ~(topspace(rfs_vtop (V n) s) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V n) s) (rfs_vatlas (V n) s) /\
                riemannian_metric (rfs_vatlas (V n) s) (rfs_vmetric (V n) s)) /\
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\ compact_in top K
     ==> ?N. !n y u. N <= n /\ y IN K
                     ==> K SUBSET W n /\
                         abs(u dot ((\z. Q n %% mfd_pullback_metric atlas (rfs_vatlas (V n) (t n))
                                                (phi n) (rfs_vmetric (V n) (t n)) z) y ** u) -
                             u dot (g0 y ** u)) <= inv(&2) * (u dot (g0 y ** u))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sl") (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[p2c_slice_limit_with] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Wk")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "dif") (LABEL_TAC "lck")))))))))) THEN
  USE_THEN "lck" (MP_TAC o C MP (CONJ (ASSUME `compact_in top (K:B->bool)`)
    (REAL_ARITH `&0 < inv(&2) pow 2`)) o SPECL [`K:B->bool`; `0`; `inv(&2) pow 2`]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_THEN(LABEL_TAC "N") THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:B`; `u:real^3`] THEN STRIP_TAC THEN
  USE_THEN "N" (MP_TAC o C MP (ASSUME `N <= n:num`) o SPEC `n:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o C MP (ASSUME `(y:B) IN K`) o SPEC `y:B`)) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:B) IN (W:num->B->bool) n /\ y IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]];
    ALL_TAC] THEN
  USE_THEN "dif" (X_CHOOSE_TAC `psi:A->B` o SPEC `n:num`) THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#
          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n))
                              (rfs_vatlas (V n) (t n)) /\
    riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "sl" MATCH_MP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `(phi:num->B->A) n y` THEN
    UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                   ((W:num->B->bool) n) (rfs_vtop ((V:num->(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n))
                   (rfs_vatlas (V n) (t n)) (IMAGE ((phi:num->B->A) n) (W n)) (phi n) psi` THEN
    REWRITE_TAC[mfd_diffeo] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
                                            CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `P = \z. (Q:num->real) n %%
                      mfd_pullback_metric (atlas:((B->bool)#(B->real^3))->bool)
                        (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) n) (t n))
                        ((phi:num->B->A) n) (rfs_vmetric (V n) (t n)) z` THEN
  SUBGOAL_THEN
   `(Q:num->real) n %%
    mfd_pullback_metric (atlas:((B->bool)#(B->real^3))->bool)
      (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) n) (t n))
      ((phi:num->B->A) n) (rfs_vmetric (V n) (t n)) y = (P:B->real^3^3) y`
  SUBST1_TAC THENL [EXPAND_TAC "P" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `S = IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)))
                        (FST(chart_at atlas y) INTER (W:num->B->bool) n)` THEN
  SUBGOAL_THEN
   `metric_field S (metric_local atlas (chart_at atlas (y:B)) (g0:B->real^3^3)) /\
    metric_field S (metric_local atlas (chart_at atlas y) P) /\
    SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) y) y IN S /\ open S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN USE_THEN "Wk" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2CO_RIEM_FIELD THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "P" THEN MATCH_MP_TAC P2CO_PB_FIELD THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`;
                            `rfs_vtop ((V:num->(real->A topology)#
                               (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                            `IMAGE ((phi:num->B->A) n) ((W:num->B->bool) n)`; `psi:A->B`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 0 (metric_local atlas (chart_at atlas (y:B)) (g0:B->real^3^3))
                (metric_local atlas (chart_at atlas y) P) (SND(chart_at atlas y) y) <
    inv(&2) pow 2`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "lck_dist2" with Failure _ -> false))
          (concl th) && not (is_forall (concl th)))) THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> y < e ==> x < e`) THEN
    MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    EXPAND_TAC "P" THEN MATCH_MP_TAC P2CO_PB_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`;
                          `rfs_vtop ((V:num->(real->A topology)#
                             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n)`;
                          `(W:num->B->bool) n`;
                          `IMAGE ((phi:num->B->A) n) ((W:num->B->bool) n)`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:real^3) IN S` THEN EXPAND_TAC "S" THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `P:B->real^3^3`; `y:B`] METRIC_LOCAL_AT) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `y:B`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sqrt(lck_dist2 0 (metric_local atlas (chart_at atlas (y:B)) (g0:B->real^3^3))
                     (metric_local atlas (chart_at atlas y) P)
                     (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) y) y)) *
    (u dot (metric_local atlas (chart_at atlas y) g0 (SND(chart_at atlas y) y) ** u))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_C0 THEN EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      UNDISCH_TAC `metric_field S (metric_local atlas (chart_at atlas (y:B)) (g0:B->real^3^3))` THEN
      REWRITE_TAC[metric_field] THEN
      DISCH_THEN(MP_TAC o SPEC `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)) y` o
                 CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `u:real^3 = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
      ASM_MESON_TAC[REAL_LT_IMP_LE]]]);;

let P2CO_VBALL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t x r.
     rfs_vball V t x r = mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x r`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vball; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

(* The images of the exhaustion lie in rescaled balls about the base points *)
(* (P2BC_BALL_IMAGE_IN with the time-0 quadratic forms on a closed g0-ball). *)

let P2CO_IMAGE_IN_BALL = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g0 xl W phi m.
     (!n s. ~(topspace(rfs_vtop (V n) s) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V n) s) (rfs_vatlas (V n) s) /\
                riemannian_metric (rfs_vatlas (V n) s) (rfs_vmetric (V n) s)) /\
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\ mfd_complete (top,atlas) g0 /\
     (!y. y IN topspace top ==> mfd_joinable (top,atlas) xl y)
     ==> ?A N. &0 < A /\
               !n. N <= n
                   ==> IMAGE (phi n) (W m) SUBSET
                       rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sl") (CONJUNCTS_THEN2 (LABEL_TAC "lim")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "join")))) THEN
  USE_THEN "lim" (STRIP_ASSUME_TAC o REWRITE_RULE[p2c_slice_limit_with]) THEN
  SUBGOAL_THEN `compact_in top (top closure_of (W:num->B->bool) m) /\
                W m SUBSET top closure_of W m`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `m:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `compact_in:(B)topology->(B->bool)->bool`))
                                 (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `top closure_of (W:num->B->bool) m`] P2CO_DIST_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `R0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `K2 = mfd_cball (top,atlas:((B->bool)#(B->real^3))->bool) (g0:B->real^3^3) xl
                             (R0 + &1)` THEN
  SUBGOAL_THEN `compact_in top (K2:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K2" THEN
    UNDISCH_TAC `mfd_complete (top,atlas:((B->bool)#(B->real^3))->bool) (g0:B->real^3^3)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `K2:B->bool`] P2CO_SL_QF0) THEN
  USE_THEN "sl" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "lim" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  MAP_EVERY EXISTS_TAC [`&2 * R0`; `N:num`] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `q:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(K2:B->bool) SUBSET (W:num->B->bool) n` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP COMPACT_IN_SUBSET_TOPSPACE (ASSUME `compact_in top (K2:B->bool)`)) THEN
    DISCH_TAC THEN ASM_CASES_TAC `K2:B->bool = {}` THENL
     [ASM_REWRITE_TAC[EMPTY_SUBSET];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th))) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `y:B`) THEN
      USE_THEN "N" (MP_TAC o SPECL [`n:num`; `y:B`; `vec 0:real^3`]) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `U = mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool) (g0:B->real^3^3) xl
                           (R0 + &1)` THEN
  SUBGOAL_THEN `open_in top (U:B->bool) /\ U SUBSET K2 /\ (xl:B) IN U` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN EXPAND_TAC "K2" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `n:num` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `mfd_diffeo:(B)topology->((B->bool)#(B->real^3)->bool)->(B->bool)->(A)topology->((A->bool)#(A->real^3)->bool)->(A->bool)->(B->A)->(A->B)->bool`))
                               (concl th))) THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#
          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n))
                              (rfs_vatlas (V n) (t n)) /\
    riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "sl" MATCH_MP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `(phi:num->B->A) n xl` THEN
    UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                   ((W:num->B->bool) n) (rfs_vtop ((V:num->(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n))
                   (rfs_vatlas (V n) (t n)) (IMAGE ((phi:num->B->A) n) (W n)) (phi n) psi` THEN
    REWRITE_TAC[mfd_diffeo] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
                                            CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `compact_in:(B)topology->(B->bool)->bool`))
                                 (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) n) (t n)`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) n) (t n)`;
                 `\z. (Q:num->real) n %%
                      rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) n) (t n) z`;
                 `U:B->bool`; `IMAGE ((phi:num->B->A) n) U`; `(phi:num->B->A) n`; `psi:A->B`;
                 `xl:B`; `R0:real`; `&2 * R0`; `&3 / &2`; `q:B`] P2BC_BALL_IMAGE_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`(W:num->B->bool) n`; `IMAGE ((phi:num->B->A) n) ((W:num->B->bool) n)`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      X_GEN_TAC `gamma:real->B` THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                     `gamma:real->B`; `xl:B`; `R0:real`] P2CO_CURVE_IN_BALL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "U" THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`y:B`; `v:real^3`] THEN DISCH_TAC THEN
      REWRITE_TAC[P2CO_PULLBACK_CMUL] THEN REWRITE_TAC[ETA_AX] THEN
      USE_THEN "N" (MP_TAC o SPECL [`n:num`; `y:B`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
       [USE_THEN "join" MATCH_MP_TAC THEN
        MATCH_MP_TAC(SET_RULE `!s t (z:B). z IN s /\ s SUBSET t ==> z IN t`) THEN
        EXISTS_TAC `(W:num->B->bool) m` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_MESON_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) n) (t n)`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) n) (t n)`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) n) (t n)`;
                 `(Q:num->real) n`; `(phi:num->B->A) n xl`; `&2 * R0`] MFD_BALL_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th])] THEN
  REWRITE_TAC[P2CO_VBALL; real_div] THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `xl:B`)) (concl th) &&
    can (find_term ((=) `x:num->A`)) (concl th))) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Open subsets of a persisting region persist (the identity                *)
(* between slices is a homeomorphism of the region, P2CV_SLICE_DIFFEO); the *)
(* region hypotheses of Prop 5.14 from the ball hypotheses of Thm 5.15.      *)
(* ------------------------------------------------------------------------- *)

let P2CO_OPEN_TRANSFER = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    Wb Wb' a b u v.
     p2c_regular_view V /\ p2cz_from_smooth V /\ rfs_persists V Wb a b /\
     a <= u /\ u <= b /\ a <= v /\ v <= b /\
     open_in (rfs_vtop V u) Wb /\ open_in (rfs_vtop V v) Wb /\
     Wb' SUBSET Wb /\ open_in (rfs_vtop V u) Wb'
     ==> open_in (rfs_vtop V v) Wb'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `subtopology (rfs_vtop V v) Wb = subtopology (rfs_vtop V u) (Wb:A->bool)`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `u:real = v` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `u < v \/ v < u` DISJ_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC; ALL_TAC] THENL
     [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `Wb:A->bool`; `a:real`; `b:real`;
                     `u:real`; `v:real`] P2CV_SLICE_DIFFEO) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[mfd_diffeo; HOMEOMORPHIC_MAPS_ID] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `Wb:A->bool`; `a:real`; `b:real`;
                     `v:real`; `u:real`] P2CV_SLICE_DIFFEO) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[mfd_diffeo; HOMEOMORPHIC_MAPS_ID] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `Wb:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[]);;

let P2CO_PERSISTS_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W a b.
     rfs_persists V W a b <=>
     !s. a < s /\ s <= b
         ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\ open_in (rfs_vtop V s) W`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; rfs_vtop; rfs_vatlas]);;

let P2CO_PERSISTS_SUBSET = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    Wb Wb' a b t0.
     p2c_regular_view V /\ p2cz_from_smooth V /\ rfs_persists V Wb a b /\
     a <= t0 /\ t0 <= b /\ open_in (rfs_vtop V t0) Wb /\
     Wb' SUBSET Wb /\ open_in (rfs_vtop V t0) Wb'
     ==> rfs_persists V Wb' a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2CO_PERSISTS_ALT] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
                open_in (rfs_vtop V s) (Wb:A->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) Wb a b` THEN
    REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CO_OPEN_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`Wb:A->bool`; `a:real`; `b:real`; `t0:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Regular views have regular slices. *)

let P2CO_REGULAR_SLICES = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)).
     (!n. p2c_regular_view (V n))
     ==> !n s. ~(topspace(rfs_vtop (V n) s) = {})
               ==> smooth_manifold_atlas (rfs_vtop (V n) s) (rfs_vatlas (V n) s) /\
                   riemannian_metric (rfs_vatlas (V n) s) (rfs_vmetric (V n) s)`,
  REWRITE_TAC[p2c_regular_view] THEN MESON_TAC[]);;

let P2CO_DIV_SIGN = prove
 (`!a q. &0 < q ==> (a / q <= &0 <=> a <= &0) /\ (&0 <= a / q <=> &0 <= a)`,
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_MUL_LZERO]);;

(* The region hypotheses of Prop 5.14 from the ball hypotheses of Thm 5.15 *)
(* (for a slice limit of the joinable class of its base point).            *)

let P2CO_REGION_FROM_BALLS = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q J (top:B topology) atlas g0 xl W phi.
     is_realinterval J /\ (&0) IN J /\ (!n. p2c_regular_view (V n)) /\
     (!n. x n IN topspace(rfs_vtop (V n) (t n))) /\
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\ mfd_complete (top,atlas) g0 /\
     (!y. y IN topspace top ==> mfd_joinable (top,atlas) xl y) /\
     (!A a b. &0 < A /\ real_interval[a,b] SUBSET J
              ==> ?CA N. !n. N <= n
                      ==> (!s. a <= s /\ s <= b
                               ==> rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))) SUBSET
                                   topspace(rfs_vtop (V n) (t n + s / Q n))) /\
                          rfs_persists (V n) (rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))))
                            (t n + a / Q n) (t n + b / Q n) /\
                          !s y. a <= s /\ s <= b /\
                                y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                ==> p3_vrm (V n) (t n + s / Q n) y <= CA * Q n)
     ==> !m a b. real_interval[a,b] SUBSET J
                 ==> ?CM N. !n. N <= n
                          ==> (!s. a <= s /\ s <= b
                                   ==> IMAGE (phi n) (W m) SUBSET
                                       topspace(rfs_vtop (V n) (t n + s / Q n))) /\
                              rfs_persists (V n) (IMAGE (phi n) (W m))
                                           (t n + a / Q n) (t n + b / Q n) /\
                              !s y. a <= s /\ s <= b /\ y IN IMAGE (phi n) (W m)
                                    ==> p3_vrm (V n) (t n + s / Q n) y <= CM * Q n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "reg") (CONJUNCTS_THEN2 (LABEL_TAC "xin")
    (CONJUNCTS_THEN2 (LABEL_TAC "lim") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "join") (LABEL_TAC "balls")))))))) THEN
  USE_THEN "reg" (LABEL_TAC "sl" o MATCH_MP P2CO_REGULAR_SLICES) THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `a:real`; `b:real`] THEN DISCH_TAC THEN
  USE_THEN "lim" (STRIP_ASSUME_TAC o REWRITE_RULE[p2c_slice_limit_with]) THEN
  ASM_CASES_TAC `a:real <= b` THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`&0`; `0`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[P2CO_PERSISTS_ALT] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `b / (Q:num->real) n < a / Q n` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC]] THEN
  SUBGOAL_THEN `real_interval[min a (&0),max b (&0)] SUBSET J` ASSUME_TAC THENL
   [SUBGOAL_THEN `(a:real) IN J /\ (b:real) IN J` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `real_interval[a,b] SUBSET J` THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_TAC THEN CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `is_realinterval J` THEN REWRITE_TAC[is_realinterval] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`min a (&0)`; `max b (&0)`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN REWRITE_TAC[real_min; real_max] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `m:num`] P2CO_IMAGE_IN_BALL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "img")))) THEN
  USE_THEN "balls" (MP_TAC o SPECL [`A:real`; `min a (&0)`; `max b (&0)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `CA:real` (X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2"))) THEN
  MAP_EVERY EXISTS_TAC [`CA:real`; `N1 + N2 + m:num`] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "img" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `N1 + N2 + m <= n:num` THEN ARITH_TAC; DISCH_THEN(LABEL_TAC "sub")] THEN
  USE_THEN "N2" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `N1 + N2 + m <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "top")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm"))) THEN
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET W n` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_W_MONO THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `N1 + N2 + m <= n:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) n) (t n))
                        (IMAGE ((phi:num->B->A) n) ((W:num->B->bool) m))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `?psi. mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                          ((W:num->B->bool) n)
                          (rfs_vtop ((V:num->(real->A topology)#
                                         (real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) n) (t n))
                          (rfs_vatlas (V n) (t n)) (IMAGE ((phi:num->B->A) n) (W n)) (phi n) psi`
    (X_CHOOSE_TAC `psi:A->B`) THENL [FIRST_ASSUM(ACCEPT_TAC o SPEC `n:num`); ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(W:num->B->bool) n`;
                   `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) n) (t n)`;
                   `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) (t n)`;
                   `IMAGE ((phi:num->B->A) n) ((W:num->B->bool) n)`; `(phi:num->B->A) n`;
                   `psi:A->B`; `(W:num->B->bool) m`] MFD_DIFFEO_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[mfd_diffeo];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) n) (t n))
                        (rfs_vball (V n) (t n) (x n) (A * inv(sqrt((Q:num->real) n))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
    MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) n`; `(t:num->real) n`; `(x:num->A) n`]
                  P2C_REGULAR_SLICE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `min a (&0) / (Q:num->real) n <= &0 /\ &0 <= max b (&0) / Q n`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2CO_DIV_SIGN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n)
                  (IMAGE ((phi:num->B->A) n) ((W:num->B->bool) m))
                  (t n + min a (&0) / Q n) (t n + max b (&0) / Q n)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CO_PERSISTS_SUBSET THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) n) (t n) (x n) (A * inv(sqrt((Q:num->real) n)))`;
      `(t:num->real) n`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[p2cz_from_smooth] THEN USE_THEN "reg" (MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[p2c_regular_view] THEN DISCH_THEN(ACCEPT_TAC o last o CONJUNCTS);
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) n) (t n) (x n) (A * inv(sqrt((Q:num->real) n)))` THEN
    CONJ_TAC THENL
     [USE_THEN "sub" ACCEPT_TAC;
      USE_THEN "top" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC P2CV_PERSISTS_MONO THEN
    MAP_EVERY EXISTS_TAC [`(t:num->real) n + min a (&0) / Q n`;
                          `(t:num->real) n + max b (&0) / Q n`] THEN
    ASM_REWRITE_TAC[REAL_LE_LADD] THEN CONJ_TAC THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "rm" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      USE_THEN "sub" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Completeness of the limit flow on [a,b] under a uniform                   *)
(* curvature bound CI.  The quadratic forms of the approximants at times s  *)
(* and 0 compare with the constant exp(8 CI (b - a)) (P2CV_QF_ALL), which   *)
(* does not depend on the region; the comparison passes to the limit, and   *)
(* at a bottom endpoint a < 0 (not the least element of J) by continuity of *)
(* the limit flow in time; complete metrics stay complete under a global    *)
(* comparison of the metrics.                                                *)
(* ------------------------------------------------------------------------- *)

let P2CO_COMPLETE_TRANSFER = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) g g' c.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     riemannian_metric atlas g' /\ &0 < c /\
     (!z v. z IN topspace top ==> v dot (g z ** v) <= c * (v dot (g' z ** v))) /\
     mfd_complete (top,atlas) g
     ==> mfd_complete (top,atlas) g'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_complete] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `r:real`] THEN DISCH_TAC THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^N^N) x (sqrt c * r)` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `mfd_complete (top,atlas) (g:A->real^N^N)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt c * mfd_dist (top,atlas) (g':A->real^N^N) x y` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFAH_DIST_COMPARE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]];
    MATCH_MP_TAC MFD_CBALL_CLOSED THEN ASM_REWRITE_TAC[]]);;

let P2CO_CONT_RIGHT_LE = prove
 (`!f a b c. f real_continuous atreal a /\ a < b /\ (!s. a < s /\ s <= b ==> c <= f s)
             ==> c <= f a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `f real_continuous atreal a` THEN REWRITE_TAC[real_continuous_atreal] THEN
  DISCH_THEN(MP_TAC o SPEC `c - f(a:real)`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a + min (d / &2) (b - a)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a + min (d / &2) (b - a)`) THEN
  ASM_REAL_ARITH_TAC);;

(* The quadratic forms of the approximants at one time converge to that of  *)
(* the limit at points of a region of the exhaustion.                       *)

let P2CO_QF_CONV = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) sub g a b m N s z v.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ p3_subseq sub /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\
     (!a b K k e. real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 < e
                  ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                                  ==> lck_dist2 k (metric_local atlas (chart_at atlas y) (g s))
                                        (metric_local atlas (chart_at atlas y)
                                           (p2cv_P V t Q atlas phi (sub n) s))
                                        (SND(chart_at atlas y) y) < e) /\
     a <= &0 /\ &0 <= b /\ real_interval[a,b] SUBSET J /\ m <= N /\
     (!n. N <= n ==> rfs_persists (V n) (IMAGE (phi n) (W m)) (t n + a / Q n) (t n + b / Q n)) /\
     (a < s \/ s = &0) /\ s <= b /\ z IN W m
     ==> ((\n. v dot (metric_local atlas (chart_at atlas z) (p2cv_P V t Q atlas phi (sub n) s)
                        (SND(chart_at atlas z) z) ** v))
          ---> v dot (g s z ** v)) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 (LABEL_TAC "lck")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "per") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  SUBGOAL_THEN `(z:B) IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (z:B). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `(W:num->B->bool) m` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `z:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:real) <= s /\ (s:real) IN J` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `real_interval[a,b] SUBSET J` THEN REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `z:B`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (z:B)))
                         (FST(chart_at atlas z) INTER (W:num->B->bool) m)`;
                 `metric_local (atlas:((B->bool)#(B->real^3))->bool) (chart_at atlas (z:B))
                               ((g:real->B->real^3^3) s)`;
                 `\n. metric_local (atlas:((B->bool)#(B->real^3))->bool) (chart_at atlas (z:B))
                        (p2cv_P (V:num->p2cvv3) t Q atlas (phi:num->B->A) ((sub:num->num) n) s)`;
                 `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (z:B)) z`; `N:num`;
                 `v:real^3`] P2CB_QF_LIM) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CR_RIEM_FIELD THEN EXISTS_TAC `top:B topology` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(SPEC `n:num` (MATCH_MP MONOTONE_BIGGER
      (REWRITE_RULE[p3_subseq] (ASSUME `p3_subseq (sub:num->num)`)))) THEN
    DISCH_TAC THEN REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CV_P_FIELD_AT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CV_HYP_ONE THEN
      MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      USE_THEN "per" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "lck" (MP_TAC o SPECL [`a:real`; `b:real`; `{z:B}`; `0`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_IN_SING]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` (LABEL_TAC "M")) THEN EXISTS_TAC `M:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "M" (MP_TAC o SPECL [`n:num`; `s:real`; `z:B`]) THEN
    REWRITE_TAC[IN_SING] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The comparison of the limit metrics at times 0 and s. *)

let P2CO_LIMIT_QF = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) sub g a b CI s z v.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ p3_subseq sub /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\
     (!a b K k e. real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 < e
                  ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                                  ==> lck_dist2 k (metric_local atlas (chart_at atlas y) (g s))
                                        (metric_local atlas (chart_at atlas y)
                                           (p2cv_P V t Q atlas phi (sub n) s))
                                        (SND(chart_at atlas y) y) < e) /\
     a <= &0 /\ &0 <= b /\ a < b /\ real_interval[a,b] SUBSET J /\ &0 <= CI /\
     (!m. ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN IMAGE (phi n) (W m)
                      ==> p3_vrm (V n) (t n + s / Q n) y <= CI * Q n) /\
     (a < s \/ s = &0) /\ s <= b /\ z IN topspace top
     ==> v dot (g (&0) z ** v) <= exp(&8 * CI * (b - a)) * (v dot (g s z ** v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 (LABEL_TAC "lck")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "CI")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `z:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?m. (z:B) IN (W:num->B->bool) m` (X_CHOOSE_TAC `m:num`) THENL
   [UNDISCH_TAC `UNIONS {(W:num->B->bool) k | k IN (:num)} = topspace top` THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `z:B`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MP (ASSUME `real_interval[a,b] SUBSET J`) o
              SPECL [`m:num`; `a:real`; `b:real`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `CM:real` (X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1"))) THEN
  USE_THEN "CI" (X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2") o SPEC `m:num`) THEN
  SUBGOAL_THEN
   `!n. N1 + N2 + m <= n
        ==> rfs_persists ((V:num->p2cvv3) n) (IMAGE ((phi:num->B->A) n) ((W:num->B->bool) m))
                         (t n + a / Q n) (t n + b / Q n)`
  (LABEL_TAC "per") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "N1" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real) <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. N1 + N2 + m <= n
        ==> v dot (metric_local atlas (chart_at atlas (z:B))
                     (p2cv_P (V:num->p2cvv3) t Q atlas (phi:num->B->A) n (&0))
                     (SND(chart_at atlas z) z) ** v) <=
            exp(&8 * CI * (b - a)) *
            (v dot (metric_local atlas (chart_at atlas z) (p2cv_P V t Q atlas phi n s)
                      (SND(chart_at atlas z) z) ** v))`
  (LABEL_TAC "cmp") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p2cv_one ((V:num->p2cvv3) n) (top,atlas) ((W:num->B->bool) m)
                           ((phi:num->B->A) n) (t n) (Q n)` ASSUME_TAC THENL
     [MATCH_MP_TAC P2CV_HYP_ONE THEN
      MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!s' y. a <= s' /\ s' <= b /\ y IN IMAGE ((phi:num->B->A) n) ((W:num->B->bool) m)
                         ==> p3_vrm ((V:num->p2cvv3) n) (t n + s' / Q n) y <= CI * Q n`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "N2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `rfs_persists ((V:num->p2cvv3) n) (IMAGE ((phi:num->B->A) n) ((W:num->B->bool) m))
                               (t n + a / Q n) (t n + b / Q n)` ASSUME_TAC THENL
     [USE_THEN "per" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (z:B)) z IN
                  IMAGE (SND(chart_at atlas z)) (FST(chart_at atlas z) INTER (W:num->B->bool) m)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CV_QF_ALL THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `(W:num->B->bool) m`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`;
                 `g:real->B->real^3^3`; `a:real`; `b:real`; `m:num`; `N1 + N2 + m:num`;
                 `&0`; `z:B`; `v:real^3`] P2CO_QF_CONV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`;
                 `g:real->B->real^3^3`; `a:real`; `b:real`; `m:num`; `N1 + N2 + m:num`;
                 `s:real`; `z:B`; `v:real^3`] P2CO_QF_CONV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  MAP_EVERY EXISTS_TAC
   [`\n. v dot (metric_local atlas (chart_at atlas (z:B))
                  (p2cv_P (V:num->p2cvv3) t Q atlas (phi:num->B->A) ((sub:num->num) n) (&0))
                  (SND(chart_at atlas z) z) ** v)`;
    `\n. exp(&8 * CI * (b - a)) *
         (v dot (metric_local atlas (chart_at atlas (z:B))
                   (p2cv_P (V:num->p2cvv3) t Q atlas (phi:num->B->A) ((sub:num->num) n) s)
                   (SND(chart_at atlas z) z) ** v))`] THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `N1 + N2 + m:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "cmp" MATCH_MP_TAC THEN
    MP_TAC(SPEC `n:num` (MATCH_MP MONOTONE_BIGGER
      (REWRITE_RULE[p3_subseq] (ASSUME `p3_subseq (sub:num->num)`)))) THEN
    ASM_ARITH_TAC]);;

(* Completeness on [a,b]. *)

let P2CO_COMPLETE_ON = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) sub g a b CI.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ p3_subseq sub /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\
     (!a b. a < b /\ real_interval[a,b] SUBSET J ==> ricci_flow_on (top,atlas) a b g) /\
     (!a b K k e. real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 < e
                  ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                                  ==> lck_dist2 k (metric_local atlas (chart_at atlas y) (g s))
                                        (metric_local atlas (chart_at atlas y)
                                           (p2cv_P V t Q atlas phi (sub n) s))
                                        (SND(chart_at atlas y) y) < e) /\
     mfd_complete (top,atlas) (g (&0)) /\
     a <= &0 /\ &0 <= b /\ real_interval[a,b] SUBSET J /\
     (!m. ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN IMAGE (phi n) (W m)
                      ==> p3_vrm (V n) (t n + s / Q n) y <= CI * Q n)
     ==> !s. a <= s /\ s <= b ==> mfd_complete (top,atlas) (g s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 (LABEL_TAC "rf")
    (CONJUNCTS_THEN2 (LABEL_TAC "lck") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CI")))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = &0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real) IN J` ASSUME_TAC THENL
   [UNDISCH_TAC `real_interval[a,b] SUBSET J` THEN REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. ?N. !n s y. N <= n /\ a <= s /\ s <= b /\
                    y IN IMAGE ((phi:num->B->A) n) ((W:num->B->bool) m)
                    ==> p3_vrm ((V:num->p2cvv3) n) (t n + s / Q n) y <= max CI (&0) * Q n`
  (LABEL_TAC "CI'") THENL
   [X_GEN_TAC `m:num` THEN USE_THEN "CI" (X_CHOOSE_TAC `N:num` o SPEC `m:num`) THEN
    EXISTS_TAC `N:num` THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `CI * (Q:num->real) n` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp(&8 * max CI (&0) * (b - a))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  MATCH_MP_TAC P2CO_COMPLETE_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`(g:real->B->real^3^3) (&0)`; `exp(&8 * max CI (&0) * (b - a))`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ALL_TAC;
    ASM_REWRITE_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`z:B`; `v:real^3`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `a < s` THENL
   [MATCH_MP_TAC P2CO_LIMIT_QF THEN
    MAP_EVERY EXISTS_TAC [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                          `J:real->bool`; `top:B topology`;
                          `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                          `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s:real = a` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?a1. a1 IN J /\ a1 < a` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a:real` o check (fun th ->
      try fst(dest_var(fst(dest_forall(concl th)))) = "a0" with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a1 (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "rf" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `is_realinterval J` THEN REWRITE_TAC[is_realinterval] THEN
    DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`a1:real`; `&0`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u. exp(&8 * max CI (&0) * (b - a)) *
                      (v dot ((g:real->B->real^3^3) u z ** v))`;
                 `a:real`; `&0`; `v dot ((g:real->B->real^3^3) (&0) z ** v)`]
                P2CO_CONT_RIGHT_LE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    EXISTS_TAC `--(&2) * mfd_ricci (atlas:((B->bool)#(B->real^3))->bool)
                           ((g:real->B->real^3^3) a) (z:B) (v:real^3) v` THEN
    MATCH_MP_TAC RFA_QFORM_DERIV THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `a1:real`; `&0`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2CO_LIMIT_QF THEN
    MAP_EVERY EXISTS_TAC [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                          `J:real->bool`; `top:B topology`;
                          `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                          `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* From a slice limit at the base time to the flow limit of                 *)
(* Thm 5.15 when the least element of J (if any) is 0: restriction to the   *)
(* joinable class of the base point, the region hypotheses from the balls,  *)
(* the flow limit P2CR_CORE (pc_p2c_fl514), completeness at 0 and on [a,b]. *)
(* ------------------------------------------------------------------------- *)

(* The uniform curvature bound on balls gives one on the images of the     *)
(* exhaustion.                                                               *)

let P2CO_CI_IMAGE = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g0 xl W phi a b CI.
     (!n. p2c_regular_view (V n)) /\
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\ mfd_complete (top,atlas) g0 /\
     (!y. y IN topspace top ==> mfd_joinable (top,atlas) xl y) /\
     (!A. &0 < A
          ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\
                          y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                          ==> p3_vrm (V n) (t n + s / Q n) y <= CI * Q n)
     ==> !m. ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN IMAGE (phi n) (W m)
                         ==> p3_vrm (V n) (t n + s / Q n) y <= CI * Q n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "reg") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CI"))))) THEN
  USE_THEN "reg" (LABEL_TAC "sl" o MATCH_MP P2CO_REGULAR_SLICES) THEN
  X_GEN_TAC `m:num` THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `m:num`] P2CO_IMAGE_IN_BALL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "img")))) THEN
  USE_THEN "CI" (MP_TAC o C MP (ASSUME `&0 < A`) o SPEC `A:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  EXISTS_TAC `N1 + N2:num` THEN REPEAT STRIP_TAC THEN
  USE_THEN "N2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_ARITH_TAC;
    USE_THEN "img" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The restricted slice limit satisfies the hypotheses of the assembly.    *)

let P2CO_HYP_FROM_SLICE = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q J (top:B topology) atlas g0 xl W phi.
     is_realinterval J /\ (&0) IN J /\
     (!a0. a0 IN J /\ (!s. s IN J ==> a0 <= s) ==> a0 = &0) /\
     (!n. p2c_regular_view (V n)) /\ (!n. x n IN topspace(rfs_vtop (V n) (t n))) /\
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\ mfd_complete (top,atlas) g0 /\
     (!A a b. &0 < A /\ real_interval[a,b] SUBSET J
              ==> ?CA N. !n. N <= n
                      ==> (!s. a <= s /\ s <= b
                               ==> rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))) SUBSET
                                   topspace(rfs_vtop (V n) (t n + s / Q n))) /\
                          rfs_persists (V n) (rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))))
                            (t n + a / Q n) (t n + b / Q n) /\
                          !s y. a <= s /\ s <= b /\
                                y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                ==> p3_vrm (V n) (t n + s / Q n) y <= CA * Q n)
     ==> p2cv_hyp V x t Q J
           (subtopology top {y | mfd_joinable (top,atlas) xl y},
            restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y})
           (restrict_metric atlas {y | mfd_joinable (top,atlas) xl y} g0) xl
           (\k. W k INTER {y | mfd_joinable (top,atlas) xl y}) phi /\
         p2c_slice_limit_with V x t Q
           (subtopology top {y | mfd_joinable (top,atlas) xl y},
            restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y})
           (restrict_metric atlas {y | mfd_joinable (top,atlas) xl y} g0) xl
           (\k. W k INTER {y | mfd_joinable (top,atlas) xl y}) phi /\
         mfd_complete (subtopology top {y | mfd_joinable (top,atlas) xl y},
                       restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y})
                      (restrict_metric atlas {y | mfd_joinable (top,atlas) xl y} g0) /\
         (!y. y IN topspace (subtopology top {y | mfd_joinable (top,atlas) xl y})
              ==> mfd_joinable (subtopology top {y | mfd_joinable (top,atlas) xl y},
                                restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y}) xl y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "reg")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lim")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "balls")))))))) THEN
  USE_THEN "reg" (LABEL_TAC "sl" o MATCH_MP P2CO_REGULAR_SLICES) THEN
  USE_THEN "lim" (STRIP_ASSUME_TAC o REWRITE_RULE[p2c_slice_limit_with]) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`] P2CO_SLICE_WITH_RESTRICT) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rlim") ASSUME_TAC) THEN
  SUBGOAL_THEN
   `mfd_complete (subtopology (top:B topology)
                    {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y},
                  restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y})
                 (restrict_metric atlas {y | mfd_joinable (top,atlas) xl y} (g0:B->real^3^3))`
  (LABEL_TAC "rcompl") THENL
   [MATCH_MP_TAC P2CO_CLASS_COMPLETE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN topspace (subtopology (top:B topology)
                         {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y})
        ==> mfd_joinable (subtopology top {y | mfd_joinable (top,atlas) xl y},
                          restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y}) xl y`
  (LABEL_TAC "rjoin") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CO_CLASS_ALL_JOINABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`;
                 `subtopology (top:B topology)
                    {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
                 `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool)
                    {y | mfd_joinable (top:B topology,atlas) xl y}`;
                 `restrict_metric (atlas:((B->bool)#(B->real^3))->bool)
                    {y | mfd_joinable (top:B topology,atlas) xl y} (g0:B->real^3^3)`;
                 `xl:B`;
                 `\k. (W:num->B->bool) k INTER
                      {y | mfd_joinable (top:B topology,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
                 `phi:num->B->A`] P2CO_REGION_FROM_BALLS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[] THEN DISCH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`;
                   `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`;
                   `subtopology (top:B topology)
                      {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
                   `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool)
                      {y | mfd_joinable (top:B topology,atlas) xl y}`;
                   `restrict_metric (atlas:((B->bool)#(B->real^3))->bool)
                      {y | mfd_joinable (top:B topology,atlas) xl y} (g0:B->real^3^3)`;
                   `xl:B`;
                   `\k. (W:num->B->bool) k INTER
                        {y | mfd_joinable (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
                               xl y}`;
                   `phi:num->B->A`] P2CR_HYP) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "rlim" ACCEPT_TAC;
    USE_THEN "rcompl" ACCEPT_TAC;
    USE_THEN "rjoin" ACCEPT_TAC]);;

(* The flow limit for views, from a complete slice limit at the base time. *)

let P2CO_FROM_SLICE_V = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q J (top:B topology) atlas g0 xl W phi.
     is_realinterval J /\ (&0) IN J /\
     (!a0. a0 IN J /\ (!s. s IN J ==> a0 <= s) ==> a0 = &0) /\
     (!n. p2c_regular_view (V n)) /\ (!n. x n IN topspace(rfs_vtop (V n) (t n))) /\
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\ mfd_complete (top,atlas) g0 /\
     (!A a b. &0 < A /\ real_interval[a,b] SUBSET J
              ==> ?CA N. !n. N <= n
                      ==> (!s. a <= s /\ s <= b
                               ==> rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))) SUBSET
                                   topspace(rfs_vtop (V n) (t n + s / Q n))) /\
                          rfs_persists (V n) (rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))))
                            (t n + a / Q n) (t n + b / Q n) /\
                          !s y. a <= s /\ s <= b /\
                                y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                ==> p3_vrm (V n) (t n + s / Q n) y <= CA * Q n)
     ==> ?sub (top':B topology) atlas' g.
            p3_subseq sub /\
            p3_flow_limit_on (\n. V (sub n)) (x o sub) (t o sub) (Q o sub) J (top',atlas') g xl /\
            (!s. s IN J ==> riemannian_metric atlas' (g s)) /\
            mfd_complete (top',atlas') (g (&0)) /\
            (!a b. a < b /\ real_interval[a,b] SUBSET J ==> ricci_flow_on (top',atlas') a b g) /\
            (!a b CI. a <= &0 /\ &0 <= b /\ real_interval[a,b] SUBSET J /\
                      (!A. &0 < A
                           ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\
                                           y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                           ==> p3_vrm (V n) (t n + s / Q n) y <= CI * Q n)
                      ==> !s. a <= s /\ s <= b ==> mfd_complete (top',atlas') (g s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2CO_HYP_FROM_SLICE) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hyp") (CONJUNCTS_THEN2 (LABEL_TAC "rlim")
    (CONJUNCTS_THEN2 (LABEL_TAC "rcompl") (LABEL_TAC "rjoin")))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  USE_THEN "hyp" (MP_TAC o MATCH_MP P2CR_CORE) THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "flw") (CONJUNCTS_THEN2 (LABEL_TAC "riem")
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (LABEL_TAC "lck")))))))) THEN
  MAP_EVERY EXISTS_TAC
   [`sub:num->num`;
    `subtopology (top:B topology)
       {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool)
       {y | mfd_joinable (top:B topology,atlas) xl y}`;
    `g:real->B->real^3^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
    MAP_EVERY EXISTS_TAC
     [`\k. (W:num->B->bool) k INTER
           {y | mfd_joinable (top:B topology,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
      `(phi:num->B->A) o (sub:num->num)`] THEN
    USE_THEN "flw" ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `CI:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CIh")))) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`;
                 `subtopology (top:B topology)
                    {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
                 `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool)
                    {y | mfd_joinable (top:B topology,atlas) xl y}`;
                 `restrict_metric (atlas:((B->bool)#(B->real^3))->bool)
                    {y | mfd_joinable (top:B topology,atlas) xl y} (g0:B->real^3^3)`;
                 `xl:B`;
                 `\k. (W:num->B->bool) k INTER
                      {y | mfd_joinable (top:B topology,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
                 `phi:num->B->A`; `a:real`; `b:real`; `CI:real`] P2CO_CI_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[] THEN DISCH_TAC] THEN
  MATCH_MP_TAC P2CO_COMPLETE_ON THEN
  MAP_EVERY EXISTS_TAC
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`;
    `restrict_metric (atlas:((B->bool)#(B->real^3))->bool)
       {y | mfd_joinable (top:B topology,atlas) xl y} (g0:B->real^3^3)`;
    `xl:B`;
    `\k. (W:num->B->bool) k INTER
         {y | mfd_joinable (top:B topology,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
    `phi:num->B->A`; `sub:num->num`; `CI:real`] THEN
  ASM_REWRITE_TAC[]);;

(* The same for the rescaled histories of Thm 5.15 along a subsequence      *)
(* carrying a slice limit at the base time.                                  *)

let P2CO_FROM_SLICE = prove
 (`!(hs:num->(A)rfs_history) x t Q J sub0 (top:B topology) atlas g0 xl.
     is_realinterval J /\ (&0) IN J /\
     (!a0. a0 IN J /\ (!s. s IN J ==> a0 <= s) ==> a0 = &0) /\
     (!n. rfs_history_ok (hs n) /\ &0 < Q n /\ x n IN topspace(rfs_top_at (hs n) (t n))) /\
     (!n. p2c_regular_view (rfs_view (hs n))) /\
     (!A a b. &0 < A /\ real_interval[a,b] SUBSET J
              ==> ?CA N. !n. N <= n
                      ==> (!s. a <= s /\ s <= b
                               ==> rfs_vball (rfs_view (hs n)) (t n) (x n)
                                     (A * inv(sqrt(Q n))) SUBSET
                                   topspace(rfs_top_at (hs n) (t n + s / Q n))) /\
                          rfs_persists (rfs_view (hs n))
                            (rfs_vball (rfs_view (hs n)) (t n) (x n) (A * inv(sqrt(Q n))))
                            (t n + a / Q n) (t n + b / Q n) /\
                          !s y. a <= s /\ s <= b /\
                                y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                       (A * inv(sqrt(Q n)))
                                ==> p3_vrm (rfs_view (hs n)) (t n + s / Q n) y <= CA * Q n) /\
     p3_subseq sub0 /\
     p3_slice_limit (\n. rfs_view (hs (sub0 n))) (x o sub0) (t o sub0) (Q o sub0)
                    (top,atlas) g0 xl
     ==> ?sub (top:B topology) atlas g xl.
              p3_subseq sub /\
              p3_flow_limit_on (\n. rfs_view (hs (sub n))) (x o sub) (t o sub) (Q o sub) J
                               (top,atlas) g xl /\
              (!s. s IN J ==> riemannian_metric atlas (g s)) /\
              mfd_complete (top,atlas) (g (&0)) /\
              (!a b. a < b /\ real_interval[a,b] SUBSET J ==> ricci_flow_on (top,atlas) a b g) /\
              (!a b CI. a <= &0 /\ &0 <= b /\ real_interval[a,b] SUBSET J /\
                        (!A. &0 < A
                             ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\
                                             y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                                    (A * inv(sqrt(Q n)))
                                             ==> p3_vrm (rfs_view (hs n)) (t n + s / Q n) y <=
                                                 CI * Q n)
                        ==> !s. a <= s /\ s <= b ==> mfd_complete (top,atlas) (g s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "base")
    (CONJUNCTS_THEN2 (LABEL_TAC "reg") (CONJUNCTS_THEN2 (LABEL_TAC "balls")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sl")))))))) THEN
  SUBGOAL_THEN `!n. n <= (sub0:num->num) n` (LABEL_TAC "big") THENL
   [UNDISCH_TAC `p3_subseq (sub0:num->num)` THEN REWRITE_TAC[p3_subseq] THEN
    DISCH_TAC THEN MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "sl" (MP_TAC o REWRITE_RULE[P2C_SLICE_LIMIT_WITH]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `W:num->B->bool`
    (X_CHOOSE_THEN `phi:num->B->A` ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`\n. rfs_view ((hs:num->(A)rfs_history) ((sub0:num->num) n))`;
                 `(x:num->A) o (sub0:num->num)`; `(t:num->real) o (sub0:num->num)`;
                 `(Q:num->real) o (sub0:num->num)`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`] P2CO_FROM_SLICE_V) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM; P2C_RFS_VIEW_PARTS] THEN
    MAP_EVERY X_GEN_TAC [`A:real`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    USE_THEN "balls" (MP_TAC o C MP (CONJ (ASSUME `&0 < A`)
      (ASSUME `real_interval[a,b] SUBSET J`)) o SPECL [`A:real`; `a:real`; `b:real`]) THEN
    DISCH_THEN(X_CHOOSE_THEN `CA:real` (X_CHOOSE_THEN `N:num` (LABEL_TAC "N"))) THEN
    MAP_EVERY EXISTS_TAC [`CA:real`; `N:num`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "N" MATCH_MP_TAC THEN
    USE_THEN "big" (MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fl")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cpl")))))))))) THEN
  MAP_EVERY EXISTS_TAC [`(sub0:num->num) o (sub:num->num)`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `p3_subseq (sub0:num->num)` THEN UNDISCH_TAC `p3_subseq (sub:num->num)` THEN
    REWRITE_TAC[p3_subseq; o_THM] THEN MESON_TAC[];
    USE_THEN "fl" MP_TAC THEN REWRITE_TAC[GSYM o_ASSOC; o_THM] THEN SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `CI:real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CIh")))) THEN
    USE_THEN "cpl" MATCH_MP_TAC THEN EXISTS_TAC `CI:real` THEN ASM_REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "CIh" (MP_TAC o C MP (ASSUME `&0 < A`) o SPEC `A:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "big" (MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The slice limit at the base time when the least element of J              *)
(* (if any) is 0: Cheeger-Gromov compactness P2CK_CG_COMPACT with the        *)
(* derivative hypothesis at a0 = 0 (case B), or Thm 5.11 with the backward   *)
(* persistence on [a1,0] for some a1 < 0 in J (case A).                      *)
(* ------------------------------------------------------------------------- *)

let P2CO_CASE_B = prove
 (`!(hs:num->(A)rfs_history) x t Q J.
     is_realinterval J /\ (&0) IN J /\ (!s. s IN J ==> &0 <= s) /\
     (!n. rfs_history_ok (hs n) /\ &0 < Q n /\ x n IN topspace(rfs_top_at (hs n) (t n))) /\
     (!n. p2c_regular_view (rfs_view (hs n))) /\
     (!A a b. &0 < A /\ real_interval[a,b] SUBSET J
              ==> ?CA N. !n. N <= n
                      ==> (!s. a <= s /\ s <= b
                               ==> rfs_vball (rfs_view (hs n)) (t n) (x n)
                                     (A * inv(sqrt(Q n))) SUBSET
                                   topspace(rfs_top_at (hs n) (t n + s / Q n))) /\
                          rfs_persists (rfs_view (hs n))
                            (rfs_vball (rfs_view (hs n)) (t n) (x n) (A * inv(sqrt(Q n))))
                            (t n + a / Q n) (t n + b / Q n) /\
                          !s y. a <= s /\ s <= b /\
                                y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                       (A * inv(sqrt(Q n)))
                                ==> p3_vrm (rfs_view (hs n)) (t n + s / Q n) y <= CA * Q n) /\
     (!a0 A l. a0 IN J /\ (!s. s IN J ==> a0 <= s) /\ &0 < A
               ==> ?CAl N. !n y. N <= n /\
                                 y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                        (A * inv(sqrt(Q n)))
                                 ==> p3_vderiv2 (rfs_view (hs n)) l (t n + a0 / Q n) y <=
                                     CAl * Q n pow (l + 2)) /\
     (?r0 kappa N. &0 < r0 /\ &0 < kappa /\
        !n. N <= n
            ==> ?v. mfd_has_volume (rfs_top_at (hs n) (t n),rfs_atlas_at (hs n) (t n))
                      (rfs_metric_at (hs n) (t n))
                      (rfs_vball (rfs_view (hs n)) (t n) (x n) (r0 * inv(sqrt(Q n)))) v /\
                    kappa * (r0 * inv(sqrt(Q n))) pow 3 <= v)
     ==> ?sub (top:(real^3)topology) atlas g xl.
              p3_subseq sub /\
              p3_flow_limit_on (\n. rfs_view (hs (sub n))) (x o sub) (t o sub) (Q o sub) J
                               (top,atlas) g xl /\
              (!s. s IN J ==> riemannian_metric atlas (g s)) /\
              mfd_complete (top,atlas) (g (&0)) /\
              (!a b. a < b /\ real_interval[a,b] SUBSET J ==> ricci_flow_on (top,atlas) a b g) /\
              (!a b CI. a <= &0 /\ &0 <= b /\ real_interval[a,b] SUBSET J /\
                        (!A. &0 < A
                             ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\
                                             y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                                    (A * inv(sqrt(Q n)))
                                             ==> p3_vrm (rfs_view (hs n)) (t n + s / Q n) y <=
                                                 CI * Q n)
                        ==> !s. a <= s /\ s <= b ==> mfd_complete (top,atlas) (g s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "base")
    (CONJUNCTS_THEN2 (LABEL_TAC "reg") (CONJUNCTS_THEN2 (LABEL_TAC "balls")
    (CONJUNCTS_THEN2 (LABEL_TAC "der") (LABEL_TAC "vol")))))))) THEN
  MP_TAC(SPEC `(:A)` P2CK_CG_COMPACT) THEN REWRITE_TAC[P2C_CG_COMPACT_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`\n. rfs_view ((hs:num->(A)rfs_history) n)`; `x:num->A`;
                             `t:num->real`; `Q:num->real`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
      MP_TAC(ISPECL [`rfs_view ((hs:num->(A)rfs_history) n)`; `(t:num->real) n`; `(x:num->A) n`]
                    P2C_REGULAR_SLICE) THEN
      ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN SIMP_TAC[];
      X_GEN_TAC `R:real` THEN DISCH_TAC THEN EXISTS_TAC `0` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
      ASM_SIMP_TAC[CLOSED_IN_CLOSURE_OF; P2C_RFS_VIEW_PARTS; P2CW_HIST_COMPACT];
      MAP_EVERY X_GEN_TAC [`R:real`; `l:num`] THEN DISCH_TAC THEN
      USE_THEN "der" (MP_TAC o SPECL [`&0`; `R:real`; `l:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN MESON_TAC[];
      USE_THEN "vol" MP_TAC THEN REWRITE_TAC[P2C_RFS_VIEW_PARTS]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub0:num->num` (X_CHOOSE_THEN `top:(real^3)topology`
    (X_CHOOSE_THEN `atlas:((real^3->bool)#(real^3->real^3))->bool`
    (X_CHOOSE_THEN `g0:real^3->real^3^3` (X_CHOOSE_THEN `xl:real^3` STRIP_ASSUME_TAC))))) THEN
  MATCH_MP_TAC P2CO_FROM_SLICE THEN
  MAP_EVERY EXISTS_TAC [`sub0:num->num`; `top:(real^3)topology`;
                        `atlas:((real^3->bool)#(real^3->real^3))->bool`;
                        `g0:real^3->real^3^3`; `xl:real^3`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `a0:real` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let P2CO_CASE_A = prove
 (`!(u:A->bool) (hs:num->(A)rfs_history) x t Q J a1.
     P2_THM_5_11_STATEMENT u (:real^3) /\
     is_realinterval J /\ (&0) IN J /\ a1 IN J /\ a1 < &0 /\
     (!a0. a0 IN J /\ (!s. s IN J ==> a0 <= s) ==> a0 = &0) /\
     (!n. rfs_history_ok (hs n) /\ &0 < Q n /\ x n IN topspace(rfs_top_at (hs n) (t n))) /\
     (!n. p2c_regular_view (rfs_view (hs n))) /\
     (!A a b. &0 < A /\ real_interval[a,b] SUBSET J
              ==> ?CA N. !n. N <= n
                      ==> (!s. a <= s /\ s <= b
                               ==> rfs_vball (rfs_view (hs n)) (t n) (x n)
                                     (A * inv(sqrt(Q n))) SUBSET
                                   topspace(rfs_top_at (hs n) (t n + s / Q n))) /\
                          rfs_persists (rfs_view (hs n))
                            (rfs_vball (rfs_view (hs n)) (t n) (x n) (A * inv(sqrt(Q n))))
                            (t n + a / Q n) (t n + b / Q n) /\
                          !s y. a <= s /\ s <= b /\
                                y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                       (A * inv(sqrt(Q n)))
                                ==> p3_vrm (rfs_view (hs n)) (t n + s / Q n) y <= CA * Q n) /\
     (?r0 kappa N. &0 < r0 /\ &0 < kappa /\
        !n. N <= n
            ==> ?v. mfd_has_volume (rfs_top_at (hs n) (t n),rfs_atlas_at (hs n) (t n))
                      (rfs_metric_at (hs n) (t n))
                      (rfs_vball (rfs_view (hs n)) (t n) (x n) (r0 * inv(sqrt(Q n)))) v /\
                    kappa * (r0 * inv(sqrt(Q n))) pow 3 <= v)
     ==> ?sub (top:(real^3)topology) atlas g xl.
              p3_subseq sub /\
              p3_flow_limit_on (\n. rfs_view (hs (sub n))) (x o sub) (t o sub) (Q o sub) J
                               (top,atlas) g xl /\
              (!s. s IN J ==> riemannian_metric atlas (g s)) /\
              mfd_complete (top,atlas) (g (&0)) /\
              (!a b. a < b /\ real_interval[a,b] SUBSET J ==> ricci_flow_on (top,atlas) a b g) /\
              (!a b CI. a <= &0 /\ &0 <= b /\ real_interval[a,b] SUBSET J /\
                        (!A. &0 < A
                             ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\
                                             y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                                    (A * inv(sqrt(Q n)))
                                             ==> p3_vrm (rfs_view (hs n)) (t n + s / Q n) y <=
                                                 CI * Q n)
                        ==> !s. a <= s /\ s <= b ==> mfd_complete (top,atlas) (g s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "511") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "base") (CONJUNCTS_THEN2 (LABEL_TAC "reg")
    (CONJUNCTS_THEN2 (LABEL_TAC "balls") (LABEL_TAC "vol")))))))))) THEN
  SUBGOAL_THEN `real_interval[a1,&0] SUBSET J` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `is_realinterval J` THEN REWRITE_TAC[is_realinterval] THEN
    DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`a1:real`; `&0`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "511" (MP_TAC o REWRITE_RULE[P2_THM_5_11_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL [`hs:num->(A)rfs_history`; `x:num->A`; `t:num->real`;
                             `Q:num->real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "balls" (MP_TAC o C MP (CONJ (ASSUME `&0 < A`)
      (ASSUME `real_interval[a1,&0] SUBSET J`)) o SPECL [`A:real`; `a1:real`; `&0`]) THEN
    DISCH_THEN(X_CHOOSE_THEN `CA:real` (X_CHOOSE_THEN `N:num` (LABEL_TAC "N"))) THEN
    MAP_EVERY EXISTS_TAC [`CA:real`; `--a1:real`; `N:num`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "N" (MP_TAC o C MP (ASSUME `N:num <= n`) o SPEC `n:num`) THEN
    USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    SUBGOAL_THEN `(t:num->real) n - --a1 * inv(Q n) = t n + a1 / Q n /\
                  t n + &0 / Q n = t n` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm"))) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "rm" (MP_TAC o SPECL [`(s - (t:num->real) n) * Q n`; `y:A`]) THEN
    SUBGOAL_THEN `(t:num->real) n + ((s - t n) * Q n) / Q n = s` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < (Q:num->real) n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN
      SUBGOAL_THEN `a1 / (Q:num->real) n < s - t n` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LDIV_EQ]];
      MATCH_MP_TAC(REAL_ARITH `&0 <= (t - s) * q ==> (s - t) * q <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub0:num->num` (X_CHOOSE_THEN `top:(real^3)topology`
    (X_CHOOSE_THEN `atlas:((real^3->bool)#(real^3->real^3))->bool`
    (X_CHOOSE_THEN `g0:real^3->real^3^3` (X_CHOOSE_THEN `xl:real^3` STRIP_ASSUME_TAC))))) THEN
  MATCH_MP_TAC P2CO_FROM_SLICE THEN
  MAP_EVERY EXISTS_TAC [`sub0:num->num`; `top:(real^3)topology`;
                        `atlas:((real^3->bool)#(real^3->real^3))->bool`;
                        `g0:real^3->real^3^3`; `xl:real^3`] THEN
  ASM_REWRITE_TAC[]);;

(* Thm 5.15 when the least element of J (if any) is 0. *)

let P2CO_THM_5_15_AB = prove
 (`!u:A->bool.
     P2_THM_5_11_STATEMENT u (:real^3) /\ P2C_HISTORY_REGULAR_STATEMENT u
     ==> !hs x t Q J.
           is_realinterval J /\ (&0) IN J /\
           (!a0. a0 IN J /\ (!s. s IN J ==> a0 <= s) ==> a0 = &0) /\
           (!n. rfs_history_ok (hs n:(A)rfs_history) /\ &0 < Q n /\
                x n IN topspace(rfs_top_at (hs n) (t n))) /\
           (!A a b. &0 < A /\ real_interval[a,b] SUBSET J
                    ==> ?CA N. !n. N <= n
                            ==> (!s. a <= s /\ s <= b
                                     ==> rfs_vball (rfs_view (hs n)) (t n) (x n)
                                           (A * inv(sqrt(Q n))) SUBSET
                                         topspace(rfs_top_at (hs n) (t n + s / Q n))) /\
                                rfs_persists (rfs_view (hs n))
                                  (rfs_vball (rfs_view (hs n)) (t n) (x n) (A * inv(sqrt(Q n))))
                                  (t n + a / Q n) (t n + b / Q n) /\
                                !s y. a <= s /\ s <= b /\
                                      y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                             (A * inv(sqrt(Q n)))
                                      ==> p3_vrm (rfs_view (hs n)) (t n + s / Q n) y <= CA * Q n) /\
           (!a0 A l. a0 IN J /\ (!s. s IN J ==> a0 <= s) /\ &0 < A
                     ==> ?CAl N. !n y. N <= n /\
                                       y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                              (A * inv(sqrt(Q n)))
                                       ==> p3_vderiv2 (rfs_view (hs n)) l (t n + a0 / Q n) y <=
                                           CAl * Q n pow (l + 2)) /\
           (?r0 kappa N. &0 < r0 /\ &0 < kappa /\
              !n. N <= n
                  ==> ?v. mfd_has_volume (rfs_top_at (hs n) (t n),rfs_atlas_at (hs n) (t n))
                            (rfs_metric_at (hs n) (t n))
                            (rfs_vball (rfs_view (hs n)) (t n) (x n) (r0 * inv(sqrt(Q n)))) v /\
                          kappa * (r0 * inv(sqrt(Q n))) pow 3 <= v)
           ==> ?sub (top:(real^3)topology) atlas g xl.
                  p3_subseq sub /\
                  p3_flow_limit_on (\n. rfs_view (hs (sub n))) (x o sub) (t o sub) (Q o sub) J
                                   (top,atlas) g xl /\
                  (!s. s IN J ==> riemannian_metric atlas (g s)) /\
                  mfd_complete (top,atlas) (g (&0)) /\
                  (!a b. a < b /\ real_interval[a,b] SUBSET J
                         ==> ricci_flow_on (top,atlas) a b g) /\
                  (!a b CI. a <= &0 /\ &0 <= b /\ real_interval[a,b] SUBSET J /\
                            (!A. &0 < A
                                 ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\
                                                 y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                                        (A * inv(sqrt(Q n)))
                                                 ==> p3_vrm (rfs_view (hs n)) (t n + s / Q n) y <=
                                                     CI * Q n)
                            ==> !s. a <= s /\ s <= b ==> mfd_complete (top,atlas) (g s))`,
  GEN_TAC THEN REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "511") (LABEL_TAC "hr")) THEN
  MAP_EVERY X_GEN_TAC [`hs:num->(A)rfs_history`; `x:num->A`; `t:num->real`; `Q:num->real`;
                       `J:real->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "base")
    (CONJUNCTS_THEN2 (LABEL_TAC "balls") (CONJUNCTS_THEN2 (LABEL_TAC "der")
    (LABEL_TAC "vol"))))))) THEN
  SUBGOAL_THEN `!n. p2c_regular_view (rfs_view ((hs:num->(A)rfs_history) n))` (LABEL_TAC "reg")
  THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "hr" MATCH_MP_TAC THEN
    USE_THEN "base" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `n:num` th)]);
    ALL_TAC] THEN
  ASM_CASES_TAC `!s. s IN J ==> &0 <= s` THENL
   [MATCH_MP_TAC P2CO_CASE_B THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC P2CO_CASE_A THEN
  MAP_EVERY EXISTS_TAC [`u:A->bool`; `a1:real`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Thm 5.15 (the least element of J, if any, is 0) and its route.            *)
(* ------------------------------------------------------------------------- *)

let P2CO_THM_5_15 = prove
 (`!u:A->bool. P2_THM_5_11_STATEMENT u (:real^3) /\ P2C_HISTORY_REGULAR_STATEMENT u
               ==> P2C_THM_5_15_STATEMENT u (:real^3)`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP P2CO_THM_5_15_AB) THEN
  ASM_REWRITE_TAC[P2C_THM_5_15_STATEMENT]);;

let P2CO_THM_5_15_ROUTE = prove
 (`!u:A->bool. P2C_THM_5_15_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_THM_5_15_ROUTE_STATEMENT] THEN MESON_TAC[P2CO_THM_5_15]);;

