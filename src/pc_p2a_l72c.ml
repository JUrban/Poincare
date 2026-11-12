(* ========================================================================= *)
(* pc_p2a_l72c: O10 part 3, box data.  For a region W over (a',b'] and a set *)
(* C compact in the slice at b', C inside W: finitely many region charts at  *)
(* b' with balls of radius 6 R k inside the chart images covering C (radii   *)
(* at least r), and uniform bounds for the region metric family on those     *)
(* balls for times in [b' - T1, b'] (up to the region top: the s-window      *)
(* around 0 with tt := b'), the lower bound lam, the upper bound Gm, the     *)
(* scalar curvature bound Rm (p2ak_bxd).  The single-box case (b' = tt the   *)
(* base time, as for flows) is the route to FL2; the view form uses one box  *)
(* datum per box.                                                            *)
(* The first part: the scalar curvature in a region chart, the chart cover,  *)
(* the bounds, the box datum.                                                *)
(* ========================================================================= *)

needs "src/pc_p2a_l72b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The scalar curvature of the slice metric at a point of a region chart is  *)
(* the local scalar curvature of the region metric family in that chart      *)
(* (the scalar step of P2A_LSINT_CHART, pc_p2a_lgeo3).                       *)
(* ------------------------------------------------------------------------- *)

let P2AK_SCALAR_CHART = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' b' U (phi:A->real^N) t y.
     p2a_svs V /\ p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < t /\ t <= b' /\ y IN U INTER W
     ==> mfd_scalar (p2a_vatlas V t) (p2a_vmetric V t) y =
         lscalar (p2a_rlocal V W b' (U INTER W,phi) t) (phi y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `t:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN
                topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (t))`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
      `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) (t)) (W:A->bool)`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (t))
                                  (p2a_vmetric V (t))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N))` THEN
    REWRITE_TAC[p2a_svs] THEN DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `t:real`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) t`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) t`;
                 `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_scalar] THEN
  ABBREV_TAC `c' = chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                          (real->A->real^N^N)) (t))
                            ((y:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `t:real`; `c':(A->bool)#(A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) THEN
  ABBREV_TAC `O = IMAGE (phi:A->real^N) ((U INTER W) INTER FST(c':(A->bool)#(A->real^N)))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `O2 = IMAGE (SND(c':(A->bool)#(A->real^N))) ((U INTER W) INTER FST c')` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `h = chart_trans (U INTER W:A->bool,phi:A->real^N) c'` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `G' = metric_local (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                              (real->A->real^N^N)) (t))
                                c' (p2a_vmetric V (t))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `!q:A. q IN U INTER W ==> (h:real^N->real^N)(phi q) = SND(c':(A->bool)#(A->real^N)) q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[chart_trans] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b'`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b'`;
                   `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `q:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^N) y IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN O
        ==> p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N) (t) y =
            mpullback (h:real^N->real^N) G' y`
  ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `q:A` THEN STRIP_TAC THEN EXPAND_TAC "h" THEN EXPAND_TAC "G'" THEN
    MATCH_MP_TAC P2A_RLOCAL_SLICE THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field O2 (G':real^N->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c':(A->bool)#(A->real^N))) (FST c')` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "G'" THEN
      UNDISCH_TAC `riemannian_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (t))
                                  (p2a_vmetric V (t))` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "O2" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lscalar (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N) (t))
            (phi y) =
    lscalar G' (SND(c':(A->bool)#(A->real^N)) y)`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS `lscalar (mpullback (h:real^N->real^N) G') ((phi:A->real^N) y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `O:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`O2:real^N->bool`; `O:real^N->bool`; `h:real^N->real^N`;
                   `chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N)`;
                   `G':real^N->real^N^N`; `(phi:A->real^N) y`] LSCALAR_PULLBACK) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Finitely many region charts at b' (chart_at of the atlas at b'), with   *)
(* closed balls of radius 6 R k around the chart images of their centres   *)
(* inside the chart images of U INTER W, whose radius-R k balls cover C;   *)
(* the radii are at least r > 0 (compactness of C in the slice at b').     *)

let P2AK_SB_CHARTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' b' C.
     p2a_region V W a' b' /\ a' < b' /\ compact_in (p2a_vtop V b') C /\ C SUBSET W
     ==> ?Fs R r.
           FINITE Fs /\ Fs SUBSET C /\ &0 < r /\
           (!k. k IN Fs
                ==> chart_at (p2a_vatlas V b') k IN p2a_vatlas V b' /\
                    k IN FST(chart_at (p2a_vatlas V b') k) /\ r <= R k /\
                    cball(SND(chart_at (p2a_vatlas V b') k) k,&6 * R k) SUBSET
                    IMAGE (SND(chart_at (p2a_vatlas V b') k))
                          (FST(chart_at (p2a_vatlas V b') k) INTER W)) /\
           (!y. y IN C
                ==> ?k. k IN Fs /\ y IN FST(chart_at (p2a_vatlas V b') k) INTER W /\
                        dist(SND(chart_at (p2a_vatlas V b') k) y,
                             SND(chart_at (p2a_vatlas V b') k) k) < R k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `b':real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  ABBREV_TAC `ch = chart_at (p2a_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b')` THEN
  SUBGOAL_THEN `(C:A->bool) SUBSET topspace(p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b')`
  ASSUME_TAC THENL [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. y IN C ==> (ch:A->(A->bool)#(A->real^N)) y IN
                                 p2a_vatlas (V:(real->A topology)#
                                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b' /\
                                 y IN FST(ch y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN EXPAND_TAC "ch" THEN MATCH_MP_TAC CHART_AT THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:A. ?R. y IN C ==> &0 < R /\
              cball(SND((ch:A->(A->bool)#(A->real^N)) y) y,&6 * R) SUBSET
              IMAGE (SND(ch y)) (FST(ch y) INTER W)`
  MP_TAC THENL
   [X_GEN_TAC `y:A` THEN ASM_CASES_TAC `(y:A) IN C` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `open(IMAGE (SND((ch:A->(A->bool)#(A->real^N)) y)) (FST(ch y) INTER W))`
    MP_TAC THENL
     [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) b'`;
        `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)) b'`;
        `FST((ch:A->(A->bool)#(A->real^N)) y)`] THEN
      ASM_SIMP_TAC[INTER_SUBSET; PAIR] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b'`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b'`;
                     `FST((ch:A->(A->bool)#(A->real^N)) y)`;
                     `SND((ch:A->(A->bool)#(A->real^N)) y)`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_SIMP_TAC[PAIR];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN
    DISCH_THEN(MP_TAC o SPEC `SND((ch:A->(A->bool)#(A->real^N)) y) y`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTER] THEN ASM_SIMP_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e / &6` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `R:A->real`) THEN
  SUBGOAL_THEN
   `!y:A. ?O. y IN C ==> open_in (p2a_vtop (V:(real->A topology)#
                            (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') O /\
                         y IN O /\
                         !z. z IN O ==> z IN FST((ch:A->(A->bool)#(A->real^N)) y) INTER W /\
                                        dist(SND(ch y) z,SND(ch y) y) < (R:A->real) y`
  MP_TAC THENL
   [X_GEN_TAC `y:A` THEN ASM_CASES_TAC `(y:A) IN C` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2A_CHART_PREIMAGE_OPEN THEN MAP_EVERY EXISTS_TAC [`a':real`; `b':real`] THEN
    ASM_SIMP_TAC[PAIR; REAL_LE_REFL; IN_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `O:A->A->bool`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `IMAGE (O:A->A->bool) C` o CONJUNCT2 o
    GEN_REWRITE_RULE I [compact_in] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Vs:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`O:A->A->bool`; `C:A->bool`; `Vs:(A->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Fs:A->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`Fs:A->bool`; `R:A->real`;
                        `if Fs = {} then &1 else inf(IMAGE (R:A->real) Fs)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!k:A. k IN Fs ==> k IN C` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[REAL_LT_01] THEN
    MP_TAC(ISPEC `IMAGE (R:A->real) Fs` INF_FINITE) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    X_GEN_TAC `k:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `IMAGE (R:A->real) Fs` INF_FINITE) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?k:A. k IN Fs /\ y IN (O:A->A->bool) k` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(C:A->bool) SUBSET UNIONS Vs` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `k:A` THEN ASM_MESON_TAC[]]);;

(* Bounds for the region metric family on a compact set of a region chart  *)
(* image for times in [b' - T1, b'], up to the top: the s-family with      *)
(* tt := b' on the window (-sqrt(b' - a'), sqrt(b' - a')) (P2AK_LLAG_UPPER, *)
(* P2A_UNIFORM_BOUNDS) and t = b' - sqrt(b' - t)^2.                         *)

let P2AK_CHART_BOUNDS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' b' U (phi:A->real^N) K T1.
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     compact K /\ K SUBSET IMAGE phi (U INTER W) /\ &0 <= T1 /\ T1 < b' - a'
     ==> ?lam Gm Rm.
           &0 < lam /\ &0 <= Gm /\ &0 <= Rm /\
           !t y u. b' - T1 <= t /\ t <= b' /\ y IN K
                   ==> lam * norm u pow 2 <=
                       u dot (p2a_rlocal V W b' (U INTER W,phi) t y ** u) /\
                       u dot (p2a_rlocal V W b' (U INTER W,phi) t y ** u) <= Gm * norm u pow 2 /\
                       abs(lscalar (p2a_rlocal V W b' (U INTER W,phi) t) y) <= Rm`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `sb = sqrt(b' - a')` THEN
  SUBGOAL_THEN `&0 < sb /\ sb pow 2 = b' - a'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sb" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt T1 < sb /\ &0 <= sqrt T1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "sb" THEN MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (--sb) sb
      (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) W b' (U INTER W,phi) (b' - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_LSMOOTH THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 < sb pow 2` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      REWRITE_TAC[ARITH_EQ; REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `--(sb:real)`; `sb:real`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N)`;
                 `b':real`; `K:real^N->bool`; `&0`; `sqrt T1`] P2AK_LLAG_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Gm:real` (X_CHOOSE_THEN `Rm:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `--(sb:real)`; `sb:real`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N)`;
                 `b':real`; `K:real^N->bool`; `&0`; `sqrt T1`] P2A_UNIFORM_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `B0:real` (X_CHOOSE_THEN `B1:real`
    (X_CHOOSE_THEN `BR:real` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `Gm:real`; `Rm:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt(b' - t) /\ sqrt(b' - t) <= sqrt T1 /\ b' - sqrt(b' - t) pow 2 = t`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_ARITH `t <= b' ==> &0 <= b' - t`] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sqrt(b' - t)`; `y:real^N`; `y:real^N`; `u:real^N`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `B1:real`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sqrt(b' - t)`; `y:real^N`; `u:real^N`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `Gm:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; SING_SUBSET] THEN SIMP_TAC[]);;

(* The box datum: charts, radii and uniform bounds for one box.             *)

let p2ak_bxd = new_definition
 `p2ak_bxd (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
           (W:A->bool) (a':real) (b':real) (C:A->bool) (T1:real)
           (Fs:A->bool) (R:A->real) (r:real) (lam:real) (Gm:real) (Rm:real) <=>
    p2a_svs V /\ p2a_region V W a' b' /\ &0 <= T1 /\ T1 < b' - a' /\
    compact_in (p2a_vtop V b') C /\ C SUBSET W /\
    FINITE Fs /\ Fs SUBSET C /\ &0 < r /\ &0 < lam /\ &0 <= Gm /\ &0 <= Rm /\
    (!k. k IN Fs
         ==> chart_at (p2a_vatlas V b') k IN p2a_vatlas V b' /\
             k IN FST(chart_at (p2a_vatlas V b') k) /\ r <= R k /\
             cball(SND(chart_at (p2a_vatlas V b') k) k,&6 * R k) SUBSET
             IMAGE (SND(chart_at (p2a_vatlas V b') k))
                   (FST(chart_at (p2a_vatlas V b') k) INTER W) /\
             !t z u. b' - T1 <= t /\ t <= b' /\
                     z IN cball(SND(chart_at (p2a_vatlas V b') k) k,&6 * R k)
                     ==> lam * norm u pow 2 <=
                         u dot (p2a_rlocal V W b' (FST(chart_at (p2a_vatlas V b') k) INTER W,
                                                   SND(chart_at (p2a_vatlas V b') k)) t z ** u) /\
                         u dot (p2a_rlocal V W b' (FST(chart_at (p2a_vatlas V b') k) INTER W,
                                                   SND(chart_at (p2a_vatlas V b') k)) t z ** u)
                         <= Gm * norm u pow 2 /\
                         abs(lscalar (p2a_rlocal V W b'
                                        (FST(chart_at (p2a_vatlas V b') k) INTER W,
                                         SND(chart_at (p2a_vatlas V b') k)) t) z)
                         <= Rm) /\
    (!y. y IN C
         ==> ?k. k IN Fs /\ y IN FST(chart_at (p2a_vatlas V b') k) INTER W /\
                 dist(SND(chart_at (p2a_vatlas V b') k) y,
                      SND(chart_at (p2a_vatlas V b') k) k) < R k)`;;

let P2AK_BXD_EXISTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' b' C T1.
     p2a_svs V /\ p2a_region V W a' b' /\ &0 <= T1 /\ T1 < b' - a' /\
     compact_in (p2a_vtop V b') C /\ C SUBSET W
     ==> ?Fs R r lam Gm Rm. p2ak_bxd V W a' b' C T1 Fs R r lam Gm Rm`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `C:A->bool`]
                P2AK_SB_CHARTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs:A->bool` (X_CHOOSE_THEN `R:A->real` (X_CHOOSE_THEN `r:real`
    STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `ch = chart_at (p2a_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b')` THEN
  SUBGOAL_THEN
   `!k:A. ?lam Gm Rm.
      k IN Fs
      ==> &0 < lam /\ &0 <= Gm /\ &0 <= Rm /\
          !t z u. b' - T1 <= t /\ t <= b' /\
                  z IN cball(SND((ch:A->(A->bool)#(A->real^N)) k) k,&6 * (R:A->real) k)
                  ==> lam * norm u pow 2 <=
                      u dot (p2a_rlocal (V:(real->A topology)#
                               (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
                               W b' (FST(ch k) INTER W,SND(ch k)) t z ** u) /\
                      u dot (p2a_rlocal V W b' (FST(ch k) INTER W,SND(ch k)) t z ** u)
                      <= Gm * norm u pow 2 /\
                      abs(lscalar (p2a_rlocal V W b' (FST(ch k) INTER W,SND(ch k)) t) z) <= Rm`
  MP_TAC THENL
   [X_GEN_TAC `k:A` THEN ASM_CASES_TAC `(k:A) IN Fs` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AK_CHART_BOUNDS THEN EXISTS_TAC `a':real` THEN
    ASM_SIMP_TAC[PAIR; COMPACT_CBALL];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `lf:A->real` (X_CHOOSE_THEN `gf:A->real`
    (X_CHOOSE_THEN `rf:A->real` (LABEL_TAC "B")))) THEN
  MAP_EVERY EXISTS_TAC
   [`Fs:A->bool`; `R:A->real`; `r:real`;
    `if Fs = {} then &1 else inf(IMAGE (lf:A->real) Fs)`;
    `if Fs = {} then &0 else sup(IMAGE (gf:A->real) Fs)`;
    `if Fs = {} then &0 else sup(IMAGE (rf:A->real) Fs)`] THEN
  REWRITE_TAC[p2ak_bxd] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `Fs:A->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01; REAL_LE_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE(IMAGE (lf:A->real) Fs) /\ ~(IMAGE lf Fs = {}) /\
                FINITE(IMAGE (gf:A->real) Fs) /\ ~(IMAGE gf Fs = {}) /\
                FINITE(IMAGE (rf:A->real) Fs) /\ ~(IMAGE rf Fs = {})` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k:A. k IN Fs
          ==> &0 < (lf:A->real) k /\ inf(IMAGE lf Fs) <= lf k /\
              &0 <= (gf:A->real) k /\ gf k <= sup(IMAGE gf Fs) /\
              &0 <= (rf:A->real) k /\ rf k <= sup(IMAGE rf Fs)`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:A` THEN DISCH_TAC THEN
    USE_THEN "B" (MP_TAC o C MP (ASSUME `(k:A) IN Fs`) o SPEC `k:A`) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `IMAGE (lf:A->real) Fs` INF_FINITE) THEN
    MP_TAC(ISPEC `IMAGE (gf:A->real) Fs` SUP_FINITE) THEN
    MP_TAC(ISPEC `IMAGE (rf:A->real) Fs` SUP_FINITE) THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k0:A. k0 IN Fs` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INF_FINITE; FORALL_IN_IMAGE];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(gf:A->real) k0` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(rf:A->real) k0` THEN ASM_SIMP_TAC[];
    X_GEN_TAC `k:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    USE_THEN "B" (MP_TAC o C MP (ASSUME `(k:A) IN Fs`) o SPEC `k:A`) THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`; `u:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `z:real^N`; `u:real^N`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `inf:(real->bool)->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(lf:A->real) k * norm(u:real^N) pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(gf:A->real) k * norm(u:real^N) pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Closed chart balls in the slices, and the exit-time lemma: a curve that  *)
(* starts in a region chart and satisfies an a priori displacement bound    *)
(* (radius 2 rho gives radius rho) stays in the chart ball of radius rho    *)
(* (supremum argument with the closed chart ball and the slice continuity   *)
(* of the curve).                                                           *)
(* ------------------------------------------------------------------------- *)

let P2AK_CHART_CBALL_CLOSED = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' b' U (phi:A->real^N) z0 rho t.
     p2a_svs V /\ p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < t /\ t <= b' /\ cball(z0,rho) SUBSET IMAGE phi (U INTER W)
     ==> closed_in (p2a_vtop V t) {y | y IN U INTER W /\ phi y IN cball(z0,rho)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `b':real`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `{y | y IN U INTER W /\ (phi:A->real^N) y IN cball(z0,rho)} =
    IMAGE (chart_inv (U INTER W,phi)) (cball(z0,rho))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `y:A` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `(phi:A->real^N) y` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
      MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)`; `a':real`; `b':real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                     `phi:A->real^N`; `z:real^N`] P2A_CHART_PIECE_FACTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `cball(z0:real^N,rho) SUBSET IMAGE (phi:A->real^N) (U INTER W)` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN CONJ_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N))` THEN
    SIMP_TAC[p2a_svs];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_IN_SUBTOPOLOGY_IMP_COMPACT THEN EXISTS_TAC `W:A->bool` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `t:real`]
                P2A_REGION_SUBTOP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) (U INTER W))` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL];
    ALL_TAC] THEN
  MATCH_MP_TAC GRGD_CHART_INV_CONTINUOUS THEN
  EXISTS_TAC `restrict_atlas (p2a_vatlas (V:(real->A topology)#
                (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') W` THEN
  ASM_SIMP_TAC[P2A_REGION_RCHART; SMOOTH_MANIFOLD_ATLAS_RESTRICT]);;

let P2AK_EXIT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) b W a' b' U (phi:A->real^N) s0 s1 rho.
     p2a_svs V /\ p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     &0 <= s0 /\ s0 <= s1 /\ s1 pow 2 <= b /\ &0 < rho /\
     (!s. s0 <= s /\ s <= s1 ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
     (!tau. &0 <= tau /\ tau <= b ==> gamma tau IN topspace(p2a_vtop V (tt - tau))) /\
     (!s O. &0 <= s /\ s pow 2 <= b /\ open_in (p2a_vtop V (tt - s pow 2)) O /\
            gamma(s pow 2) IN O
            ==> ?e. &0 < e /\
                    !r. &0 <= r /\ r pow 2 <= b /\ abs(r - s) < e ==> gamma(r pow 2) IN O) /\
     gamma(s0 pow 2) IN U INTER W /\
     cball(phi(gamma(s0 pow 2)),&2 * rho) SUBSET IMAGE phi (U INTER W) /\
     (!s'. s0 <= s' /\ s' <= s1 /\
           (!s. s0 <= s /\ s <= s'
                ==> gamma(s pow 2) IN U INTER W /\
                    dist(phi(gamma(s pow 2)),phi(gamma(s0 pow 2))) <= &2 * rho)
           ==> dist(phi(gamma(s' pow 2)),phi(gamma(s0 pow 2))) <= rho)
     ==> !s. s0 <= s /\ s <= s1
             ==> gamma(s pow 2) IN U INTER W /\
                 dist(phi(gamma(s pow 2)),phi(gamma(s0 pow 2))) <= rho`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `z0 = (phi:A->real^N)((gamma:real->A)(s0 pow 2))` THEN
  ABBREV_TAC `P = \s. (gamma:real->A)(s pow 2) IN U INTER W /\
                      dist((phi:A->real^N)(gamma(s pow 2)),z0) <= rho` THEN
  SUBGOAL_THEN `(P:real->bool) s0` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `S = {s | s0 <= s /\ s <= s1 /\ !s'. s0 <= s' /\ s' <= s ==> (P:real->bool) s'}` THEN
  SUBGOAL_THEN `(s0:real) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `s':real = s0` (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `S:real->bool` SUP) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN EXISTS_TAC `s1:real` THEN
    EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC `ss = sup S` THEN STRIP_TAC THEN
  SUBGOAL_THEN `s0 <= ss /\ ss <= s1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        not(can (find_term ((=) `b:real`)) (concl th)) &&
        can (find_term ((=) `ss:real`)) (concl th) && not(is_imp(snd(strip_forall(concl th))) &&
        is_forall(fst(dest_imp(snd(strip_forall(concl th)))))))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ss:real`)) (concl th) && is_imp(snd(strip_forall(concl th))) &&
        is_forall(fst(dest_imp(snd(strip_forall(concl th))))))) THEN
      EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s'. s0 <= s' /\ s' < ss ==> (P:real->bool) s'` ASSUME_TAC THENL
   [X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?x:real. x IN S /\ s' < x` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(prove
       (`!S ss s':real. (!b. (!x. x IN S ==> x <= b) ==> ss <= b) /\ s' < ss
                        ==> ?x. x IN S /\ s' < x`,
        MESON_TAC[REAL_NOT_LT])) THEN
      EXISTS_TAC `ss:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:real) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* P at the supremum: the chart ball is closed in the slice *)
  SUBGOAL_THEN `(P:real->bool) ss` ASSUME_TAC THENL
   [ASM_CASES_TAC `ss:real = s0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                   `phi:A->real^N`; `z0:real^N`; `rho:real`; `tt - ss pow 2`]
                  P2AK_CHART_CBALL_CLOSED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPEC `ss:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `a':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(z0:real^N,&2 * rho)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[closed_in] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ss:real`;
      `topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) (tt - ss pow 2)) DIFF
       {y | y IN U INTER W /\ (phi:A->real^N) y IN cball(z0,rho)}`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_POW_2] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `~(P:real->bool) ss` THEN EXPAND_TAC "P" THEN
          REWRITE_TAC[IN_CBALL] THEN MESON_TAC[DIST_SYM]]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `rr = max s0 (ss - e / &2)` THEN
    SUBGOAL_THEN `s0 <= rr /\ rr < ss /\ abs(rr - ss) < e` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "rr" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `rr:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e:real`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `rr:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ss:real`)) (concl th) &&
      can (find_term ((=) `P:real->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN
    REWRITE_TAC[IN_CBALL] THEN MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  (* the supremum is s1 *)
  SUBGOAL_THEN `ss:real = s1` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `ss < s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(P:real->bool) ss` THEN EXPAND_TAC "P" THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                   `phi:A->real^N`; `tt - ss pow 2`; `(gamma:real->A)(ss pow 2)`; `rho:real`]
                  P2A_CHART_PREIMAGE_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPEC `ss:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `a':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:A->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ss:real`; `O:A->bool`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `sx = min s1 (ss + e / &2)` THEN
    SUBGOAL_THEN `ss < sx /\ sx <= s1 /\ sx - ss < e` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "sx" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `!s. s0 <= s /\ s <= sx
          ==> (gamma:real->A)(s pow 2) IN U INTER W /\
              dist((phi:A->real^N)(gamma(s pow 2)),z0) <= &2 * rho`
    ASSUME_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s <= ss` THENL
       [SUBGOAL_THEN `(P:real->bool) s` MP_TAC THENL
         [ASM_CASES_TAC `s:real = ss` THENL
           [ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `ss:real`)) (concl th) &&
            can (find_term ((=) `P:real->bool`)) (concl th))) THEN
          ASM_REAL_ARITH_TAC;
          EXPAND_TAC "P" THEN SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `e:real`)) (concl th))) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(gamma:real->A)(s pow 2)` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `O:A->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(phi:A->real^N)((gamma:real->A)(s pow 2))`;
                     `(phi:A->real^N)((gamma:real->A)(ss pow 2))`; `z0:real^N`] DIST_TRIANGLE) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(sx:real) IN S` MP_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s':real` THEN STRIP_TAC THEN EXPAND_TAC "P" THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `s':real` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `sx:real`)) (concl th))) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&2 * rho`)) (concl th) &&
        not(can (find_term ((=) `sx:real`)) (concl th)) &&
        is_imp(snd(strip_forall(concl th))))) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sx:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `sx <= ss` MP_TAC THENL [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(P:real->bool) s` MP_TAC THENL
   [ASM_CASES_TAC `s:real = ss` THENL
     [UNDISCH_TAC `(P:real->bool) ss` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ss:real`)) (concl th) &&
      can (find_term ((=) `P:real->bool`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    EXPAND_TAC "P" THEN EXPAND_TAC "z0" THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Estimates for curves in a box with top tt (the base time): the           *)
(* L-integrand is at least -sqrt(tau) Rm on C (P2AK_BXD_LINT_LOWER), hence  *)
(* every L-piece is at most Lb + 2 sqrt(b) Rm b; the chart curve of a       *)
(* p2a_admx curve in a chart ball satisfies the displacement bound          *)
(* |Y(s2) - Y(s1)|^2 <= (s2 - s1) E, E = (2 / lam)(Lb + 4 b                 *)
(* sqrt(b) Rm) (P2AK_BXD_FE, also from s1 = 0 by continuity), and a curve   *)
(* starting in the ball of radius R k of a chart stays within r of its      *)
(* start for (s1 - s0) E <= r^2 (P2AK_BXD_STAY, by P2AK_EXIT).              *)
(* ------------------------------------------------------------------------- *)

let P2AK_BXD_LINT_LOWER = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' b' C T1 Fs R r lam Gm Rm tt (gamma:real->A) b tau.
     p2ak_bxd V W a' b' C T1 Fs R r lam Gm Rm /\
     b' - T1 <= tt - tau /\ tt - tau <= b' /\ &0 <= tau /\ gamma tau IN C
     ==> --(sqrt tau * Rm) <= p2a_L_integrand V tt gamma b tau`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ak_bxd] THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_L_integrand] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(gamma:real->A) tau` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `C:A->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tt - tau`;
    `SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) b') k) ((gamma:real->A) tau)`;
    `vec 0:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(R:A->real) k` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`;
                 `FST(chart_at (p2a_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') k)`;
                 `SND(chart_at (p2a_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') k)`;
                 `tt - tau`; `(gamma:real->A) tau`] P2AK_SCALAR_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[PAIR] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `--(a * b) = a * --b`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
  MP_TAC(SPEC `mfd_speed (p2a_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau))
                 (p2a_vmetric V (tt - tau)) (gamma:real->A) (&0) b tau` REAL_LE_POW_2) THEN
  ASM_REAL_ARITH_TAC);;

let P2AK_INT_PIECE_UPPER = prove
 (`!f a b p q c Lb.
     f real_integrable_on real_interval[a,b] /\ a <= p /\ p <= q /\ q <= b /\
     real_integral (real_interval[a,b]) f <= Lb /\ &0 <= c /\
     (!t. a <= t /\ t <= b ==> --c <= f t)
     ==> real_integral (real_interval[p,q]) f <= Lb + &2 * c * (b - a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `f real_integrable_on real_interval[a,p] /\ f real_integrable_on real_interval[p,q] /\
                f real_integrable_on real_interval[q,b]` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (real_interval[a,b]) f =
                real_integral (real_interval[a,p]) f + real_integral (real_interval[p,q]) f +
                real_integral (real_interval[q,b]) f` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`; `q:real`] REAL_INTEGRAL_COMBINE) THEN
    MP_TAC(ISPECL [`f:real->real`; `a:real`; `q:real`; `p:real`] REAL_INTEGRAL_COMBINE) THEN
    SUBGOAL_THEN `f real_integrable_on real_interval[a,q]` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--c * (p - a) <= real_integral (real_interval[a,p]) f /\
                --c * (b - q) <= real_integral (real_interval[q,b]) f` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`a:real`; `p:real`; `--c:real`] REAL_INTEGRAL_CONST);
      MP_TAC(ISPECL [`q:real`; `b:real`; `--c:real`] REAL_INTEGRAL_CONST)] THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c * (p - a) <= c * (b - a) /\ c * (b - q) <= c * (b - a)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2AK_BXD_FE_POS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' C T1 Fs R r lam Gm Rm tt (x:A) b (gamma:real->A) Lb k s1 s2.
     p2ak_bxd V W a' tt C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     p2a_admx V tt x b gamma /\ b <= T1 /\
     (!tau. &0 <= tau /\ tau <= b ==> gamma tau IN C) /\
     p2a_L_length V tt gamma b <= Lb /\
     k IN Fs /\ &0 < s1 /\ s1 < s2 /\ s2 pow 2 <= b /\
     (!s. s1 <= s /\ s <= s2
          ==> gamma(s pow 2) IN FST(chart_at (p2a_vatlas V tt) k) INTER W /\
              SND(chart_at (p2a_vatlas V tt) k) (gamma(s pow 2)) IN
              cball(SND(chart_at (p2a_vatlas V tt) k) k,&6 * R k))
     ==> dist(SND(chart_at (p2a_vatlas V tt) k) (gamma(s2 pow 2)),
              SND(chart_at (p2a_vatlas V tt) k) (gamma(s1 pow 2))) pow 2
         <= (s2 - s1) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt /\
                cball((phi:A->real^N) k,&6 * (R:A->real) k) SUBSET IMAGE phi (U INTER W) /\
                !t z u. tt - T1 <= t /\ t <= tt /\ z IN cball(phi k,&6 * R k)
                        ==> lam * norm u pow 2 <=
                            u dot (p2a_rlocal V W tt (U INTER W,phi) t z ** u) /\
                            u dot (p2a_rlocal V W tt (U INTER W,phi) t z ** u)
                            <= Gm * norm u pow 2 /\
                            abs(lscalar (p2a_rlocal V W tt (U INTER W,phi) t) z) <= Rm`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b /\ s2 <= sqrt b /\ sqrt b < sqrt(tt - a')` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `s2:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_MONO_LT THEN
      MP_TAC(SPEC `s2:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `tt:real`; `U:A->bool`; `phi:A->real^N`;
                 `s1:real`; `s2:real`; `&0`; `sqrt(tt - a')`;
                 `cball((phi:A->real^N) k,&6 * (R:A->real) k)`; `lam:real`; `Rm:real`]
                P2AK_PIECE_SQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s pow 2 < sqrt(tt - a') pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `sqrt(tt - a') pow 2 = tt - a'` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `u:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`tt - s pow 2`; `y:real^N`; `u:real^N`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `s pow 2 <= s2 pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real->bool` STRIP_ASSUME_TAC) THEN
  (* the displacement bound *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2ak_sq]) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`;
                 `\v:real^1. vector_derivative (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (at v)`;
                 `K:real->bool`; `s1:real`; `s2:real`] P2AK_FE_DISP) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
  (* the L-length of the piece *)
  SUBGOAL_THEN `real_integral (real_interval[s1 pow 2,s2 pow 2])
                  (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                      (real->A->real^N^N)) tt (gamma:real->A) b)
                <= Lb + &2 * (sqrt b * Rm) * (b - &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AK_INT_PIECE_UPPER THEN
    UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x b gamma` THEN
    REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN ASM_REWRITE_TAC[GSYM p2a_L_length] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `s1:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(sqrt tau * Rm)` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC P2AK_BXD_LINT_LOWER THEN
        MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `tt:real`; `C:A->bool`; `T1:real`;
                              `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`] THEN
        ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s2 pow 2 * Rm * (s2 - s1) <= b * Rm * sqrt b` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[s1,s2])
      (\s. norm(vector_derivative (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                  (at (lift s))) pow 2)
    <= &2 / lam * (Lb + &4 * b * sqrt b * Rm)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 / lam * (real_integral (real_interval[s1 pow 2,s2 pow 2])
                             (p2a_L_integrand (V:(real->A topology)#
                                (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
                                tt (gamma:real->A) b) +
                           &2 * s2 pow 2 * Rm * (s2 - s1))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[dist] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(s2 - s1) *
              real_integral (real_interval[s1,s2])
                (\s. norm(vector_derivative (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                            (at (lift s))) pow 2)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let P2AK_BXD_FE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' C T1 Fs R r lam Gm Rm tt (x:A) b (gamma:real->A) Lb k s1 s2.
     p2ak_bxd V W a' tt C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     p2a_admx V tt x b gamma /\ b <= T1 /\
     (!tau. &0 <= tau /\ tau <= b ==> gamma tau IN C) /\
     p2a_L_length V tt gamma b <= Lb /\
     k IN Fs /\ &0 <= s1 /\ s1 <= s2 /\ s2 pow 2 <= b /\
     (!s. s1 <= s /\ s <= s2
          ==> gamma(s pow 2) IN FST(chart_at (p2a_vatlas V tt) k) INTER W /\
              SND(chart_at (p2a_vatlas V tt) k) (gamma(s pow 2)) IN
              cball(SND(chart_at (p2a_vatlas V tt) k) k,&6 * R k))
     ==> dist(SND(chart_at (p2a_vatlas V tt) k) (gamma(s2 pow 2)),
              SND(chart_at (p2a_vatlas V tt) k) (gamma(s1 pow 2))) pow 2
         <= (s2 - s1) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s1:real = s2` THENL
   [ASM_REWRITE_TAC[DIST_REFL; REAL_SUB_REFL; REAL_MUL_LZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < s1` THENL
   [MATCH_MP_TAC P2AK_BXD_FE_POS THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`;
                          `R:A->real`; `r:real`; `Gm:real`; `x:A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s1 = &0 /\ &0 < s2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* continuity of the chart curve on [0,s2] *)
  SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift(&0),lift s2]` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_ADM_CHART_CONT THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `tt:real`; `b:real`; `W:A->bool`;
                          `a':real`; `tt:real`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AXR_ADMX_SCONT THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `s pow 2 <= s2 pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\v. norm((phi:A->real^N)((gamma:real->A)(s2 pow 2)) - phi(gamma(drop v pow 2))) pow 2 -
         (s2 - drop v) * E`;
    `interval(lift(&0),lift s2)`; `&0`] CONTINUOUS_LE_ON_CLOSURE) THEN
  SUBGOAL_THEN `closure(interval(lift(&0),lift s2)) = interval[lift(&0),lift s2]`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN REWRITE_TAC[INTERVAL_NE_EMPTY_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN BETA_TAC THEN REWRITE_TAC[LIFT_SUB] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL; LIFT_SUB; LIFT_DROP] THEN
        MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`;
                   `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                   `tt:real`; `x:A`; `b:real`; `gamma:real->A`; `Lb:real`; `k:A`;
                   `s:real`; `s2:real`] P2AK_BXD_FE_POS) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `s':real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
        can (find_term ((=) `s2:real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `lift(&0)`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[dist] THEN REAL_ARITH_TAC);;

let P2AK_BXD_STAY = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' C T1 Fs R r lam Gm Rm tt (x:A) b (gamma:real->A) Lb k s0 s1.
     p2ak_bxd V W a' tt C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     p2a_admx V tt x b gamma /\ b <= T1 /\
     (!tau. &0 <= tau /\ tau <= b ==> gamma tau IN C) /\
     p2a_L_length V tt gamma b <= Lb /\ &0 <= Lb /\
     k IN Fs /\ &0 <= s0 /\ s0 <= s1 /\ s1 pow 2 <= b /\
     gamma(s0 pow 2) IN FST(chart_at (p2a_vatlas V tt) k) INTER W /\
     dist(SND(chart_at (p2a_vatlas V tt) k) (gamma(s0 pow 2)),
          SND(chart_at (p2a_vatlas V tt) k) k) < R k /\
     (s1 - s0) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm)) <= r pow 2
     ==> !s. s0 <= s /\ s <= s1
             ==> gamma(s pow 2) IN FST(chart_at (p2a_vatlas V tt) k) INTER W /\
                 dist(SND(chart_at (p2a_vatlas V tt) k) (gamma(s pow 2)),
                      SND(chart_at (p2a_vatlas V tt) k) (gamma(s0 pow 2))) <= r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt /\
                r <= (R:A->real) k /\
                cball((phi:A->real^N) k,&6 * R k) SUBSET IMAGE phi (U INTER W)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL
   [MP_TAC(SPEC `s1:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AK_EXIT THEN
  MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)`; `tt:real`; `b:real`; `a':real`; `tt:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 <= s1 pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x b gamma` THEN
    SIMP_TAC[p2a_admx];
    MATCH_MP_TAC P2AXR_ADMX_SCONT THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((phi:A->real^N) k,&6 * (R:A->real) k)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`; `z:real^N`]
                  DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`]
                  DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s':real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`;
                 `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                 `tt:real`; `x:A`; `b:real`; `gamma:real->A`; `Lb:real`; `k:A`;
                 `s0:real`; `s':real`] P2AK_BXD_FE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `s':real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_CBALL] THEN
    MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`;
                   `(phi:A->real^N)((gamma:real->A)(s pow 2))`] DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`]
                  DIST_SYM) THEN
    MP_TAC(ISPECL [`(phi:A->real^N)((gamma:real->A)(s pow 2))`;
                   `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(s' - s0) * E <= r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s1 - s0) * E` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
  ASM_REAL_ARITH_TAC);;

