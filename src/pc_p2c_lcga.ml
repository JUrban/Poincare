(* ========================================================================= *)
(* Unit pc_p2c_lcga (Part 2C, the general form G of local compactness, first *)
(* unit): local geometry of the deep parts of a sequence of regular views    *)
(* (MT Def 5.1 and the proof of Thm 5.6): the hypothesis bundle p2ga_hyp of  *)
(* P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT, the delta-deep sets, the level     *)
(* regions (deep-path distance to the base point), the shift lemmas, the     *)
(* normal-chart data of pc_p2c_lcn at deep points, local packing and nets of *)
(* the level regions.                                                        *)
(* ========================================================================= *)

needs "src/pc_p2b_lcreqg.ml";;
needs "src/pc_p2c_lcn.ml";;
needs "src/pc_grg_dist_in.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The hypotheses of the general form G as one predicate, the time-0 slices, *)
(* and the delta-deep sets (MT Def 5.1 in the form of p2b_lc_deep): monotone *)
(* in delta, and points near a deep point are deep.  The conjuncts of        *)
(* p2ga_hyp after the first are called H1 (for every delta, the              *)
(* delta/2-balls about delta-deep points persist from -tau to 0, with abs Rm *)
(* <= K on (-tau,0]), H2 (the volume lower bound kappa (delta/2)^3 of these  *)
(* balls at time 0) and H3 (the base points are delta0-deep).                *)
(* ------------------------------------------------------------------------- *)

let p2ga_hyp = new_definition
 `p2ga_hyp (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (U:num->A->bool) (z:num->A) <=>
    (!n. p2c_regular_view (V n) /\
         open_in (rfs_vtop (V n) (&0)) (U n) /\ z n IN U n) /\
    (!delta. &0 < delta
             ==> ?K tau N. &0 < tau /\
                   !n y. N <= n /\ y IN U n /\ p2b_lc_deep (V n) (U n) y delta
                         ==> rfs_persists (V n) (rfs_vball (V n) (&0) y (delta / &2))
                                          (--tau) (&0) /\
                             !s y'. --tau < s /\ s <= &0 /\
                                    y' IN rfs_vball (V n) (&0) y (delta / &2)
                                    ==> mfd_rm_norm (rfs_vatlas (V n) s)
                                                    (rfs_vmetric (V n) s) y' <= K) /\
    (!delta. &0 < delta
             ==> ?kappa N. &0 < kappa /\
                   !n y. N <= n /\ y IN U n /\ p2b_lc_deep (V n) (U n) y delta
                         ==> ?v. mfd_has_volume (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                   (rfs_vmetric (V n) (&0))
                                   (rfs_vball (V n) (&0) y (delta / &2)) v /\
                                 kappa * (delta / &2) pow 3 <= v) /\
    (?delta0. &0 < delta0 /\ !n. p2b_lc_deep (V n) (U n) (z n) delta0)`;;

(* The general form is the statement for all sequences satisfying p2ga_hyp. *)

let P2GA_HYP_G = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT u w <=>
     !(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) U z.
       p2ga_hyp V U z
             ==> ?sub (top:B topology) atlas g zl W phi Vl.
                   p3_subseq sub /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
                   riemannian_metric atlas g /\ zl IN topspace top /\
                   (!k. open_in top (W k) /\ zl IN W k /\ compact_in top (top closure_of W k) /\
                        top closure_of W k SUBSET W (SUC k)) /\
                   UNIONS {W k | k IN (:num)} = topspace top /\
                   (!k. phi k zl = z (sub k)) /\
                   (!k. IMAGE (phi k) (W k) SUBSET U (sub k) /\
                        ?psi. mfd_diffeo top atlas (W k) (rfs_vtop (V (sub k)) (&0))
                                         (rfs_vatlas (V (sub k)) (&0))
                                         (IMAGE (phi k) (W k)) (phi k) psi) /\
                   (!K m eta. compact_in top K /\ &0 < eta
                              ==> ?k0. !k. k0 <= k
                                           ==> K SUBSET W k /\
                                               !y. y IN K
                                                   ==> lck_dist2 m
                                                         (metric_local atlas (chart_at atlas y) g)
                                                         (rfs_pullback (rfs_vatlas (V (sub k)) (&0))
                                                            (phi k o chart_inv (chart_at atlas y))
                                                            (rfs_vmetric (V (sub k)) (&0)))
                                                         (SND(chart_at atlas y) y) < eta) /\
                   (!delta A. &0 < delta /\ &0 < A
                              ==> ?m k0. m <= k0 /\
                                   !k gamma.
                                     k0 <= k /\
                                     mfd_c1_curve (rfs_vtop (V (sub k)) (&0),
                                                   rfs_vatlas (V (sub k)) (&0)) gamma (&0) (&1) /\
                                     gamma (&0) = z (sub k) /\
                                     mfd_length (rfs_vatlas (V (sub k)) (&0))
                                                (rfs_vmetric (V (sub k)) (&0)) gamma (&0) (&1) <= A /\
                                     (!s. &0 <= s /\ s <= &1
                                          ==> p2b_lc_deep (V (sub k)) (U (sub k)) (gamma s) delta)
                                     ==> !s. &0 <= s /\ s <= &1
                                             ==> ?y'. y' IN W m /\ phi k y' = gamma s) /\
                   p2c_regular_view Vl /\
                   rfs_vtop Vl (&0) = top /\ rfs_vatlas Vl (&0) = atlas /\ rfs_vmetric Vl (&0) = g /\
                   (!X a. open_in top X /\ compact_in top (top closure_of X) /\ a < &0 /\
                          (?Kb N. !k. N <= k
                                      ==> X SUBSET W k /\
                                          rfs_persists (V (sub k)) (IMAGE (phi k) X) a (&0) /\
                                          !s y. a < s /\ s <= &0 /\ y IN IMAGE (phi k) X
                                                ==> mfd_rm_norm (rfs_vatlas (V (sub k)) s)
                                                                (rfs_vmetric (V (sub k)) s) y <= Kb)
                          ==> p2c_vflow Vl X a (&0) /\
                              !K m eta b. compact_in top K /\ K SUBSET X /\ a < b /\ &0 < eta
                                ==> ?k0. !k s y. k0 <= k /\ b <= s /\ s <= &0 /\ y IN K
                                                 ==> lck_dist2 m
                                                       (metric_local (rfs_vatlas Vl s)
                                                          (chart_at (rfs_vatlas Vl s) y)
                                                          (rfs_vmetric Vl s))
                                                       (rfs_pullback (rfs_vatlas (V (sub k)) s)
                                                          (phi k o chart_inv
                                                             (chart_at (rfs_vatlas Vl s) y))
                                                          (rfs_vmetric (V (sub k)) s))
                                                       (SND(chart_at (rfs_vatlas Vl s) y) y) < eta)`,
  REWRITE_TAC[P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT; p2ga_hyp]);;

(* The time-0 slices are Riemannian manifolds; base points and the open sets *)
(* lie in them.                                                              *)

let P2GA_SLICE = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z n.
     p2ga_hyp V U z
     ==> hausdorff_space (rfs_vtop (V n) (&0)) /\
         smooth_manifold_atlas (rfs_vtop (V n) (&0)) (rfs_vatlas (V n) (&0)) /\
         riemannian_metric (rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0)) /\
         U n SUBSET topspace (rfs_vtop (V n) (&0)) /\ z n IN U n /\
         z n IN topspace (rfs_vtop (V n) (&0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ga_hyp] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num` o CONJUNCT1) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:num->A->bool) n SUBSET topspace (rfs_vtop (V n) (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:num->A) n IN topspace (rfs_vtop (V n) (&0))` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CD_SLICE THEN EXISTS_TAC `(z:num->A) n` THEN
  ASM_REWRITE_TAC[]);;

(* Deepness is monotone in delta, and passes to nearby points. *)

let P2GA_DEEP_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U y d d'.
     p2b_lc_deep V U y d /\ d' <= d ==> p2b_lc_deep V U y d'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_lc_deep] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_vball V (&0) (y:A) d' SUBSET rfs_vball V (&0) y d` ASSUME_TAC THENL
   [REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CU_CLOSURE_COMPACT_MONO THEN EXISTS_TAC `rfs_vball V (&0) (y:A) d` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `rfs_vtop V (&0) closure_of rfs_vball V (&0) (y:A) d` THEN
    ASM_SIMP_TAC[CLOSURE_OF_MONO]]);;

let P2GA_DEEP_SHIFT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U y d q r d'.
     smooth_manifold_atlas (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
     riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) /\
     p2b_lc_deep V U y d /\ q IN rfs_vball V (&0) y r /\ r + d' <= d
     ==> p2b_lc_deep V U q d'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_lc_deep] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_vball V (&0) (q:A) d' SUBSET rfs_vball V (&0) y d` ASSUME_TAC THENL
   [REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (y:A) (r + d')` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CU_BALL_SHIFT THEN ASM_REWRITE_TAC[GSYM P2CO_VBALL];
      MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CU_CLOSURE_COMPACT_MONO THEN EXISTS_TAC `rfs_vball V (&0) (y:A) d` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `rfs_vtop V (&0) closure_of rfs_vball V (&0) (y:A) d` THEN
    ASM_SIMP_TAC[CLOSURE_OF_MONO]]);;

(* The delta-deep set of a view in U. *)

let p2ga_dp = new_definition
 `p2ga_dp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
          (U:A->bool) (d:real) = {y | y IN U /\ p2b_lc_deep V U y d}`;;

let P2GA_DP_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U d d'.
     d' <= d ==> p2ga_dp V U d SUBSET p2ga_dp V U d'`,
  REWRITE_TAC[p2ga_dp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[P2GA_DEEP_MONO]);;

let P2GA_DEEP_IN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U y d.
     smooth_manifold_atlas (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
     riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) /\
     y IN topspace (rfs_vtop V (&0)) /\ &0 < d /\ p2b_lc_deep V U y d
     ==> y IN U`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_lc_deep] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN rfs_vball V (&0) y d` MP_TAC THENL
   [REWRITE_TAC[P2CO_VBALL] THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (&0)`;
                 `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) (&0) y d`] CLOSURE_OF_SUBSET) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_SUBSET THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

let P2GA_DP_SHIFT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U y d q r d'.
     smooth_manifold_atlas (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
     riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) /\
     y IN p2ga_dp V U d /\ q IN rfs_vball V (&0) y r /\ r + d' <= d /\ &0 < d'
     ==> q IN p2ga_dp V U d'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ga_dp; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2b_lc_deep (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) U q d'` ASSUME_TAC THENL
   [MATCH_MP_TAC P2GA_DEEP_SHIFT THEN
    MAP_EVERY EXISTS_TAC [`y:A`; `d:real`; `r:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2GA_DEEP_IN THEN
  MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)`; `d':real`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(q:A) IN rfs_vball V (&0) y r` THEN REWRITE_TAC[P2CO_VBALL] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (&0)`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)`; `y:A`; `r:real`]
                P2CU_BALL_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The level regions (MT X(delta,R) of the proof of Thm 5.6, in              *)
(* path form): the points joined to the base point z by a curve inside the  *)
(* d-deep set of deep length < a.  They contain z, lie in the d-deep set    *)
(* and in the ball B(z,a), grow when d decreases or a increases, and a ball *)
(* B(p,r), p in the region and r <= d / 2, lies in the region for d / 2 and *)
(* a + r (the shift lemma).                                                  *)
(* ------------------------------------------------------------------------- *)

let p2ga_Y = new_definition
 `p2ga_Y (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
         (U:A->bool) (z:A) (d:real) (a:real) =
    {p | mfd_joinable_in (rfs_vtop V (&0),rfs_vatlas V (&0)) (p2ga_dp V U d) z p /\
         mfd_dist_in (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                     (p2ga_dp V U d) z p < a}`;;

let P2GA_Y_BASE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z d a.
     smooth_manifold_atlas (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
     riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) /\
     z IN topspace (rfs_vtop V (&0)) /\ z IN p2ga_dp V U d /\ &0 < a
     ==> z IN p2ga_Y V U z d a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2ga_Y; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[MFD_JOINABLE_IN_REFL; MFD_DIST_IN_REFL]);;

let P2GA_Y_DP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z d a p.
     p IN p2ga_Y V U z d a ==> p IN p2ga_dp V U d`,
  REWRITE_TAC[p2ga_Y; IN_ELIM_THM; mfd_joinable_in] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `p:A`)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC);;

let P2GA_Y_BALL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z d a.
     smooth_manifold_atlas (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
     riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0))
     ==> p2ga_Y V U z d a SUBSET rfs_vball V (&0) z a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; p2ga_Y; IN_ELIM_THM; P2CO_VBALL; mfd_ball] THEN
  X_GEN_TAC `p:A` THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_IN_IMP THEN
    EXISTS_TAC `p2ga_dp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) U d` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_dist_in (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                  (p2ga_dp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) U d) z p` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_LE_DIST_IN THEN ASM_REWRITE_TAC[]]);;

let P2GA_Y_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z d a d' a'.
     smooth_manifold_atlas (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
     riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) /\
     d' <= d /\ a <= a'
     ==> p2ga_Y V U z d a SUBSET p2ga_Y V U z d' a'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; p2ga_Y; IN_ELIM_THM] THEN
  X_GEN_TAC `p:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2ga_dp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) U d SUBSET p2ga_dp V U d'` ASSUME_TAC THENL
   [MATCH_MP_TAC P2GA_DP_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_IN_MONO THEN
    EXISTS_TAC `p2ga_dp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) U d` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_dist_in (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                  (p2ga_dp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) U d) z p` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_IN_MONO THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]]);;

(* A short curve from a deep point stays deep: the shift lemma. *)

let P2GA_Y_SHIFT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z d a p q r.
     smooth_manifold_atlas (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
     riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) /\
     p IN p2ga_Y V U z d a /\ q IN rfs_vball V (&0) p r /\ &0 < d /\ r <= d / &2
     ==> q IN p2ga_Y V U z (d / &2) (a + r)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `top = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)` THEN
  SUBGOAL_THEN `(p:A) IN p2ga_dp V U d` ASSUME_TAC THENL
   [MATCH_MP_TAC P2GA_Y_DP THEN MAP_EVERY EXISTS_TAC [`z:A`; `a:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2ga_dp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) U d SUBSET p2ga_dp V U (d / &2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2GA_DP_MONO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* a curve from p to q of length < r *)
  SUBGOAL_THEN
   `?gamma. mfd_c1_curve (top:A topology,atlas:((A->bool)#(A->real^3))->bool) gamma (&0) (&1) /\ gamma(&0) = p /\ gamma(&1) = q /\
            mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) < r`
  (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `(q:A) IN rfs_vball V (&0) p r` THEN
    ASM_REWRITE_TAC[P2CO_VBALL; mfd_ball; IN_ELIM_THM; mfd_dist] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`{mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) | gamma |
        mfd_c1_curve (top:A topology,atlas:((A->bool)#(A->real^3))->bool) gamma (&0) (&1) /\ gamma(&0) = p /\ gamma(&1) = q}`;
      `r:real`] INF_APPROACH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
        UNDISCH_TAC `mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (p:A) q` THEN REWRITE_TAC[mfd_joinable] THEN
        MESON_TAC[];
        EXISTS_TAC `&0` THEN REWRITE_TAC[GRGD_IN_LENGTHS] THEN REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_LENGTH_POS_LE THEN
        EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[GRGD_IN_LENGTHS] THEN MESON_TAC[]];
    ALL_TAC] THEN
  (* the curve stays in B(p,r), hence in the d/2-deep set *)
  SUBGOAL_THEN `!s. s IN real_interval[&0,&1] ==> (gamma:real->A) s IN p2ga_dp V U (d / &2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2GA_DP_SHIFT THEN
    MAP_EVERY EXISTS_TAC [`p:A`; `d:real`; `r:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[P2CO_VBALL] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `gamma:real->A`; `p:A`; `r:real`] P2CO_CURVE_IN_BALL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable_in (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (p2ga_dp V U (d / &2)) (p:A) q`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_joinable_in] THEN EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist_in (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (p2ga_dp V U (d / &2)) p q < r`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^3^3) gamma (&0) (&1)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `p2ga_dp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) U (d / &2)`;
                   `gamma:real->A`; `&0`; `&1`] MFD_DIST_IN_LE_LENGTH) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(p:A) IN p2ga_Y V U z d a` THEN
  ASM_REWRITE_TAC[p2ga_Y; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable_in (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (p2ga_dp V U (d / &2)) (z:A) p` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_IN_MONO THEN
    EXISTS_TAC `p2ga_dp (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) U d` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_IN_TRANS THEN EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `mfd_dist_in (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (p2ga_dp V U (d / &2)) z p +
              mfd_dist_in (top:A topology,atlas:((A->bool)#(A->real^3))->bool) g (p2ga_dp V U (d / &2)) p q` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_IN_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!y. x <= y /\ y < a /\ u < r ==> x + u < a + r`) THEN
  EXISTS_TAC `mfd_dist_in (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                (g:A->real^3^3) (p2ga_dp V U d) z p` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_IN_MONO THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Local packing at deep points.  With abs Rm <= K on the                    *)
(* d/2-ball of a d-deep point t (H1 at s = 0), CMP_RELVOL bounds the volume  *)
(* of B(t,5r/2) by V_(-K)(5r/2) when 5 r <= d; with the lower bound H2 at    *)
(* level r for the r/2-balls around deep points, an r-separated subset of   *)
(* the deep set inside B(t,2r) has at most M points, M uniform in n.  And   *)
(* a set all of whose r-separated subsets have at most P points has an      *)
(* r-net of at most P points (a separated subset of maximal cardinality).   *)
(* ------------------------------------------------------------------------- *)

let P2GA_RICCI_LOWER = prove
 (`!top atlas (g:A->real^3^3) y K w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN topspace top /\ mfd_rm_norm atlas g y <= K
     ==> --(&(dimindex(:3) - 1) * K) * (w dot (g y ** w)) <= mfd_ricci atlas g y w w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `y:A`; `--K:real`; `w:real^3`] CMPZ_MFD_RICCI_SEC_LOWER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `y:A`; `u:real^3`; `v:real^3`] MFD_SECTIONAL_LE_RM_NORM) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Nets from a packing bound (any symmetric d with d y y < r). *)

let P2GA_NET_FROM_PACK = prove
 (`!(d:A->A->real) Y r P.
     (!y. y IN Y ==> d y y < r) /\ (!y z. d y z = d z y) /\
     (!S. S SUBSET Y /\ (!y z. y IN S /\ z IN S /\ ~(y = z) ==> r <= d y z)
          ==> FINITE S /\ CARD S <= P)
     ==> ?T. T SUBSET Y /\ FINITE T /\ CARD T <= P /\
             !p. p IN Y ==> ?t. t IN T /\ d t p < r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pk"))) THEN
  MP_TAC(ISPEC `\n. ?S. S SUBSET (Y:A->bool) /\
                        (!y z. y IN S /\ z IN S /\ ~(y = z) ==> r <= (d:A->A->real) y z) /\
                        CARD S = n` num_MAX) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `0` THEN EXISTS_TAC `{}:A->bool` THEN
      REWRITE_TAC[EMPTY_SUBSET; NOT_IN_EMPTY; CARD_CLAUSES];
      EXISTS_TAC `P:num` THEN X_GEN_TAC `n:num` THEN
      DISCH_THEN(X_CHOOSE_THEN `S:A->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "pk" (MP_TAC o SPEC `S:A->bool`) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `S0:A->bool` STRIP_ASSUME_TAC) (LABEL_TAC "max"))) THEN
  REMOVE_THEN "pk" (MP_TAC o SPEC `S0:A->bool`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `S0:A->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  SUBGOAL_THEN `~((p:A) IN (S0:A->bool))` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `p:A`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:A` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `r:real`)) (concl th) &&
      not (can (find_term ((=) `S0:A->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "max" (MP_TAC o SPEC `m + 1`) THEN REWRITE_TAC[NOT_IMP] THEN
  CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  EXISTS_TAC `(p:A) INSERT (S0:A->bool)` THEN
  ASM_SIMP_TAC[CARD_CLAUSES; IN_INSERT; INSERT_SUBSET; ADD1] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `z:A`] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* The local packing bound. *)

let P2GA_LOCAL_PACK = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z d r.
     p2ga_hyp V U z /\ &0 < r /\ &5 * r <= d
     ==> ?M N. !n t S.
                 N <= n /\ t IN p2ga_dp (V n) (U n) d /\
                 S SUBSET p2ga_dp (V n) (U n) d /\ S SUBSET rfs_vball (V n) (&0) t (&2 * r) /\
                 (!y y'. y IN S /\ y' IN S /\ ~(y = y')
                         ==> r <= mfd_dist (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                           (rfs_vmetric (V n) (&0)) y y')
                 ==> FINITE S /\ CARD S <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2ga_hyp]) THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:real` (X_CHOOSE_THEN `tau:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h1"))))) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [p2ga_hyp]) THEN
  DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa:real` (X_CHOOSE_THEN `N2:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h2")))) THEN
  ABBREV_TAC `K = max K0 (&0)` THEN
  SUBGOAL_THEN `&0 <= K /\ K0 <= K` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `c = kappa * (r / &2) pow 3` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `VV = cmp_vmodel (:3) (--K) (&5 * r / &2)` THEN
  X_CHOOSE_TAC `M:num` (SPEC `VV / c` REAL_ARCH_SIMPLE) THEN
  MAP_EVERY EXISTS_TAC [`M:num`; `N1 + N2:num`] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `t:A`; `S:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep"))))) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `U:num->A->bool`; `z:num->A`; `n:num`] P2GA_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `top = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) n) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) (&0)` THEN
  SUBGOAL_THEN `(t:A) IN U (n:num) /\ p2b_lc_deep (V n) (U n) t d` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(t:A) IN p2ga_dp (V (n:num)) (U n) d` THEN REWRITE_TAC[p2ga_dp; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* the volume of B(t,5r/2) *)
  SUBGOAL_THEN `compact_in top (top closure_of mfd_ball (top,atlas) (g:A->real^3^3) t (d / &2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CU_CLOSURE_COMPACT_MONO THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^3^3) t d` THEN
    UNDISCH_TAC `p2b_lc_deep (V (n:num)) (U n) (t:A) d` THEN
    ASM_REWRITE_TAC[p2b_lc_deep; P2CO_VBALL] THEN SIMP_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (top closure_of mfd_ball (top,atlas) (g:A->real^3^3) t (&5 * r / &2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CU_CLOSURE_COMPACT_MONO THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^3^3) t (d / &2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `t:A`; `&5 * r / &2`] P2CU_BALL_HAS_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
  SUBGOAL_THEN `w <= VV` ASSUME_TAC THENL
   [MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                  `t:A`; `K:real`; `d / &2`; `&5 * r / &2`; `&5 * r / &2`; `w:real`; `w:real`]
                 (REWRITE_RULE[CMP_RELVOL_STATEMENT] (ISPECL [`(:A)`; `(:3)`] CMP_RELVOL))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`y:A`; `v:real^3`] THEN DISCH_TAC THEN
        MATCH_MP_TAC P2GA_RICCI_LOWER THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[P2CU_BALL_SUBSET; SUBSET]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K0:real` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "h1" (MP_TAC o SPECL [`n:num`; `t:A`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPECL [`&0`; `y:A`] o CONJUNCT2) THEN
        ASM_REWRITE_TAC[P2CO_VBALL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      EXPAND_TAC "VV" THEN SIMP_TAC[]];
    ALL_TAC] THEN
  (* every finite subset of S is small *)
  SUBGOAL_THEN `!Ts. Ts SUBSET S /\ FINITE Ts ==> CARD(Ts:A->bool) <= M` (LABEL_TAC "card") THENL
   [X_GEN_TAC `Ts:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `\y:A. mfd_ball (top,atlas) (g:A->real^3^3) y (r / &2)`;
                   `c:real`; `Ts:A->bool`] P2CU_DISJOINT_VOLUME) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(y:A) IN U (n:num) /\ p2b_lc_deep (V n) (U n) y d` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `(S:A->bool) SUBSET p2ga_dp (V (n:num)) (U n) d` THEN
          REWRITE_TAC[SUBSET; p2ga_dp; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM SET_TAC[];
          ALL_TAC] THEN
        USE_THEN "h2" (MP_TAC o SPECL [`n:num`; `y:A`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC P2GA_DEEP_MONO THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_REWRITE_TAC[P2CO_VBALL];
        MAP_EVERY X_GEN_TAC [`y:A`; `y':A`] THEN STRIP_TAC THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        X_GEN_TAC `p:A` THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
        USE_THEN "sep" (MP_TAC o SPECL [`y:A`; `y':A`]) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `y:A`; `p:A`; `y':A`] MFD_DIST_TRIANGLE) THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `y':A`; `p:A`] MFD_DIST_SYM) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        ANTS_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `v <= w` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`;
                            `UNIONS (IMAGE (\y:A. mfd_ball (top,atlas) (g:A->real^3^3) y (r / &2)) Ts)`;
                            `mfd_ball (top,atlas) (g:A->real^3^3) t (&5 * r / &2)`]
                          MFD_HAS_VOLUME_MONO) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&5 * r / &2 = &2 * r + r / &2` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC P2CU_BALL_SHIFT THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(S:A->bool) SUBSET rfs_vball (V (n:num)) (&0) t (&2 * r)` THEN
      ASM_REWRITE_TAC[P2CO_VBALL] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `&(CARD(Ts:A->bool)) * c <= VV` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(CARD(Ts:A->bool)) <= VV / c` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`SUC M`; `S:A->bool`] CHOOSE_SUBSET_STRONG) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `Ts:A->bool` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "card" (MP_TAC o SPEC `Ts:A->bool`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC THEN REMOVE_THEN "card" MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* A backward step along a curve.  The length from the start                *)
(* is continuous (an integral of the continuous speed), so it takes every   *)
(* value between 0 and the total length (IVT); a curve inside S from z to p *)
(* of length l >= r gives a point q with deep distance <= l - r from z      *)
(* inside S and distance <= r to p.                                          *)
(* ------------------------------------------------------------------------- *)

let P2GA_LENGTH_IVT = prove
 (`!top atlas (g:A->real^3^3) (gamma:real->A) c.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     &0 <= c /\ c <= mfd_length atlas g gamma (&0) (&1)
     ==> ?s. &0 <= s /\ s <= &1 /\ mfd_length atlas g gamma (&0) s = c`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `f = mfd_speed atlas (g:A->real^3^3) (gamma:real->A) (&0) (&1)` THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= &1
        ==> mfd_length atlas (g:A->real^3^3) (gamma:real->A) (&0) s =
            real_integral (real_interval[&0,s]) f`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "f" THEN MATCH_MP_TAC GRGD_LENGTH_SUBINTERVAL THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `f real_continuous_on real_interval[&0,&1]` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN MATCH_MP_TAC MFD_SPEED_CONTINUOUS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u. real_integral (real_interval[&0,u]) (f:real->real)`; `&0`; `&1`;
                 `c:real`] REAL_IVT_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL THEN
      EXISTS_TAC `(f:real->real) x` THEN
      MP_TAC(ISPECL [`f:real->real`; `&0`; `&1`] REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_INTEGRAL_REFL];
      FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN
      REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN EXISTS_TAC `s:real` THEN
    ASM_SIMP_TAC[]]);;

let P2GA_BACKSTEP = prove
 (`!top atlas (g:A->real^3^3) S (gamma:real->A) r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     (!t. t IN real_interval[&0,&1] ==> gamma t IN S) /\
     &0 <= r /\ r <= mfd_length atlas g gamma (&0) (&1)
     ==> ?q. mfd_joinable_in (top,atlas) S (gamma (&0)) q /\
             mfd_dist_in (top,atlas) g S (gamma (&0)) q <=
             mfd_length atlas g gamma (&0) (&1) - r /\
             mfd_joinable (top,atlas) q (gamma (&1)) /\
             mfd_dist (top,atlas) g q (gamma (&1)) <= r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `mfd_length atlas (g:A->real^3^3) (gamma:real->A) (&0) (&1) - r`]
                P2GA_LENGTH_IVT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `&0`; `s:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,s] ==> (gamma:real->A) t IN S` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `S:A->bool`)) (concl th))) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable_in (top:A topology,atlas:((A->bool)#(A->real^3))->bool) S ((gamma:real->A) (&0)) (gamma s)` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_joinable_in] THEN
    EXISTS_TAC `(gamma:real->A) o (\x. &0 + (s - &0) * x)` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `gamma:real->A`; `&0`; `s:real`] GRGD_AFFINE_CURVE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `s:real`)) (concl th) &&
                                                  can (find_term ((=) `S:A->bool`)) (concl th))) THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_SUB_RZERO; REAL_ADD_LID] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `s = s * &1`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist_in (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) S ((gamma:real->A) (&0)) (gamma s) <=
                mfd_length atlas g gamma (&0) s` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_IN_LE_LENGTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) ((gamma:real->A) s) (gamma (&1)) <=
                mfd_length atlas g gamma s (&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^3))->bool) ((gamma:real->A) s) (gamma (&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(gamma:real->A) s` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Nets of the shells (the packing argument without a volume                *)
(* upper bound for the whole region).  In one manifold, with a set D, a      *)
(* base point z in D, r > 0, and the local packing bound M (r-separated      *)
(* subsets of D inside B(t,2r), t in D, have at most M points), the shell   *)
(* of the points joined to z inside D by deep length < i r / 2 has an r-net *)
(* in D of at most (M+1)^i points, each the base point or in the shell.     *)
(* Step: a shell point p with deep length >= r/2 has a point q of the       *)
(* previous shell with d(q,p) <= r/2 (P2GA_BACKSTEP), so p lies in B(t,2r)  *)
(* for a net point t of the previous shell; maximal separated subsets of    *)
(* these balls (P2GA_NET_FROM_PACK) and the base point form the new net.    *)
(* ------------------------------------------------------------------------- *)

let p2ga_shell = new_definition
 `p2ga_shell (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) D z a =
    {p | mfd_joinable_in (top,atlas) D z p /\ mfd_dist_in (top,atlas) g D z p < a}`;;

let P2GA_SHELL_D = prove
 (`!top atlas (g:A->real^3^3) D z a p.
     p IN p2ga_shell (top,atlas) g D z a ==> p IN D`,
  REWRITE_TAC[p2ga_shell; IN_ELIM_THM; mfd_joinable_in] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `p:A`)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC);;

let P2GA_SHELL_NETS = prove
 (`!top atlas (g:A->real^3^3) D z r M.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     D SUBSET topspace top /\ z IN D /\ &0 < r /\
     (!t S. t IN D /\ S SUBSET D /\ S SUBSET mfd_ball (top,atlas) g t (&2 * r) /\
            (!y y'. y IN S /\ y' IN S /\ ~(y = y') ==> r <= mfd_dist (top,atlas) g y y')
            ==> FINITE S /\ CARD S <= M)
     ==> !i. ?Tn. FINITE Tn /\ CARD Tn <= (M + 1) EXP i /\ Tn SUBSET D /\
                  (!t. t IN Tn ==> t = z \/ t IN p2ga_shell (top,atlas) g D z (&i * r / &2)) /\
                  !p. p IN p2ga_shell (top,atlas) g D z (&i * r / &2)
                      ==> ?t. t IN Tn /\ p IN mfd_ball (top,atlas) g t r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pack")))))) THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  INDUCT_TAC THENL
   [EXISTS_TAC `{}:A->bool` THEN
    REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES; EXP; LE_0; EMPTY_SUBSET; NOT_IN_EMPTY] THEN
    REWRITE_TAC[p2ga_shell; IN_ELIM_THM; REAL_MUL_LZERO; real_div] THEN
    X_GEN_TAC `p:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `D:A->bool`; `z:A`; `p:A`] MFD_DIST_IN_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `Tn:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Tin") (LABEL_TAC "Tcov")))))) THEN
  ABBREV_TAC `Sh = p2ga_shell (top,atlas) (g:A->real^3^3) D z (&(SUC i) * r / &2)` THEN
  SUBGOAL_THEN `(Sh:A->bool) SUBSET D` ASSUME_TAC THENL
   [EXPAND_TAC "Sh" THEN REWRITE_TAC[SUBSET] THEN MESON_TAC[P2GA_SHELL_D]; ALL_TAC] THEN
  (* nets of the sets Sh INTER B(t,2r), t in Tn *)
  SUBGOAL_THEN
   `!t. ?R. t IN Tn
            ==> R SUBSET (Sh INTER mfd_ball (top,atlas) (g:A->real^3^3) t (&2 * r)) /\
                FINITE R /\ CARD R <= M /\
                !p. p IN Sh INTER mfd_ball (top,atlas) g t (&2 * r)
                    ==> ?u. u IN R /\ mfd_dist (top,atlas) g u p < r`
  MP_TAC THENL
   [X_GEN_TAC `t:A` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC P2GA_NET_FROM_PACK THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `y:A`] MFD_DIST_REFL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`y:A`; `y':A`] THEN MATCH_MP_TAC MFD_DIST_SYM THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `S:A->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(t:A) IN D` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "pack" MATCH_MP_TAC THEN EXISTS_TAC `t:A` THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:A->A->bool` (LABEL_TAC "R")) THEN
  SUBGOAL_THEN `!t. t IN Tn ==> FINITE((R:A->A->bool) t) /\ CARD(R t) <= M /\
                                R t SUBSET Sh INTER mfd_ball (top,atlas) (g:A->real^3^3) t (&2 * r)`
  (LABEL_TAC "Rf") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "R" (MP_TAC o SPEC `t:A`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(z:A) INSERT UNIONS (IMAGE (R:A->A->bool) Tn)` THEN
  SUBGOAL_THEN `FINITE (UNIONS (IMAGE (R:A->A->bool) Tn))` ASSUME_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT];
    (* cardinality *)
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `SUC(CARD(UNIONS (IMAGE (R:A->A->bool) Tn)))` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CARD_CLAUSES] THEN COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `CARD(UNIONS (IMAGE (R:A->A->bool) Tn)) <= CARD Tn * M` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`Tn:A->bool`; `R:A->A->bool`; `CARD(Tn:A->bool)`; `M:num`]
                    CARD_UNIONS_LE) THEN
      REWRITE_TAC[SIMPLE_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[HAS_SIZE];
      ALL_TAC] THEN
    SUBGOAL_THEN `1 <= (M + 1) EXP i` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `CARD(Tn:A->bool) * M <= (M + 1) EXP i * M` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[EXP; ARITH_RULE `(M + 1) * x = x * M + x`] THEN ASM_ARITH_TAC;
    (* in D *)
    REWRITE_TAC[INSERT_SUBSET; UNIONS_SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:A` THEN DISCH_TAC THEN USE_THEN "Rf" (MP_TAC o SPEC `t:A`) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    (* the base point or a shell point *)
    REWRITE_TAC[IN_INSERT; IN_UNIONS; EXISTS_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    USE_THEN "Rf" (MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the covering *)
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_joinable_in (top,atlas) D (z:A) p /\
                mfd_dist_in (top,atlas) (g:A->real^3^3) D z p < &(SUC i) * r / &2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:A) IN Sh` THEN EXPAND_TAC "Sh" THEN REWRITE_TAC[p2ga_shell; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `mfd_dist_in (top,atlas) (g:A->real^3^3) D z p < r / &2` THENL
   [EXISTS_TAC `z:A` THEN REWRITE_TAC[IN_INSERT; mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_IN_IMP THEN EXISTS_TAC `D:A->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `mfd_dist_in (top,atlas) (g:A->real^3^3) D z p` THEN
      CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_LE_DIST_IN THEN ASM_REWRITE_TAC[];
                      ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* a curve in D from z to p of length < (SUC i) r / 2, and the backward step *)
  SUBGOAL_THEN
   `?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = z /\ gamma(&1) = p /\
            (!t. &0 <= t /\ t <= &1 ==> gamma t IN D) /\
            mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) < &(SUC i) * r / &2`
  (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THENL
   [MP_TAC(ISPECL
     [`{mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) | gamma |
        mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = z /\ gamma(&1) = p /\
        (!t. &0 <= t /\ t <= &1 ==> gamma t IN D)}`;
      `&(SUC i) * r / &2`] INF_APPROACH) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS_IN] THEN
        UNDISCH_TAC `mfd_joinable_in (top:A topology,atlas:((A->bool)#(A->real^3))->bool) D z p` THEN
        REWRITE_TAC[mfd_joinable_in] THEN MESON_TAC[];
        EXISTS_TAC `&0` THEN X_GEN_TAC `L:real` THEN DISCH_TAC THEN
        MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] GRGD_LENGTHS_IN_POS_LE) THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `g:A->real^3^3`; `D:A->bool`; `z:A`; `p:A`] THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `mfd_dist_in (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                       (g:A->real^3^3) D z p < &(SUC i) * r / &2` THEN
        REWRITE_TAC[mfd_dist_in]];
      REWRITE_TAC[GRGD_IN_LENGTHS_IN] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist_in (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                  (g:A->real^3^3) D z p <= mfd_length atlas g gamma (&0) (&1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_dist_in (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                    (g:A->real^3^3) D ((gamma:real->A)(&0)) (gamma(&1)) <=
                  mfd_length atlas g gamma (&0) (&1)` MP_TAC THENL
     [MATCH_MP_TAC MFD_DIST_IN_LE_LENGTH THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `D:A->bool`; `gamma:real->A`; `r / &2`] P2GA_BACKSTEP) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(q:A) IN p2ga_shell (top,atlas) (g:A->real^3^3) D z (&i * r / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[p2ga_shell; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) < &(SUC i) * r / &2` THEN
    UNDISCH_TAC `mfd_dist_in (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                   (g:A->real^3^3) D z q <= mfd_length atlas g gamma (&0) (&1) - r / &2` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "Tcov" (MP_TAC o SPEC `q:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(q:A) IN mfd_ball (top,atlas) (g:A->real^3^3) t r` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^3))->bool) t p`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN Sh INTER mfd_ball (top,atlas) (g:A->real^3^3) t (&2 * r)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; mfd_ball; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `t:A`; `q:A`; `p:A`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `mfd_dist (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                   (g:A->real^3^3) q p <= r / &2` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "R" (MP_TAC o C MP (ASSUME `(t:A) IN Tn`) o SPEC `t:A`) THEN
  DISCH_THEN(MP_TAC o C MP (ASSUME `(p:A) IN Sh INTER mfd_ball (top,atlas) (g:A->real^3^3) t (&2 * r)`) o
             SPEC `p:A` o last o CONJUNCTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:A` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_INSERT; IN_UNIONS; EXISTS_IN_IMAGE] THEN DISJ2_TAC THEN
    EXISTS_TAC `t:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "Rf" (MP_TAC o C MP (ASSUME `(t:A) IN Tn`) o SPEC `t:A`) THEN
  REWRITE_TAC[SUBSET; IN_INTER; mfd_ball; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `u:A` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_MESON_TAC[MFD_JOINABLE_TRANS; MFD_JOINABLE_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The normal-chart data at deep points (pc_p2c_lcn).  At a                  *)
(* d-deep point y (n large) and any orthonormal frame E, p2cd_ok holds with  *)
(* r1 = d/2, a0 = -tau (H1) and r0 up to a uniform injectivity radius i0     *)
(* (P2CD_INJ with H1 at s = 0 and H2); with the gauge P2CD_GAUGE0 and       *)
(* P2CD_RADIUS this gives one radius rho < 1, rho <= d/16, and the level   *)
(* data of the CG chain at every d-deep point: injectivity ball, abs Rm     *)
(* <= K on B(y,rho), the exp metric a metric field on ball(0,rho) with C^m  *)
(* bounds on ball(0,rho/2), and B(y,rho) inside U.                          *)
(* ------------------------------------------------------------------------- *)

let P2GA_DEEP_OK = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z d.
     p2ga_hyp V U z /\ &0 < d
     ==> ?K tau i0 N. &0 <= K /\ &0 < tau /\ &0 < i0 /\ i0 < d / &2 /\
           !n y E r0. N <= n /\ y IN p2ga_dp (V n) (U n) d /\
                      mfd_orthonormal_frame (rfs_vmetric (V n) (&0)) y E /\
                      &0 < r0 /\ r0 <= i0 /\ K * r0 pow 2 <= &1
                      ==> p2cd_ok (V n) y E r0 (d / &2) (--tau) K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2ga_hyp]) THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:real` (X_CHOOSE_THEN `tau:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h1"))))) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [p2ga_hyp]) THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa:real` (X_CHOOSE_THEN `N2:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h2")))) THEN
  ABBREV_TAC `K = max K0 (&0)` THEN
  SUBGOAL_THEN `&0 <= K /\ K0 <= K` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`K + &1`; `d / &2`; `kappa * (d / &2) pow 3`]
                (INST_TYPE [`:A`,`:A`] P2CD_INJ)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")))) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `tau:real`; `i0:real`; `N1 + N2:num`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:A`; `E:real^3^3`; `r0:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `U:num->A->bool`; `z:num->A`; `n:num`] P2GA_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN U n /\ p2b_lc_deep (V n) (U (n:num)) y d` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN p2ga_dp (V n) (U (n:num)) d` THEN REWRITE_TAC[p2ga_dp; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace (rfs_vtop (V (n:num)) (&0))` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "h1" (MP_TAC o SPECL [`n:num`; `y:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm")) THEN
  REWRITE_TAC[p2cd_ok] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> ACCEPT_TAC(CONJUNCT1(SPEC `n:num` (CONJUNCT1
      (GEN_REWRITE_RULE I [p2ga_hyp] th))))) ORELSE
    (UNDISCH_TAC `p2ga_hyp (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) U z` THEN
     REWRITE_TAC[p2ga_hyp] THEN SIMP_TAC[]);
    MATCH_MP_TAC MFD_INJ_BALL_MONO THEN EXISTS_TAC `i0:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `p2ga_hyp (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) U z` THEN
      REWRITE_TAC[p2ga_hyp] THEN SIMP_TAC[];
      MATCH_MP_TAC P2CU_CLOSURE_COMPACT_MONO THEN
      EXISTS_TAC `rfs_vball (V (n:num)) (&0) (y:A) d` THEN
      UNDISCH_TAC `p2b_lc_deep (V n) (U (n:num)) (y:A) d` THEN
      REWRITE_TAC[p2b_lc_deep] THEN SIMP_TAC[] THEN DISCH_TAC THEN
      REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `w:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `K0:real` THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "h2" (MP_TAC o SPECL [`n:num`; `y:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]]];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `w:A`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K0:real` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The level data at deep points (the bound clauses of the CG chain). *)

let P2GA_DEEP_CHART = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z d.
     p2ga_hyp V U z /\ &0 < d
     ==> ?rho K N. &0 < rho /\ rho <= &1 / &2 /\ rho <= d / &16 /\ &0 <= K /\ K * rho pow 2 <= &1 /\
           (!n y. N <= n /\ y IN p2ga_dp (V n) (U n) d
                  ==> mfd_inj_ball (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                   (rfs_vmetric (V n) (&0)) y rho /\
                      (!w. w IN mfd_ball (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                         (rfs_vmetric (V n) (&0)) y rho
                           ==> mfd_rm_norm (rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0)) w
                               <= K) /\
                      mfd_ball (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                               (rfs_vmetric (V n) (&0)) y rho SUBSET U n) /\
           (!m. ?B. !n y E. N <= n /\ y IN p2ga_dp (V n) (U n) d /\
                            mfd_orthonormal_frame (rfs_vmetric (V n) (&0)) y E
                            ==> metric_field (ball(vec 0,rho))
                                  (cmp_expmetric (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                                 (rfs_vmetric (V n) (&0)) y E) /\
                                !w. norm w < rho / &2
                                    ==> lck_dist2 m (\z. mat 1)
                                          (cmp_expmetric (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                                         (rfs_vmetric (V n) (&0)) y E) w <= B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `U:num->A->bool`; `z:num->A`; `d:real`]
                P2GA_DEEP_OK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `tau:real` (X_CHOOSE_THEN `i0:real`
    (X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ok"))))))))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Cg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g0")) o
              MATCH_MP (INST_TYPE [`:A`,`:A`] P2CD_GAUGE0)) THEN
  MP_TAC(ISPECL [`min i0 (min (d / &8) (&1))`; `K:real`; `Cg:real`] P2CD_RADIUS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`rho:real`; `K:real`; `N:num`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`; `U:num->A->bool`; `z:num->A`; `n:num`] P2GA_SLICE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:A) IN U n /\ p2b_lc_deep (V n) (U (n:num)) y d` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:A) IN p2ga_dp (V n) (U (n:num)) d` THEN REWRITE_TAC[p2ga_dp; IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:A) IN topspace (rfs_vtop (V (n:num)) (&0))` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V (n:num):(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) (&0)`;
                   `rfs_vatlas (V (n:num):(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) (&0)`;
                   `rfs_vmetric (V (n:num):(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                          (real->A->real^3^3)) (&0)`; `y:A`] P2CU_FRAME_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:real^3^3`) THEN
    USE_THEN "ok" (MP_TAC o SPECL [`n:num`; `y:A`; `E:real^3^3`; `rho:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p2cd_ok] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_rm_norm" with Failure _ -> false))
            (concl th))) THEN
      REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(w:A) IN mfd_ball (rfs_vtop (V (n:num)) (&0),rfs_vatlas (V n) (&0))
                                     (rfs_vmetric (V n) (&0)) y rho` THEN
      REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t ==> (x:A) IN s ==> x IN t`) THEN
      MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `rfs_vtop (V (n:num)) (&0) closure_of rfs_vball (V n) (&0) (y:A) d` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `rfs_vball (V (n:num)) (&0) (y:A) d` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC CLOSURE_OF_SUBSET THEN REWRITE_TAC[P2CO_VBALL] THEN
          MATCH_MP_TAC P2CU_BALL_SUBSET THEN ASM_REWRITE_TAC[]];
        UNDISCH_TAC `p2b_lc_deep (V n) (U (n:num)) (y:A) d` THEN SIMP_TAC[p2b_lc_deep]]];
    ALL_TAC] THEN
  X_GEN_TAC `m:num` THEN
  USE_THEN "g0" (MP_TAC o SPECL [`rho:real`; `d / &2`; `--tau`; `m:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "B")) THEN EXISTS_TAC `B:real` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:A`; `E:real^3^3`] THEN STRIP_TAC THEN
  USE_THEN "ok" (MP_TAC o SPECL [`n:num`; `y:A`; `E:real^3^3`; `rho:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) n`; `y:A`; `E:real^3^3`; `rho:real`; `d / &2`;
                 `--tau`; `K:real`] P2CD_OK_PB0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "eq") (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`; `U:num->A->bool`; `z:num->A`; `n:num`] P2GA_SLICE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `p2cd_ok ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) n) y E rho (d / &2) (--tau) K` THEN
    REWRITE_TAC[p2cd_ok] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_vtop (V (n:num):(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) (&0)`;
                   `rfs_vatlas (V (n:num):(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) (&0)`;
                   `rfs_vmetric (V (n:num):(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                          (real->A->real^3^3)) (&0)`;
                   `y:A`; `E:real^3^3`; `rho:real`; `K:real`] P2CU_EXPMETRIC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_rm_norm" with Failure _ -> false))
          (concl th))) THEN
    REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(w:A) IN mfd_ball (rfs_vtop (V (n:num)) (&0),rfs_vatlas (V n) (&0))
                                   (rfs_vmetric (V n) (&0)) y rho` THEN
    REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t ==> (x:A) IN s ==> x IN t`) THEN
    MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    REMOVE_THEN "B" (MP_TAC o SPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) n`; `y:A`; `E:real^3^3`;
                                  `w:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= b ==> y <= b`) THEN
    MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `ball(vec 0:real^3,rho)` THEN
    REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL_0]]);;

(* ------------------------------------------------------------------------- *)
(* The nets of one level.  For a deepness d, a spacing r with                *)
(* 5 r <= d and r <= 1, and a bound a > 0: for all large n an enumeration y *)
(* of an r-net, y 0 = z n, all points in the region Y(d,a + r), covering   *)
(* Y(d,a) by r-balls with indices below a P uniform in n (P2GA_LOCAL_PACK,  *)
(* P2GA_SHELL_NETS at the least shell index i with a <= i r / 2).           *)
(* ------------------------------------------------------------------------- *)

let P2GA_Y_SHELL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z d a.
     p2ga_Y V U z d a =
     p2ga_shell (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (p2ga_dp V U d) z a`,
  REWRITE_TAC[p2ga_Y; p2ga_shell]);;

let P2GA_SHELL_MONO = prove
 (`!top atlas (g:A->real^3^3) D z a b.
     a <= b ==> p2ga_shell (top,atlas) g D z a SUBSET p2ga_shell (top,atlas) g D z b`,
  REWRITE_TAC[p2ga_shell; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LTE_TRANS]);;

let P2GA_ENUM = prove
 (`!(Tn:A->bool) z P.
     FINITE Tn /\ CARD Tn + 1 <= P
     ==> ?y:num->A. y 0 = z /\ (!s. y s = z \/ y s IN Tn) /\
                    (!t. t IN Tn ==> ?s. s < P /\ y s = t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Tn:A->bool`; `CARD(Tn:A->bool)`] HAS_SIZE_INDEX) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\s. if s = 0 then (z:A) else if s <= CARD(Tn:A->bool) then f(s - 1) else z` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:num` THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `t:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:A` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    EXISTS_TAC `i + 1` THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(i + 1 = 0) /\ (i + 1) - 1 = i`] THEN
    SUBGOAL_THEN `i + 1 <= CARD(Tn:A->bool)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

(* The shell index. *)

let P2GA_SHELL_INDEX = prove
 (`!a r. &0 < a /\ &0 < r
         ==> ?i. a <= &i * r / &2 /\ &i * r / &2 <= a + r / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\i. &2 * a / r <= &i` num_WOP) THEN REWRITE_TAC[REAL_ARCH_SIMPLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `i - 1`))) THEN
  ASM_CASES_TAC `i = 0` THENL
   [UNDISCH_TAC `&2 * a / r <= &i` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &2 * a / r` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `~(i = 0) ==> 1 <= i`; REAL_NOT_LE] THEN
  DISCH_TAC THEN EXISTS_TAC `i:num` THEN
  UNDISCH_TAC `&2 * a / r <= &i` THEN UNDISCH_TAC `&i - &1 < &2 * a / r` THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_ARITH `&2 * a / r = (&2 * a) / r`] THEN
  REWRITE_TAC[real_div] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2GA_LEVEL_NETS = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z d r a.
     p2ga_hyp V U z /\ &0 < r /\ &5 * r <= d /\ r <= &1 /\ &0 < a /\
     (!n. z n IN p2ga_dp (V n) (U n) d)
     ==> ?P N. !n. N <= n
                   ==> ?y:num->A.
                         y 0 = z n /\
                         (!s. y s IN p2ga_Y (V n) (U n) (z n) d (a + r)) /\
                         (!p. p IN p2ga_Y (V n) (U n) (z n) d a
                              ==> ?s. s < P /\
                                      p IN mfd_ball (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                                    (rfs_vmetric (V n) (&0)) (y s) r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `U:num->A->bool`; `z:num->A`; `d:real`; `r:real`]
                P2GA_LOCAL_PACK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (X_CHOOSE_THEN `N:num` (LABEL_TAC "pack"))) THEN
  MP_TAC(SPECL [`a:real`; `r:real`] P2GA_SHELL_INDEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`(M + 1) EXP i + 1`; `N:num`] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `U:num->A->bool`; `z:num->A`; `n:num`] P2GA_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2ga_dp (V (n:num)) ((U:num->A->bool) n) d SUBSET topspace (rfs_vtop (V n) (&0))` ASSUME_TAC THENL
   [REWRITE_TAC[p2ga_dp; SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V (n:num):(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) (&0)`;
                 `rfs_vatlas (V (n:num):(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) (&0)`;
                 `rfs_vmetric (V (n:num):(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (&0)`;
                 `p2ga_dp (V (n:num)) ((U:num->A->bool) n) d`; `(z:num->A) n`; `r:real`; `M:num`]
                P2GA_SHELL_NETS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:A`; `S:A->bool`] THEN STRIP_TAC THEN
    USE_THEN "pack" (MATCH_MP_TAC o SPECL [`n:num`; `t:A`; `S:A->bool`]) THEN
    ASM_REWRITE_TAC[P2CO_VBALL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `Tn:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Tin") (LABEL_TAC "Tcov")))))) THEN
  MP_TAC(ISPECL [`Tn:A->bool`; `(z:num->A) n`; `(M + 1) EXP i + 1`] P2GA_ENUM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_ADD_RCANCEL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:num->A` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:num` THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o SPEC `s:num` o check (fun th ->
      can (find_term ((=) `Tn:A->bool`)) (concl th) && is_forall(concl th) &&
      not (can (find_term (fun t -> t = `P2GA_ENUM`)) (concl th)) &&
      is_disj(snd(strip_forall(concl th))))) THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2GA_Y_BASE THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "Tin" (MP_TAC o C MP (ASSUME `(y:num->A) s IN Tn`) o SPEC `(y:num->A) s`) THEN
      STRIP_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2GA_Y_BASE THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[P2GA_Y_SHELL] THEN
        MATCH_MP_TAC(SET_RULE `!x:A s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
        EXISTS_TAC `p2ga_shell (rfs_vtop (V (n:num)) (&0),rfs_vatlas (V n) (&0))
                      (rfs_vmetric (V n) (&0)) (p2ga_dp (V n) (U n) d) ((z:num->A) n)
                      (&i * r / &2)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2GA_SHELL_MONO THEN ASM_REAL_ARITH_TAC]];
    X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    USE_THEN "Tcov" (MP_TAC o SPEC `p:A`) THEN ANTS_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!x:A s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `p2ga_Y (V (n:num)) (U n) ((z:num->A) n) d a` THEN
      ASM_REWRITE_TAC[P2GA_Y_SHELL] THEN MATCH_MP_TAC P2GA_SHELL_MONO THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:A` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Tn:A->bool`)) (concl th) &&
      is_exists(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* All levels at once.  With delta0 of H3, level j has the                   *)
(* deepness d0 / 2^j, the region Y(d0/2^j, j + 1/2) and the net spacing     *)
(* rho j / 8; from the index N0 j on, the net points yc j k s (yc j k 0 =   *)
(* z k) lie in Y(d0/2^j, j + 1), carry the level data of the CG chain       *)
(* (P2GA_DEEP_CHART at deepness d0/2^j) and cover the region by balls of    *)
(* radius rho j / 8 with indices below P j (P2GA_LEVEL_NETS).               *)
(* ------------------------------------------------------------------------- *)

let P2GA_LEVELS_RAW = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z.
     p2ga_hyp V U z
     ==> ?d0 rho K N0 B P yc.
           &0 < d0 /\ (!n. z n IN p2ga_dp (V n) (U n) d0) /\
           (!j. &0 < rho j /\ rho j <= &1 / &2 /\ rho j <= d0 / &2 pow j / &16 /\
                &0 <= K j /\ K j * rho j pow 2 <= &1) /\
           (!j k s. N0 j <= k
                    ==> yc j k s IN p2ga_dp (V k) (U k) (d0 / &2 pow j) /\
                        mfd_inj_ball (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                     (rfs_vmetric (V k) (&0)) (yc j k s) (rho j) /\
                        (!w. w IN mfd_ball (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                           (rfs_vmetric (V k) (&0)) (yc j k s) (rho j)
                             ==> mfd_rm_norm (rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0)) w
                                 <= K j) /\
                        mfd_ball (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                 (rfs_vmetric (V k) (&0)) (yc j k s) (rho j) SUBSET U k) /\
           (!j m k s E. N0 j <= k /\
                        mfd_orthonormal_frame (rfs_vmetric (V k) (&0)) (yc j k s) E
                        ==> metric_field (ball(vec 0,rho j))
                              (cmp_expmetric (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                             (rfs_vmetric (V k) (&0)) (yc j k s) E) /\
                            !w. norm w < rho j / &2
                                ==> lck_dist2 m (\z. mat 1)
                                      (cmp_expmetric (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                                     (rfs_vmetric (V k) (&0)) (yc j k s) E) w
                                    <= B j m) /\
           (!j k. N0 j <= k
                  ==> yc j k 0 = z k /\
                      (!s. yc j k s IN p2ga_Y (V k) (U k) (z k) (d0 / &2 pow j) (&j + &1)) /\
                      (!p. p IN p2ga_Y (V k) (U k) (z k) (d0 / &2 pow j) (&j + &1 / &2)
                           ==> ?s. s < P j /\
                                   p IN mfd_ball (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                                 (rfs_vmetric (V k) (&0)) (yc j k s)
                                                 (rho j / &32)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I [p2ga_hyp]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `!n. (z:num->A) n IN p2ga_dp (V n) (U n) d0` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[p2ga_dp; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`; `U:num->A->bool`; `z:num->A`; `n:num`] P2GA_SLICE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. &0 < d0 / &2 pow j /\ d0 / &2 pow j <= d0` ASSUME_TAC THENL
   [GEN_TAC THEN SUBGOAL_THEN `&1 <= &2 pow j` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < d /\ &1 <= x /\ d <= d * x ==> d <= d * x`) THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the chart data per level *)
  SUBGOAL_THEN
   `!j. ?rho K N. &0 < rho /\ rho <= &1 / &2 /\ rho <= (d0 / &2 pow j) / &16 /\ &0 <= K /\
                  K * rho pow 2 <= &1 /\
                  (!n y. N <= n /\ y IN p2ga_dp (V n) (U n) (d0 / &2 pow j)
                         ==> mfd_inj_ball (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                          (rfs_vmetric (V n) (&0)) y rho /\
                             (!w. w IN mfd_ball (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                                (rfs_vmetric (V n) (&0)) y rho
                                  ==> mfd_rm_norm (rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0)) w
                                      <= K) /\
                             mfd_ball (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                      (rfs_vmetric (V n) (&0)) y rho SUBSET (U:num->A->bool) n) /\
                  (!m. ?B. !n y E. N <= n /\ y IN p2ga_dp (V n) (U n) (d0 / &2 pow j) /\
                                   mfd_orthonormal_frame (rfs_vmetric (V n) (&0)) y E
                                   ==> metric_field (ball(vec 0,rho))
                                         (cmp_expmetric (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                                        (rfs_vmetric (V n) (&0)) y E) /\
                                       !w. norm w < rho / &2
                                           ==> lck_dist2 m (\z. mat 1)
                                                 (cmp_expmetric (rfs_vtop (V n) (&0),
                                                                 rfs_vatlas (V n) (&0))
                                                                (rfs_vmetric (V n) (&0)) y E) w <= B)`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`; `U:num->A->bool`; `z:num->A`;
                   `d0 / &2 pow j`] P2GA_DEEP_CHART) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:num->real` (X_CHOOSE_THEN `K:num->real`
    (X_CHOOSE_THEN `Nc:num->num` (LABEL_TAC "ch")))) THEN
  USE_THEN "ch" (MP_TAC o GEN `j:num` o last o CONJUNCTS o SPEC `j:num`) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num->num->real` (LABEL_TAC "B")) THEN
  (* the nets per level *)
  SUBGOAL_THEN
   `!j. ?P N. !n. N <= (n:num)
                  ==> ?y:num->A.
                        y 0 = (z:num->A) n /\
                        (!s. y s IN p2ga_Y (V n) (U n) (z n) (d0 / &2 pow j)
                                           ((&j + &1 / &2) + (rho:num->real) j / &32)) /\
                        (!p. p IN p2ga_Y (V n) (U n) (z n) (d0 / &2 pow j) (&j + &1 / &2)
                             ==> ?s. s < P /\
                                     p IN mfd_ball (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                                   (rfs_vmetric (V n) (&0)) (y s) (rho j / &32))`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`; `U:num->A->bool`; `z:num->A`;
                   `d0 / &2 pow j`; `(rho:num->real) j / &32`; `&j + &1 / &2`]
                  P2GA_LEVEL_NETS) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ch" (MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
      X_GEN_TAC `n:num` THEN
      MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) n`; `(U:num->A->bool) n`; `d0:real`;
                     `d0 / &2 pow j`] P2GA_DP_MONO) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num->num` (X_CHOOSE_THEN `Nl:num->num` MP_TAC)) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[SKOLEM_THM] o
             GEN_REWRITE_RULE (BINDER_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `yc:num->num->num->A` (LABEL_TAC "net")) THEN
  MAP_EVERY EXISTS_TAC [`d0:real`; `rho:num->real`; `K:num->real`;
                        `\j. (Nc:num->num) j + (Nl:num->num) j`; `B:num->num->real`;
                        `P:num->num`; `yc:num->num->num->A`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!j k s. Nc j + Nl j <= k
            ==> (yc:num->num->num->A) j k s IN p2ga_Y (V k) (U k) (z k) (d0 / &2 pow j) (&j + &1)`
  (LABEL_TAC "inY") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "net" (MP_TAC o SPECL [`j:num`; `k:num`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:num` o CONJUNCT1 o CONJUNCT2) THEN
    MATCH_MP_TAC(SET_RULE `!x:A s t. s SUBSET t ==> x IN s ==> x IN t`) THEN
    MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`; `U:num->A->bool`; `z:num->A`; `k:num`] P2GA_SLICE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2GA_Y_MONO THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    USE_THEN "ch" (MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(yc:num->num->num->A) j k s IN p2ga_dp (V k) (U k) (d0 / &2 pow j)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2GA_Y_DP THEN
      MAP_EVERY EXISTS_TAC [`(z:num->A) k`; `&j + &1`] THEN
      USE_THEN "inY" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ch" (MP_TAC o SPEC `j:num`) THEN
    DISCH_THEN(MP_TAC o SPECL [`k:num`; `(yc:num->num->num->A) j k s`] o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(yc:num->num->num->A) j k s IN p2ga_dp (V k) (U k) (d0 / &2 pow j)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2GA_Y_DP THEN
      MAP_EVERY EXISTS_TAC [`(z:num->A) k`; `&j + &1`] THEN
      USE_THEN "inY" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "B" (MP_TAC o SPECL [`j:num`; `m:num`; `k:num`; `(yc:num->num->num->A) j k s`;
                                  `E:real^3^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "net" (MP_TAC o SPECL [`j:num`; `k:num`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    USE_THEN "inY" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Curves of the path-lifting clause lie in the level regions.               *)
(* A C^1 curve from z of length <= A all of whose points are delta-deep     *)
(* lies in Y(d,a) for every d <= delta and a > A (its initial pieces are     *)
(* curves inside the deep set, P2GA_BACKSTEP-style reparametrisation).      *)
(* ------------------------------------------------------------------------- *)

let P2GA_CURVE_IN_Y = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U z gamma delta A d a.
     smooth_manifold_atlas (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
     riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) /\
     mfd_c1_curve (rfs_vtop V (&0),rfs_vatlas V (&0)) gamma (&0) (&1) /\ gamma (&0) = z /\
     mfd_length (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) gamma (&0) (&1) <= A /\
     (!s. &0 <= s /\ s <= &1 ==> p2b_lc_deep V U (gamma s) delta) /\
     &0 < d /\ d <= delta /\ A < a
     ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN p2ga_Y V U z d a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ABBREV_TAC `top = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)` THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,s] ==> (gamma:real->A) t IN p2ga_dp V U d`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[p2ga_dp; IN_ELIM_THM] THEN
    SUBGOAL_THEN `p2b_lc_deep V U ((gamma:real->A) t) d` ASSUME_TAC THENL
     [MATCH_MP_TAC P2GA_DEEP_MONO THEN EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2GA_DEEP_IN THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)`; `d:real`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `&0`; `&1`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `&0`; `s:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `s:real`; `&1`] MFD_LENGTH_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[p2ga_Y; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(gamma:real->A)(&0) = z`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_joinable_in] THEN
    EXISTS_TAC `(gamma:real->A) o (\x. &0 + (s - &0) * x)` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `gamma:real->A`; `&0`; `s:real`] GRGD_AFFINE_CURVE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `s:real`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "p2ga_dp" with Failure _ -> false))
          (concl th))) THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_SUB_RZERO; REAL_ADD_LID] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `s = s * &1`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^3^3) (gamma:real->A) (&0) s` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_IN_LE_LENGTH THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]]);;

