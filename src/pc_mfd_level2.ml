(* ========================================================================= *)
(* pc_mfd_level2: the induced metric of a regular level set.  Its            *)
(* representative in ANY adapted chart c, read through ANY ambient chart c'  *)
(* of atlas, is K^T G_c' K with K the 3x2 derivative of w |-> SND c'         *)
(* (chart_inv c w), a function of the charts only (LVS_METRIC_LOCAL); the    *)
(* induced metric is a Riemannian metric of the leaf (LVS_RIEMANNIAN);       *)
(* compact leaves have an area (LVS_AREA); comparison of induced metrics and *)
(* areas (LVS_METRIC_QF_COMPARE, LVS_AREA_COMPARE, with the                  *)
(* dimension-generic LVS_HAS_VOLUME_COMPARE_QF).                             *)
(* ========================================================================= *)

needs "src/pc_mfd_level.ml";;
needs "src/pc_grg_area.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Chart transitions for general charts, and the ambient metric at x read    *)
(* through any chart containing x.                                           *)
(* ------------------------------------------------------------------------- *)

let LVS_CHART_TRANS_GEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c c'.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas
     ==> open (IMAGE (SND c) (FST c INTER FST c')) /\
         smooth_map_on (IMAGE (SND c) (FST c INTER FST c')) (chart_trans c c') /\
         (!x. x IN FST c ==> chart_trans c c' (SND c x) = SND c' x)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `c:(A->bool)#(A->real^N)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `c':(A->bool)#(A->real^N)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `psi:A->real^N`
    SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CHART_TRANS_SMOOTH THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CHART_TRANS_AT THEN ASM_MESON_TAC[]]);;

let LVS_G_AT_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c' x.
     smooth_manifold_atlas top atlas /\ c' IN atlas /\ x IN topspace top /\
     x IN FST c'
     ==> g x = mpullback (chart_trans (chart_at atlas x) c')
                         (metric_local atlas c' g) (SND(chart_at atlas x) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) x`
               PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `c':(A->bool)#(A->real^N)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `psi:A->real^N`
    SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[IN_INTER]);;

(* ------------------------------------------------------------------------- *)
(* The chart formula.  For an adapted chart c and an ambient chart c' at     *)
(* x = chart_inv c z, the derivative K of w |-> SND c' (chart_inv c w) at z  *)
(* factors through the preferred charts (LVS_KCHAIN), and metric_local of    *)
(* lvs_metric in c at z is K^T G_c' K.                                       *)
(* ------------------------------------------------------------------------- *)

let LVS_KCHAIN = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u c c' x.
     smooth_manifold_atlas top atlas /\ open_in top W /\ lvs_regular atlas W f u /\
     c IN lvs_atlas top atlas W f u /\ c' IN atlas /\ x IN FST c /\ x IN FST c'
     ==> linear(frechet_derivative (chart_trans (chart_at atlas x) c')
                                   (at (SND(chart_at atlas x) x))) /\
         linear(lvs_jac top atlas W f u x) /\
         linear(chart_jac c (chart_at (lvs_atlas top atlas W f u) x) x) /\
         frechet_derivative (\w. SND c' (chart_inv c w)) (at (SND c x)) =
         frechet_derivative (chart_trans (chart_at atlas x) c')
                            (at (SND(chart_at atlas x) x)) o
         (lvs_jac top atlas W f u x o
          chart_jac c (chart_at (lvs_atlas top atlas W f u) x) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[lvs_jac; chart_jac] THEN
  ABBREV_TAC `L = lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u` THEN
  ABBREV_TAC `N = lvs_set (W:A->bool) (f:A->real) u` THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology top (N:A->bool))
                          (L:((A->bool)#(A->real^2))->bool)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "N"] THEN MATCH_MP_TAC LVS_MANIFOLD THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology top (N:A->bool)) = N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN ASM_SIMP_TAC[LVS_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (N:A->bool)`; `L:((A->bool)#(A->real^2))->bool`;
                 `c:(A->bool)#(A->real^2)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN N` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`W:A->bool`; `f:A->real`; `u:real`] LVS_SET_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (N:A->bool)`; `L:((A->bool)#(A->real^2))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c3 = chart_at (L:((A->bool)#(A->real^2))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c4 = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (N:A->bool)`; `L:((A->bool)#(A->real^2))->bool`;
                 `c3:(A->bool)#(A->real^2)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c4:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c':(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the three derivatives *)
  MP_TAC(ISPECL [`subtopology top (N:A->bool)`; `L:((A->bool)#(A->real^2))->bool`;
                 `c:(A->bool)#(A->real^2)`; `c3:(A->bool)#(A->real^2)`]
                LVS_CHART_TRANS_GEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c4:(A->bool)#(A->real^3)`; `c':(A->bool)#(A->real^3)`]
                LVS_CHART_TRANS_GEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`;
                 `c3:(A->bool)#(A->real^2)`; `c4:(A->bool)#(A->real^3)`]
                LVS_CHART_AMBIENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(chart_trans (c:(A->bool)#(A->real^2)) c3 has_derivative
     frechet_derivative (chart_trans c c3) (at (SND c x))) (at (SND c x))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^2))) (FST c INTER FST(c3:(A->bool)#(A->real^2)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. SND(c4:(A->bool)#(A->real^3)) (chart_inv (c3:(A->bool)#(A->real^2)) w))
     has_derivative
     frechet_derivative (\w. SND c4 (chart_inv c3 w)) (at (SND c3 x)))
    (at (chart_trans (c:(A->bool)#(A->real^2)) c3 (SND c x)))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{w | w IN IMAGE (SND(c3:(A->bool)#(A->real^2))) (FST c3) /\
                     chart_inv c3 w IN FST(c4:(A->bool)#(A->real^3))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(chart_trans (c4:(A->bool)#(A->real^3)) c' has_derivative
     frechet_derivative (chart_trans c4 c') (at (SND c4 x)))
    (at (SND c4 (chart_inv (c3:(A->bool)#(A->real^2))
                  (chart_trans (c:(A->bool)#(A->real^2)) c3 (SND c x)))))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c4:(A->bool)#(A->real^3))) (FST c4 INTER FST(c':(A->bool)#(A->real^3)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((chart_trans (c4:(A->bool)#(A->real^3)) c' o
      ((\w. SND c4 (chart_inv (c3:(A->bool)#(A->real^2)) w)) o
       chart_trans (c:(A->bool)#(A->real^2)) c3)) has_derivative
     (frechet_derivative (chart_trans c4 c') (at (SND c4 x)) o
      (frechet_derivative (\w. SND c4 (chart_inv c3 w)) (at (SND c3 x)) o
       frechet_derivative (chart_trans c c3) (at (SND c x))))) (at (SND c x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR];
    ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR];
    ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR];
    ALL_TAC] THEN
  MATCH_MP_TAC(GSYM FRECHET_DERIVATIVE_AT) THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC
   `chart_trans (c4:(A->bool)#(A->real^3)) c' o
    ((\w. SND c4 (chart_inv (c3:(A->bool)#(A->real^2)) w)) o
     chart_trans (c:(A->bool)#(A->real^2)) c3)` THEN
  EXISTS_TAC
   `IMAGE (SND(c:(A->bool)#(A->real^2)))
          (FST c INTER FST(c3:(A->bool)#(A->real^2)) INTER
           ((N:A->bool) INTER (FST(c4:(A->bool)#(A->real^3)) INTER
                               FST(c':(A->bool)#(A->real^3)))))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`subtopology top (N:A->bool)`;
                          `L:((A->bool)#(A->real^2))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    REWRITE_TAC[chart_trans] THEN ASM_SIMP_TAC[]]);;

let LVS_METRIC_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u c c' z.
     smooth_manifold_atlas top atlas /\ open_in top W /\ lvs_regular atlas W f u /\
     c IN lvs_atlas top atlas W f u /\ c' IN atlas /\
     z IN IMAGE (SND c) (FST c) /\ chart_inv c z IN FST c'
     ==> metric_local (lvs_atlas top atlas W f u) c
                      (lvs_metric top atlas g W f u) z =
         transp(matrix(frechet_derivative (\w. SND c' (chart_inv c w)) (at z))) **
         metric_local atlas c' g (SND c' (chart_inv c z)) **
         matrix(frechet_derivative (\w. SND c' (chart_inv c w)) (at z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology top (lvs_set W f u))
                          (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LVS_MANIFOLD]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set W f u):A topology`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u`;
                 `c:(A->bool)#(A->real^2)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^2)) z` THEN
  SUBGOAL_THEN `(x:A) IN FST(c:(A->bool)#(A->real^2)) /\ SND c x = z`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "x" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `SND (c:(A->bool)#(A->real^2)) x = z` THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:A) IN lvs_set W f u` MP_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `W:A->bool`; `f:A->real`; `u:real`]
                    LVS_TOPSPACE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      MP_TAC(ISPECL [`W:A->bool`; `f:A->real`; `u:real`] LVS_SET_SUBSET) THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`;
                 `c:(A->bool)#(A->real^2)`; `c':(A->bool)#(A->real^3)`; `x:A`]
                LVS_KCHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [metric_local] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[lvs_metric] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `c':(A->bool)#(A->real^3)`; `x:A`]
                LVS_G_AT_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) x`;
                 `c':(A->bool)#(A->real^3)`] LVS_CHART_TRANS_GEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mpullback] THEN ASM_SIMP_TAC[] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_COMPOSE] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The induced metric is a Riemannian metric of the leaf.  Entries of K^T G  *)
(* K are dots of smooth vector fields; K is injective since SND c' o e is a  *)
(* local diffeomorphism and lvs_iota is injective.                           *)
(* ------------------------------------------------------------------------- *)

let LVS_CONGRUENCE_ENTRY = prove
 (`!(L:real^2->real^3) (M:real^3^3) i j.
     linear L /\ 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
     ==> (transp(matrix L) ** M ** matrix L)$i$j = L(basis i) dot (M ** L(basis j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!A:real^2^2. A$i$j = basis i dot (A ** basis j)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_2; MATRIX_VECTOR_MUL_BASIS] THEN
    ASM_SIMP_TAC[column; LAMBDA_BETA; DIMINDEX_2];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let LVS_PARAM_CHART_DIFFEO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A) e' c.
     smooth_manifold_atlas top atlas /\
     mfd_diffeo euclidean (open_set_atlas (:real^N)) s top atlas (IMAGE e s) e e' /\
     c IN atlas
     ==> diffeomorphism_on {y | y IN s /\ e y IN FST c}
                           (IMAGE (SND c) (FST c INTER IMAGE e s))
                           (SND c o e) (e' o chart_inv c)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `c:(A->bool)#(A->real^N)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `psi:A->real^N`
    SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `s:real^N->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^N))->bool`; `IMAGE (e:real^N->A) s`;
                 `e:real^N->A`; `e':A->real^N`; `(:real^N)`; `\x:real^N. x`;
                 `V:A->bool`; `psi:A->real^N`] MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[LVS_EUCLIDEAN_ATLAS; open_set_atlas; IN_SING] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^N. x) {x | x IN (:real^N) INTER s /\ (e:real^N->A) x IN V} =
    {y | y IN s /\ e y IN V}`
  SUBST1_TAC THENL [REWRITE_TAC[IMAGE_ID; INTER_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{y | y IN V INTER IMAGE (e:real^N->A) s /\ (e':A->real^N) y IN (:real^N)} =
    V INTER IMAGE e s`
  SUBST1_TAC THENL [REWRITE_TAC[IN_UNIV] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(psi:A->real^N) o (e:real^N->A) o chart_inv ((:real^N),(\x:real^N. x)) =
    psi o e`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^N. x) o (e':A->real^N) o chart_inv (V:A->bool,psi:A->real^N) =
    e' o chart_inv (V,psi)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[]);;

let LVS_K_INJECTIVE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u c c' z v.
     smooth_manifold_atlas top atlas /\ open_in top W /\ lvs_regular atlas W f u /\
     c IN lvs_atlas top atlas W f u /\ c' IN atlas /\
     z IN IMAGE (SND c) (FST c) /\ chart_inv c z IN FST c' /\
     frechet_derivative (\w. SND c' (chart_inv c w)) (at z) v = vec 0
     ==> v = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(c:(A->bool)#(A->real^2)) IN lvs_atlas top atlas W f u` THEN
  REWRITE_TAC[LVS_ATLAS_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `e:real^3->A`
    (X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`] LVS_ADAPTED_LEAF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SND; th])))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
  SUBGOAL_THEN
   `!w. lvs_iota w IN s
        ==> chart_inv (IMAGE (e:real^3->A) s INTER lvs_set W f u,
                       (\x. lvs_proj((e':A->real^3) x))) w = e(lvs_iota w)`
  (LABEL_TAC "ci") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LVS_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`;
                          `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`;
                 `c':(A->bool)#(A->real^3)`] LVS_PARAM_CHART_SMOOTH) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`;
                 `c':(A->bool)#(A->real^3)`] LVS_PARAM_CHART_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `sc = {y | y IN s /\ (e:real^3->A) y IN FST(c':(A->bool)#(A->real^3))}` THEN
  SUBGOAL_THEN `lvs_iota z IN (sc:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "sc" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    USE_THEN "ci" (MP_TAC o SPEC `z:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c':(A->bool)#(A->real^3))) (FST c' INTER IMAGE (e:real^3->A) s)`;
                 `sc:real^3->bool`;
                 `SND(c':(A->bool)#(A->real^3)) o (e:real^3->A)`;
                 `(e':A->real^3) o chart_inv (c':(A->bool)#(A->real^3))`;
                 `lvs_iota z`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\w. SND(c':(A->bool)#(A->real^3))
             (chart_inv (IMAGE (e:real^3->A) s INTER lvs_set W f u,
                         (\x. lvs_proj((e':A->real^3) x))) w)) (at z) =
    frechet_derivative (SND c' o e) (at (lvs_iota z)) o lvs_iota`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(GSYM FRECHET_DERIVATIVE_AT) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `(SND(c':(A->bool)#(A->real^3)) o (e:real^3->A)) o lvs_iota` THEN
    EXISTS_TAC `{w:real^2 | lvs_iota w IN sc}` THEN
    ASM_SIMP_TAC[LVS_OPEN_IOTA_PREIMAGE; IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^2` THEN EXPAND_TAC "sc" THEN
      REWRITE_TAC[IN_ELIM_THM; o_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; LVS_IOTA_LINEAR]];
    ALL_TAC] THEN
  UNDISCH_TAC
   `frechet_derivative
      (\w. SND(c':(A->bool)#(A->real^3))
             (chart_inv (IMAGE (e:real^3->A) s INTER lvs_set W f u,
                         (\x. lvs_proj((e':A->real^3) x))) w)) (at z) v = vec 0` THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`sc:real^3->bool`;
    `IMAGE (SND(c':(A->bool)#(A->real^3))) (FST c' INTER IMAGE (e:real^3->A) s)`;
    `(e':A->real^3) o chart_inv (c':(A->bool)#(A->real^3))`;
    `SND(c':(A->bool)#(A->real^3)) o (e:real^3->A)`;
    `(SND(c':(A->bool)#(A->real^3)) o (e:real^3->A)) (lvs_iota z)`]
   LRG_DIFFEO_DERIV) THEN
  ASM_SIMP_TAC[DIFFEOMORPHISM_ON_SYM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lvs_iota v = vec 0` MP_TAC THENL
   [SUBGOAL_THEN
     `frechet_derivative ((e':A->real^3) o chart_inv (c':(A->bool)#(A->real^3)))
        (at ((SND c' o (e:real^3->A)) (lvs_iota z)))
        (frechet_derivative (SND c' o e) (at (lvs_iota z)) (lvs_iota v)) =
      lvs_iota v`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME
     `frechet_derivative (SND(c':(A->bool)#(A->real^3)) o (e:real^3->A))
        (at (lvs_iota z)) (lvs_iota v) = vec 0`] THEN
    REWRITE_TAC[MATCH_MP LINEAR_0 (ASSUME
     `linear(frechet_derivative ((e':A->real^3) o
               chart_inv (c':(A->bool)#(A->real^3)))
             (at ((SND c' o (e:real^3->A)) (lvs_iota z))))`)] THEN
    MESON_TAC[];
    DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM LVS_IOTA_INJ] THEN
    ASM_REWRITE_TAC[MATCH_MP LINEAR_0 LVS_IOTA_LINEAR]]);;

let LVS_RIEMANNIAN = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ lvs_regular atlas W f u
     ==> riemannian_metric (lvs_atlas top atlas W f u)
                           (lvs_metric top atlas g W f u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^2)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology top (lvs_set W f u))
                          (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LVS_MANIFOLD]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set W f u):A topology`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u`;
                 `c:(A->bool)#(A->real^2)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (SND c) (FST c)
        ==> ?c'. c' IN (atlas:((A->bool)#(A->real^3))->bool) /\
                 chart_inv (c:(A->bool)#(A->real^2)) z IN FST c'`
  (LABEL_TAC "cp") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    EXISTS_TAC `chart_at (atlas:((A->bool)#(A->real^3))->bool)
                         (chart_inv (c:(A->bool)#(A->real^2)) z)` THEN
    MATCH_MP_TAC CHART_AT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^2)) z IN lvs_set W f u` MP_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `W:A->bool`; `f:A->real`; `u:real`]
                    LVS_TOPSPACE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      MP_TAC(ISPECL [`W:A->bool`; `f:A->real`; `u:real`] LVS_SET_SUBSET) THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
    ALL_TAC] THEN
  REWRITE_TAC[metric_field] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "cp" (MP_TAC o SPEC `z:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c':(A->bool)#(A->real^3)` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `W:A->bool`; `f:A->real`; `u:real`;
                   `c:(A->bool)#(A->real^2)`; `c':(A->bool)#(A->real^3)`]
                  LVS_CHART_AMBIENT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `{w | w IN IMAGE (SND(c:(A->bool)#(A->real^2))) (FST c) /\
                     chart_inv c w IN FST(c':(A->bool)#(A->real^3))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC
     `(vectorize:real^2^2->real^(2,2)finite_prod) o
      (\w. transp(matrix(frechet_derivative
                   (\w'. SND(c':(A->bool)#(A->real^3))
                           (chart_inv (c:(A->bool)#(A->real^2)) w')) (at w))) **
           metric_local atlas c' g (SND c' (chart_inv c w)) **
           matrix(frechet_derivative (\w'. SND c' (chart_inv c w')) (at w)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC LVS_METRIC_LOCAL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `O = {w | w IN IMAGE (SND(c:(A->bool)#(A->real^2))) (FST c) /\
                         chart_inv c w IN FST(c':(A->bool)#(A->real^3))}` THEN
    SUBGOAL_THEN
     `!w. w IN O
          ==> linear(frechet_derivative
                       (\w'. SND(c':(A->bool)#(A->real^3))
                               (chart_inv (c:(A->bool)#(A->real^2)) w')) (at w))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `O:real^2->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LRG_SMOOTH_VECTORIZE; DIMINDEX_2] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC
     `\w. lift(frechet_derivative
                 (\w'. SND(c':(A->bool)#(A->real^3))
                         (chart_inv (c:(A->bool)#(A->real^2)) w')) (at w) (basis i) dot
               (metric_local atlas c' g (SND c' (chart_inv c w)) **
                frechet_derivative (\w'. SND c' (chart_inv c w')) (at w) (basis j)))` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC LVS_CONGRUENCE_ENTRY THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
    MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
    SUBGOAL_THEN
     `(vectorize:real^3^3->real^(3,3)finite_prod) o
      (\w. metric_local (atlas:((A->bool)#(A->real^3))->bool) c' g
             (SND c' (chart_inv (c:(A->bool)#(A->real^2)) w))) =
      ((vectorize:real^3^3->real^(3,3)finite_prod) o metric_local atlas c' g) o
      (\w. SND c' (chart_inv c w))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (SND(c':(A->bool)#(A->real^3))) (FST c')` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) g` THEN
    REWRITE_TAC[riemannian_metric; metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `c':(A->bool)#(A->real^3)`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "O" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  USE_THEN "cp" (MP_TAC o SPEC `z:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':(A->bool)#(A->real^3)` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `c:(A->bool)#(A->real^2)`; `c':(A->bool)#(A->real^3)`; `z:real^2`]
                LVS_METRIC_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) g` THEN
  REWRITE_TAC[riemannian_metric; metric_field] THEN
  DISCH_THEN(MP_TAC o SPEC `c':(A->bool)#(A->real^3)`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `SND(c':(A->bool)#(A->real^3)) (chart_inv (c:(A->bool)#(A->real^2)) z)`) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `linear(frechet_derivative
             (\w. SND(c':(A->bool)#(A->real^3))
                    (chart_inv (c:(A->bool)#(A->real^2)) w)) (at z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `W:A->bool`; `f:A->real`; `u:real`;
                   `c:(A->bool)#(A->real^2)`; `c':(A->bool)#(A->real^3)`]
                  LVS_CHART_AMBIENT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{w | w IN IMAGE (SND(c:(A->bool)#(A->real^2))) (FST c) /\
                     chart_inv c w IN FST(c':(A->bool)#(A->real^3))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(v:real^2 = vec 0)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC LVS_K_INJECTIVE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `W:A->bool`; `f:A->real`; `u:real`;
                        `c:(A->bool)#(A->real^2)`; `c':(A->bool)#(A->real^3)`;
                        `z:real^2`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Areas.  Compact leaves have an area; comparison of volumes under          *)
(* comparison of metrics in any dimension (MFD_HAS_VOLUME_COMPARE_QF of      *)
(* pc_grg_area is stated for real^3); induced metrics and leaf areas compare *)
(* as the ambient metrics do.                                                *)
(* ------------------------------------------------------------------------- *)

let LVS_HAS_VOLUME_COMPARE_QF = prove
 (`!top atlas (g:A->real^N^N) g' S v v' lam.
     smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ riemannian_metric atlas g' /\ &0 <= lam /\
     mfd_has_volume (top,atlas) g S v /\ mfd_has_volume (top,atlas) g' S v' /\
     (!y w. y IN S ==> w dot (g y ** w) <= lam * (w dot (g' y ** w)))
     ==> v <= sqrt lam pow dimindex(:N) * v'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `\x:A. &1`; `S:A->bool`; `v:real`]
                  MFD_HAS_INTEGRAL_IMP_MEASURABLE) THEN
    ASM_REWRITE_TAC[GSYM mfd_has_volume] THEN SIMP_TAC[mfd_lebesgue_measurable];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g':A->real^N^N`; `g:A->real^N^N`; `S:A->bool`; `v':real`;
                 `v:real`; `sqrt lam pow dimindex(:N)`] MFD_HAS_VOLUME_COMPARE) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE; SQRT_POS_LE]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC GRGA_SQRT_DET_QF_LE THEN ASM_SIMP_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE THEN
  REWRITE_TAC[positive_definite; symmetric_matrix] THEN
  ASM_MESON_TAC[RIEMANNIAN_METRIC_POS]);;

let LVS_METRIC_QF_COMPARE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) g1 g2 W f u x lam v.
     (!w. w dot (g1 x ** w) <= lam * (w dot (g2 x ** w)))
     ==> v dot (lvs_metric top atlas g1 W f u x ** v) <=
         lam * (v dot (lvs_metric top atlas g2 W f u x ** v))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lvs_metric] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_REWRITE_TAC[]);;

let LVS_AREA = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ open_in top W /\ lvs_regular atlas W f u /\
     compact_in top (lvs_set W f u)
     ==> ?a. mfd_has_volume (subtopology top (lvs_set W f u),
                             lvs_atlas top atlas W f u)
                            (lvs_metric top atlas g W f u) (lvs_set W f u) a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_HAS_VOLUME_COMPACT THEN
  ASM_SIMP_TAC[LVS_HAUSDORFF; LVS_MANIFOLD; LVS_RIEMANNIAN;
               COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL]);;

let LVS_AREA_COMPARE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) g1 g2 W f u S a1 a2 lam.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g1 /\
     riemannian_metric atlas g2 /\ open_in top W /\ lvs_regular atlas W f u /\
     &0 <= lam /\
     mfd_has_volume (subtopology top (lvs_set W f u),lvs_atlas top atlas W f u)
                    (lvs_metric top atlas g1 W f u) S a1 /\
     mfd_has_volume (subtopology top (lvs_set W f u),lvs_atlas top atlas W f u)
                    (lvs_metric top atlas g2 W f u) S a2 /\
     (!x w. x IN S ==> w dot (g1 x ** w) <= lam * (w dot (g2 x ** w)))
     ==> a1 <= lam * a2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set W f u):A topology`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u`;
                 `lvs_metric top (atlas:((A->bool)#(A->real^3))->bool) g1 W f u`;
                 `lvs_metric top (atlas:((A->bool)#(A->real^3))->bool) g2 W f u`;
                 `S:A->bool`; `a1:real`; `a2:real`; `lam:real`]
                LVS_HAS_VOLUME_COMPARE_QF) THEN
  ASM_SIMP_TAC[LVS_MANIFOLD; LVS_RIEMANNIAN; DIMINDEX_2; SQRT_POW_2] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LVS_METRIC_QF_COMPARE THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The induced metric at a point is its representative in the preferred      *)
(* adapted chart, and the 3x2 Jacobian lvs_jac is linear and injective at    *)
(* the points of the leaf.                                                   *)
(* ------------------------------------------------------------------------- *)

let LVS_METRIC_AT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u x.
     smooth_manifold_atlas top atlas /\ open_in top W /\ lvs_regular atlas W f u /\
     x IN lvs_set W f u
     ==> metric_local (lvs_atlas top atlas W f u)
                      (chart_at (lvs_atlas top atlas W f u) x)
                      (lvs_metric top atlas g W f u)
                      (SND(chart_at (lvs_atlas top atlas W f u) x) x) =
         lvs_metric top atlas g W f u x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
  EXISTS_TAC `subtopology top (lvs_set W f u):A topology` THEN
  ASM_SIMP_TAC[LVS_MANIFOLD; LVS_TOPSPACE]);;

let LVS_JAC_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u x.
     smooth_manifold_atlas top atlas /\ open_in top W /\ lvs_regular atlas W f u /\
     x IN lvs_set W f u
     ==> linear(lvs_jac top atlas W f u x) /\
         (!v. lvs_jac top atlas W f u x v = vec 0 ==> v = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology top (lvs_set W f u))
                          (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LVS_MANIFOLD]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`W:A->bool`; `f:A->real`; `u:real`] LVS_SET_SUBSET) THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set W f u):A topology`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u`;
                 `x:A`] CHART_AT) THEN
  ASM_SIMP_TAC[LVS_TOPSPACE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set W f u):A topology`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u`;
                 `chart_at (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool)
                                      W f u) x`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[lvs_jac] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `W:A->bool`; `f:A->real`; `u:real`;
                   `chart_at (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool)
                                        W f u) x`;
                   `chart_at (atlas:((A->bool)#(A->real^3))->bool) x`]
                  LVS_CHART_AMBIENT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC
     `{w | w IN IMAGE (SND(chart_at (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool)
                                              W f u) x))
                       (FST(chart_at (lvs_atlas top atlas W f u) x)) /\
           chart_inv (chart_at (lvs_atlas top atlas W f u) x) w IN
           FST(chart_at atlas x)}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; FUN_IN_IMAGE];
    X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC LVS_K_INJECTIVE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `W:A->bool`; `f:A->real`; `u:real`;
      `chart_at (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u) x`;
      `chart_at (atlas:((A->bool)#(A->real^3))->bool) x`;
      `SND(chart_at (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u) x) x`] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

