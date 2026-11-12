(* ========================================================================= *)
(* pc_p2b_tube3: MT Thm 10.2, the bad-tube half, Part II: sphere separation  *)
(* of the limit of the cut tubes, traversal by level spheres, the fit of     *)
(* necks in the tubes, the transfer of necks from the approximants to the    *)
(* limit (P2BT_LIM_NECK).  Part III and the route theorem are in             *)
(* pc_p2b_tube4.                                                             *)
(* ========================================================================= *)

needs "src/pc_p2b_tube2.ml";;
needs "src/pc_lck_swap.ml";;
needs "src/pc_p2b_capfix.ml";;   (* P2BF_NECK_UNIF_RENORM *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* First facts about the limit.  Neck spheres separate in the limit (the     *)
(* approximants' spheres separate; P2B_SEP_EMBED_CORE).                      *)
(* ========================================================================= *)

let P2BT_LIM_SEP = prove
 (`!eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN U z sub
    (top:B topology) atlas g zl W (phi:num->B->A) Vl.
     p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\
     p2bt_lim V U z sub top atlas g zl W phi Vl
     ==> apx_sphere_sep top atlas`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bt_lim] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2B_SEP_EMBED_CORE THEN
  MAP_EVERY EXISTS_TAC
   [`W:num->B->bool`; `phi:num->B->A`;
    `\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`;
    `\k. rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) (&0)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o check (fun th ->
      can (term_match [] `!k:num. open_in (top:B topology) ((W:num->B->bool) k) /\ P k`)
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(top:B topology) closure_of (W:num->B->bool) k` THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET; OPEN_IN_SUBSET];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `k:num` THEN BETA_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o check (fun th ->
      can (term_match [] `!k:num. IMAGE ((phi:num->B->A) k) ((W:num->B->bool) k) SUBSET Y k /\ P k`)
          (concl th))) THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
      REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(MP_TAC o SPEC `(sub:num->num) k`) THEN
      SIMP_TAC[p2bt_one];
      UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
      REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(MP_TAC o SPEC `(sub:num->num) k`) THEN
      SIMP_TAC[p2bt_one];
      EXISTS_TAC `psi:A->B` THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* The profile traverses the necks centred on it.  A constant-speed shortest *)
(* curve on [0,1] through the central sphere of an eps-neck whose ends lie   *)
(* outside the neck meets every level sphere of level in [-a, a], a >= 1/(2  *)
(* eps) (P2BT_TRAVERSE_LEVELS).  The proof is that of P2BT_TRAVERSE of       *)
(* pc_p2b_tube with the level spheres in the conclusion instead of the end   *)
(* slabs: inside the excursion of the curve through the neck the norm of the *)
(* chart is continuous, and its two ends lie beyond the two end levels (no   *)
(* U-turn, by A.6).                                                          *)
(* ========================================================================= *)

let P2BT_TRAVERSE_LEVELS = prove
 (`!u:A->bool.
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !top atlas (g:A->real^3^3) eps x e gamma s a.
              &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
              apx_shortest (top,atlas) g gamma (&0) (&1) /\
              (!t. t IN real_interval[&0,&1]
                   ==> mfd_speed atlas g gamma (&0) (&1) t =
                       mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1))) /\
              &0 <= s /\ s <= &1 /\ gamma s IN IMAGE (e:real^3->A) (sphere(vec 0,&1)) /\
              ~(gamma(&0) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
              ~(gamma(&1) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
              inv(&2 * eps) <= a /\ a < inv eps
              ==> !r. exp(--a / sqrt(&2)) <= r /\ r <= exp(a / sqrt(&2))
                      ==> ?t. &0 <= t /\ t <= &1 /\
                              gamma t IN IMAGE (e:real^3->A) (sphere(vec 0,r))`,
  GEN_TAC THEN REWRITE_TAC[P2B_APX_A6_CS_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e6:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a6"))) THEN
  EXISTS_TAC `min e6 (&1 / &1024)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] P2BT_NECK_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `N = IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                               (gamma:real->A)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
    SIMP_TAC[apx_shortest; mfd_c1_curve];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) s IN N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN UNDISCH_TAC `(gamma:real->A) s IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    UNDISCH_TAC `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `N:A->bool`; `s:real`] P2BT_EXCURSION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
  (* the radii *)
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps /\ &0 < a` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&2 * eps)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `rlo = exp(--inv eps / sqrt(&2))` THEN
  ABBREV_TAC `rhi = exp(inv eps / sqrt(&2))` THEN
  ABBREV_TAC `ra = exp(a / sqrt(&2))` THEN
  ABBREV_TAC `ra' = exp(--a / sqrt(&2))` THEN
  SUBGOAL_THEN `rlo < ra' /\ ra' < &1 /\ &1 < ra /\ ra < rhi /\ &0 < rlo`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rlo"; "rhi"; "ra"; "ra'"] THEN
    REWRITE_TAC[REAL_EXP_POS_LT; GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom eps = annulus rlo rhi` ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the middle region K and its last and first visits *)
  ABBREV_TAC `K = IMAGE (e:real^3->A) {y | ra' <= norm y /\ norm y <= ra}` THEN
  SUBGOAL_THEN `compact_in top (K:A->bool) /\ closed_in top K /\ K SUBSET N` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | ra' <= norm y /\ norm y <= ra} SUBSET rfs_neck_dom eps`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `compact_in top (K:A->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "K" THEN MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `{y:real^3 | ra' <= norm y /\ norm y <= ra} =
                    cball(vec 0,ra) DIFF ball(vec 0,ra')` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN EXPAND_TAC "K" THEN EXPAND_TAC "N" THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) s IN K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    UNDISCH_TAC `(gamma:real->A) s IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!p q. &0 <= p /\ q <= &1
                      ==> real_compact {t | t IN real_interval[p,q] /\
                                            (gamma:real->A) t IN K}`
  (LABEL_TAC "kc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BT_CURVE_PREIMAGE_COMPACT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "kc" (MP_TAC o SPECL [`s:real`; `d:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPEC `{t | t IN real_interval[s,d] /\ (gamma:real->A) t IN K}`
    REAL_COMPACT_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "mmax"))) THEN
  USE_THEN "kc" (MP_TAC o SPECL [`c:real`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPEC `{t | t IN real_interval[c,s] /\ (gamma:real->A) t IN K}`
    REAL_COMPACT_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "mmin"))) THEN
  SUBGOAL_THEN `m < d /\ c < m'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      MAP_EVERY UNDISCH_TAC [`(K:A->bool) SUBSET N`; `~((gamma:real->A) d IN N)`;
                             `(gamma:real->A) d IN K`] THEN SET_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      MAP_EVERY UNDISCH_TAC [`(K:A->bool) SUBSET N`; `~((gamma:real->A) m' IN N)`;
                             `(gamma:real->A) m' IN K`] THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `c2 = (c + m') / &2` THEN ABBREV_TAC `d2 = (m + d) / &2` THEN
  SUBGOAL_THEN `c < c2 /\ c2 < m' /\ m < d2 /\ d2 < d /\ c2 < s /\ s < d2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c2"; "d2"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* points of the excursion in chart coordinates *)
  SUBGOAL_THEN `!t. c < t /\ t < d
                    ==> (e':A->real^3) ((gamma:real->A) t) IN annulus rlo rhi /\
                        e(e'(gamma t)) = gamma t`
  (LABEL_TAC "chart") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gamma:real->A) t IN N` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (e':A->real^3) N = rfs_neck_dom eps` THEN
    UNDISCH_TAC `!y. y IN N ==> (e:real^3->A)((e':A->real^3) y) = y` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(gamma:real->A) t IN N` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. c < t /\ t < d /\ ~((gamma:real->A) t IN K)
        ==> norm((e':A->real^3) (gamma t)) < ra' \/ ra < norm(e'(gamma t))`
  (LABEL_TAC "off") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "chart" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `~((gamma:real->A) t IN K)` THEN EXPAND_TAC "K" THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `(e':A->real^3) ((gamma:real->A) t)`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((gamma:real->A) c2 IN K) /\ ~((gamma:real->A) d2 IN K)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "mmin" (MP_TAC o SPEC `c2:real`); USE_THEN "mmax" (MP_TAC o SPEC `d2:real`)] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  (* the U-turn is impossible *)
  SUBGOAL_THEN `inv(&100 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) <
                mfd_length atlas g gamma c2 d2 /\
                &0 < mfd_dist (top,atlas) g ((gamma:real->A)(&0)) (gamma(&1))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?w:real^3. w IN sphere(vec 0,&1) /\ (gamma:real->A) s = (e:real^3->A) w`
    (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THENL
     [UNDISCH_TAC `(gamma:real->A) s IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "chart" (MP_TAC o SPEC `d2:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ABBREV_TAC `yd = (e':A->real^3) ((gamma:real->A) d2)` THEN
    SUBGOAL_THEN `(yd:real^3) IN rfs_neck_dom eps /\ (w:real^3) IN rfs_neck_dom eps /\
                  apx_sval w = &0`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN SET_TAC[];
        UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN
        SIMP_TAC[IN_SPHERE_0; apx_sval; LOG_1; REAL_MUL_RZERO]];
      ALL_TAC] THEN
    SUBGOAL_THEN `a < abs(apx_sval yd) /\ abs(apx_sval yd) < inv eps` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `yd:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
      ASM_SIMP_TAC[P2BT_SVAL_NORM] THEN
      USE_THEN "off" (MP_TAC o SPEC `d2:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
                      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `w:real^3`; `yd:real^3`]
      APX_NECK_DIST_LOWER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG; REAL_ABS_0; REAL_SUB_RZERO] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `(gamma:real->A) s`)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `s:real`; `d2:real`] P2BT_CS_SUB) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `c2:real`; `d2:real`] P2BT_CS_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) ((gamma:real->A) s) (gamma d2) =
                  mfd_length atlas g gamma s d2`
    ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN
      UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
      REWRITE_TAC[apx_shortest] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^3^3) ((gamma:real->A)(&0)) (gamma(&1))` THEN
    ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
    SUBGOAL_THEN `&0 < h /\ &1 / &2 <= sqrt(&1 - eps) /\ &0 <= L` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
        UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
        MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "L" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN
        UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
        SIMP_TAC[apx_shortest]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `mn = min (abs(apx_sval(yd:real^3))) (&2 * inv eps - abs(apx_sval yd))` THEN
    SUBGOAL_THEN `a <= mn` ASSUME_TAC THENL [EXPAND_TAC "mn" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&1 / &2 * h * a <= (d2 - s) * L` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1 - eps) * h * mn` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_ARITH `&0 <= &1 / &2`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `(d2 - s) * L <= (d2 - c2) * L /\ h * inv(&2 * eps) <= h * a`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&100 * eps) * h < &1 / &2 * h * inv(&2 * eps)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN
      SUBGOAL_THEN `&0 < h * inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < h * a` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (d2 - s) * L` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r t1 t2. sphere(vec 0,r) SUBSET rfs_neck_dom eps /\
              c2 <= t1 /\ t1 < s /\ s < t2 /\ t2 <= d2 /\
              (gamma:real->A) t1 IN IMAGE (e:real^3->A) (sphere(vec 0,r)) /\
              gamma t2 IN IMAGE (e:real^3->A) (sphere(vec 0,r))
              ==> F`
  (LABEL_TAC "uturn") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `c2:real`; `d2:real`] P2BT_CS_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "a6" (MP_TAC o SPECL
      [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
       `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`; `c2:real`; `d2:real`; `r:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(gamma:real->A) t IN N` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; EXPAND_TAC "N" THEN SIMP_TAC[]]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`t1:real`; `t2:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `t1:real`; `t2:real`] P2BT_CS_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_length atlas (g:A->real^3^3) gamma t1 t2 = &0` MP_TAC THENL
     [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
      REWRITE_TAC[apx_shortest] THEN
      DISCH_THEN(MP_TAC o SPECL [`t1:real`; `t2:real`] o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `(gamma:real->A) t1`)) THEN
      MATCH_MP_TAC MFD_DIST_REFL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(N:A->bool) SUBSET topspace top` THEN EXPAND_TAC "N" THEN
      UNDISCH_TAC `sphere(vec 0,r) SUBSET rfs_neck_dom eps` THEN
      UNDISCH_TAC `(gamma:real->A) t1 IN IMAGE (e:real^3->A) (sphere(vec 0,r))` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (t2 - t1) * mfd_dist (top,atlas) (g:A->real^3^3) ((gamma:real->A)(&0)) (gamma(&1))`
    MP_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the level function along the excursion *)
  SUBGOAL_THEN `(\t. norm((e':A->real^3) ((gamma:real->A) t))) real_continuous_on
                real_interval[c2,d2]`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM GRGD_CONTINUOUS_MAP_REAL] THEN
    SUBGOAL_THEN `(\t. norm((e':A->real^3) ((gamma:real->A) t))) = norm o e' o gamma`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
    REWRITE_TAC[P2BT_NORM_CONTINUOUS] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `subtopology top (N:A->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_INTO_SUBTOPOLOGY THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
        EXISTS_TAC `real_interval[&0,&1]` THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE;
                    IN_REAL_INTERVAL] THEN
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      UNDISCH_TAC `continuous_map (subtopology top (N:A->bool),euclidean) (e':A->real^3)` THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((e':A->real^3) ((gamma:real->A) s)) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(gamma:real->A) s IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(e':A->real^3) ((e:real^3->A) w) = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. c2 <= t /\ t <= d2 /\ norm((e':A->real^3) ((gamma:real->A) t)) = ra
                    ==> gamma t IN IMAGE (e:real^3->A) (sphere(vec 0,ra))` (LABEL_TAC "onra") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "chart" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
    EXISTS_TAC `(e':A->real^3) ((gamma:real->A) t)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. c2 <= t /\ t <= d2 /\ norm((e':A->real^3) ((gamma:real->A) t)) = ra'
                    ==> gamma t IN IMAGE (e:real^3->A) (sphere(vec 0,ra'))` (LABEL_TAC "onra'") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "chart" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
    EXISTS_TAC `(e':A->real^3) ((gamma:real->A) t)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0,ra) SUBSET rfs_neck_dom eps /\
                sphere(vec 0,ra') SUBSET rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
    CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. c2 <= t /\ t <= d2 /\ norm((e':A->real^3) ((gamma:real->A) t)) = r
                    ==> gamma t IN IMAGE (e:real^3->A) (sphere(vec 0,r))` (LABEL_TAC "onr") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "chart" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
    EXISTS_TAC `(e':A->real^3) ((gamma:real->A) t)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "off" (MP_TAC o SPEC `c2:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "off" (MP_TAC o SPEC `d2:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `rc = norm((e':A->real^3) ((gamma:real->A) c2))` THEN
  ABBREV_TAC `rd = norm((e':A->real^3) ((gamma:real->A) d2))` THEN
  ABBREV_TAC `rho = \t. norm((e':A->real^3) ((gamma:real->A) t))` THEN
  SUBGOAL_THEN `rho real_continuous_on real_interval[c2,s] /\
                rho real_continuous_on real_interval[s,d2]` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[c2,d2]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(rho:real->real) c2 = rc /\ rho d2 = rd /\ rho s = &1 /\
                (!t. rho t = norm((e':A->real^3) ((gamma:real->A) t)))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "rho" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[c2,d2] /\ (rho:real->real) t = r
        ==> ?t. &0 <= t /\ t <= &1 /\ (gamma:real->A) t IN IMAGE (e:real^3->A) (sphere(vec 0,r))`
  (LABEL_TAC "hit") THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    EXISTS_TAC `t:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "onr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(rho:real->real) t = r` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_interval[c2,s] SUBSET real_interval[c2,d2] /\
                real_interval[s,d2] SUBSET real_interval[c2,d2]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [(* rd < ra' and rc < ra': U-turn at ra' *)
    MP_TAC(SPECL [`rho:real->real`; `c2:real`; `s:real`; `ra':real`] REAL_IVT_INCREASING) THEN
    MP_TAC(SPECL [`rho:real->real`; `s:real`; `d2:real`; `ra':real`] REAL_IVT_DECREASING) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC)] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `~(t1:real = s) /\ ~(t2:real = s)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "uturn" (MP_TAC o SPECL [`ra':real`; `t1:real`; `t2:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      USE_THEN "onra'" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[]];
    (* rd < ra', rc > ra: decreasing traversal *)
    ASM_CASES_TAC `r <= &1` THENL
     [MP_TAC(SPECL [`rho:real->real`; `s:real`; `d2:real`; `r:real`] REAL_IVT_DECREASING) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      USE_THEN "hit" MATCH_MP_TAC THEN EXISTS_TAC `t:real` THEN ASM SET_TAC[];
      MP_TAC(SPECL [`rho:real->real`; `c2:real`; `s:real`; `r:real`] REAL_IVT_DECREASING) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      USE_THEN "hit" MATCH_MP_TAC THEN EXISTS_TAC `t:real` THEN ASM SET_TAC[]];
    (* rd > ra, rc < ra': increasing traversal *)
    ASM_CASES_TAC `r <= &1` THENL
     [MP_TAC(SPECL [`rho:real->real`; `c2:real`; `s:real`; `r:real`] REAL_IVT_INCREASING) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      USE_THEN "hit" MATCH_MP_TAC THEN EXISTS_TAC `t:real` THEN ASM SET_TAC[];
      MP_TAC(SPECL [`rho:real->real`; `s:real`; `d2:real`; `r:real`] REAL_IVT_INCREASING) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      USE_THEN "hit" MATCH_MP_TAC THEN EXISTS_TAC `t:real` THEN ASM SET_TAC[]];
    (* both > ra: U-turn at ra *)
    MP_TAC(SPECL [`rho:real->real`; `c2:real`; `s:real`; `ra:real`] REAL_IVT_DECREASING) THEN
    MP_TAC(SPECL [`rho:real->real`; `s:real`; `d2:real`; `ra:real`] REAL_IVT_INCREASING) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC)] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `~(t1:real = s) /\ ~(t2:real = s)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "uturn" (MP_TAC o SPECL [`ra:real`; `t1:real`; `t2:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      USE_THEN "onra" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* Points of the window necks near the profile.  A point of the window neck  *)
(* EN s at level |s(y)| <= 19/(20 eps) lies within 101/100 h sqrt(2) pi of   *)
(* the profile point at the same level, which lies within 101/100 h (|s(y)|  *)
(* + sqrt(2) pi) of gamma(s) (traversal).                                    *)
(* ========================================================================= *)

let P2BT_WINDOW_ENDS_OUT = prove
 (`?eps0. &0 < eps0 /\
     !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN s.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\ p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
        s0 <= s /\ s <= s1
        ==> ~(gamma(&0) IN IMAGE (EN s) (rfs_neck_dom eps)) /\
            ~(gamma(&1) IN IMAGE (EN s) (rfs_neck_dom eps))`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nr"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_R) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
    `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:real`; `Q:real`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_TUBE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  UNDISCH_TAC `p2bt_one eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
  REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  ABBREV_TAC `R = mfd_scalar (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)) (rfs_vmetric V (&0))` THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (CONJ (ASSUME `s0 <= s:real`) (ASSUME `s:real <= s1`)) o
    check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&2 * C`)) (concl th) &&
      can (find_term ((=) `&32 * C pow 2`)) (concl th))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < C pow 2 /\ C < C pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(R:A->real) ((gamma:real->A) s) * (&2 * C) <= R (gamma(&1)) /\
                R (gamma s) * &1 < R (gamma s) * C`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < &2 * C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ];
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THEN (REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "nr" (MP_TAC o SPECL
    [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`; `eps:real`; `(gamma:real->A) s`;
     `(EN:real->real^3->A) s`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    (lhand(concl th) = `(gamma:real->A)(&0)` || lhand(concl th) = `(gamma:real->A)(&1)`))) THEN
  ASM_REAL_ARITH_TAC));;

let P2BT_WINDOW_LEVEL_POINT = prove
 (`!u:A->bool.
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN s y.
              &0 < eps /\ eps <= eps0 /\ &1 < C /\
              p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
              s0 <= s /\ s <= s1 /\ y IN rfs_neck_dom eps /\
              abs(apx_sval y) <= &19 / &20 * inv eps
              ==> ?t'. &0 <= t' /\ t' <= &1 /\
                       mfd_joinable (rfs_vtop V (&0),rfs_vatlas V (&0)) (EN s y) (gamma t') /\
                       mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (EN s y) (gamma t') <=
                       &101 / &100 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s))) * (sqrt(&2) * pi) /\
                       abs(t' - s) *
                       mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&0)) (gamma(&1)) <=
                       &101 / &100 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s))) *
                       (abs(apx_sval y) + sqrt(&2) * pi)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr")) o
    MATCH_MP P2BT_TRAVERSE_LEVELS) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "out"))
    (INST_TYPE [`:A`,`:A`] P2BT_WINDOW_ENDS_OUT) THEN
  EXISTS_TAC `min (min e0 e1) (min e2 (&1 / &50))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1 /\ eps <= e2 /\ eps <= &1 / &50` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "out" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
    `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:real`; `Q:real`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
    `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:real`; `Q:real`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_TUBE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_ONE_DIST o CONJ (ASSUME `&1 < C`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dist"))) THEN
  UNDISCH_TAC `p2bt_one eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
  REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  ABBREV_TAC `L = mfd_dist (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0),
                    rfs_vatlas V (&0)) (rfs_vmetric V (&0)) ((gamma:real->A)(&0)) (gamma(&1))` THEN
  ABBREV_TAC `top = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[apx_ch_ctx] THEN STRIP_TAC THEN
  UNDISCH_TAC `(gamma:real->A) s IN IMAGE ((EN:real->real^3->A) s) (sphere(vec 0,&1))` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps /\ apx_sval y0 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab; annulus; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MP_TAC(SPEC `--inv eps / sqrt(&2)` REAL_EXP_POS_LT) THEN
    REWRITE_TAC[GSYM NORM_POS_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "tr" (MP_TAC o SPECL
    [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
     `eps:real`; `(gamma:real->A) s`; `(EN:real->real^3->A) s`; `gamma:real->A`; `s:real`;
     `&19 / &20 * inv eps`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_MUL] THEN
      SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `norm(y:real^3)`) THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`y:real^3`; `&19 / &20 * inv eps`] P2BN_SVAL_NORM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `--(&19 / &20 * inv eps) / sqrt(&2) = --(&19 / &20 * inv eps) / sqrt(&2)`
    (K ALL_TAC) THENL [REFL_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t':real` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(gamma:real->A) t' IN IMAGE ((EN:real->real^3->A) s) (sphere(vec 0,norm(y:real^3)))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y2:real^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y2:real^3) IN rfs_neck_dom eps /\ apx_sval y2 = apx_sval y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN
      REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab; annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval]];
    ALL_TAC] THEN
  UNDISCH_TAC `apx_eng_n2 top atlas (g:A->real^3^3) eps (&1 / &100)` THEN
  REWRITE_TAC[apx_eng_n2] THEN DISCH_THEN(fun th ->
    MP_TAC(SPECL [`(gamma:real->A) s`; `(EN:real->real^3->A) s`; `y:real^3`; `y2:real^3`] th) THEN
    MP_TAC(SPECL [`(gamma:real->A) s`; `(EN:real->real^3->A) s`; `y0:real^3`; `y2:real^3`] th)) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID; REAL_SUB_LZERO; REAL_ABS_NEG] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `(&1 + &1 / &100) = &101 / &100`] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `s <= t' \/ t' < s`) THENL
   [USE_THEN "dist" (MP_TAC o SPECL [`s:real`; `t':real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs(t' - s) = t' - s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    USE_THEN "dist" (MP_TAC o SPECL [`t':real`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs(t' - s) = s - t'` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `(gamma:real->A) t'`; `(gamma:real->A) s`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Balls about window profile points are deep in the cut tube.  The ball of  *)
(* radius r + delta about gamma(tau) lies in a closed slab of level (r +     *)
(* delta)/h' of the window neck EN tau, inside its middle half               *)
(* (P2BN_BALL_LEVELS), and within A1 of the window start; so every point of  *)
(* B(gamma tau, r) is delta-deep in U.                                       *)
(* ========================================================================= *)

let P2BT_CLOSURE_BALL_CBALL = prove
 (`!top atlas (g:A->real^N^N) x r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
     ==> top closure_of mfd_ball (top,atlas) g x r SUBSET mfd_cball (top,atlas) g x r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
  ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
  REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]);;

let P2BT_PROFILE_BALL_DEEP = prove
 (`?eps0. &0 < eps0 /\
     !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1 tau r delta q.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\ p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
        s0 <= tau /\ tau <= s1 /\ &0 < r /\ &0 < delta /\
        (r + delta) / (&99 / &100 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma tau)))) < inv(&2 * eps) /\
        (tau - s0) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&0)) (gamma(&1)) +
        r + delta < A1 /\
        q IN mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma tau) r
        ==> q IN p2bt_cutset eps V gamma EN s0 s1 A1 /\
            p2b_lc_deep V (p2bt_cutset eps V gamma EN s0 s1 A1) q delta`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  EXISTS_TAC `min e0 (&1 / &4)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= &1 / &4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
    `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:real`; `Q:real`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_TUBE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `tau:real` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_ONE_DIST o CONJ (ASSUME `&1 < C`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dist"))) THEN
  UNDISCH_TAC `p2bt_one eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
  REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  ABBREV_TAC `L = mfd_dist (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0),
                    rfs_vatlas V (&0)) (rfs_vmetric V (&0)) ((gamma:real->A)(&0)) (gamma(&1))` THEN
  ABBREV_TAC `top = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[apx_ch_ctx] THEN STRIP_TAC THEN
  UNDISCH_TAC `(gamma:real->A) tau IN IMAGE ((EN:real->real^3->A) tau) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps /\ apx_sval y0 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  ABBREV_TAC `Lam = (r + delta) / (&99 / &100 * inv(sqrt(mfd_scalar atlas (g:A->real^3^3)
                                                      ((gamma:real->A) tau))))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(gamma:real->A) tau`; `(EN:real->real^3->A) tau`; `y0:real^3`;
                 `&0`; `r + delta`] P2BN_BALL_LEVELS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_0; REAL_LE_REFL; REAL_ADD_LID] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&2 * eps)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ADD_LID] THEN STRIP_TAC THEN
  (* the slab lies in the tube *)
  SUBGOAL_THEN
   `IMAGE ((EN:real->real^3->A) tau) {z | ~(z = vec 0) /\ abs(apx_sval z) <= Lam} SUBSET
    p2bt_tube eps EN s0 s1`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2bt_tube; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN EXISTS_TAC `tau:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the closed ball of radius r + delta lies within A1 of the start *)
  SUBGOAL_THEN
   `!p. p IN mfd_cball (top,atlas) (g:A->real^3^3) ((gamma:real->A) tau) (r + delta)
        ==> p IN mfd_ball (top,atlas) g (gamma s0) A1`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:A` THEN REWRITE_TAC[mfd_cball; mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "dist" (MP_TAC o SPECL [`s0:real`; `tau:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A) tau` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `(gamma:real->A) s0`; `(gamma:real->A) tau`; `p:A`] MFD_DIST_TRIANGLE) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `top closure_of mfd_ball (top,atlas) (g:A->real^3^3) q delta SUBSET
    top closure_of mfd_ball (top,atlas) g ((gamma:real->A) tau) (r + delta)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MONO THEN
    UNDISCH_TAC `(q:A) IN mfd_ball (top,atlas) (g:A->real^3^3) ((gamma:real->A) tau) r` THEN
    REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
    X_GEN_TAC `p:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `q:A` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `(gamma:real->A) tau`; `q:A`; `p:A`] MFD_DIST_TRIANGLE) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(gamma:real->A) tau`; `r + delta`] P2BT_CLOSURE_BALL_CBALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `top closure_of mfd_ball (top,atlas) (g:A->real^3^3) q delta SUBSET
    p2bt_cutset eps (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma EN s0 s1 A1`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2bt_cutset; SUBSET_INTER] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^3^3) ((gamma:real->A) tau) (r + delta)` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[SUBSET]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:A) IN top closure_of mfd_ball (top,atlas) (g:A->real^3^3) q delta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!a b (x:A). x IN a /\ a SUBSET b ==> x IN b`) THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^3^3) q delta` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
      UNDISCH_TAC `(q:A) IN mfd_ball (top,atlas) (g:A->real^3^3) ((gamma:real->A) tau) r` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN
      ASM_SIMP_TAC[MFD_BALL_OPEN]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2b_lc_deep; P2BT_VBALL_ALT] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `top closure_of mfd_ball (top,atlas) (g:A->real^3^3) ((gamma:real->A) tau)
                (r + delta)` THEN
  ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF]);;

(* ========================================================================= *)
(* Scales on a neck agree within 2 per cent (APX_NECK_CURV with alpha =      *)
(* 1/100: R(e y) is within 1 per cent of R(x)).                              *)
(* ========================================================================= *)

let P2BT_NECK_H = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) eps x e y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> &99 / &100 * mfd_scalar atlas g x <= mfd_scalar atlas g (e y) /\
            mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x /\
            inv(sqrt(mfd_scalar atlas g (e y))) <= &51 / &50 * inv(sqrt(mfd_scalar atlas g x)) /\
            inv(sqrt(mfd_scalar atlas g x)) <= &51 / &50 * inv(sqrt(mfd_scalar atlas g (e y)))`,
  MP_TAC(SPEC `&1 / &100`
    (REWRITE_RULE[APX_NECK_CURV_STATEMENT] (ISPEC `UNIV:A->bool` APX_NECK_CURV))) THEN
  REWRITE_TAC[REAL_ARITH `&0 < &1 / &100`] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nc"))) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "nc" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                 `mfd_scalar atlas (g:A->real^3^3) x`; `y:real^3`] LSCALAR_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`]
                APX_PULLBACK_SCALAR_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])) THEN
  SUBGOAL_THEN `&99 / &100 * mfd_scalar atlas (g:A->real^3^3) x <= mfd_scalar atlas g ((e:real^3->A) y) /\
                mfd_scalar atlas g (e y) <= &101 / &100 * mfd_scalar atlas g x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `abs(mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) y) /
                     mfd_scalar atlas g x - &1) <= &1 / &100` THEN
    UNDISCH_TAC `&0 < mfd_scalar atlas (g:A->real^3^3) x` THEN
    SPEC_TAC(`mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) y)`,`a:real`) THEN
    SPEC_TAC(`mfd_scalar atlas (g:A->real^3^3) x`,`b:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `a / b - &1 = (a - b) / b` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    UNDISCH_TAC `abs((a - b) / b) <= &1 / &100` THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < b ==> abs b = b`; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC P2BT_INV_SQRT_LE THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC REAL_RAT_REDUCE_CONV) THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Necks at tube points fit in the tube.  A point q within 3/5 h_w / eps of  *)
(* a point w = EN sig y of the middle half of a window neck lies within 11/2 *)
(* h of a profile point gamma(tau'), |tau' - sig| L <= 6/5 h / eps (h =      *)
(* R(gamma sig)^(-1/2)): w is near the profile point at its level in EN sig, *)
(* and q near the profile point at its level in the window neck of that      *)
(* point (P2BT_WINDOW_LEVEL_POINT twice).                                    *)
(* ========================================================================= *)

let P2BT_NECK_FIT_ONE = prove
 (`!u:A->bool.
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN sig y q.
              &0 < eps /\ eps <= eps0 /\ &1 < C /\
              p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
              s0 <= sig /\ sig <= s1 /\ y IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) /\
              &6 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig))) * inv eps <=
              (sig - s0) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&0)) (gamma(&1)) /\
              (!s'. sig <= s' /\
                    (s' - sig) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&0)) (gamma(&1)) <=
                    &6 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig))) * inv eps
                    ==> s' <= s1) /\
              mfd_joinable (rfs_vtop V (&0),rfs_vatlas V (&0)) (EN sig y) q /\
              mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (EN sig y) q <
              &3 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (EN sig y))) * inv eps
              ==> ?tau'. s0 <= tau' /\ tau' <= s1 /\
                         abs(tau' - sig) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&0)) (gamma(&1)) <=
                         &6 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig))) * inv eps /\
                         mfd_joinable (rfs_vtop V (&0),rfs_vatlas V (&0)) (gamma tau') q /\
                         mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma tau') q <
                         &11 / &2 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig))) /\
                         inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma tau'))) <=
                         &27 / &25 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig))) /\
                         inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig))) <=
                         &27 / &25 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma tau')))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wlp")) o
    MATCH_MP P2BT_WINDOW_LEVEL_POINT) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_H) THEN
  EXISTS_TAC `min (min e0 e1) (min e2 (&1 / &1000))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1 /\ eps <= e2 /\ eps <= &1 / &1000` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
     `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:real`; `Q:real`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_TUBE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "nk" o CONJUNCT1 o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_ONE_DIST o CONJ (ASSUME `&1 < C`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dist"))) THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps /\ abs(apx_sval y) < inv(&2 * eps)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2BT_MIDDLE_IN_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ASM SET_TAC[];
      UNDISCH_TAC `(y:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1000 <= inv eps /\ inv(&2 * eps) = inv eps / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &1000`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
      REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC P2BT_SQRT2_PI THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt(&2) * pi` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE]; ALL_TAC] THEN
  (* the first level point *)
  USE_THEN "wlp" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
     `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:real`; `Q:real`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `sig:real`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "nk" (MP_TAC o C MATCH_MP (CONJ (ASSUME `s0 <= sig:real`) (ASSUME `sig:real <= s1`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    (let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "p2bt_one"))) THEN
  REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  ABBREV_TAC `L = mfd_dist (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0),
                    rfs_vatlas V (&0)) (rfs_vmetric V (&0)) ((gamma:real->A)(&0)) (gamma(&1))` THEN
  ABBREV_TAC `top = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3)` THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[apx_ch_ctx] THEN STRIP_TAC THEN
  ABBREV_TAC `h = inv(sqrt((R:A->real) ((gamma:real->A) sig)))` THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS o check (fun th ->
      is_comb(concl th) && (let c,_ = strip_comb(concl th) in
        is_const c && fst(dest_const c) = "rfs_neck") &&
      can (find_term ((=) `(gamma:real->A) sig`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* bounds for tau *)
  SUBGOAL_THEN `abs(tau - sig) * L <= &51 / &100 * h * inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&101 / &100 * h * (abs(apx_sval(y:real^3)) + sqrt(&2) * pi)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `h * (abs(apx_sval(y:real^3)) + sqrt(&2) * pi) <= h * (inv eps / &2 + &24 / &5)`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `h * &1000 <= h * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ASSUME `&0 < h`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s0 <= tau /\ tau <= s1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(sig - s0) * L <= abs(tau - sig) * L` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < h * inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_CASES_TAC `tau <= sig` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `s1:real`)) (concl th) &&
        can (find_term ((=) `&6 / &5`)) (concl th))) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `abs(tau - sig) = tau - sig` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < h * inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* symmetric distances along the profile *)
  SUBGOAL_THEN
   `!a b. &0 <= a /\ a <= &1 /\ &0 <= b /\ b <= &1
          ==> mfd_joinable (top,atlas) ((gamma:real->A) a) (gamma b) /\
              mfd_dist (top,atlas) (g:A->real^3^3) (gamma a) (gamma b) = abs(b - a) * L`
  (LABEL_TAC "dist2") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH `a <= b \/ b < a`) THENL
     [USE_THEN "dist" (MP_TAC o SPECL [`a:real`; `b:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `abs(b - a) = b - a` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "dist" (MP_TAC o SPECL [`b:real`; `a:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `abs(b - a) = a - b` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `(gamma:real->A) b`; `(gamma:real->A) a`] MFD_JOINABLE_SYM) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
        ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `(gamma:real->A) a`; `(gamma:real->A) b`]
                      MFD_DIST_SYM) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* the centre of EN sig *)
  UNDISCH_TAC `(gamma:real->A) sig IN IMAGE ((EN:real->real^3->A) sig) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps /\ apx_sval y0 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  (* gamma tau lies in EN sig: scales *)
  USE_THEN "dist2" (MP_TAC o SPECL [`sig:real`; `tau:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(gamma:real->A) sig`; `(EN:real->real^3->A) sig`; `y0:real^3`;
                 `(gamma:real->A) tau`] APX_NECK_EXIT_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `&0 < h * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `inv(sqrt((R:A->real) ((gamma:real->A) sig))) = h` THEN
    UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) = R` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `yt:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  ABBREV_TAC `hT = inv(sqrt((R:A->real) ((gamma:real->A) tau)))` THEN
  ABBREV_TAC `hw = inv(sqrt((R:A->real) ((EN:real->real^3->A) sig y)))` THEN
  SUBGOAL_THEN `hT <= &51 / &50 * h /\ h <= &51 / &50 * hT /\ hw <= &51 / &50 * h`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "nh" (fun th ->
      MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                    `eps:real`; `(gamma:real->A) sig`; `(EN:real->real^3->A) sig`; `yt:real^3`] th) THEN
      MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                    `eps:real`; `(gamma:real->A) sig`; `(EN:real->real^3->A) sig`; `y:real^3`] th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `(EN:real->real^3->A) sig yt = (gamma:real->A) tau` THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `mfd_scalar atlas (g:A->real^3^3) = R`]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < hT` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h * (sqrt(&2) * pi) <= h * (&24 / &5) /\ hT * (sqrt(&2) * pi) <= hT * (&24 / &5) /\
                h * &1000 <= h * inv eps /\ hT * &1000 <= hT * inv eps /\
                hw * inv eps <= (&51 / &50 * h) * inv eps /\
                h * inv eps <= (&51 / &50 * hT) * inv eps /\
                hT * inv eps <= (&51 / &50 * h) * inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* step 7: q is near gamma tau *)
  SUBGOAL_THEN `mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                ((gamma:real->A) tau) ((EN:real->real^3->A) sig y)`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas) ((gamma:real->A) tau) q /\
                mfd_dist (top,atlas) (g:A->real^3^3) (gamma tau) q < &633 / &1000 * hT * inv eps`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(EN:real->real^3->A) sig y` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `(gamma:real->A) tau`; `(EN:real->real^3->A) sig y`; `q:A`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `(gamma:real->A) tau`; `(EN:real->real^3->A) sig y`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* step 8: q lies in EN tau at level at most 633/990 / eps *)
  USE_THEN "nk" (MP_TAC o C MATCH_MP (CONJ (ASSUME `s0 <= tau:real`) (ASSUME `tau:real <= s1`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0T:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0T:real^3) IN rfs_neck_dom eps /\ apx_sval y0T = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&633 / &1000 * hT * inv eps) / (&99 / &100 * hT) = &633 / &990 * inv eps`
  ASSUME_TAC THENL [UNDISCH_TAC `&0 < hT` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(gamma:real->A) tau`; `(EN:real->real^3->A) tau`; `y0T:real^3`;
                 `&0`; `&633 / &1000 * hT * inv eps`] P2BN_BALL_LEVELS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_0; REAL_LE_REFL; REAL_ADD_LID] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ADD_LID] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[SUBSET] THEN
  DISCH_THEN(MP_TAC o SPEC `q:A`) THEN
  ANTS_TAC THENL [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `yq:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(yq:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `&633 / &990 * inv eps` P2BN_CLOSED_SLAB) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `eps:real` o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* step 9: the profile point at the level of q in EN tau *)
  USE_THEN "wlp" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
     `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:real`; `Q:real`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `tau:real`; `yq:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau':real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `abs(tau' - tau) * L <= &66 / &100 * hT * inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&101 / &100 * hT * (abs(apx_sval(yq:real^3)) + sqrt(&2) * pi)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `hT * (abs(apx_sval(yq:real^3)) + sqrt(&2) * pi) <=
                  hT * (&633 / &990 * inv eps + &24 / &5)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ASSUME `hT * &1000 <= hT * inv eps`) THEN MP_TAC(ASSUME `&0 < hT`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(tau' - sig) * L <= &119 / &100 * h * inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(tau' - tau) * L + abs(tau - sig) * L` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s0 <= tau' /\ tau' <= s1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(sig - s0) * L <= abs(tau' - sig) * L` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < h * inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ASSUME `&6 / &5 * h * inv eps <= (sig - s0) * L`) THEN
      MP_TAC(ASSUME `abs(tau' - sig) * L <= &119 / &100 * h * inv eps`) THEN
      REAL_ARITH_TAC;
      ASM_CASES_TAC `tau' <= sig` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `s1:real`)) (concl th) &&
        can (find_term ((=) `&6 / &5`)) (concl th))) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `abs(tau' - sig) = tau' - sig` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 < h * inv eps` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  (* step 12: the scale at gamma tau' *)
  USE_THEN "dist2" (MP_TAC o SPECL [`tau:real`; `tau':real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(gamma:real->A) tau`; `(EN:real->real^3->A) tau`; `y0T:real^3`;
                 `(gamma:real->A) tau'`] APX_NECK_EXIT_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `&0 < hT * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `yt':real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `inv(sqrt((R:A->real) ((gamma:real->A) tau'))) <= &51 / &50 * hT /\
                hT <= &51 / &50 * inv(sqrt(R(gamma tau')))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "nh" (MP_TAC o SPECL
      [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
       `eps:real`; `(gamma:real->A) tau`; `(EN:real->real^3->A) tau`; `yt':real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(EN:real->real^3->A) tau yt' = (gamma:real->A) tau'` THEN
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `tau':real` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_JOINABLE_SYM];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `(gamma:real->A) tau'`; `q:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Closeness seen from the other side.  If the pullback by phi of g' is      *)
(* C^m-close to g at psi x (in the charts of the B side), then the pullback  *)
(* by psi of g is C^m-close to g' at x (in the charts of the A side), up to  *)
(* the factor M of the reverse base change: lck_dist2 is natural under       *)
(* diffeomorphisms (P2B9S_LCK_NATURAL), g' is the pullback of its own        *)
(* pullback (P2B9S_PB_PB), and the roles of the two bases can be exchanged   *)
(* (LCK_CK_BASE_REV, LCK_DIST2_REFLECT of pc_lck_swap).                      *)
(* ========================================================================= *)

let P2BT_LCK_FLIP = prove
 (`!m. ?M. &0 <= M /\
     !top atlas (g:B->real^3^3) top' atlas' (g':A->real^3^3) W (phi:B->A) psi x d.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
        mfd_diffeo top atlas W top' atlas' (IMAGE phi W) phi psi /\
        x IN IMAGE phi W /\ d <= &1 / &4 /\
        lck_dist2 m (metric_local atlas (chart_at atlas (psi x)) g)
                    (metric_local atlas (chart_at atlas (psi x))
                                  (mfd_pullback_metric atlas atlas' phi g'))
                    (SND(chart_at atlas (psi x)) (psi x)) <= d
        ==> lck_dist2 m (metric_local atlas' (chart_at atlas' x) g')
                        (metric_local atlas' (chart_at atlas' x)
                                      (mfd_pullback_metric atlas' atlas psi g))
                        (SND(chart_at atlas' x) x) <= M * d`,
  GEN_TAC THEN
  X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rev"))
    (INST_TYPE [`:3`,`:N`] (SPEC `m:num` LCK_CK_BASE_REV)) THEN
  EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in top (W:B->bool) /\ open_in top' (IMAGE (phi:B->A) W)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_diffeo top (atlas:((B->bool)#(B->real^3))->bool) (W:B->bool)
                 top' (atlas':((A->bool)#(A->real^3))->bool) (IMAGE (phi:B->A) W) phi psi` THEN
    SIMP_TAC[mfd_diffeo];
    ALL_TAC] THEN
  ABBREV_TAC `y = (psi:A->B) x` THEN
  SUBGOAL_THEN `(y:B) IN W /\ (phi:B->A) y = x` STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `H0 = mfd_pullback_metric atlas atlas' (phi:B->A) (g':A->real^3^3)` THEN
  SUBGOAL_THEN
   `lck_dist2 m (metric_local atlas' (chart_at atlas' x) (g':A->real^3^3))
                (metric_local atlas' (chart_at atlas' x)
                   (mfd_pullback_metric atlas' atlas (psi:A->B) (g:B->real^3^3)))
                (SND(chart_at atlas' x) x) =
    lck_dist2 m (metric_local atlas' (chart_at atlas' x) (mfd_pullback_metric atlas' atlas psi H0))
                (metric_local atlas' (chart_at atlas' x) (mfd_pullback_metric atlas' atlas psi g))
                (SND(chart_at atlas' x) x)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
                   `mfd_pullback_metric atlas' atlas (psi:A->B) (H0:B->real^3^3)`;
                   `IMAGE (phi:B->A) W`; `x:A`] P2B9S_METRIC_LOCAL_EQ_ON) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN EXPAND_TAC "H0" THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2B9S_PB_PB THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `top':A topology`; `W:B->bool`;
                            `IMAGE (phi:B->A) W`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `s:real^3->bool` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)` THEN
  SUBGOAL_THEN `(c:(B->bool)#(B->real^3)) IN atlas /\ (y:B) IN FST c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC CHART_AT THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `top':A topology`;
                 `atlas':((A->bool)#(A->real^3))->bool`; `W:B->bool`; `IMAGE (phi:B->A) W`;
                 `phi:B->A`; `psi:A->B`; `g':A->real^3^3`; `c:(B->bool)#(B->real^3)`; `y:B`]
                P2B9S_PB_FIELD_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `O:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open (IMAGE (SND c) (FST (c:(B->bool)#(B->real^3))))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s = O INTER IMAGE (SND c) (FST (c:(B->bool)#(B->real^3)))` THEN
  SUBGOAL_THEN `open (s:real^3->bool) /\ SND c (y:B) IN s /\
                metric_field s (metric_local atlas c (H0:B->real^3^3)) /\
                metric_field s (metric_local atlas c (g:B->real^3^3))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[OPEN_INTER];
      ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `O:real^3->bool` THEN
      EXPAND_TAC "H0" THEN ASM_SIMP_TAC[OPEN_INTER; INTER_SUBSET];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND c) (FST (c:(B->bool)#(B->real^3)))` THEN
      ASM_SIMP_TAC[OPEN_INTER; INTER_SUBSET] THEN
      UNDISCH_TAC `riemannian_metric (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `IMAGE (phi:B->A) W`; `W:B->bool`;
                 `psi:A->B`; `phi:B->A`; `H0:B->real^3^3`; `g:B->real^3^3`; `m:num`; `x:A`;
                 `s:real^3->bool`] P2B9S_LCK_NATURAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "rev" (MP_TAC o SPECL
    [`s:real^3->bool`; `metric_local atlas c (g:B->real^3^3)`;
     `metric_local atlas c (H0:B->real^3^3)`; `metric_local atlas c (g:B->real^3^3)`;
     `SND (c:(B->bool)#(B->real^3)) (y:B)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `d:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `s:real^3->bool`; `metric_local atlas c (g:B->real^3^3)`;
                 `metric_local atlas c (H0:B->real^3^3)`; `SND (c:(B->bool)#(B->real^3)) (y:B)`] LCK_DIST2_REFLECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `M * lck_dist2 m (metric_local atlas c (g:B->real^3^3))
                              (metric_local atlas c (H0:B->real^3^3)) (SND (c:(B->bool)#(B->real^3)) (y:B))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `d:real`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Necks of the approximants pass to the limit.  An eps1-neck of the A side  *)
(* inside an open U in the image of phi, where the pullback by phi of the A  *)
(* metric is C^m-close to the B metric on psi U, gives an eps2-neck psi o e  *)
(* on the B side (P2BT_LCK_FLIP and P2BF_NECK_UNIF_RENORM of pc_p2b_capfix   *)
(* with R0 = 1).                                                             *)
(* ========================================================================= *)

let P2BT_NECK_TO_LIMIT = prove
 (`!eps1 eps2. &0 < eps1 /\ eps1 < eps2 /\ eps2 < &1 / &4
     ==> ?m eta. &0 < eta /\
           !top atlas (g:B->real^3^3) top' atlas' (g':A->real^3^3) W (phi:B->A) psi U z e.
              smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
              smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
              mfd_diffeo top atlas W top' atlas' (IMAGE phi W) phi psi /\
              open_in top' U /\ U SUBSET IMAGE phi W /\
              rfs_neck (top',atlas') g' eps1 z e /\ IMAGE e (rfs_neck_dom eps1) SUBSET U /\
              &1 <= mfd_scalar atlas' g' z /\
              (!y. y IN IMAGE psi U
                   ==> lck_dist2 m (metric_local atlas (chart_at atlas y) g)
                                   (metric_local atlas (chart_at atlas y)
                                                 (mfd_pullback_metric atlas atlas' phi g'))
                                   (SND(chart_at atlas y) y) < eta)
              ==> rfs_neck (top,atlas) g eps2 (psi z) (psi o e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(INST_TYPE [`:A`,`:A`; `:B`,`:B`]
    (SPECL [`eps1:real`; `eps2:real`; `&1`] P2BF_NECK_UNIF_RENORM)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dn:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nu"))) THEN
  X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fl"))
    (INST_TYPE [`:A`,`:A`; `:B`,`:B`] (SPEC `rfs_kreg dn` P2BT_LCK_FLIP)) THEN
  MAP_EVERY EXISTS_TAC [`rfs_kreg dn`; `min (&1 / &4) (dn pow 2 / (&2 * (M + &1)))`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `eta = min (&1 / &4) (dn pow 2 / (&2 * (M + &1)))` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "nu" (MP_TAC o SPECL
    [`dn:real`; `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
     `U:A->bool`; `z:A`; `e:real^3->A`; `&1`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `psi:A->B`; `phi:B->A`]) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01; REAL_MUL_LID] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (phi:B->A) W`; `W:B->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_mclose; MATRIX_CMUL_LID; ETA_AX] THEN
  EXISTS_TAC `M * eta` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `eta <= dn pow 2 / (&2 * (M + &1))` MP_TAC THENL
     [EXPAND_TAC "eta" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < dn pow 2` MP_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < eta` MP_TAC THENL
     [EXPAND_TAC "eta" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 <= M ==> &0 < &2 * (M + &1)`] THEN
    UNDISCH_TAC `&0 <= M` THEN
    SPEC_TAC(`dn pow 2`,`D:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `M * eta <= (M + &1) * eta` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  USE_THEN "fl" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `top':A topology`; `W:B->bool`; `phi:B->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [EXPAND_TAC "eta" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM SET_TAC[]);;

(* ========================================================================= *)
(* The profile beyond a window point of bounded curvature.  For k large, a   *)
(* window point sigma with R(gamma sigma) <= K at arc length below A1 + 9/10 *)
(* h/eps has R <= 9/4 R(gamma sigma) on the next 17/10 h/eps of the profile  *)
(* (P2BT_PROFILE_NEAR_R twice), which therefore stays inside the window and  *)
(* below A1 - c (P2BT_FAR_END with 9/4 K).                                   *)
(* ========================================================================= *)

let P2BT_WINDOW_FAR = prove
 (`?eps0. &0 < eps0 /\
     !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\
        p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\ p2bt_cut eps C A V gamma s0 s1 A1
        ==> !K. &0 < K
                ==> ?c N. &0 < c /\
                      !k sig. N <= k /\ s0 k <= sig /\ sig <= s1 k /\
                              mfd_scalar (rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0)) (gamma k sig) <= K /\
                              (sig - s0 k) * mfd_dist (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0))
                          (gamma k (&0)) (gamma k (&1)) <
                              A1 + &9 / &10 * inv(sqrt(mfd_scalar (rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0)) (gamma k sig))) * inv eps
                              ==> (sig - s0 k) * mfd_dist (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0))
                          (gamma k (&0)) (gamma k (&1)) +
                                  &17 / &10 * inv(sqrt(mfd_scalar (rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0)) (gamma k sig))) * inv eps
                                  <= A1 - c /\
                                  (!s'. sig <= s' /\
                                        (s' - sig) * mfd_dist (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0))
                          (gamma k (&0)) (gamma k (&1)) <=
                                        &17 / &10 * inv(sqrt(mfd_scalar (rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0)) (gamma k sig))) * inv eps
                                        ==> s' <= s1 k)`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pn"))
    (INST_TYPE [`:A`,`:A`] P2BT_PROFILE_NEAR_R) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fe"))
    (INST_TYPE [`:A`,`:A`] P2BT_FAR_END) THEN
  EXISTS_TAC `min e0 e1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `K:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "fe" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&9 / &4 * K`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far")))) THEN
  MP_TAC(SPEC `&8 * C pow 2 * &9 / &4 * K` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  MAP_EVERY EXISTS_TAC [`c1:real`; `MAX N1 N2`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `sig:real`] THEN
  REWRITE_TAC[ARITH_RULE `MAX N1 N2 <= k <=> N1 <= k /\ N2 <= k`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2bt_one eps C A k ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) ((t:num->real) k)
              ((Q:num->real) k) ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
              ((gamma:num->real->A) k) ((s0:num->real) k) ((s1:num->real) k)
              ((EN:num->real->real^3->A) k)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(ACCEPT_TAC o SPEC `k:num`);
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_ONE_DIST o CONJ (ASSUME `&1 < C`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  ABBREV_TAC `L = mfd_dist (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (&0),rfs_vatlas (V k) (&0))
                   (rfs_vmetric (V k) (&0)) ((gamma:num->real->A) k (&0)) (gamma k (&1))` THEN
  ABBREV_TAC `R = mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (&0)) (rfs_vmetric (V k) (&0))` THEN
  ABBREV_TAC `h = inv(sqrt((R:A->real) ((gamma:num->real->A) k sig)))` THEN
  SUBGOAL_THEN `&0 < (R:A->real) ((gamma:num->real->A) k sig) /\ &0 < h /\
                inv(sqrt K) <= h`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (R:A->real) ((gamma:num->real->A) k sig)` ASSUME_TAC THENL
     [UNDISCH_TAC `p2bt_one eps C A k ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) ((t:num->real) k)
              ((Q:num->real) k) ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
              ((gamma:num->real->A) k) ((s0:num->real) k) ((s1:num->real) k)
              ((EN:num->real->real^3->A) k)` THEN REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN
      p2bt_drop_rescale_eq_tac THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (CONJ (ASSUME `(s0:num->real) k <= sig`)
        (ASSUME `sig <= (s1:num->real) k`)) o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&2 * C`)) (concl th) &&
        can (find_term ((=) `&32 * C pow 2`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < C pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "h" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[SQRT_POS_LT];
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  (* the window end has large curvature *)
  SUBGOAL_THEN `&9 / &4 * K < (R:A->real) ((gamma:num->real->A) k ((s1:num->real) k)) /\
                (s0:num->real) k < s1 k /\ s1 k < &1 /\ &0 < s0 k`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_one eps C A k ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) ((t:num->real) k)
              ((Q:num->real) k) ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
              ((gamma:num->real->A) k) ((s0:num->real) k) ((s1:num->real) k)
              ((EN:num->real->real^3->A) k)` THEN REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN
    p2bt_drop_rescale_eq_tac THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (&0))
                                         (rfs_vmetric (V k) (&0)) = R`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < C pow 2 /\ &0 < &8 * C pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < C pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 * C * (R:A->real) ((gamma:num->real->A) k (&1)) =
                  (&8 * C pow 2) * R (gamma k ((s1:num->real) k))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&1 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&N2 <= &k` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `(&8 * C pow 2) * (&9 / &4 * K) < (&8 * C pow 2) * (R:A->real) ((gamma:num->real->A) k ((s1:num->real) k))`
    MP_TAC THENL
     [MP_TAC(SPEC `C:real` REAL_LE_POW_2) THEN
      SUBGOAL_THEN `&0 <= C pow 4` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ]];
    ALL_TAC] THEN
  (* step 1 *)
  SUBGOAL_THEN
   `!s'. &0 <= s' /\ s' <= &1 /\ abs(s' - sig) * L < &99 / &100 * h * inv eps
         ==> (R:A->real) ((gamma:num->real->A) k s') <= &3 / &2 * R (gamma k sig)`
  (LABEL_TAC "st1") THENL
   [X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    USE_THEN "pn" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`; `k:num`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k`; `(t:num->real) k`; `(Q:num->real) k`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k`; `(gamma:num->real->A) k`;
     `(s0:num->real) k`; `(s1:num->real) k`; `(EN:num->real->real^3->A) k`; `sig:real`; `s':real`;
                                   `(R:A->real) ((gamma:num->real->A) k sig)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `sig2 = sig + (&19 / &20 * h * inv eps) / L` THEN
  SUBGOAL_THEN `(sig2 - sig) * L = &19 / &20 * h * inv eps /\ sig < sig2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sig2" THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> s < s + x`) THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h * inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `sig2 <= (s1:num->real) k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "st1" (MP_TAC o SPEC `(s1:num->real) k`) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `abs((s1:num->real) k - sig) * L <= (sig2 - sig) * L` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(R:A->real) ((gamma:num->real->A) k sig2) <= &3 / &2 * R (gamma k sig)` ASSUME_TAC THENL
   [USE_THEN "st1" MATCH_MP_TAC THEN
    SUBGOAL_THEN `abs(sig2 - sig) = sig2 - sig` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* step 2 *)
  SUBGOAL_THEN `&4 / &5 * h <= inv(sqrt(&3 / &2 * (R:A->real) ((gamma:num->real->A) k sig)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    SUBGOAL_THEN `sqrt(&3 / &2 * (R:A->real) ((gamma:num->real->A) k sig)) =
                  sqrt(&3 / &2) * sqrt(R (gamma k sig))` SUBST1_TAC THENL
     [REWRITE_TAC[SQRT_MUL]; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `inv(&5 / &4) <= inv(sqrt(&3 / &2))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
        CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
      REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s'. sig <= s' /\ s' <= &1 /\ (s' - sig) * L <= &17 / &10 * h * inv eps
         ==> (R:A->real) ((gamma:num->real->A) k s') <= &9 / &4 * R (gamma k sig)`
  (LABEL_TAC "st2") THENL
   [X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(s' - sig) * L < &99 / &100 * h * inv eps` THENL
     [USE_THEN "st1" (MP_TAC o SPEC `s':real`) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `abs(s' - sig) = s' - sig` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "pn" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`; `k:num`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k`; `(t:num->real) k`; `(Q:num->real) k`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k`; `(gamma:num->real->A) k`;
     `(s0:num->real) k`; `(s1:num->real) k`; `(EN:num->real->real^3->A) k`; `sig2:real`; `s':real`;
                                   `&3 / &2 * (R:A->real) ((gamma:num->real->A) k sig)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&99 / &100 * (&4 / &5 * h) * inv eps` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `abs(s' - sig2) * L <= &3 / &4 * h * inv eps` MP_TAC THENL
         [ASM_CASES_TAC `sig2 <= s'` THENL
           [SUBGOAL_THEN `abs(s' - sig2) = s' - sig2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
            UNDISCH_TAC `(sig2 - sig) * L = &19 / &20 * h * inv eps` THEN
            UNDISCH_TAC `(s' - sig) * L <= &17 / &10 * h * inv eps` THEN
            REAL_ARITH_TAC;
            SUBGOAL_THEN `abs(s' - sig2) = sig2 - s'` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
            UNDISCH_TAC `(sig2 - sig) * L = &19 / &20 * h * inv eps` THEN
            UNDISCH_TAC `~((s' - sig) * L < &99 / &100 * h * inv eps)` THEN
            MP_TAC(ASSUME `&0 < h * inv eps`) THEN REAL_ARITH_TAC];
          MP_TAC(ASSUME `&0 < h * inv eps`) THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the window does not end before 17/10 h / eps *)
  SUBGOAL_THEN `!s'. sig <= s' /\ (s' - sig) * L <= &17 / &10 * h * inv eps ==> s' <= (s1:num->real) k`
  ASSUME_TAC THENL
   [X_GEN_TAC `s':real` THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "st2" (MP_TAC o SPEC `(s1:num->real) k`) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `((s1:num->real) k - sig) * L <= (s' - sig) * L` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the window point lies below A1 - c1 *)
  SUBGOAL_THEN `(sig - (s0:num->real) k) * L < A1 - c1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    ASM_CASES_TAC `(sig - (s0:num->real) k) * L <= A1 + c1` THENL
     [USE_THEN "far" (MP_TAC o SPECL [`k:num`; `sig:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `sx = (s0:num->real) k + (A1 + c1) / L` THEN
    SUBGOAL_THEN `(sx - (s0:num->real) k) * L = A1 + c1` ASSUME_TAC THENL
     [EXPAND_TAC "sx" THEN UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= A1` ASSUME_TAC THENL
     [UNDISCH_TAC `p2bt_cut eps C A (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 A1` THEN
      REWRITE_TAC[p2bt_cut] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      SUBGOAL_THEN `&0 <= &4 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
        SIMP_TAC[SQRT_POS_LE; REAL_LE_MUL; REAL_LE_POW_2; REAL_POS] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s0:num->real) k <= sx /\ sx < sig` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "sx" THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> s <= s + x`) THEN MATCH_MP_TAC REAL_LE_DIV THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `x < sig - s ==> s + x < sig`) THEN
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "st1" (MP_TAC o SPEC `sx:real`) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `abs(sx - sig) * L = (sig - (s0:num->real) k) * L - (sx - s0 k) * L`
      SUBST1_TAC THENL
       [SUBGOAL_THEN `abs(sx - sig) = sig - sx` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      DISCH_TAC] THEN
    USE_THEN "far" (MP_TAC o SPECL [`k:num`; `sx:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `sy = (s0:num->real) k + (A1 - c1) / L` THEN
  SUBGOAL_THEN `(sy - (s0:num->real) k) * L = A1 - c1` ASSUME_TAC THENL
   [EXPAND_TAC "sy" THEN UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `sig < sy` ASSUME_TAC THENL
   [EXPAND_TAC "sy" THEN MATCH_MP_TAC(REAL_ARITH `sig - s < x ==> sig < s + x`) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(sy - sig) * L <= &17 / &10 * h * inv eps` ASSUME_TAC THENL
   [SUBGOAL_THEN `(sy - sig) * L = (sy - (s0:num->real) k) * L - (sig - s0 k) * L` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sy <= (s1:num->real) k` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `(s1:num->real) k`)) (concl th) &&
      can (find_term ((=) `&17 / &10`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_scalar")) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "st2" (MP_TAC o SPEC `sy:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "far" (MP_TAC o SPECL [`k:num`; `sy:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Curves along the profile and then into a small ball.  The concatenation   *)
(* of the profile segment from gamma a to gamma b with a short curve from    *)
(* gamma b to q (grgd_concat): its length, and every point is a profile      *)
(* point between a and b or lies in the ball about gamma b.                  *)
(* ========================================================================= *)

let P2BT_SS_RANGE = prove
 (`(!t. &0 <= t /\ t <= &1 / &2 ==> &0 <= grgd_ss (&0) t /\ grgd_ss (&0) t <= &1) /\
   (!t. &1 / &2 <= t /\ t <= &1 ==> &0 <= grgd_ss (&1) t /\ grgd_ss (&1) t <= &1)`,
  SUBGOAL_THEN `!u. &0 <= u /\ u <= &1 ==> &0 <= &3 * u pow 2 - &2 * u pow 3 /\
                                           &3 * u pow 2 - &2 * u pow 3 <= &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `&3 * u pow 2 - &2 * u pow 3 = u pow 2 * (&3 - &2 * u)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&1 - (&3 * u pow 2 - &2 * u pow 3) = (&1 - u) pow 2 * (&1 + &2 * u)`
      MP_TAC THENL
       [REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 <= (&1 - u) pow 2 * (&1 + &2 * u)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  REWRITE_TAC[grgd_ss] THEN CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2BT_REACH_CURVE = prove
 (`!top atlas (g:A->real^3^3) (gamma:real->A) a b q r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     &0 <= a /\ a <= &1 /\ &0 <= b /\ b <= &1 /\
     mfd_joinable (top,atlas) (gamma b) q /\ mfd_dist (top,atlas) g (gamma b) q < r
     ==> ?c. mfd_c1_curve (top,atlas) c (&0) (&1) /\ c(&0) = gamma a /\ c(&1) = q /\
             mfd_length atlas g c (&0) (&1) <
             mfd_length atlas g gamma (min a b) (max a b) + r /\
             (!s. &0 <= s /\ s <= &1
                  ==> (?t. min a b <= t /\ t <= max a b /\ c s = gamma t) \/
                      c s IN mfd_ball (top,atlas) g (gamma b) r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(gamma:real->A) b`; `q:A`; `r:real`] P2BT_DIST_LT_CURVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c2:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `c2:real->A`; `(gamma:real->A) b`; `r:real`] LIM_CURVE_IN_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the profile piece from gamma a to gamma b *)
  SUBGOAL_THEN
   `?c1. mfd_c1_curve (top,atlas) c1 (&0) (&1) /\ c1(&0) = (gamma:real->A) a /\ c1(&1) = gamma b /\
         mfd_length atlas (g:A->real^3^3) c1 (&0) (&1) =
         mfd_length atlas g gamma (min a b) (max a b) /\
         (!s. &0 <= s /\ s <= &1 ==> ?t. min a b <= t /\ t <= max a b /\ c1 s = gamma t)`
  STRIP_ASSUME_TAC THENL
   [DISJ_CASES_TAC(REAL_ARITH `a <= b \/ b < a`) THENL
     [SUBGOAL_THEN `min a b = a /\ max a b = b` (CONJUNCTS_THEN SUBST1_TAC) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `mfd_c1_curve (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                      (gamma:real->A) a b` ASSUME_TAC THENL
       [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
        MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `(gamma:real->A) o (\x. a + (b - a) * x)` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `gamma:real->A`; `a:real`; `b:real`] GRGD_AFFINE_CURVE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC GRGD_AFFINE_LENGTH THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXISTS_TAC `a + (b - a) * s` THEN
        REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> a <= a + x`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `x <= (b - a) * &1 ==> a + x <= b`) THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]];
      SUBGOAL_THEN `min a b = b /\ max a b = a` (CONJUNCTS_THEN SUBST1_TAC) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `mfd_c1_curve (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                      (gamma:real->A) b a` ASSUME_TAC THENL
       [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
        MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `gamma:real->A`; `b:real`; `a:real`] GRGD_AFFINE_CURVE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `(gamma:real->A) o (\x. b + (a - b) * x)`] GRGD_REVERSE_01) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      EXISTS_TAC `\t. ((gamma:real->A) o (\x. b + (a - b) * x)) (&0 + &1 - t)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC GRGD_AFFINE_LENGTH THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXISTS_TAC `b + (a - b) * (&0 + &1 - s)` THEN
        REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> b <= b + x`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `x <= (a - b) * &1 ==> b + x <= a`) THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  EXISTS_TAC `grgd_concat (c1:real->A) c2` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:real->A`; `c2:real->A`] GRGD_CONCAT_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `c1:real->A`; `c2:real->A`] GRGD_CONCAT_LENGTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:real->A`; `c2:real->A`] GRGD_CONCAT_PIECES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s <= &1 / &2` THENL
   [DISJ1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `real_interval[&0,&1 / &2]`)) (concl th))) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(CONJUNCT1 P2BT_SS_RANGE) THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    DISJ2_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `real_interval[&1 / &2,&1]`)) (concl th))) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(CONJUNCT2 P2BT_SS_RANGE) THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* Points near a forward tube point are reachable from the base point by     *)
(* deep curves of bounded length (one approximant).  A point q within 3/5    *)
(* h_w/eps of w = EN sig y is within 11/2 h of a window profile point gamma  *)
(* tau' (P2BT_NECK_FIT_ONE); the profile from the base point to gamma tau'   *)
(* and then a short curve to q (P2BT_REACH_CURVE) is delta-deep              *)
(* (P2BT_PROFILE_BALL_DEEP) when the forward margin, the profile curvature   *)
(* bound Kp and delta are as below.                                          *)
(* ========================================================================= *)

let P2BT_REACH_ONE = prove
 (`!u:A->bool.
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1 sig y q delta Kp Ap.
              &0 < eps /\ eps <= eps0 /\ &1 < C /\
              p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
              s0 <= sig /\ sig <= s1 /\ y IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) /\
              &6 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig))) * inv eps <= (sig - s0) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&0)) (gamma(&1)) /\
              (!s'. sig <= s' /\ (s' - sig) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&0)) (gamma(&1)) <= &6 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig))) * inv eps
                    ==> s' <= s1) /\
              (sig - s0) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&0)) (gamma(&1)) + &17 / &10 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig))) * inv eps <= A1 /\
              &4 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps <= A1 /\
              A1 - &2 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig))) * inv eps <= Ap /\
              (!s'. s0 <= s' /\ s' <= s1 /\ (s' - s0) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&0)) (gamma(&1)) <= Ap
                    ==> mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s') <= Kp) /\
              &0 < Kp /\ &0 < delta /\ delta <= inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma sig))) / &4 /\ delta <= inv(sqrt Kp) / &4 /\
              mfd_joinable (rfs_vtop V (&0),rfs_vatlas V (&0)) (EN sig y) q /\
              mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (EN sig y) q <
              &3 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (EN sig y))) * inv eps
              ==> ?c. mfd_c1_curve (rfs_vtop V (&0),rfs_vatlas V (&0)) c (&0) (&1) /\
                      c(&0) = gamma(s0 + (&2 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps) /
                                         mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&0)) (gamma(&1))) /\
                      c(&1) = q /\
                      mfd_length (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) c (&0) (&1) <= A1 + &1 /\
                      (!s. &0 <= s /\ s <= &1
                           ==> p2b_lc_deep V (p2bt_cutset eps V gamma EN s0 s1 A1) (c s) delta)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fit")) o
    MATCH_MP P2BT_NECK_FIT_ONE) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "deep"))
    (INST_TYPE [`:A`,`:A`] P2BT_PROFILE_BALL_DEEP) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "zb"))
    (INST_TYPE [`:A`,`:A`] P2BT_ZBASE_FACTS) THEN
  EXISTS_TAC `min (min e0 e1) (min e2 (&1 / &1000))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1 /\ eps <= e2 /\ eps <= &1 / &1000` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "fit" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
     `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:real`; `Q:real`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `sig:real`; `y:real^3`; `q:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau':real` STRIP_ASSUME_TAC) THEN
  USE_THEN "zb" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
     `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:real`; `Q:real`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_ONE_DIST o CONJ (ASSUME `&1 < C`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dist"))) THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    (let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "p2bt_one"))) THEN
  REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  ABBREV_TAC `L = mfd_dist (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0),
                    rfs_vatlas V (&0)) (rfs_vmetric V (&0)) ((gamma:real->A)(&0)) (gamma(&1))` THEN
  ABBREV_TAC `top = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3)` THEN
  ABBREV_TAC `h = inv(sqrt((R:A->real) ((gamma:real->A) sig)))` THEN
  ABBREV_TAC `h0 = inv(sqrt(&32 * C pow 2))` THEN
  ABBREV_TAC `sz = s0 + (&2 / &5 * h0 * inv eps) / L` THEN
  SUBGOAL_THEN `&0 < h /\ h <= h0 /\ h0 <= &5 / &28 /\ &1000 <= inv eps /\
                &500 <= inv(&2 * eps)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MATCH_MP (CONJ (ASSUME `s0 <= sig:real`) (ASSUME `sig:real <= s1`)) o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&2 * C`)) (concl th) &&
        can (find_term ((=) `&32 * C pow 2`)) (concl th))) THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `&1 <= C pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "h" THEN EXPAND_TAC "h0" THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
      EXPAND_TAC "h0" THEN
      SUBGOAL_THEN `&5 / &28 = inv(&28 / &5)` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`eps:real`; `&1 / &1000`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
      MP_TAC(SPECL [`&2 * eps`; `&2 * &1 / &1000`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `h * &1000 <= h * inv eps /\ h0 * &1000 <= h0 * inv eps /\
                h * inv eps <= h0 * inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* positions *)
  SUBGOAL_THEN `(tau' - s0) * L <= A1 - &1 / &2 * h * inv eps /\
                (sz - s0) * L <= A1 - &2 / &5 * h * inv eps`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `(tau' - s0) * L <= (sig - s0) * L + abs(tau' - sig) * L` MP_TAC THENL
       [REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the curve *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `sz:real`; `tau':real`; `q:A`; `&11 / &2 * h`]
                P2BT_REACH_CURVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real->A` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s0 <= min sz tau' /\ max sz tau' <= s1 /\
                (max sz tau' - s0) * L <= A1 - &2 / &5 * h * inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^3^3) gamma (min sz tau') (max sz tau') + &11 / &2 * h` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_length atlas (g:A->real^3^3) gamma (min sz tau') (max sz tau') =
                  (max sz tau' - min sz tau') * L` SUBST1_TAC THENL
     [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
      REWRITE_TAC[apx_shortest] THEN
      DISCH_THEN(MP_TAC o SPECL [`min sz tau'`; `max sz tau'`] o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "dist" (MP_TAC o SPECL [`min sz tau'`; `max sz tau'`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(max sz tau' - min sz tau') * L <= (max sz tau' - s0) * L` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ASSUME `&0 < h`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `min sz tau'`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_ball")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `tt:real` STRIP_ASSUME_TAC) ASSUME_TAC) THENL
   [(* a profile point *)
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s0 <= tt /\ tt <= s1` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(R:A->real) ((gamma:real->A) tt) <= Kp` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Kp:real`)) (concl th))) THEN
      REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(tt - s0) * L <= (max sz tau' - s0) * L` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(sqrt Kp) <= inv(sqrt((R:A->real) ((gamma:real->A) tt)))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN
        FIRST_ASSUM(MP_TAC o C MATCH_MP (CONJ (ASSUME `s0 <= tt:real`) (ASSUME `tt:real <= s1`)) o
          check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `&2 * C`)) (concl th) &&
            can (find_term ((=) `&32 * C pow 2`)) (concl th))) THEN
        SUBGOAL_THEN `&0 < C pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MP_TAC o C MATCH_MP (CONJ (ASSUME `s0 <= tt:real`) (ASSUME `tt:real <= s1`)) o
          check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `&2 * C`)) (concl th) &&
            can (find_term ((=) `&32 * C pow 2`)) (concl th))) THEN
        SUBGOAL_THEN `&0 < C pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(delta + delta) / (&99 / &100 * inv(sqrt((R:A->real) ((gamma:real->A) tt)))) <
                  inv(&2 * eps)` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < &99 / &100 * inv(sqrt((R:A->real) ((gamma:real->A) tt)))` ASSUME_TAC THENL
       [MP_TAC(ASSUME `&0 < delta`) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      SUBGOAL_THEN `&500 * (&99 / &100 * inv(sqrt((R:A->real) ((gamma:real->A) tt)))) <=
                    inv(&2 * eps) * (&99 / &100 * inv(sqrt(R (gamma tt))))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(tt - s0) * L + delta + delta < A1` ASSUME_TAC THENL
     [SUBGOAL_THEN `(tt - s0) * L <= (max sz tau' - s0) * L` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ASSUME `&0 < h`) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(gamma:real->A) tt IN mfd_ball (top,atlas) (g:A->real^3^3) (gamma tt) delta`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `gamma:real->A`;
                     `&0`; `&1`; `tt:real`] MFD_C1_CURVE_IN_TOPSPACE) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "deep" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
     `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:real`; `Q:real`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `A1:real`; `tt:real`; `delta:real`; `delta:real`;
                                     `(gamma:real->A) tt`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    (* a point near gamma tau' *)
    SUBGOAL_THEN `(&11 / &2 * h + delta) /
                  (&99 / &100 * inv(sqrt((R:A->real) ((gamma:real->A) tau')))) < inv(&2 * eps)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < &99 / &100 * inv(sqrt((R:A->real) ((gamma:real->A) tau')))` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      SUBGOAL_THEN `&500 * (&99 / &100 * inv(sqrt((R:A->real) ((gamma:real->A) tau')))) <=
                    inv(&2 * eps) * (&99 / &100 * inv(sqrt(R (gamma tau'))))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(tau' - s0) * L + &11 / &2 * h + delta < A1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "deep" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
     `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:real`; `Q:real`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `A1:real`; `tau':real`; `&11 / &2 * h`;
                                     `delta:real`; `(c:real->A) s`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The closeness clause of the local-limit statement in the form of the      *)
(* transfer lemma: on the chart domain the local expression of the pullback  *)
(* metric is the rfs_pullback through the chart (P2BL_PB_CHART), so their    *)
(* C^m distances to the limit metric agree (LCK_DIST2_LOCAL).                *)
(* ========================================================================= *)

let P2BT_LIM_CLOSE_CONVERT = prove
 (`!top atlas (g:B->real^3^3) top' atlas' (g':A->real^3^3) W (phi:B->A) psi y m.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top atlas W top' atlas' (IMAGE phi W) phi psi /\ y IN W
     ==> lck_dist2 m (metric_local atlas (chart_at atlas y) g)
                     (metric_local atlas (chart_at atlas y)
                                   (mfd_pullback_metric atlas atlas' phi g'))
                     (SND(chart_at atlas y) y) =
         lck_dist2 m (metric_local atlas (chart_at atlas y) g)
                     (rfs_pullback atlas' (phi o chart_inv (chart_at atlas y)) g')
                     (SND(chart_at atlas y) y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (W:B->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)` THEN
  SUBGOAL_THEN `(c:(B->bool)#(B->real^3)) IN atlas /\ (y:B) IN FST c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC CHART_AT THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN
  EXISTS_TAC `IMAGE (SND c) (FST (c:(B->bool)#(B->real^3)) INTER W)` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                   `FST(c:(B->bool)#(B->real^3)) INTER W`] CHART_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BL_PB_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `top':A topology`; `W:B->bool`;
                          `IMAGE (phi:B->A) W`; `psi:A->B`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Forward points of the limit are centres of 2 eps-necks.  If phi k P (k    *)
(* large) lies in the middle half of a window neck at arc length >= 6/5      *)
(* h/eps with R <= K, the strong eps-neck at phi k P, as a 19/10 eps-neck,   *)
(* lies in the ball of radius 3/5 h/eps, whose points are reached by deep    *)
(* curves (P2BT_REACH_ONE) and so lie in phi k (W m) (the lifting clause of  *)
(* the local-limit statement); the closeness clause on the closure of W m    *)
(* and P2BT_NECK_TO_LIMIT give the 2 eps-neck psi o e at P.                  *)
(* ========================================================================= *)

let P2BT_LIM_NECK = prove
 (`!u:A->bool.
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1
            sub (top:B topology) atlas g zl W phi Vl.
              &0 < eps /\ eps <= eps0 /\ &1 < C /\
              p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\
              p2bt_cut eps C A V gamma s0 s1 A1 /\
              p2bt_lim V (\n. p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1)
                       (p2bt_zbase eps C V gamma s0) sub top atlas g zl W phi Vl
              ==> !K. &0 < K
                      ==> ?N. !k P sig y.
                            N <= k /\ P IN W k /\
                            s0 (sub k) <= sig /\ sig <= s1 (sub k) /\
                            y IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) /\
                            phi k P = EN (sub k) sig y /\
                            &6 / &5 * inv(sqrt(mfd_scalar (rfs_vatlas (V (sub k)) (&0)) (rfs_vmetric (V (sub k)) (&0)) (gamma (sub k) sig))) * inv eps <=
                            (sig - s0 (sub k)) * mfd_dist (rfs_vtop (V (sub k)) (&0),rfs_vatlas (V (sub k)) (&0)) (rfs_vmetric (V (sub k)) (&0))
                                    (gamma (sub k) (&0)) (gamma (sub k) (&1)) /\
                            mfd_scalar (rfs_vatlas (V (sub k)) (&0)) (rfs_vmetric (V (sub k)) (&0)) (phi k P) <= K
                            ==> ?e. rfs_neck (top,atlas) g (&2 * eps) P e`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "reach")) o
    MATCH_MP P2BT_REACH_ONE) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wfar"))
    (INST_TYPE [`:A`,`:A`] P2BT_WINDOW_FAR) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nh"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_H) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  EXISTS_TAC `min (min e0 e1) (min (min e2 e3) (&1 / &1000))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `K:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1 /\ eps <= e2 /\ eps <= e3 /\ eps <= &1 / &1000`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "wfar" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`; `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `gamma:num->real->A`; `s0:num->real`; `s1:num->real`;
     `EN:num->real->real^3->A`; `A1:real`]) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * K`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far")))) THEN
  ABBREV_TAC `hK = inv(sqrt(&2 * K))` THEN
  SUBGOAL_THEN `&0 < hK /\ &0 < inv eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "hK" THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    TRY(MATCH_MP_TAC SQRT_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `A1 - &2 / &5 * hK * inv eps` o CONJUNCT1 o CONJUNCT2 o
    CONJUNCT2 o GEN_REWRITE_RULE I [p2bt_cut]) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `&0 < hK * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kp0:real` (LABEL_TAC "kp")) THEN
  ABBREV_TAC `Kp = max (&1) Kp0` THEN
  SUBGOAL_THEN `&0 < Kp /\ Kp0 <= Kp` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kp" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `delta = min (hK / &4) (inv(sqrt Kp) / &4)` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= hK / &4 /\ delta <= inv(sqrt Kp) / &4`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN
    SUBGOAL_THEN `&0 < inv(sqrt Kp)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(TOP_DEPTH_CONV BETA_CONV) o
    GEN_REWRITE_RULE I [p2bt_lim] o check (fun th -> is_comb(concl th) &&
      (let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "p2bt_lim"))) THEN
  (* the lifting of deep curves *)
  FIRST_ASSUM(MP_TAC o SPECL [`delta:real`; `A1 + &1`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_length")) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_lc_deep")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bt_cut eps C A (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 A1` THEN
    REWRITE_TAC[p2bt_cut] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `&0 <= &4 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
      SIMP_TAC[SQRT_POS_LE; REAL_LE_MUL; REAL_LE_POW_2; REAL_POS] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `k0:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lift")))) THEN
  (* the transfer *)
  MP_TAC(INST_TYPE [`:A`,`:A`; `:B`,`:B`]
    (SPECL [`&19 / &10 * eps`; `&2 * eps`] P2BT_NECK_TO_LIMIT)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m0:num` (X_CHOOSE_THEN `eta:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr")))) THEN
  (* closeness on the closure of W m *)
  FIRST_ASSUM(MP_TAC o SPECL [`top closure_of (W:num->B->bool) m`; `m0:num`; `eta:real`] o
    check (fun th -> let vs,bd = strip_forall(concl th) in
      length vs = 3 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) bd &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) bd)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
      can (term_match [] `!k:num. open_in (top:B topology) ((W:num->B->bool) k) /\ P k`)
          (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "conv")) THEN
  EXISTS_TAC `MAX (MAX N1 k0) (MAX k1 m)` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `P:B`; `sig:real`; `y:real^3`] THEN
  REWRITE_TAC[ARITH_RULE `MAX (MAX N1 k0) (MAX k1 m) <= k <=>
                          N1 <= k /\ k0 <= k /\ k1 <= k /\ m <= k`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `N1 <= (sub:num->num) k` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MONOTONE_BIGGER o REWRITE_RULE[p3_subseq] o check (fun th ->
      is_comb(concl th) && (let c,_ = strip_comb(concl th) in
        is_const c && fst(dest_const c) = "p3_subseq"))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bt_one eps C A ((sub:num->num) k) ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
              ((t:num->real) ((sub:num->num) k)) ((Q:num->real) ((sub:num->num) k)) ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k))
              ((gamma:num->real->A) ((sub:num->num) k)) ((s0:num->real) ((sub:num->num) k)) ((s1:num->real) ((sub:num->num) k))
              ((EN:num->real->real^3->A) ((sub:num->num) k))` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(ACCEPT_TAC o SPEC `(sub:num->num) k`);
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (term_match [] `!k:num. IMAGE ((phi:num->B->A) k) ((W:num->B->bool) k) SUBSET Y k /\ P k`)
        (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psi:A->B`)) THEN
  (* tube facts at sub k *)
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`; `(t:num->real) ((sub:num->num) k)`; `(Q:num->real) ((sub:num->num) k)`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`; `(gamma:num->real->A) ((sub:num->num) k)`;
     `(s0:num->real) ((sub:num->num) k)`; `(s1:num->real) ((sub:num->num) k)`; `(EN:num->real->real^3->A) ((sub:num->num) k)`] P2BT_TUBE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "nk")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "sn")))) THEN
  USE_THEN "nk" (MP_TAC o SPEC `sig:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_ONE_DIST o CONJ (ASSUME `&1 < C`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dist"))) THEN
  SUBGOAL_THEN `(phi:num->B->A) k P IN
                p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)) ((gamma:num->real->A) ((sub:num->num) k))
                  ((EN:num->real->real^3->A) ((sub:num->num) k)) ((s0:num->real) ((sub:num->num) k)) ((s1:num->real) ((sub:num->num) k)) A1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!(f:B->A) s t x. IMAGE f s SUBSET t /\ x IN s ==> f x IN t`) THEN
    EXISTS_TAC `(W:num->B->bool) k` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the views at sub k *)
  FIRST_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    (let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "p2bt_one"))) THEN
  REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  ABBREV_TAC `Vn = (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)` THEN
  ABBREV_TAC `gn = (gamma:num->real->A) ((sub:num->num) k)` THEN
  ABBREV_TAC `ENn = (EN:num->real->real^3->A) ((sub:num->num) k)` THEN
  ABBREV_TAC `L = mfd_dist (rfs_vtop (Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0),rfs_vatlas Vn (&0)) (rfs_vmetric Vn (&0))
                    ((gn:real->A)(&0)) (gn(&1))` THEN
  ABBREV_TAC `top' = rfs_vtop (Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `atlas' = rfs_vatlas (Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `g' = rfs_vmetric (Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `R = mfd_scalar atlas' (g':A->real^3^3)` THEN
  ABBREV_TAC `w = (phi:num->B->A) k (P:B)` THEN
  ABBREV_TAC `h = inv(sqrt((R:A->real) ((gn:real->A) sig)))` THEN
  ABBREV_TAC `hw = inv(sqrt((R:A->real) w))` THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) && lhs(concl th) = `w:A`)) THEN
  (* facts at the window neck *)
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps /\ abs(apx_sval y) < inv(&2 * eps)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2BT_MIDDLE_IN_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t (x:real^3). x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(y:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(gn:real->A) sig IN IMAGE ((ENn:real->real^3->A) sig) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps /\ apx_sval y0 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                                  `g':A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[apx_ch_ctx] THEN STRIP_TAC THEN
  USE_THEN "nh" (MP_TAC o SPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
    `g':A->real^3^3`; `eps:real`; `(gn:real->A) sig`; `(ENn:real->real^3->A) sig`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (R:A->real) ((gn:real->A) sig) /\ R (gn sig) <= &2 * K /\ &0 < h /\
                hK <= h /\ &1000 <= inv eps /\ &32 * C pow 2 <= R (gn sig)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MATCH_MP (CONJ (ASSUME `(s0:num->real) ((sub:num->num) k) <= sig`)
      (ASSUME `sig <= (s1:num->real) ((sub:num->num) k)`)) o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&2 * C`)) (concl th) &&
        can (find_term ((=) `&32 * C pow 2`)) (concl th))) THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `&0 < C pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (R:A->real) ((gn:real->A) sig)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[SQRT_POS_LT];
      EXPAND_TAC "h" THEN EXPAND_TAC "hK" THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[SQRT_POS_LT] THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`eps:real`; `&1 / &1000`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC P2BT_SQRT2_PI THEN DISCH_TAC THEN
  (* the window position of sig is below A1 + 9/10 h / eps *)
  SUBGOAL_THEN `(sig - (s0:num->real) ((sub:num->num) k)) * L < A1 + &9 / &10 * h * inv eps`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(w:A) IN p2bt_cutset eps (Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gn ENn ((s0:num->real) ((sub:num->num) k))
                   ((s1:num->real) ((sub:num->num) k)) A1` THEN
    ASM_REWRITE_TAC[p2bt_cutset; IN_INTER; mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    UNDISCH_TAC `apx_eng_n2 top' atlas' (g':A->real^3^3) eps (&1 / &100)` THEN
    REWRITE_TAC[apx_eng_n2] THEN
    DISCH_THEN(MP_TAC o SPECL [`(gn:real->A) sig`; `(ENn:real->real^3->A) sig`;
                               `y0:real^3`; `y:real^3`]) THEN
    ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG] THEN STRIP_TAC THEN
    USE_THEN "dist" (MP_TAC o SPECL [`(s0:num->real) ((sub:num->num) k)`; `sig:real`]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `&0 < (s0:num->real) ((sub:num->num) k)` THEN
      UNDISCH_TAC `(s0:num->real) ((sub:num->num) k) <= sig` THEN
      UNDISCH_TAC `sig <= (s1:num->real) ((sub:num->num) k)` THEN
      UNDISCH_TAC `(s1:num->real) ((sub:num->num) k) < &1` THEN REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
                   `(gn:real->A) ((s0:num->real) ((sub:num->num) k))`; `w:A`;
                   `(gn:real->A) sig`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`;
                     `w:A`; `(gn:real->A) sig`] MFD_JOINABLE_SYM) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
                   `w:A`; `(gn:real->A) sig`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `h * (abs(apx_sval(y:real^3)) + sqrt(&2) * pi) <= h * (inv eps / &2 + &24 / &5) /\
                  h * &1000 <= h * inv eps` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      (SUBGOAL_THEN `inv(&2 * eps) = inv eps / &2` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
        [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
         UNDISCH_TAC `&0 < h` THEN UNDISCH_TAC `abs(apx_sval(y:real^3)) < inv eps / &2` THEN
         UNDISCH_TAC `sqrt(&2) * pi <= &24 / &5` THEN UNDISCH_TAC `&1000 <= inv eps` THEN
         REAL_ARITH_TAC]);
      ALL_TAC] THEN
    MP_TAC(ASSUME `&0 < h`) THEN
    UNDISCH_TAC `mfd_dist (top':A topology,atlas':((A->bool)#(A->real^3))->bool) (g':A->real^3^3)
                   ((gn:real->A) ((s0:num->real) ((sub:num->num) k))) (w:A) < A1` THEN
    UNDISCH_TAC `mfd_dist (top':A topology,atlas':((A->bool)#(A->real^3))->bool) (g':A->real^3^3)
                   ((gn:real->A) sig) (w:A) <=
                 (&1 + &1 / &100) * h * (abs(apx_sval(y:real^3)) + sqrt(&2) * pi)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h * inv eps /\ hK * inv eps <= h * inv eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
                    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the forward margins *)
  USE_THEN "far" (MP_TAC o SPECL [`(sub:num->num) k`; `sig:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "marg")) THEN
  (* the points of the 3/5 ball lie in phi k (W m) *)
  SUBGOAL_THEN
   `!q. q IN mfd_ball (top',atlas') (g':A->real^3^3) w (&3 / &5 * hw * inv eps)
        ==> ?y'. y' IN (W:num->B->bool) m /\ (phi:num->B->A) k y' = q`
  (LABEL_TAC "cov") THENL
   [X_GEN_TAC `q:A` THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "reach" (MP_TAC o SPECL
      [`eps:real`; `C:real`; `A:real`; `(sub:num->num) k`;
       `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) ((sub:num->num) k)`; `(t:num->real) ((sub:num->num) k)`;
       `(Q:num->real) ((sub:num->num) k)`; `Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `gn:real->A`;
       `(s0:num->real) ((sub:num->num) k)`; `(s1:num->real) ((sub:num->num) k)`;
       `ENn:real->real^3->A`; `A1:real`; `sig:real`; `y:real^3`; `q:A`; `delta:real`;
       `Kp:real`; `A1 - &2 / &5 * hK * inv eps`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `s':real` THEN STRIP_TAC THEN USE_THEN "marg" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `p2bt_cut eps C A (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 A1` THEN
        REWRITE_TAC[p2bt_cut] THEN SIMP_TAC[];
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s':real` THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kp0:real` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "kp" (MP_TAC o SPECL [`(sub:num->num) k`; `s':real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `cc:real->A` STRIP_ASSUME_TAC) THEN
    USE_THEN "lift" (MP_TAC o SPECL [`k:num`; `cc:real->A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[p2bt_zbase] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPEC `&1`) THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS]];
    ALL_TAC] THEN
  (* the strong neck at w *)
  USE_THEN "sn" (MP_TAC o SPEC `w:A`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(w:A) IN p2bt_cutset eps (Vn:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gn ENn ((s0:num->real) ((sub:num->num) k))
                   ((s1:num->real) ((sub:num->num) k)) A1` THEN
    SIMP_TAC[p2bt_cutset; IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_strong_neck; P2BN_EVOLVING_NECK_ALT] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->A` (ASSUME_TAC o CONJUNCT1)) THEN
  SUBGOAL_THEN `rfs_neck (top',atlas') (g':A->real^3^3) (&19 / &10 * eps) w e` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_MONO_GEN THEN EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the neck lies in the 3/5 ball *)
  SUBGOAL_THEN `IMAGE (e:real^3->A) (rfs_neck_dom (&19 / &10 * eps)) SUBSET
                mfd_ball (top',atlas') (g':A->real^3^3) w (&3 / &5 * hw * inv eps)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top',atlas') (g':A->real^3^3) eps w e` THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    UNDISCH_TAC `(w:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y1:real^3) IN rfs_neck_dom eps /\ apx_sval y1 = &0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom eps /\ abs(apx_sval z) < inv(&19 / &10 * eps)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(SPECL [`eps:real`; `&19 / &10 * eps`] APX_NECK_DOM_MONO) THEN
        ANTS_TAC THENL
         [ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `(z:real^3) IN rfs_neck_dom (&19 / &10 * eps)` THEN SET_TAC[]];
        UNDISCH_TAC `(z:real^3) IN rfs_neck_dom (&19 / &10 * eps)` THEN
        REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `apx_eng_n2 top' atlas' (g':A->real^3^3) eps (&1 / &100)` THEN
    REWRITE_TAC[apx_eng_n2] THEN
    DISCH_THEN(MP_TAC o SPECL [`w:A`; `e:real^3->A`; `y1:real^3`; `z:real^3`]) THEN
    ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG] THEN STRIP_TAC THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(&19 / &10 * eps) = &10 / &19 * inv eps` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < hw` ASSUME_TAC THENL
     [EXPAND_TAC "hw" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
      UNDISCH_TAC `&99 / &100 * (R:A->real) ((gn:real->A) sig) <= R (w:A)` THEN
      UNDISCH_TAC `&0 < (R:A->real) ((gn:real->A) sig)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `hw * (abs(apx_sval(z:real^3)) + sqrt(&2) * pi) <=
                  hw * (&10 / &19 * inv eps + &24 / &5) /\ hw * &1000 <= hw * inv eps`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      UNDISCH_TAC `&0 < hw` THEN UNDISCH_TAC `abs(apx_sval(z:real^3)) < &10 / &19 * inv eps` THEN
      UNDISCH_TAC `sqrt(&2) * pi <= &24 / &5` THEN UNDISCH_TAC `&1000 <= inv eps` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ASSUME `&0 < hw`) THEN
    UNDISCH_TAC `mfd_dist (top':A topology,atlas':((A->bool)#(A->real^3))->bool) (g':A->real^3^3)
                   (w:A) ((e:real^3->A) z) <=
                 (&1 + &1 / &100) * hw * (abs(apx_sval(z:real^3)) + sqrt(&2) * pi)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* W m lies in W k *)
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET W k` ASSUME_TAC THENL
   [SUBGOAL_THEN `!j. (W:num->B->bool) m SUBSET W (m + j)` MP_TAC THENL
     [INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUBSET_REFL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(W:num->B->bool) (m + j)` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o SPEC `m + j:num` o check (fun th ->
        can (term_match [] `!k:num. open_in (top:B topology) ((W:num->B->bool) k) /\ P k`)
            (concl th))) THEN
      STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `(top:B topology) closure_of (W:num->B->bool) (m + j)` THEN
      ASM_SIMP_TAC[CLOSURE_OF_SUBSET; OPEN_IN_SUBSET];
      DISCH_THEN(MP_TAC o SPEC `k - m:num`) THEN
      SUBGOAL_THEN `m + k - m = k:num` SUBST1_TAC THENL
       [UNDISCH_TAC `m <= k:num` THEN ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  (* the closeness on the closure of W m at k *)
  USE_THEN "conv" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS o check (fun th ->
    let c,args = strip_comb(concl th) in
    is_const c && fst(dest_const c) = "mfd_diffeo" && length args = 8 &&
    hd args = `top:B topology`)) THEN
  (* the transfer *)
  USE_THEN "tr" (MP_TAC o SPECL
    [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
     `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
     `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`;
     `mfd_ball (top',atlas') (g':A->real^3^3) w (&3 / &5 * hw * inv eps)`; `w:A`;
     `e:real^3->A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[MFD_BALL_OPEN];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
      USE_THEN "cov" (MP_TAC o SPEC `q:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(W:num->B->bool) m SUBSET W k` THEN SET_TAC[];
      SUBGOAL_THEN `&1 <= C pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
      USE_THEN "cov" (MP_TAC o SPEC `q:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y':B` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(psi:A->B) q = y'` SUBST1_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `(y':B) IN (W:num->B->bool) m` THEN
        UNDISCH_TAC `(W:num->B->bool) m SUBSET W k` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `top':A topology`; `atlas':((A->bool)#(A->real^3))->bool`; `g':A->real^3^3`;
                     `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`; `y':B`; `m0:num`]
                    P2BT_LIM_CLOSE_CONVERT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y':B) IN (W:num->B->bool) m` THEN
        UNDISCH_TAC `(W:num->B->bool) m SUBSET W k` THEN SET_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "cl" (MP_TAC o SPEC `y':B`) THEN ANTS_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!s t (x:B). x IN s /\ s SUBSET t ==> x IN t`) THEN
        EXISTS_TAC `(W:num->B->bool) m` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
        FIRST_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
          can (term_match [] `!k:num. open_in (top:B topology) ((W:num->B->bool) k) /\ P k`)
              (concl th))) THEN
        MESON_TAC[OPEN_IN_SUBSET];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->B) w = P` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `(phi:num->B->A) k P = w`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `(psi:A->B) o (e:real^3->A)` THEN ASM_REWRITE_TAC[]);;

