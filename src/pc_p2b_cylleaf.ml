(* ========================================================================= *)
(* Unit pc_p2b_cylleaf: the cylinder model from the round leaf flow,         *)
(* P2B_CYL_FROM_LEAF on the statement of pc_p2b_cylleafreq, a step of the    *)
(* proof of P2B_SPLIT_ROUND_STATEMENT.  Route: (b) the leaf metrics h(t) of  *)
(* L = lvs_set V0 h0 u0 form a 2-d Ricci flow with spatially constant R, so  *)
(* h(t) = (1 - R0 (t - s0)) h(s0); (c) the leaf at s0 is round of curvature  *)
(* R0/2, its Cartan pair and the X-flow give the model map p of g(s0), a     *)
(* local isometry from G0(c^2), c^2 = 2/R0, onto, one-to-one through the     *)
(* orbit bijection, with dp(y/c) = X (generic forms of lemmas of             *)
(* pc_p2b_shsplit); (d) g(t) = a g(s0) + (1 - a) w w^T, w = g(s0) X, first   *)
(* on L and then everywhere by the flow charts, so p pulls g(t + s0) back to *)
(* lam cylinder_flow(t/lam), lam = c^2/2 = 1/R0.                             *)
(* ========================================================================= *)

needs "src/pc_p2b_cylleafreq.ml";;
needs "src/pc_p2b_shsplit.ml";;
needs "src/pc_p2b_kglob.ml";;
needs "src/pc_p2b_kleafg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Step (b): a 2-d Ricci flow on t < b whose scalar curvature is spatially   *)
(* constant is h(t) = (1 - rho0 (t - s0)) h(s0), rho0 the scalar curvature   *)
(* at time s0 (2-d Einstein gives d/dt h = -R h entrywise; ratios with a     *)
(* fixed entry are constant; R scales inversely).                            *)
(* ========================================================================= *)

let P2BCL_SCALAR_CONG = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (G1:A->real^N^N) G2 z.
     smooth_manifold_atlas top atlas /\ (!x. x IN topspace top ==> G1 x = G2 x) /\
     z IN topspace top
     ==> mfd_scalar atlas G1 z = mfd_scalar atlas G2 z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_scalar] THEN
  MATCH_MP_TAC LSCALAR_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)))
                    (FST(chart_at atlas z))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A))`]
                SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A))`]
                CHART_INV) THEN
  ASM_REWRITE_TAC[PAIR] THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[metric_local] THEN
    SUBGOAL_THEN `chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) z' IN topspace top`
    (fun th -> ASM_SIMP_TAC[th]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z':real^N`) THEN ASM_REWRITE_TAC[PAIR] THEN
    STRIP_TAC THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]]);;

let p2bcl_has_const s th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = s)) (concl th);;

let P2BCL_FLOW2_ODE = prove
 (`!top (atlas:((B->bool)#(B->real^2))->bool) (h:real->B->real^2^2) b x0.
     (!a. a < b ==> ricci_flow_on (top,atlas) a b h) /\ x0 IN topspace top /\
     (!t x y. t < b /\ x IN topspace top /\ y IN topspace top
              ==> mfd_scalar atlas (h t) x = mfd_scalar atlas (h t) y)
     ==> (!t. t < b ==> smooth_manifold_atlas top atlas /\ riemannian_metric atlas (h t)) /\
         (!t. t < b ==> &0 < h t x0$1$1) /\
         (!t x i j. t < b /\ x IN topspace top /\ 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
                    ==> ((\s. h s x$i$j) has_real_derivative
                         (--(mfd_scalar atlas (h t) x0) * h t x$i$j)) (atreal t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. t < b ==> ricci_flow_on (top,atlas) (t - &1) b (h:real->B->real^2^2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t < b ==> smooth_manifold_atlas top (atlas:((B->bool)#(B->real^2))->bool) /\
                  riemannian_metric atlas ((h:real->B->real^2^2) t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `t < b:real`)) THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^2))->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `b - &1`) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`;
                   `(h:real->B->real^2^2) t`; `x0:B`] P2BSS_G_AT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `basis 1:real^2` o CONJUNCT1 o CONJUNCT2) THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_2; ARITH; RFB_BASIS_DOT_MATRIX];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (atlas:((B->bool)#(B->real^2))->bool) ((h:real->B->real^2^2) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `t < b:real`) o
    check (fun th -> p2bcl_has_const "ricci_flow_on" th && is_forall(concl th))) THEN
  REWRITE_TAC[ricci_flow_on] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:B`; `i:num`; `j:num`] o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `a = b ==> (f has_real_derivative a) n ==> (f has_real_derivative b) n`) THEN
  ASM_SIMP_TAC[mfd_ricci_matrix; LAMBDA_BETA; DIMINDEX_2] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`;
                 `(h:real->B->real^2^2) t`; `x:B`; `basis i:real^2`; `basis j:real^2`]
                P2BSS_EINSTEIN2_MFD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[RFB_BASIS_DOT_MATRIX; DIMINDEX_2] THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `t < b:real`)
    (CONJ (ASSUME `(x:B) IN topspace top`) (ASSUME `(x0:B) IN topspace top`)))]) o
    check (fun th -> p2bcl_has_const "mfd_scalar" th && is_forall(concl th))) THEN
  REAL_ARITH_TAC);;

let P2BCL_FLOW2_SCALE = prove
 (`!top (atlas:((B->bool)#(B->real^2))->bool) (h:real->B->real^2^2) b s0 x0.
     (!a. a < b ==> ricci_flow_on (top,atlas) a b h) /\ s0 < b /\ x0 IN topspace top /\
     (!t x y. t < b /\ x IN topspace top /\ y IN topspace top
              ==> mfd_scalar atlas (h t) x = mfd_scalar atlas (h t) y)
     ==> !t x. t < b /\ x IN topspace top
               ==> h t x = (&1 - mfd_scalar atlas (h s0) x0 * (t - s0)) %% h s0 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`;
                 `h:real->B->real^2^2`; `b:real`; `x0:B`] P2BCL_FLOW2_ODE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rm") (CONJUNCTS_THEN2 (LABEL_TAC "pos") (LABEL_TAC "ode"))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^2))->bool)` ASSUME_TAC THENL
   [USE_THEN "rm" (MP_TAC o SPEC `s0:real`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* the entries are proportional to the fixed entry h t x0$1$1 *)
  SUBGOAL_THEN
   `!t x i j. t < b /\ x IN topspace top /\ 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
              ==> (h:real->B->real^2^2) t x$i$j * h s0 x0$1$1 = h s0 x$i$j * h t x0$1$1`
  (LABEL_TAC "ratio") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!u. u < b ==> ((\u. (h:real->B->real^2^2) u x$i$j / h u x0$1$1) has_real_derivative &0)
                    (atreal u)`
    ASSUME_TAC THENL
     [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`\s. (h:real->B->real^2^2) s x$i$j`;
                     `--(mfd_scalar atlas ((h:real->B->real^2^2) u) x0) * h u x$i$j`;
                     `\s. (h:real->B->real^2^2) s x0$1$1`;
                     `--(mfd_scalar atlas ((h:real->B->real^2^2) u) x0) * h u x0$1$1`;
                     `u:real`] HAS_REAL_DERIVATIVE_DIV_ATREAL) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [USE_THEN "pos" (fun th -> ASSUME_TAC(MP (SPEC `u:real` th) (ASSUME `u < b:real`))) THEN
        REPEAT CONJ_TAC THENL
         [USE_THEN "ode" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          USE_THEN "ode" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
          ASM_SIMP_TAC[REAL_LT_IMP_NZ]];
        ALL_TAC] THEN
      MATCH_MP_TAC(MESON[] `a = b ==> (f has_real_derivative a) n ==> (f has_real_derivative b) n`) THEN
      REWRITE_TAC[real_div; REAL_ARITH `(--r * y) * z - y * --r * z = &0`; REAL_MUL_LZERO];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\u. (h:real->B->real^2^2) u x$i$j / h u x0$1$1`;
                   `real_interval(min t s0 - &1,b)`] HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real` (fun th -> MP_TAC(SPEC `t:real` th) THEN
                                                 MP_TAC(SPEC `s0:real` th))) THEN
    REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    USE_THEN "pos" (fun th -> ASSUME_TAC(MP (SPEC `t:real` th) (ASSUME `t < b:real`)) THEN
                              ASSUME_TAC(MP (SPEC `s0:real` th) (ASSUME `s0 < b:real`))) THEN
    UNDISCH_TAC `(h:real->B->real^2^2) t x$i$j / h t x0$1$1 = C` THEN
    UNDISCH_TAC `(h:real->B->real^2^2) s0 x$i$j / h s0 x0$1$1 = C` THEN
    UNDISCH_TAC `&0 < (h:real->B->real^2^2) t x0$1$1` THEN
    UNDISCH_TAC `&0 < (h:real->B->real^2^2) s0 x0$1$1` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  USE_THEN "pos" (fun th -> ASSUME_TAC(MP (SPEC `s0:real` th) (ASSUME `s0 < b:real`))) THEN
  SUBGOAL_THEN
   `!t x. t < b /\ x IN topspace top
          ==> (h:real->B->real^2^2) t x = (h t x0$1$1 / h s0 x0$1$1) %% h s0 x`
  (LABEL_TAC "prop") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; MATRIX_CMUL_COMPONENT] THEN
    REPEAT CONJ_TAC THEN
    MATCH_MP_TAC(REAL_FIELD `&0 < d /\ y * d = c * z ==> y = z / d * c`) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ratio" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t < b ==> mfd_scalar atlas ((h:real->B->real^2^2) t) x0 =
                  mfd_scalar atlas (h s0) x0 / (h t x0$1$1 / h s0 x0$1$1)`
  (LABEL_TAC "rsc") THENL
   [REPEAT STRIP_TAC THEN
    ABBREV_TAC `A = (h:real->B->real^2^2) t x0$1$1 / h s0 x0$1$1` THEN
    SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL
     [EXPAND_TAC "A" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`;
                   `(h:real->B->real^2^2) t`; `\x. A %% (h:real->B->real^2^2) s0 x`; `x0:B`]
                  P2BCL_SCALAR_CONG) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
      EXPAND_TAC "A" THEN USE_THEN "prop" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mfd_scalar; METRIC_LOCAL_CMUL; ETA_AX] THEN
    MATCH_MP_TAC LSCALAR_SCALE THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^2))->bool) (x0:B)))
                      (FST(chart_at atlas x0))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^2))->bool`; `x0:B`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "rm" (fun th -> MP_TAC(CONJUNCT2(MP (SPEC `s0:real` th) (ASSUME `s0 < b:real`)))) THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t < b ==> ((\t. (h:real->B->real^2^2) t x0$1$1 / h s0 x0$1$1 +
                        mfd_scalar atlas (h s0) x0 * t) has_real_derivative &0) (atreal t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "pos" (fun th -> ASSUME_TAC(MP (SPEC `t:real` th) (ASSUME `t < b:real`))) THEN
    MP_TAC(ISPECL [`\t. (h:real->B->real^2^2) t x0$1$1 / h s0 x0$1$1`;
                   `--(mfd_scalar atlas ((h:real->B->real^2^2) t) x0) * h t x0$1$1 / h s0 x0$1$1`;
                   `\t. mfd_scalar atlas ((h:real->B->real^2^2) s0) x0 * t`;
                   `mfd_scalar atlas ((h:real->B->real^2^2) s0) x0`; `atreal t`]
                  HAS_REAL_DERIVATIVE_ADD) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[real_div] THEN
        MP_TAC(ISPECL [`\s. (h:real->B->real^2^2) s x0$1$1`;
                       `--(mfd_scalar atlas ((h:real->B->real^2^2) t) x0) * h t x0$1$1`;
                       `inv((h:real->B->real^2^2) s0 x0$1$1)`; `t:real`]
                      HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
        USE_THEN "ode" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        MP_TAC(ISPECL [`\x:real. x`; `&1`; `mfd_scalar atlas ((h:real->B->real^2^2) s0) x0`;
                       `t:real`] HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
        REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_RID]];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[] `a = b ==> (f has_real_derivative a) n ==> (f has_real_derivative b) n`) THEN
    USE_THEN "rsc" (fun th -> REWRITE_TAC[MP (SPEC `t:real` th) (ASSUME `t < b:real`)]) THEN
    UNDISCH_TAC `&0 < (h:real->B->real^2^2) t x0$1$1` THEN
    UNDISCH_TAC `&0 < (h:real->B->real^2^2) s0 x0$1$1` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. (h:real->B->real^2^2) t x0$1$1 / h s0 x0$1$1 +
                      mfd_scalar atlas (h s0) x0 * t`;
                 `real_interval(min t s0 - &1,b)`] HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (fun th -> MP_TAC(SPEC `t:real` th) THEN
                                               MP_TAC(SPEC `s0:real` th))) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  USE_THEN "prop" (fun th -> REWRITE_TAC[MP (SPECL [`t:real`; `x:B`] th)
    (CONJ (ASSUME `t < b:real`) (ASSUME `(x:B) IN topspace top`))]) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < (h:real->B->real^2^2) s0 x0$1$1` THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> p2bcl_has_const "mfd_scalar" th &&
                                                 not(is_forall(concl th))))) THEN
  CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* Step (c), the leaf: the level set L = lvs_set V h u of a primitive h of   *)
(* G(X,.) on an open V (X unit and G-parallel) is a smooth Riemannian        *)
(* surface tangent to X-perp; a compact connected surface of constant        *)
(* curvature K0 > 0 is covered by a Cartan pair glued by mu (generic form of *)
(* P2BSS_LEAF_PAIR).                                                         *)
(* ========================================================================= *)

let P2BCL_LEAF_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3) (X:A->real^3) V h u.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\
     (!x. x IN topspace top ==> X x dot (G x ** X x) = &1) /\
     open_in top V /\ p2bkg_prim atlas G X V h
     ==> lvs_regular atlas V h u /\
         lvs_set V h u SUBSET topspace top /\
         topspace(subtopology top (lvs_set V h u)) = lvs_set V h u /\
         smooth_manifold_atlas (subtopology top (lvs_set V h u)) (lvs_atlas top atlas V h u) /\
         riemannian_metric (lvs_atlas top atlas V h u) (lvs_metric top atlas G V h u) /\
         mfd_smooth_map (lvs_atlas top atlas V h u) atlas (lvs_set V h u) (\x. x) /\
         (!x z. x IN lvs_set V h u
                ==> lvs_jac top atlas V h u x z dot (G x ** X x) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(V:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `lvs_regular (atlas:((A->bool)#(A->real^3))->bool) V h u` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BKG_LEVEL_REGULAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `G:A->real^3^3`; `X:A->real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bkg_prim (atlas:((A->bool)#(A->real^3))->bool) G (X:A->real^3) V h` THEN
    REWRITE_TAC[p2bkg_prim] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[lvs_set] THEN ASM SET_TAC[];
    MATCH_MP_TAC LVS_TOPSPACE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LVS_MANIFOLD THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LVS_RIEMANNIAN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LVS_INCLUSION_SMOOTH THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BKL_JAC_TANGENT THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]]);;

let P2BCL_SURFACE_PAIR = prove
 (`!top2 (atlas2:((A->bool)#(A->real^2))->bool) (g2:A->real^2^2) K0 x0.
     hausdorff_space top2 /\ connected_space top2 /\ compact_space top2 /\
     smooth_manifold_atlas top2 atlas2 /\ riemannian_metric atlas2 g2 /\ &0 < K0 /\
     x0 IN topspace top2 /\
     (!x u v. x IN topspace top2 /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional atlas2 g2 x u v = K0)
     ==> ?FS FN.
           mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
             (top2,atlas2) (\x. K0 %% g2 x) (:real^2) FS /\
           mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
             (top2,atlas2) (\x. K0 %% g2 x) (:real^2) FN /\
           (!z. ~(z = Cx(&1)) ==> FN(p2bss_mob z) = FS z) /\
           IMAGE FS (:real^2) UNION IMAGE FN (:real^2) = topspace top2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (atlas2:((A->bool)#(A->real^2))->bool) (\x. K0 %% g2 x)`
  ASSUME_TAC THENL [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x u v. x IN topspace top2 /\ ~collinear {vec 0,u,v}
            ==> mfd_sectional (atlas2:((A->bool)#(A->real^2))->bool) (\x. K0 %% g2 x) x u v = &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top2:A topology`; `atlas2:((A->bool)#(A->real^2))->bool`;
                   `g2:A->real^2^2`; `K0:real`; `x:A`; `u:real^2`; `v:real^2`] P2BSS_SEC_SCALE) THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top2:A topology`; `atlas2:((A->bool)#(A->real^2))->bool`;
                 `\x:A. K0 %% (g2:A->real^2^2) x`; `x0:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:real^2^2`) THEN
  SUBGOAL_THEN `transp(&2 %% E) ** (K0 %% (g2:A->real^2^2) x0) ** (&2 %% E) =
                p2bss_gs (vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `transp(E:real^2^2) ** (K0 %% (g2:A->real^2^2) x0) ** E = mat 1` THEN
    REWRITE_TAC[TRANSP_MATRIX_CMUL; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; p2bss_gs; NORM_0] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&2 %% K0 %% &2 %% (transp (E:real^2^2) ** (g2:A->real^2^2) x0 ** E) =
                  (&2 * &2) %% (K0 %% (transp E ** g2 x0 ** E))` SUBST1_TAC THENL
     [REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top2:A topology`; `atlas2:((A->bool)#(A->real^2))->bool`;
                 `\x:A. K0 %% (g2:A->real^2^2) x`; `x0:A`; `&2 %% (E:real^2^2)`]
                P2BSS_CARTAN_PAIR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` (X_CHOOSE_THEN `L2:real^2^2` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`p2bss_cartan (top2,atlas2) (\x:A. K0 %% (g2:A->real^2^2) x) x0 (&2 %% E)`;
    `p2bss_cartan (top2,atlas2) (\x:A. K0 %% (g2:A->real^2^2) x) q L2`] THEN
  SUBGOAL_THEN
   `mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs (top2,atlas2)
      (\x:A. K0 %% (g2:A->real^2^2) x) (:real^2)
      (p2bss_cartan (top2,atlas2) (\x:A. K0 %% g2 x) x0 (&2 %% E)) /\
    mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs (top2,atlas2)
      (\x:A. K0 %% (g2:A->real^2^2) x) (:real^2)
      (p2bss_cartan (top2,atlas2) (\x:A. K0 %% g2 x) q L2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2BSS_CARTAN_LISOM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BSS_PAIR_ONTO THEN
  MAP_EVERY EXISTS_TAC [`atlas2:((A->bool)#(A->real^2))->bool`; `\x:A. K0 %% (g2:A->real^2^2) x`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Step (c), the model map: generic forms of P2BSS_E_FACTS, P2BSS_E_GRAM and *)
(* P2BSS_PSI_LISOM (pc_p2b_shsplit) for the leaf N = lvs_set V hf s0 of a    *)
(* primitive hf of g(Y,.) on an open V (P2BCL_LEAF_FACTS replaces the        *)
(* shrinker hypotheses).  For a local isometry F of the stereographic plane  *)
(* into (N, k g_N), E z = F(z1,z2) and Psi_F z = Phi_(z3)(E z) is a local    *)
(* isometry (real^3, Bc(inv k)) -> M.  The versions in pc_p2b_shsplit are    *)
(* the instances V = topspace top, hf = p2bss_h.                             *)
(* ========================================================================= *)

let P2BCL_E_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) V hf s0 k
    (Fc:real^2->A).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g Y V hf /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set V hf s0),lvs_atlas top atlas V hf s0)
       (\x. k %% lvs_metric top atlas g V hf s0 x) (:real^2) Fc
     ==> continuous_map (euclidean,top) (\z. Fc(lvs_proj z)) /\
         mfd_smooth_map (open_set_atlas (:real^3)) atlas (:real^3) (\z. Fc(lvs_proj z)) /\
         (!z t. Fc(lvs_proj(z + t % basis 3)) = Fc(lvs_proj z)) /\
         (!w. Fc w IN lvs_set V hf s0) /\
         (!z a. mfd_differential (open_set_atlas (:real^3)) atlas (\z. Fc(lvs_proj z)) z a =
                lvs_jac top atlas V hf s0 (Fc(lvs_proj z))
                  (mfd_differential (open_set_atlas (:real^2))
                     (lvs_atlas top atlas V hf s0) Fc (lvs_proj z) (lvs_proj a)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `V:A->bool`; `hf:A->real`; `s0:real`] P2BCL_LEAF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `N = lvs_set V (hf:A->real) s0` THEN
  ABBREV_TAC `atlasN = lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) V (hf:A->real) s0` THEN
  SUBGOAL_THEN `open_in (euclidean:(real^2)topology) (:real^2) /\
                open_in (euclidean:(real^3)topology) (:real^3)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM OPEN_IN; OPEN_UNIV]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_local_isometry]) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. (Fc:real^2->A) w IN N` ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (euclidean,top) (Fc:real^2->A)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology (subtopology top N) N,top) (\x:A. x)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN REWRITE_TAC[CONTINUOUS_MAP_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology top N) (N:A->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth_map (open_set_atlas (:real^2)) (atlas:((A->bool)#(A->real^3))->bool) (:real^2) (Fc:real^2->A)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(Fc:real^2->A) = (\x:A. x) o Fc` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                         `subtopology top (N:A->bool)`; `atlasN:((A->bool)#(A->real^2))->bool`;
                         `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `(:real^2)`; `N:A->bool`; `Fc:real^2->A`; `\x:A. x`]
                        MFD_SMOOTH_MAP_COMPOSE) THEN
    ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^3. (Fc:real^2->A)(lvs_proj z)) = Fc o lvs_proj` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth_map (open_set_atlas (:real^3)) (open_set_atlas (:real^2)) (:real^3)
                               lvs_proj` ASSUME_TAC THENL
   [REWRITE_TAC[MFD_SMOOTH_MAP_OPEN_SET_ATLAS; IN_UNIV; INTER_UNIV] THEN
    REWRITE_TAC[SET_RULE `{x:real^3 | T} = UNIV`] THEN
    MATCH_MP_TAC LVS_PROJ_SMOOTH THEN REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^2)topology` THEN
    ASM_REWRITE_TAC[LVS_PROJ_CONTINUOUS_MAP];
    MATCH_MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                         `euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                         `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `(:real^3)`; `(:real^2)`; `lvs_proj`; `Fc:real^2->A`]
                        MFD_SMOOTH_MAP_COMPOSE) THEN
    ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; LVS_PROJ_CONTINUOUS_MAP;
                    SUBSET_UNIV];
    REWRITE_TAC[P2BSS_PROJ_SHIFT3];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(:real^3)`; `(:real^2)`; `lvs_proj`; `Fc:real^2->A`; `z:real^3`]
                GEOI_DIFF_COMPOSE) THEN
  ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; LVS_PROJ_CONTINUOUS_MAP; IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM; P2BSS_PROJ_MDIFF] THEN
  MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`;
                 `subtopology top (N:A->bool)`; `atlasN:((A->bool)#(A->real^2))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(:real^2)`; `N:A->bool`; `Fc:real^2->A`; `\x:A. x`; `lvs_proj(z:real^3)`]
                GEOI_DIFF_COMPOSE) THEN
  ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; IN_UNIV] THEN
  SUBGOAL_THEN `(\x:A. x) o (Fc:real^2->A) = Fc` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM] THEN
  EXPAND_TAC "atlasN" THEN REWRITE_TAC[P2BSS_INCL_MDIFF]);;

let P2BCL_E_GRAM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) V hf s0 k
    (Fc:real^2->A).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g Y V hf /\ &0 < k /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set V hf s0),lvs_atlas top atlas V hf s0)
       (\x. k %% lvs_metric top atlas g V hf s0 x) (:real^2) Fc
     ==> !z a.
           mfd_differential (open_set_atlas (:real^3)) atlas (\z. Fc(lvs_proj z)) z a dot
           (g(Fc(lvs_proj z)) **
            mfd_differential (open_set_atlas (:real^3)) atlas (\z. Fc(lvs_proj z)) z a) =
           inv k * (lvs_proj a dot (p2bss_gs (lvs_proj z) ** lvs_proj a)) /\
           mfd_differential (open_set_atlas (:real^3)) atlas (\z. Fc(lvs_proj z)) z a dot
           (g(Fc(lvs_proj z)) ** Y(Fc(lvs_proj z))) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `V:A->bool`; `hf:A->real`; `s0:real`; `k:real`; `Fc:real^2->A`]
                P2BCL_E_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `V:A->bool`; `hf:A->real`; `s0:real`] P2BCL_LEAF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `N = lvs_set V (hf:A->real) s0` THEN
  ABBREV_TAC `atlasN = lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) V (hf:A->real) s0` THEN
  ABBREV_TAC `gN = lvs_metric top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
                              V (hf:A->real) s0` THEN
  ABBREV_TAC `w = lvs_proj(z:real^3)` THEN ABBREV_TAC `v = lvs_proj(a:real^3)` THEN
  ABBREV_TAC `x = (Fc:real^2->A) w` THEN
  ABBREV_TAC `D = mfd_differential (open_set_atlas (:real^2))
                    (atlasN:((A->bool)#(A->real^2))->bool) (Fc:real^2->A) w` THEN
  SUBGOAL_THEN `(x:A) IN N` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `V:A->bool`;
                 `hf:A->real`; `s0:real`; `x:A`] LVS_JAC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MP_TAC(ISPECL [`euclidean:(real^2)topology`; `open_set_atlas (:real^2)`; `p2bss_gs`;
                 `subtopology top (N:A->bool)`; `atlasN:((A->bool)#(A->real^2))->bool`;
                 `\x:A. k %% (gN:A->real^2^2) x`; `(:real^2)`; `Fc:real^2->A`; `w:real^2`]
                GEOH_LISOM_DIFF) THEN
  ASM_SIMP_TAC[P2BSS_GS_FACTS; RIEMANNIAN_METRIC_CMUL; IN_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN `linear(D:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^2)topology`; `subtopology top (N:A->bool)`;
                          `(:real^2)`] THEN
    ASM_REWRITE_TAC[P2BSS_GS_FACTS; IN_UNIV] THEN
    ASM_MESON_TAC[mfd_local_isometry];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM MATRIX_WORKS] THEN
  REWRITE_TAC[P2BSS_CONG_DOT] THEN
  SUBGOAL_THEN `transp(matrix(lvs_jac top (atlas:((A->bool)#(A->real^3))->bool) V
                                   (hf:A->real) s0 x)) **
                (g:A->real^3^3) x **
                matrix(lvs_jac top atlas V hf s0 x) =
                (gN:A->real^2^2) x` SUBST1_TAC THENL
   [EXPAND_TAC "gN" THEN REWRITE_TAC[lvs_metric]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID]);;

let P2BCL_PSI_LISOM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) V hf s0 k
    (Fc:real^2->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g Y V hf /\ &0 < k /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set V hf s0),lvs_atlas top atlas V hf s0)
       (\x. k %% lvs_metric top atlas g V hf s0 x) (:real^2) Fc
     ==> mfd_local_isometry (euclidean,open_set_atlas (:real^3)) (p2bss_bc (inv k)) (top,atlas) g
           (:real^3) (\z. mfd_geo (top,atlas) g (Fc(lvs_proj z)) (Y(Fc(lvs_proj z))) (z$3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `V:A->bool`; `hf:A->real`; `s0:real`; `k:real`; `Fc:real^2->A`]
                P2BCL_E_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dE"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `V:A->bool`; `hf:A->real`; `s0:real`; `k:real`; `Fc:real^2->A`]
                P2BCL_E_GRAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "egram") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `\z:real^3. (Fc:real^2->A)(lvs_proj z)`] P2BSS_PSI_FACTS) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "d3") (LABEL_TAC "dh")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `\z:real^3. (Fc:real^2->A)(lvs_proj z)`] P2BSS_PSI_METRIC) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "gram") THEN
  MATCH_MP_TAC GEOI_LISOM_FROM_DIFF THEN
  ASM_SIMP_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; IN_UNIV; P2BSS_BC_METRIC; REAL_LT_INV] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM OPEN_IN; OPEN_UNIV]; ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN
  ABBREV_TAC `M = mfd_differential (open_set_atlas (:real^3)) (atlas:((A->bool)#(A->real^3))->bool)
                    (\z. mfd_geo (top,atlas) (g:A->real^3^3) ((Fc:real^2->A)(lvs_proj z))
                                 ((Y:A->real^3)(Fc(lvs_proj z))) (z$3)) z` THEN
  ABBREV_TAC `G = (g:A->real^3^3)(mfd_geo (top,atlas) g ((Fc:real^2->A)(lvs_proj z))
                                   ((Y:A->real^3)(Fc(lvs_proj z))) (z$3))` THEN
  SUBGOAL_THEN `linear(M:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `top:A topology`; `(:real^3)`] THEN
    ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; IN_UNIV] THEN
    REWRITE_TAC[GSYM OPEN_IN; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(G:real^3^3) = G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`;
      `mfd_geo (top,atlas) (g:A->real^3^3) ((Fc:real^2->A)(lvs_proj z))
               ((Y:A->real^3)(Fc(lvs_proj z))) (z$3)`] P2BSS_G_AT) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `continuous_map (euclidean,top)
                   (\z. mfd_geo (top,atlas) (g:A->real^3^3) ((Fc:real^2->A)(lvs_proj z))
                                ((Y:A->real^3)(Fc(lvs_proj z))) (z$3))` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(M:real^3->real^3) (basis 3) =
                (Y:A->real^3)(mfd_geo (top,atlas) (g:A->real^3^3) ((Fc:real^2->A)(lvs_proj z))
                                      (Y(Fc(lvs_proj z))) (z$3))` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN USE_THEN "d3" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOI_QUAD_EQ THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM P2BSS_CONG_DOT] THEN
    MATCH_MP_TAC P2BKF_SYM_DOT THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[P2BSS_BC_DOT] THEN
    SUBGOAL_THEN `lvs_proj (v:real^3) dot lvs_proj (u:real^3) = lvs_proj u dot lvs_proj v`
    SUBST1_TAC THENL [MATCH_ACCEPT_TAC DOT_SYM; REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `u:real^3` THEN REWRITE_TAC[GSYM P2BSS_CONG_DOT] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  SUBGOAL_THEN `u = lvs_iota(lvs_proj u) + (u:real^3)$3 % basis 3` SUBST1_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH;
             LVS_IOTA_COMPONENT; LVS_PROJ_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `uh = lvs_iota(lvs_proj(u:real^3))` THEN
  SUBGOAL_THEN `(uh:real^3)$3 = &0 /\ lvs_proj uh = lvs_proj(u:real^3)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "uh" THEN REWRITE_TAC[LVS_IOTA_COMPONENT; LVS_PROJ_IOTA]; ALL_TAC] THEN
  USE_THEN "gram" (MP_TAC o SPECL [`z:real^3`; `uh:real^3`; `uh:real^3`]) THEN
  REWRITE_TAC[ASSUME `(uh:real^3)$3 = &0`] THEN
  USE_THEN "egram" (MP_TAC o SPECL [`z:real^3`; `uh:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(Y:A->real^3)(mfd_geo (top,atlas) (g:A->real^3^3) ((Fc:real^2->A)(lvs_proj z))
                         (Y(Fc(lvs_proj z))) (z$3)) dot (G ** (M:real^3->real^3) uh) = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^3^3`;
                   `(Y:A->real^3)(mfd_geo (top,atlas) (g:A->real^3^3) ((Fc:real^2->A)(lvs_proj z))
                                         (Y(Fc(lvs_proj z))) (z$3))`;
                   `(M:real^3->real^3) uh`] P2BKF_SYM_DOT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lvs_proj(basis 3:real^3) = vec 0` ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; LVS_PROJ_COMPONENT; VEC_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
               DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  REWRITE_TAC[P2BSS_BC_DOT] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; LVS_PROJ_LINEAR; DOT_LZERO; DOT_RZERO; VECTOR_MUL_RZERO;
               VECTOR_ADD_RID; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[p2bss_gs; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Step (c), the glued map: generic forms of P2BSS_PCHART_LISOM,             *)
(* P2BSS_P_LISOM, P2BSS_PSI_T_Y and P2BSS_P_Y for the leaf lvs_set V hf s0:  *)
(* the glued map p2bss_p is a local isometry from (real^3 - 0, G0(c^2)), c = *)
(* sqrt(1/k), to (M, g), and dp_y(y / c) = Y(p y).                           *)
(* ========================================================================= *)

let P2BCL_PCHART_LISOM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) V hf s0 k
    (Fc:real^2->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g Y V hf /\ &0 < k /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set V hf s0),
        lvs_atlas top atlas V hf s0)
       (\x. k %% lvs_metric top atlas g V hf s0 x) (:real^2) Fc
     ==> mfd_local_isometry
           (subtopology euclidean {y:real^3 | ~(norm y = y$3)},
            open_set_atlas {y:real^3 | ~(norm y = y$3)}) (p2bss_g0 (sqrt(inv k) pow 2))
           (top,atlas) g {y:real^3 | ~(norm y = y$3)}
           (p2bss_psi (top,atlas) g Y Fc o p2bss_theta (sqrt(inv k)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(inv k) /\ sqrt(inv k) pow 2 = inv k` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(SPEC `sqrt(inv k)` P2BSS_THETA_LISOM) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `V:A->bool`; `hf:A->real`; `s0:real`; `k:real`; `Fc:real^2->A`]
                P2BCL_PSI_LISOM) THEN
  ASM_REWRITE_TAC[GSYM P2BSS_PSI_ETA] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2BSS_LISOM_COMPOSE THEN
  MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                        `p2bss_bc (inv k)`; `(:real^3)`] THEN
  ASM_REWRITE_TAC[IN_UNIV; GEOI_EUCLIDEAN_ATLAS] THEN
  ASM_SIMP_TAC[P2BSS_BC_METRIC; REAL_LT_INV] THEN
  MATCH_MP_TAC P2BSS_G0_RIEMANNIAN THEN
  REWRITE_TAC[P2BPC_OFF_RAY_OPEN; P2BSS_ZE1_OPEN] THEN
  ASM_SIMP_TAC[REAL_LT_INV]);;


let P2BCL_P_LISOM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) V hf s0 k FS FN.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g Y V hf /\ &0 < k /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set V hf s0),
        lvs_atlas top atlas V hf s0)
       (\x. k %% lvs_metric top atlas g V hf s0 x) (:real^2) FS /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set V hf s0),
        lvs_atlas top atlas V hf s0)
       (\x. k %% lvs_metric top atlas g V hf s0 x) (:real^2) FN /\
     (!z. ~(z = Cx(&1)) ==> FN(p2bss_mob z) = FS z)
     ==> mfd_local_isometry
           (subtopology euclidean {y:real^3 | ~(y = vec 0)},
            open_set_atlas {y:real^3 | ~(y = vec 0)}) (p2bss_g0 (sqrt(inv k) pow 2))
           (top,atlas) g {y:real^3 | ~(y = vec 0)}
           (p2bss_p (top,atlas) g Y FS FN (sqrt(inv k)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = sqrt(inv k)` THEN
  SUBGOAL_THEN `&0 < c pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LT_INV]; ALL_TAC] THEN
  ABBREV_TAC `Z = {y:real^3 | ~(y = vec 0)}` THEN
  ABBREV_TAC `Zn = {y:real^3 | ~(norm y = y$3)}` THEN
  ABBREV_TAC `Ze1 = {y:real^3 | ~(norm y = y$1)}` THEN
  MP_TAC P2BSS_ZSETS THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. y IN Z ==> y IN Zn \/ y IN Ze1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Z"; "Zn"; "Ze1"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN Z ==> ~(y = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Fc. mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
           (subtopology top (lvs_set V (hf:A->real) s0),
            lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) V hf s0)
           (\x. k %% lvs_metric top atlas (g:A->real^3^3) V hf s0 x)
           (:real^2) Fc
         ==> mfd_local_isometry (subtopology euclidean Zn,open_set_atlas Zn) (p2bss_g0 (c pow 2))
               (top,atlas) g Zn (p2bss_psi (top,atlas) g Y Fc o p2bss_theta c)`
  (LABEL_TAC "chart") THENL
   [GEN_TAC THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["Zn"; "c"] THEN
    MATCH_MP_TAC P2BCL_PCHART_LISOM THEN
    MAP_EVERY EXISTS_TAC [`V:A->bool`; `hf:A->real`; `s0:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_local_isometry (subtopology euclidean Ze1,open_set_atlas Ze1) (p2bss_g0 (c pow 2))
      (top,atlas) (g:A->real^3^3) Ze1
      ((p2bss_psi (top,atlas) g (Y:A->real^3) FN o p2bss_theta c) o p2bss_qinv)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_LISOM_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (Zn:real^3->bool)`; `open_set_atlas (Zn:real^3->bool)`;
                          `p2bss_g0 (c pow 2)`; `Zn:real^3->bool`] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(SPEC `c pow 2` P2BSS_QINV_LISOM) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!S. open S /\ S SUBSET (Z:real^3->bool)
                      ==> smooth_manifold_atlas (subtopology euclidean S) (open_set_atlas S) /\
                          riemannian_metric (open_set_atlas S) (p2bss_g0 (c pow 2))`
    ASSUME_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2BSS_G0_RIEMANNIAN THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["Ze1"; "Zn"] THEN REWRITE_TAC[IN_ELIM_THM; P2BSS_QINV_ZN];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOH_LISOM_LOCAL THEN ASM_SIMP_TAC[OPEN_SET_ATLAS] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; SUBSET_REFL]; ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(y:real^3) IN Zn` THENL
   [MAP_EVERY EXISTS_TAC [`Zn:real^3->bool`;
                          `p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FS o p2bss_theta c`] THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`Zn:real^3->bool`; `Z:real^3->bool`; `Zn:real^3->bool`; `p2bss_g0 (c pow 2)`;
                     `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FS o p2bss_theta c`]
                    P2BSS_LISOM_OPEN_SET_MONO) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "chart" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[p2bss_p; o_THM] THEN X_GEN_TAC `w:real^3` THEN
      EXPAND_TAC "Zn" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN Ze1` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Ze1:real^3->bool`;
                        `(p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FN o p2bss_theta c) o
                         p2bss_qinv`] THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_EQ] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`Ze1:real^3->bool`; `Z:real^3->bool`; `Ze1:real^3->bool`; `p2bss_g0 (c pow 2)`;
                   `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `(p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FN o p2bss_theta c) o
                    p2bss_qinv`] P2BSS_LISOM_OPEN_SET_MONO) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2bss_p; o_THM] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BSS_GLUE THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(w:real^3) IN Ze1` THEN EXPAND_TAC "Ze1" THEN SIMP_TAC[IN_ELIM_THM]);;

let P2BCL_PSI_T_Y = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) V hf s0 k
    (Fc:real^2->A) Z' (Tc:real^3->real^3) y v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g Y V hf /\ &0 < k /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set V hf s0),
        lvs_atlas top atlas V hf s0)
       (\x. k %% lvs_metric top atlas g V hf s0 x) (:real^2) Fc /\
     open Z' /\ y IN Z' /\
     continuous_map (subtopology euclidean Z',euclidean) Tc /\
     mfd_smooth_map (open_set_atlas Z') (open_set_atlas (:real^3)) Z' Tc /\
     frechet_derivative Tc (at y) v = basis 3
     ==> mfd_differential (open_set_atlas Z') atlas (p2bss_psi (top,atlas) g Y Fc o Tc) y v =
         Y(p2bss_psi (top,atlas) g Y Fc (Tc y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `V:A->bool`; `hf:A->real`; `s0:real`; `k:real`; `Fc:real^2->A`]
                P2BCL_PSI_LISOM) THEN
  ASM_REWRITE_TAC[GSYM P2BSS_PSI_ETA; mfd_local_isometry; SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `V:A->bool`; `hf:A->real`; `s0:real`; `k:real`; `Fc:real^2->A`]
                P2BCL_E_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `Y:A->real^3`; `\z:real^3. (Fc:real^2->A)(lvs_proj z)`] P2BSS_PSI_FACTS) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[GSYM P2BSS_PSI_ETA] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (Z':real^3->bool)`; `open_set_atlas (Z':real^3->bool)`;
                 `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `Z':real^3->bool`; `(:real^3)`; `Tc:real^3->real^3`;
                 `p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) Fc`; `y:real^3`]
                GEOI_DIFF_COMPOSE) THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; IN_UNIV;
               SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT; OPEN_IN_OPEN_EQ; SUBSET_REFL] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[o_THM] THEN
  ASM_SIMP_TAC[CMPW_PM_DIFF; MFDD_OPEN_SET_CHART_AT; IN_UNIV; ETA_AX] THEN
  REWRITE_TAC[p2bss_psi]);;


let P2BCL_P_Y = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) V hf s0 k FS FN.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) Y /\
     (!x. x IN topspace top ==> Y x dot (g x ** Y x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g Y V hf /\ &0 < k /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set V hf s0),
        lvs_atlas top atlas V hf s0)
       (\x. k %% lvs_metric top atlas g V hf s0 x) (:real^2) FS /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set V hf s0),
        lvs_atlas top atlas V hf s0)
       (\x. k %% lvs_metric top atlas g V hf s0 x) (:real^2) FN /\
     (!z. ~(z = Cx(&1)) ==> FN(p2bss_mob z) = FS z)
     ==> !y. ~(y = vec 0)
             ==> mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas
                   (p2bss_p (top,atlas) g Y FS FN (sqrt(inv k))) y (inv(sqrt(inv k)) % y) =
                 Y(p2bss_p (top,atlas) g Y FS FN (sqrt(inv k)) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  ABBREV_TAC `c = sqrt(inv k)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV]; ALL_TAC] THEN
  MP_TAC P2BSS_ZSETS THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:real` P2BSS_THETA_LISOM) THEN
  ASM_REWRITE_TAC[mfd_local_isometry; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(SPEC `c pow 2` P2BSS_QINV_LISOM) THEN
  ASM_REWRITE_TAC[mfd_local_isometry; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN STRIP_TAC THEN
  ASM_CASES_TAC `~(norm(y:real^3) = y$3)` THENL
   [MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `{y:real^3 | ~(y = vec 0)}`;
                   `{y:real^3 | ~(norm y = y$3)}`;
                   `p2bss_p (top,atlas) (g:A->real^3^3) (Y:A->real^3) FS FN c`;
                   `p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FS o p2bss_theta c`;
                   `y:real^3`] P2BSS_MDIFF_LOCAL) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [SIMP_TAC[p2bss_p; o_THM]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(Y:A->real^3)(p2bss_psi (top,atlas) (g:A->real^3^3) Y FS (p2bss_theta c y))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BCL_PSI_T_Y THEN
      MAP_EVERY EXISTS_TAC [`V:A->bool`; `hf:A->real`; `s0:real`; `k:real`] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN EXPAND_TAC "c" THEN
      MATCH_MP_TAC P2BSS_DTHETA_RADIAL THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "c" THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV];
      ASM_REWRITE_TAC[p2bss_p]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(norm(y:real^3) = y$1)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN {y:real^3 | ~(norm y = y$1)}
                ==> p2bss_p (top,atlas) (g:A->real^3^3) (Y:A->real^3) FS FN c w =
                    (p2bss_psi (top,atlas) g Y FN o (p2bss_theta c o p2bss_qinv)) w`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM; p2bss_p] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P2BSS_GLUE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `{y:real^3 | ~(y = vec 0)}`;
                 `{y:real^3 | ~(norm y = y$1)}`;
                 `p2bss_p (top,atlas) (g:A->real^3^3) (Y:A->real^3) FS FN c`;
                 `p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FN o
                  (p2bss_theta c o p2bss_qinv)`;
                 `y:real^3`] P2BSS_MDIFF_LOCAL) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`c:real`; `y:real^3`] P2BSS_THETA_QINV_DERIV) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean {y:real^3 | ~(norm y = y$1)},euclidean)
                   (p2bss_theta c o p2bss_qinv) /\
    mfd_smooth_map (open_set_atlas {y:real^3 | ~(norm y = y$1)}) (open_set_atlas (:real^3))
                   {y:real^3 | ~(norm y = y$1)} (p2bss_theta c o p2bss_qinv)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean {y:real^3 | ~(norm y = y$3)}` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ISPECL [`subtopology euclidean {y:real^3 | ~(norm y = y$1)}`;
                           `open_set_atlas {y:real^3 | ~(norm y = y$1)}`;
                           `subtopology euclidean {y:real^3 | ~(norm y = y$3)}`;
                           `open_set_atlas {y:real^3 | ~(norm y = y$3)}`;
                           `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                           `{y:real^3 | ~(norm y = y$1)}`; `{y:real^3 | ~(norm y = y$3)}`;
                           `p2bss_qinv`; `p2bss_theta c`] MFD_SMOOTH_MAP_COMPOSE) THEN
      ASM_SIMP_TAC[OPEN_SET_ATLAS; GEOI_EUCLIDEAN_ATLAS; OPEN_IN_OPEN_EQ; SUBSET_REFL;
                   SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; P2BSS_QINV_ZN]];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[o_THM]
   (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
            `Y:A->real^3`; `V:A->bool`; `hf:A->real`; `s0:real`; `k:real`; `FN:real^2->A`;
            `{y:real^3 | ~(norm y = y$1)}`; `p2bss_theta c o p2bss_qinv`; `y:real^3`;
            `inv c % (y:real^3)`] P2BCL_PSI_T_Y)) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; o_THM] THEN EXPAND_TAC "c" THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* Step (c), orbits: p y = Phi_(c log|y|)(z) with z in the leaf L, and p     *)
(* maps real^3 - 0 onto M when every point of M lies on the orbit of a point *)
(* of L (the orbit form of P2BSS_P_ONTO).                                    *)
(* ========================================================================= *)

let P2BCL_P_PHI = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) FS FN c L y.
     (!w. FS w IN L) /\ (!w. FN w IN L)
     ==> ?z:A. z IN L /\
               p2bss_p (top,atlas) g Y FS FN c y =
               p2bkf_phi (top,atlas) g Y (c * log(norm y)) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2bss_p; P2BSS_PSI_PHI] THEN
  COND_CASES_TAC THEN REWRITE_TAC[P2BSS_THETA_COMPONENTS; P2BSS_QINV_FACTS] THEN
  ASM_MESON_TAC[]);;

let P2BCL_P_ONTO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (Y:A->real^3) FS FN c L.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) Y /\ ~(c = &0) /\
     L SUBSET topspace top /\
     IMAGE FS (:real^2) UNION IMAGE FN (:real^2) = L /\
     (!z. ~(z = Cx(&1)) ==> FN(p2bss_mob z) = FS z) /\
     (!x. x IN topspace top ==> ?r z. z IN L /\ p2bkf_phi (top,atlas) g Y r z = x)
     ==> IMAGE (p2bss_p (top,atlas) g Y FS FN c) {y:real^3 | ~(y = vec 0)} = topspace top`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!w. (FS:real^2->A) w IN L) /\ (!w. (FN:real^2->A) w IN L)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `IMAGE (FS:real^2->A) (:real^2) UNION IMAGE FN (:real^2) = L`) THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Y:A->real^3`; `FS:real^2->A`; `FN:real^2->A`; `c:real`; `L:A->bool`;
                   `y:real^3`] P2BCL_P_PHI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `Y:A->real^3`; `c * log(norm(y:real^3))`; `z:A`] P2BKF_PHI_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:A) IN topspace top`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(x0:A) IN L` THEN
  SUBST1_TAC(SYM(ASSUME `IMAGE (FS:real^2->A) (:real^2) UNION IMAGE FN (:real^2) = L`)) THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE; IN_UNIV] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `w:real^2` (ASSUME_TAC o SYM))) THENL
   [EXISTS_TAC `p2bss_xi c (vector[(w:real^2)$1; w$2; t])` THEN CONJ_TAC THENL
     [REWRITE_TAC[p2bss_p] THEN ASM_SIMP_TAC[P2BSS_XI_ZN; P2BSS_THETA_XI] THEN
      REWRITE_TAC[P2BSS_PSI_PHI; P2BSS_PROJ3] THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`c:real`; `vector[(w:real^2)$1; w$2; t]:real^3`] P2BSS_XI_ZN) THEN
      ASM_REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[NORM_0; VEC_COMPONENT]];
    ALL_TAC] THEN
  EXISTS_TAC `p2bss_qrot (p2bss_xi c (vector[(w:real^2)$1; w$2; t]))` THEN
  SUBGOAL_THEN `~(norm(p2bss_xi c (vector[(w:real^2)$1; w$2; t])) =
                  p2bss_xi c (vector[w$1; w$2; t])$3)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2BSS_XI_ZN]; ALL_TAC] THEN
  ABBREV_TAC `u = p2bss_xi c (vector[(w:real^2)$1; w$2; t])` THEN
  SUBGOAL_THEN `p2bss_qinv(p2bss_qrot u) = u /\ norm(p2bss_qrot u) = norm u /\
                ~(norm(p2bss_qrot u) = p2bss_qrot u$1)` STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[P2BSS_QINV_ZN] THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2 P2BSS_QINV_FACTS)] THEN
    ASM_REWRITE_TAC[P2BSS_QINV_FACTS];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `~(norm(p2bss_qrot u) = p2bss_qrot u$1)` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NORM_0; VEC_COMPONENT]] THEN
  SUBGOAL_THEN `p2bss_psi (top,atlas) (g:A->real^3^3) (Y:A->real^3) FN
                  (p2bss_theta c (p2bss_qinv (p2bss_qrot u))) = x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `p2bss_xi c (vector[(w:real^2)$1; w$2; t]) = u`)) THEN
    ASM_SIMP_TAC[P2BSS_THETA_XI] THEN
    REWRITE_TAC[P2BSS_PSI_PHI; P2BSS_PROJ3] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2bss_p] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC P2BSS_GLUE THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Step (d), the metric identity: on X-perp the metrics scale with the leaf  *)
(* flow, so g(t) = a g(s0) + (1 - a) w w^T, w = g(s0) X, a = 1 - R(s0) (t -  *)
(* s0): first at the points of the leaf (two quadratic forms agreeing on the *)
(* leaf tangents, on X and with no cross terms), then at every point by      *)
(* transport along the X-flow (the flow charts p2bkf_fmap preserve every     *)
(* metric for which X is parallel).                                          *)
(* ========================================================================= *)

let P2BCL_OUTER_MUL = prove
 (`!(w:real^3) v. ((lambda i j. w$i * w$j):real^3^3) ** v = (w dot v) % w`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA; VECTOR_MUL_COMPONENT; dot] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; SUM_3] THEN REAL_ARITH_TAC);;

let P2BCL_OUTER_FORM = prove
 (`!(G0:real^3^3) (w:real^3) a u v.
     u dot ((a %% G0 + (&1 - a) %% (lambda i j. w$i * w$j)) ** v) =
     a * (u dot (G0 ** v)) + (&1 - a) * ((w dot u) * (w dot v))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL; P2BCL_OUTER_MUL;
              DOT_RADD; DOT_RMUL] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_RING);;

let P2BCL_SPLIT_FORM_EQ = prove
 (`!(G1:real^3^3) (G0:real^3^3) (J:real^2->real^3) (Xv:real^3) (w:real^3) a.
     transp G1 = G1 /\ transp G0 = G0 /\ linear J /\
     (!v. J v = vec 0 ==> v = vec 0) /\
     G1 ** Xv = w /\ G0 ** Xv = w /\ Xv dot w = &1 /\
     (!v. J v dot w = &0) /\
     (!v. J v dot (G1 ** J v) = a * (J v dot (G0 ** J v)))
     ==> G1 = a %% G0 + (&1 - a) %% (lambda i j. w$i * w$j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Tm = \z:real^3. (J:real^2->real^3)(lvs_proj z) + z$3 % (Xv:real^3)` THEN
  SUBGOAL_THEN `linear(Tm:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "Tm" THEN REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; LVS_PROJ_LINEAR; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. ?z. (Tm:real^3->real^3) z = y` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_INJECTIVE_IMP_SURJECTIVE THEN ASM_SIMP_TAC[LINEAR_INJECTIVE_0] THEN
    X_GEN_TAC `z:real^3` THEN EXPAND_TAC "Tm" THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3)$3 = &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. v dot (w:real^3)`) THEN
      ASM_REWRITE_TAC[DOT_LADD; DOT_LMUL; DOT_LZERO] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `lvs_proj(z:real^3) = vec 0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(J:real^2->real^3)(lvs_proj z) + (z:real^3)$3 % (Xv:real^3) = vec 0` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    UNDISCH_TAC `(z:real^3)$3 = &0` THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; LVS_PROJ_COMPONENT;
                VEC_COMPONENT] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. (Xv:real^3) dot ((G1:real^3^3) ** (J:real^2->real^3) v) = &0 /\
                    Xv dot ((G0:real^3^3) ** J v) = &0`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`G1:real^3^3`; `Xv:real^3`; `(J:real^2->real^3) v`] P2BKF_SYM_DOT);
      MP_TAC(ISPECL [`G0:real^3^3`; `Xv:real^3`; `(J:real^2->real^3) v`] P2BKF_SYM_DOT)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOI_QUAD_EQ THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2BKF_SYM_DOT THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[P2BCL_OUTER_FORM] THEN
    MP_TAC(ISPECL [`G0:real^3^3`; `u:real^3`; `v:real^3`] P2BKF_SYM_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `p:real^3` THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `z:real^3` (SUBST1_TAC o SYM) o SPEC `p:real^3` o
    check (fun th -> is_forall(concl th) && is_exists(snd(dest_forall(concl th))))) THEN
  EXPAND_TAC "Tm" THEN REWRITE_TAC[P2BCL_OUTER_FORM] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_LADD; DOT_RADD;
              DOT_LMUL; DOT_RMUL] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RING);;

let P2BCL_LEAF_SCALE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) b (X:A->real^3) V h u
    s0 x0.
     (!a. a < b ==> ricci_flow_on (top,atlas) a b g) /\ open_in top V /\
     (!s. s < b ==> p2b_parallel_on atlas (g s) (topspace top) X /\
                    (!y. y IN topspace top ==> X y dot (g s y ** X y) = &1) /\
                    p2bkg_prim atlas (g s) X V h) /\
     (!s y z. s < b /\ y IN lvs_set V h u /\ z IN lvs_set V h u
              ==> mfd_scalar atlas (g s) y = mfd_scalar atlas (g s) z) /\
     s0 < b /\ x0 IN lvs_set V h u
     ==> !t x. t < b /\ x IN lvs_set V h u
               ==> lvs_metric top atlas (g t) V h u x =
                   (&1 - mfd_scalar atlas (g s0) x0 * (t - s0)) %%
                   lvs_metric top atlas (g s0) V h u x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `b:real`; `X:A->real^3`; `V:A->bool`; `h:A->real`;
                 `u:real`] P2BKL_LEAF_FLOW_ALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [MP_TAC(SPEC `s0 - &1`
      (ASSUME `!a. a < b ==> ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[ricci_flow_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool)
                                  ((g:real->A->real^3^3) s0)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BKL_RF_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if p2bcl_has_const "p2bkg_prim" th && is_forall(concl th)
    then STRIP_ASSUME_TAC(MP (SPEC `s0:real` th) (ASSUME `s0 < b`)) else NO_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) s0`; `X:A->real^3`; `V:A->bool`; `h:A->real`;
                 `u:real`] P2BCL_LEAF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set V (h:A->real) u)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) V (h:A->real) u`;
                 `\t. lvs_metric top (atlas:((A->bool)#(A->real^3))->bool)
                                 ((g:real->A->real^3^3) t) V (h:A->real) u`;
                 `b:real`; `s0:real`; `x0:A`] P2BCL_FLOW2_SCALE) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`]) THEN ASM_SIMP_TAC[]);;

let P2BCL_LEAF_METRIC_ID = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) b (X:A->real^3) V h u
    s0 x0.
     (!a. a < b ==> ricci_flow_on (top,atlas) a b g) /\ open_in top V /\
     (!s. s < b ==> p2b_parallel_on atlas (g s) (topspace top) X /\
                    (!y. y IN topspace top ==> X y dot (g s y ** X y) = &1) /\
                    p2bkg_prim atlas (g s) X V h) /\
     (!s y. s < b /\ y IN topspace top ==> g s y ** X y = g s0 y ** X y) /\
     (!s y z. s < b /\ y IN lvs_set V h u /\ z IN lvs_set V h u
              ==> mfd_scalar atlas (g s) y = mfd_scalar atlas (g s) z) /\
     s0 < b /\ x0 IN lvs_set V h u
     ==> !t x. t < b /\ x IN lvs_set V h u
               ==> g t x =
                   (&1 - mfd_scalar atlas (g s0) x0 * (t - s0)) %% g s0 x +
                   (&1 - (&1 - mfd_scalar atlas (g s0) x0 * (t - s0))) %%
                   (lambda i j. (g s0 x ** X x)$i * (g s0 x ** X x)$j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN X_GEN_TAC `x:A` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `b:real`; `X:A->real^3`; `V:A->bool`; `h:A->real`;
                 `u:real`; `s0:real`; `x0:A`] P2BCL_LEAF_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:A`]) THEN
  ASM_REWRITE_TAC[lvs_metric] THEN DISCH_TAC THEN
  ABBREV_TAC `a = &1 - mfd_scalar atlas ((g:real->A->real^3^3) s0) x0 * (t - s0)` THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [MP_TAC(SPEC `s0 - &1`
      (ASSUME `!a. a < b ==> ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[ricci_flow_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool)
                                  ((g:real->A->real^3^3) s0) /\
                riemannian_metric atlas (g t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2BKL_RF_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if p2bcl_has_const "p2bkg_prim" th && is_forall(concl th)
    then STRIP_ASSUME_TAC(MP (SPEC `s0:real` th) (ASSUME `s0 < b`)) else NO_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) s0`; `X:A->real^3`; `V:A->bool`; `h:A->real`;
                 `u:real`] P2BCL_LEAF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `V:A->bool`;
                 `h:A->real`; `u:real`; `x:A`] LVS_JAC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BCL_SPLIT_FORM_EQ THEN
  MAP_EVERY EXISTS_TAC [`lvs_jac top (atlas:((A->bool)#(A->real^3))->bool) V (h:A->real) u x`;
                        `(X:A->real^3) x`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `x:A`] P2BSS_G_AT) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) s0`; `x:A`] P2BSS_G_AT) THEN
    ASM_SIMP_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^2` THEN
  MP_TAC(ISPECL [`matrix(lvs_jac top (atlas:((A->bool)#(A->real^3))->bool) V (h:A->real) u x)`;
                 `(g:real->A->real^3^3) t x`; `v:real^2`; `v:real^2`] P2BSS_CONG_DOT) THEN
  MP_TAC(ISPECL [`matrix(lvs_jac top (atlas:((A->bool)#(A->real^3))->bool) V (h:A->real) u x)`;
                 `(g:real->A->real^3^3) s0 x`; `v:real^2`; `v:real^2`] P2BSS_CONG_DOT) THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL]);;

let P2BCL_TRANSPORT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G0:A->real^3^3) (G1:A->real^3^3) (X:A->real^3)
    a z r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas G0 /\
     mfd_complete (top,atlas) G0 /\ p2b_parallel_on atlas G0 (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (G0 x ** X x) = &1) /\
     riemannian_metric atlas G1 /\ p2b_parallel_on atlas G1 (topspace top) X /\
     z IN topspace top /\
     G1 z = a %% G0 z + (&1 - a) %% (lambda i j. (G0 z ** X z)$i * (G0 z ** X z)$j)
     ==> G1 (p2bkf_phi (top,atlas) G0 X r z) =
         a %% G0 (p2bkf_phi (top,atlas) G0 X r z) +
         (&1 - a) %% (lambda i j. (G0 (p2bkf_phi (top,atlas) G0 X r z) **
                                   X (p2bkf_phi (top,atlas) G0 X r z))$i *
                                  (G0 (p2bkf_phi (top,atlas) G0 X r z) **
                                   X (p2bkf_phi (top,atlas) G0 X r z))$j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(G0:A->real^3^3) z ** (X:A->real^3) z`; `(X:A->real^3) z`]
                P2BKF_HCOMPLEMENT) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `u2:real^3` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `fm = p2bkf_fmap (top,atlas) (G0:A->real^3^3) (X:A->real^3) z u1 u2` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G0:A->real^3^3`;
                 `X:A->real^3`; `z:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(fm:real^3->A) (vec 0) = z` ASSUME_TAC THENL
   [EXPAND_TAC "fm" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `G0:A->real^3^3`; `X:A->real^3`; `z:A`; `u1:real^3`; `u2:real^3`;
                   `vec 0:real^3`] P2BKF_FMAP_D0) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas (:real^3)) atlas (fm:real^3->A) (vec 0) (basis 3) =
    (X:A->real^3) z /\
    (!q. mfd_differential (open_set_atlas (:real^3)) atlas (fm:real^3->A) (vec 0) q = vec 0
         ==> q = vec 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "fm" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `G0:A->real^3^3`; `X:A->real^3`; `z:A`; `u1:real^3`; `u2:real^3`;
                     `basis 3:real^3`] P2BKF_FMAP_D0) THEN
      ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_MUL_LID];
      X_GEN_TAC `q:real^3` THEN EXPAND_TAC "fm" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `G0:A->real^3^3`; `X:A->real^3`; `z:A`; `u1:real^3`; `u2:real^3`;
                     `q:real^3`] P2BKF_FMAP_D0) THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(q:real^3)$1`; `(q:real^3)$2`; `(q:real^3)$3`] o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> try fst(dest_var t) = "u1"
                                                  with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(fm:real^3->A)(r % basis 3) = p2bkf_phi (top,atlas) G0 (X:A->real^3) r z`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G0:A->real^3^3`;
                   `X:A->real^3`; `z:A`; `u1:real^3`; `u2:real^3`; `vec 0:real^3`; `r:real`]
                  P2BKF_FMAP_SHIFT) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G0:A->real^3^3`;
                 `X:A->real^3`; `r:real`; `z:A`] P2BKF_PHI_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `y = p2bkf_phi (top,atlas) (G0:A->real^3^3) (X:A->real^3) r z` THEN
  ABBREV_TAC `D0 = mfd_differential (open_set_atlas (:real^3)) (atlas:((A->bool)#(A->real^3))->bool)
                                    (fm:real^3->A) (vec 0)` THEN
  ABBREV_TAC `Dr = mfd_differential (open_set_atlas (:real^3)) (atlas:((A->bool)#(A->real^3))->bool)
                                    (fm:real^3->A) (r % basis 3)` THEN
  SUBGOAL_THEN
   `!p q. (Dr:real^3->real^3) p dot ((G0:A->real^3^3) y ** Dr q) =
          (D0:real^3->real^3) p dot (G0 z ** D0 q) /\
          Dr p dot ((G1:A->real^3^3) y ** Dr q) = D0 p dot (G1 z ** D0 q)`
  (LABEL_TAC "inv") THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `G0:A->real^3^3`; `G0:A->real^3^3`; `X:A->real^3`; `z:A`; `u1:real^3`;
                     `u2:real^3`; `vec 0:real^3`; `r:real`; `p:real^3`; `q:real^3`]
                    P2BKF_FMAP_METRIC_INV2);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `G0:A->real^3^3`; `G1:A->real^3^3`; `X:A->real^3`; `z:A`; `u1:real^3`;
                     `u2:real^3`; `vec 0:real^3`; `r:real`; `p:real^3`; `q:real^3`]
                    P2BKF_FMAP_METRIC_INV2)] THEN
    ASM_REWRITE_TAC[VECTOR_ADD_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Dr:real^3->real^3) (basis 3) = (X:A->real^3) y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `G0:A->real^3^3`; `X:A->real^3`; `z:A`; `u1:real^3`; `u2:real^3`;
                   `r % basis 3:real^3`] P2BKF_FMAP_D3) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(Dr:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "Dr" THEN MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `top:A topology`; `(:real^3)`] THEN
    ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; SUBTOPOLOGY_UNIV; IN_UNIV] THEN
    REWRITE_TAC[GSYM OPEN_IN; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^3. ?q. (Dr:real^3->real^3) q = p` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_INJECTIVE_IMP_SURJECTIVE THEN ASM_SIMP_TAC[LINEAR_INJECTIVE_0] THEN
    X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_var t) = "D0" with Failure _ -> false)) (concl th) &&
      not(can (find_term (fun t -> try fst(dest_var t) = "Dr" with Failure _ -> false))
              (concl th)))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `G0:A->real^3^3`; `z:A`] P2BSS_G_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `(D0:real^3->real^3) q` o CONJUNCT1 o CONJUNCT2) THEN
    USE_THEN "inv" (MP_TAC o CONJUNCT1 o SPECL [`q:real^3`; `q:real^3`]) THEN
    REWRITE_TAC[ASSUME `(Dr:real^3->real^3) q = vec 0`; MATRIX_VECTOR_MUL_RZERO; DOT_LZERO] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOI_QUAD_EQ THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2BKF_SYM_DOT THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `G1:A->real^3^3`; `y:A`] P2BSS_G_AT) THEN
    ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[P2BCL_OUTER_FORM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `G0:A->real^3^3`; `y:A`] P2BSS_G_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(G0:A->real^3^3) y`; `u:real^3`; `v:real^3`] P2BKF_SYM_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `p:real^3` THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:real^3` (SUBST1_TAC o SYM) o SPEC `p:real^3` o
    check (fun th -> is_forall(concl th) && is_exists(snd(dest_forall(concl th))))) THEN
  REWRITE_TAC[P2BCL_OUTER_FORM] THEN
  SUBGOAL_THEN `((G0:A->real^3^3) y ** (X:A->real^3) y) dot (Dr:real^3->real^3) q =
                (G0 z ** X z) dot (D0:real^3->real^3) q` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN
    SUBST1_TAC(SYM(ASSUME `(Dr:real^3->real^3) (basis 3) = (X:A->real^3) y`)) THEN
    SUBST1_TAC(SYM(ASSUME `(D0:real^3->real^3) (basis 3) = (X:A->real^3) z`)) THEN
    USE_THEN "inv" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  USE_THEN "inv" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[P2BCL_OUTER_FORM]);;

let P2BCL_METRIC_ID = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) b (X:A->real^3) V h u
    s0 x0.
     hausdorff_space top /\
     (!a. a < b ==> ricci_flow_on (top,atlas) a b g) /\
     (!s. s < b ==> mfd_complete (top,atlas) (g s)) /\ open_in top V /\
     (!s. s < b ==> p2b_parallel_on atlas (g s) (topspace top) X /\
                    (!y. y IN topspace top ==> X y dot (g s y ** X y) = &1) /\
                    p2bkg_prim atlas (g s) X V h) /\
     (!s y. s < b /\ y IN topspace top ==> g s y ** X y = g s0 y ** X y) /\
     (!s y z. s < b /\ y IN lvs_set V h u /\ z IN lvs_set V h u
              ==> mfd_scalar atlas (g s) y = mfd_scalar atlas (g s) z) /\
     (!y. y IN topspace top
          ==> ?r z. z IN lvs_set V h u /\ p2bkf_phi (top,atlas) (g s0) X r z = y) /\
     s0 < b /\ x0 IN lvs_set V h u
     ==> !t y. t < b /\ y IN topspace top
               ==> g t y =
                   (&1 - mfd_scalar atlas (g s0) x0 * (t - s0)) %% g s0 y +
                   (&1 - (&1 - mfd_scalar atlas (g s0) x0 * (t - s0))) %%
                   (lambda i j. (g s0 y ** X y)$i * (g s0 y ** X y)$j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN X_GEN_TAC `y:A` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:A) IN topspace top`) o
    check (fun th -> p2bcl_has_const "p2bkf_phi" th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `p2bkf_phi (top,atlas) ((g:real->A->real^3^3) s0) (X:A->real^3) r z = y` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [MP_TAC(SPEC `s0 - &1`
      (ASSUME `!a. a < b ==> ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[ricci_flow_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool)
                                  ((g:real->A->real^3^3) s0) /\
                riemannian_metric atlas (g t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2BKL_RF_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if p2bcl_has_const "p2bkg_prim" th && is_forall(concl th)
    then STRIP_ASSUME_TAC(MP (SPEC `s0:real` th) (ASSUME `s0 < b`)) else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if p2bcl_has_const "p2bkg_prim" th && is_forall(concl th)
    then STRIP_ASSUME_TAC(MP (SPEC `t:real` th) (ASSUME `t < b`)) else NO_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) s0`; `X:A->real^3`; `V:A->bool`; `h:A->real`;
                 `u:real`] P2BCL_LEAF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ASSUME `lvs_set V (h:A->real) u SUBSET topspace top`) THEN
    MP_TAC(ASSUME `(z:A) IN lvs_set V h u`) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_complete (top,atlas) ((g:real->A->real^3^3) s0)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if p2bcl_has_const "mfd_complete" th && is_forall(concl th)
      then ACCEPT_TAC(MP (SPEC `s0:real` th) (ASSUME `s0 < b`)) else NO_TAC);
    ALL_TAC] THEN
  MATCH_MP_TAC P2BCL_TRANSPORT THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `b:real`; `X:A->real^3`; `V:A->bool`; `h:A->real`;
                 `u:real`; `s0:real`; `x0:A`] P2BCL_LEAF_METRIC_ID) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Steps (c) and (d), assembly: the model map of one metric G (local         *)
(* isometry, X clause, onto, one-to-one, parametrization on balls) from a    *)
(* Cartan pair of the leaf and the orbit bijection; the Cartan pair of a     *)
(* round leaf; the X-flows of two metrics agree; the pullback of a metric a  *)
(* G0 + (1 - a) w w^T by the model map; the cylinder form.                   *)
(* ========================================================================= *)

let P2BCL_MODEL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3) (X:A->real^3) V hf u k FS FN.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ p2b_lorient top atlas /\
     riemannian_metric atlas G /\ mfd_complete (top,atlas) G /\
     p2b_parallel_on atlas G (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (G x ** X x) = &1) /\
     open_in top V /\ p2bkg_prim atlas G X V hf /\ &0 < k /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set V hf u),lvs_atlas top atlas V hf u)
       (\x. k %% lvs_metric top atlas G V hf u x) (:real^2) FS /\
     mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
       (subtopology top (lvs_set V hf u),lvs_atlas top atlas V hf u)
       (\x. k %% lvs_metric top atlas G V hf u x) (:real^2) FN /\
     (!z. ~(z = Cx(&1)) ==> FN(p2bss_mob z) = FS z) /\
     IMAGE FS (:real^2) UNION IMAGE FN (:real^2) = lvs_set V hf u /\
     (!y. y IN topspace top
          ==> ?r z. z IN lvs_set V hf u /\ p2bkf_phi (top,atlas) G X r z = y) /\
     (!z z' r r'. z IN lvs_set V hf u /\ z' IN lvs_set V hf u /\
                  p2bkf_phi (top,atlas) G X r z = p2bkf_phi (top,atlas) G X r' z'
                  ==> z = z' /\ r = r')
     ==> mfd_local_isometry
           (subtopology euclidean {y:real^3 | ~(y = vec 0)},
            open_set_atlas {y:real^3 | ~(y = vec 0)}) (p2bss_g0 (sqrt(inv k) pow 2))
           (top,atlas) G {y:real^3 | ~(y = vec 0)}
           (p2bss_p (top,atlas) G X FS FN (sqrt(inv k))) /\
         (!y. ~(y = vec 0)
              ==> mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas
                    (p2bss_p (top,atlas) G X FS FN (sqrt(inv k))) y (inv(sqrt(inv k)) % y) =
                  X(p2bss_p (top,atlas) G X FS FN (sqrt(inv k)) y)) /\
         IMAGE (p2bss_p (top,atlas) G X FS FN (sqrt(inv k))) {y:real^3 | ~(y = vec 0)} =
         topspace top /\
         (!y z. ~(y = vec 0) /\ ~(z = vec 0)
                ==> (p2bss_p (top,atlas) G X FS FN (sqrt(inv k)) y =
                     p2bss_p (top,atlas) G X FS FN (sqrt(inv k)) z <=> z = y)) /\
         (!y. ~(y = vec 0)
              ==> ?r. &0 < r /\ r < norm y /\
                      mfd_param top atlas (ball(y,r)) (p2bss_p (top,atlas) G X FS FN (sqrt(inv k))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                 `X:A->real^3`; `V:A->bool`; `hf:A->real`; `u:real`; `k:real`;
                 `FS:real^2->A`; `FN:real^2->A`] P2BCL_P_LISOM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                 `X:A->real^3`; `V:A->bool`; `hf:A->real`; `u:real`; `k:real`;
                 `FS:real^2->A`; `FN:real^2->A`] P2BCL_P_Y) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(!w. (FS:real^2->A) w IN lvs_set V hf u) /\ (!w. (FN:real^2->A) w IN lvs_set V hf u)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                     `X:A->real^3`; `V:A->bool`; `hf:A->real`; `u:real`; `k:real`;
                     `FS:real^2->A`] P2BCL_E_FACTS);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                     `X:A->real^3`; `V:A->bool`; `hf:A->real`; `u:real`; `k:real`;
                     `FN:real^2->A`] P2BCL_E_FACTS)] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lvs_set V (hf:A->real) u SUBSET topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                   `X:A->real^3`; `V:A->bool`; `hf:A->real`; `u:real`] P2BCL_LEAF_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = sqrt(inv k)` THEN
  SUBGOAL_THEN `&0 < c /\ c pow 2 = inv k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c = &0) /\ &0 < c pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_POW_LT]; ALL_TAC] THEN
  ABBREV_TAC `p = p2bss_p (top,atlas) (G:A->real^3^3) (X:A->real^3) FS FN c` THEN
  SUBGOAL_THEN
   `!y. ~(y = vec 0)
        ==> ?z. z IN lvs_set V hf u /\
                (p:real^3->A) y = p2bkf_phi (top,atlas) G (X:A->real^3) (c * log(norm y)) z`
  (LABEL_TAC "pphi") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "p" THEN MATCH_MP_TAC P2BCL_P_PHI THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y1 y2. ~(y1 = vec 0) /\ ~(y2 = vec 0) /\ (p:real^3->A) y1 = p y2 ==> norm y1 = norm y2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "pphi" (fun th ->
      MP_TAC(MP (SPEC `y1:real^3` th) (ASSUME `~(y1:real^3 = vec 0)`)) THEN
      MP_TAC(MP (SPEC `y2:real^3` th) (ASSUME `~(y2:real^3 = vec 0)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `z2:A` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `z1:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `c * log(norm(y1:real^3)) = c * log(norm(y2:real^3))` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`z1:A`; `z2:A`; `c * log(norm(y1:real^3))`;
                                   `c * log(norm(y2:real^3))`] o
        check (fun th -> p2bcl_has_const "p2bkf_phi" th && is_forall(concl th) &&
                         can (find_term (fun t -> try fst(dest_var t) = "r'"
                                                  with Failure _ -> false)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_EQ_MUL_LCANCEL; LOG_INJ; NORM_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> ((p:real^3->A) y = p z <=> z = y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_P_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `G:A->real^3^3`; `X:A->real^3`; `c pow 2`; `c:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC P2BCL_P_ONTO THEN
    EXISTS_TAC `lvs_set V (hf:A->real) u` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BSS_P_PARAM THEN
    MAP_EVERY EXISTS_TAC [`G:A->real^3^3`; `c pow 2`] THEN ASM_REWRITE_TAC[]]);;

let P2BCL_LEAF_PAIR_AT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3) (X:A->real^3) V h u x0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\
     p2b_parallel_on atlas G (topspace top) X /\
     (!y. y IN topspace top ==> X y dot (G y ** X y) = &1) /\
     open_in top V /\ p2bkg_prim atlas G X V h /\
     compact_in top (lvs_set V h u) /\ connected_in top (lvs_set V h u) /\
     x0 IN lvs_set V h u /\ &0 < mfd_scalar atlas G x0 /\
     (!y. y IN lvs_set V h u ==> mfd_scalar atlas G y = mfd_scalar atlas G x0)
     ==> ?FS FN.
           mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
             (subtopology top (lvs_set V h u),lvs_atlas top atlas V h u)
             (\x. (mfd_scalar atlas G x0 / &2) %% lvs_metric top atlas G V h u x) (:real^2) FS /\
           mfd_local_isometry (euclidean,open_set_atlas (:real^2)) p2bss_gs
             (subtopology top (lvs_set V h u),lvs_atlas top atlas V h u)
             (\x. (mfd_scalar atlas G x0 / &2) %% lvs_metric top atlas G V h u x) (:real^2) FN /\
           (!z. ~(z = Cx(&1)) ==> FN(p2bss_mob z) = FS z) /\
           IMAGE FS (:real^2) UNION IMAGE FN (:real^2) = lvs_set V h u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                 `X:A->real^3`; `V:A->bool`; `h:A->real`; `u:real`] P2BCL_LEAF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set V (h:A->real) u)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) V (h:A->real) u`;
                 `lvs_metric top (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3)
                             V (h:A->real) u`;
                 `mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3) x0 / &2`;
                 `x0:A`] P2BCL_SURFACE_PAIR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY];
      UNDISCH_TAC `connected_in top (lvs_set V (h:A->real) u)` THEN SIMP_TAC[connected_in];
      ASM_SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY];
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `a:real^2`; `c:real^2`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology top (lvs_set V (h:A->real) u)`;
                   `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) V (h:A->real) u`;
                   `lvs_metric top (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3)
                               V (h:A->real) u`;
                   `x:A`; `a:real^2`; `c:real^2`] RFA_S2_MFD_SEC_SCAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                   `X:A->real^3`; `V:A->bool`; `h:A->real`; `u:real`; `x:A`]
                  P2BKL_LEVEL_SCALAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MP (SPEC `x:A` (ASSUME `!y. y IN lvs_set V (h:A->real) u
                                          ==> mfd_scalar atlas (G:A->real^3^3) y =
                                              mfd_scalar atlas G x0`))
                   (ASSUME `(x:A) IN lvs_set V h u`)];
    REWRITE_TAC[]]);;

let P2BCL_PHI_TIME = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g1:A->real^3^3) (g2:A->real^3^3) (X:A->real^3)
    r z.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g1 /\ riemannian_metric atlas g2 /\
     mfd_complete (top,atlas) g1 /\ mfd_complete (top,atlas) g2 /\
     p2b_parallel_on atlas g1 (topspace top) X /\ p2b_parallel_on atlas g2 (topspace top) X /\
     z IN topspace top
     ==> p2bkf_phi (top,atlas) g1 X r z = p2bkf_phi (top,atlas) g2 X r z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bkf_phi] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
                 `g2:A->real^3^3`; `X:A->real^3`; `z:A`] P2BKF_ORBIT_TIME) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let P2BCL_RFS_PB_FORMULA = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (p:real^N->A) G U y.
     smooth_manifold_atlas top atlas /\ open U /\ y IN U /\ p y IN topspace top
     ==> rfs_pullback atlas p G y =
         transp(matrix(mfd_differential (open_set_atlas U) atlas p y)) ** G(p y) **
         matrix(mfd_differential (open_set_atlas U) atlas p y)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMPW_PM_DIFF] THEN
  REWRITE_TAC[rfs_pullback; mpullback; o_THM] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `G:A->real^N^N`;
                 `(p:real^N->A) y`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]);;

let P2BCL_CYLM_FORM = prove
 (`!al be (y:real^3) u v.
     u dot ((al %% mat 1 + be %% (lambda i j. y$i * y$j)) ** v) =
     al * (u dot v) + be * ((y dot u) * (y dot v))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID;
              P2BCL_OUTER_MUL; DOT_RADD; DOT_RMUL] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_RING);;

let P2BCL_PULLBACK_ID = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G0:A->real^3^3) (G1:A->real^3^3) (X:A->real^3)
    (p:real^3->A) c a y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G0 /\ &0 < c /\
     mfd_local_isometry
       (subtopology euclidean {y:real^3 | ~(y = vec 0)},open_set_atlas {y:real^3 | ~(y = vec 0)})
       (p2bss_g0 (c pow 2)) (top,atlas) G0 {y:real^3 | ~(y = vec 0)} p /\
     (!y. ~(y = vec 0)
          ==> mfd_differential (open_set_atlas {y:real^3 | ~(y = vec 0)}) atlas p y (inv c % y) =
              X(p y)) /\
     (!x. x IN topspace top
          ==> G1 x = a %% G0 x + (&1 - a) %% (lambda i j. (G0 x ** X x)$i * (G0 x ** X x)$j)) /\
     ~(y = vec 0)
     ==> rfs_pullback atlas p G1 y =
         (a * c pow 2 / norm y pow 2) %% mat 1 +
         ((&1 - a) * c pow 2 / norm y pow 4) %% (lambda i j. y$i * y$j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Z = {y:real^3 | ~(y = vec 0)}` THEN
  SUBGOAL_THEN `open (Z:real^3->bool) /\ (y:real^3) IN Z` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN REWRITE_TAC[P2BSS_ZSETS; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology (subtopology euclidean Z) Z,top) (p:real^3->A) /\
    mfd_smooth_map (open_set_atlas Z) (atlas:((A->bool)#(A->real^3))->bool) Z p`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `mfd_local_isometry (subtopology euclidean Z,open_set_atlas Z)
                     (p2bss_g0 (c pow 2)) (top,atlas) (G0:A->real^3^3) Z (p:real^3->A)`) THEN
    REWRITE_TAC[mfd_local_isometry] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    MP_TAC(ASSUME `(y:real^3) IN Z`) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_pullback atlas (p:real^3->A) G0 y = p2bss_g0 (c pow 2) y` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BSS_LISOM_RFS THEN
    MAP_EVERY EXISTS_TAC [`Z:real^3->bool`; `top:A topology`; `Z:real^3->bool`] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_differential (open_set_atlas Z) atlas (p:real^3->A) y (inv c % y) =
                (X:A->real^3)(p y)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> p2bcl_has_const "mfd_differential" th &&
                                                  is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(mfd_differential (open_set_atlas Z) (atlas:((A->bool)#(A->real^3))->bool)
                                        (p:real^3->A) y)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (Z:real^3->bool)`; `top:A topology`;
                          `Z:real^3->bool`] THEN
    ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_IN_OPEN_EQ; SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:real^3->A`;
                 `G0:A->real^3^3`; `Z:real^3->bool`; `y:real^3`] P2BCL_RFS_PB_FORMULA) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:real^3->A`;
                 `G1:A->real^3^3`; `Z:real^3->bool`; `y:real^3`] P2BCL_RFS_PB_FORMULA) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Dm = mfd_differential (open_set_atlas Z) (atlas:((A->bool)#(A->real^3))->bool)
                                    (p:real^3->A) y` THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!u v. (Dm:real^3->real^3) u dot ((G0:A->real^3^3) ((p:real^3->A) y) ** Dm v) =
                      (c pow 2 / norm(y:real^3) pow 2) * (u dot v)`
  (LABEL_TAC "g0") THENL
   [REPEAT GEN_TAC THEN ASM_SIMP_TAC[GSYM MATRIX_WORKS] THEN
    REWRITE_TAC[GSYM P2BKF_TRIPLE_DOT] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[SYM th]) o
      check (fun th -> is_eq(concl th) && p2bcl_has_const "transp" th &&
                       p2bcl_has_const "p2bss_g0" th)) THEN
    REWRITE_TAC[p2bss_g0; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp((G0:A->real^3^3) ((p:real^3->A) y)) = G0 (p y)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `G0:A->real^3^3`; `(p:real^3->A) y`] P2BSS_G_AT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. ((G0:A->real^3^3) ((p:real^3->A) y) ** (X:A->real^3) (p y)) dot
                    (Dm:real^3->real^3) u =
                    (c pow 2 / norm(y:real^3) pow 2) * inv c * (y dot u)`
  (LABEL_TAC "wx") THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
    SUBST1_TAC(SYM(ASSUME `(Dm:real^3->real^3) (inv c % y) = (X:A->real^3)((p:real^3->A) y)`)) THEN
    USE_THEN "g0" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[DOT_RMUL] THEN REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC GEOI_QUAD_EQ THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[P2BKF_TRIPLE_DOT] THEN ASM_SIMP_TAC[MATRIX_WORKS] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[P2BCL_OUTER_FORM] THEN
    MP_TAC(ISPECL [`(G0:A->real^3^3) ((p:real^3->A) y)`; `(Dm:real^3->real^3) u`;
                   `(Dm:real^3->real^3) v`] P2BKF_SYM_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[P2BCL_CYLM_FORM] THEN REWRITE_TAC[DOT_SYM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `u:real^3` THEN REWRITE_TAC[P2BKF_TRIPLE_DOT] THEN ASM_SIMP_TAC[MATRIX_WORKS] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[P2BCL_OUTER_FORM; P2BCL_CYLM_FORM] THEN
  USE_THEN "g0" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "wx" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` MP_TAC THENL [ASM_SIMP_TAC[NORM_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < c` THEN
  SPEC_TAC(`norm(y:real^3)`,`n:real`) THEN SPEC_TAC(`(y:real^3) dot u`,`d:real`) THEN
  SPEC_TAC(`(u:real^3) dot u`,`e:real`) THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN CONV_TAC REAL_FIELD);;

let P2BCL_CYL_FORM = prove
 (`!c R0 t (y:real^3).
     &0 < c /\ R0 * c pow 2 = &2 /\ ~(y = vec 0)
     ==> ((&1 - R0 * t) * c pow 2 / norm y pow 2) %% mat 1 +
         ((&1 - (&1 - R0 * t)) * c pow 2 / norm y pow 4) %% (lambda i j. y$i * y$j) =
         (c pow 2 / &2) %% cylinder_flow (t / (c pow 2 / &2)) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `R0 = &2 / c pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `R0 * c pow 2 = &2` THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` MP_TAC THENL [ASM_SIMP_TAC[NORM_POS_LT]; ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[cylinder_flow; MATRIX_CMUL_ADD_LDISTRIB; MATRIX_CMUL_ASSOC] THEN
  BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < norm(y:real^3)` THEN UNDISCH_TAC `&0 < c` THEN
  SPEC_TAC(`norm(y:real^3)`,`n:real`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The main theorem.  At a time s0 < b: the leaf L is round of curvature K0  *)
(* = R0/2 (R0 the scalar curvature on L at s0), its Cartan pair gives the    *)
(* model map p of g(s0) (P2BCL_MODEL, flows of gs and g(s0) agree), c =      *)
(* sqrt(1/K0), lam = c^2/2 = 1/R0, and by the metric identity g(t + s0) = (1 *)
(* - R0 t) g(s0) + R0 t w w^T the pullback of g(t + s0) by p is lam          *)
(* cylinder_flow(t/lam) for every t <= 0.                                    *)
(* ========================================================================= *)

let P2B_CYL_FROM_LEAF = prove
 (`!w:B->bool. P2B_REQ_CYL_FROM_LEAF_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_REQ_CYL_FROM_LEAF_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `gs:B->real^3^3`; `b:real`; `X:B->real^3`;
                       `V0:B->bool`; `h0:B->real`; `u0:real`] THEN
  STRIP_TAC THEN X_GEN_TAC `s0:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!s. s < b
        ==> riemannian_metric atlas ((g:real->B->real^3^3) s) /\
            mfd_complete (top,atlas) (g s) /\
            p2b_parallel_on atlas (g s) (topspace top) (X:B->real^3) /\
            (!y. y IN topspace top ==> X y dot (g s y ** X y) = &1) /\
            p2bkg_prim atlas (g s) X V0 h0`
  (LABEL_TAC "ts") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BKL_RF_RIEMANNIAN THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `b:real`] THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "ts" (STRIP_ASSUME_TAC o C MP (ASSUME `s0 < b`) o SPEC `s0:real`) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `X:B->real^3`; `V0:B->bool`; `h0:B->real`;
                 `u0:real`] P2BCL_LEAF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* a point of the leaf *)
  SUBGOAL_THEN `?x0:B. x0 IN lvs_set V0 h0 u0` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> p2bcl_has_const "mfd_diffeo" th)) THEN
    REWRITE_TAC[mfd_diffeo; homeomorphic_maps] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> p2bcl_has_const "continuous_map" th &&
                       can (find_term (fun t -> try fst(dest_var t) = "psi1"
                                                with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV; SUBSET; FORALL_IN_IMAGE;
                IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `basis 1:real^3`) THEN
    SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:B) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ASSUME `lvs_set V0 (h0:B->real) u0 SUBSET topspace top`) THEN
    MP_TAC(ASSUME `(x0:B) IN lvs_set V0 h0 u0`) THEN SET_TAC[];
    ALL_TAC] THEN
  (* the scalar curvature on the leaf at s0 *)
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) s0) x0 /\
                (!y. y IN lvs_set V0 h0 u0
                     ==> mfd_scalar atlas (g s0) y = mfd_scalar atlas (g s0) x0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`s0:real`; `x0:B`]
        (ASSUME `!s y. s < b /\ y IN topspace top
                       ==> &0 < mfd_scalar atlas ((g:real->B->real^3^3) s) y`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `y:B` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`s0:real`; `y:B`; `x0:B`]
        (ASSUME `!s y z. s < b /\ y IN lvs_set V0 h0 u0 /\ z IN lvs_set V0 h0 u0
                         ==> mfd_scalar atlas ((g:real->B->real^3^3) s) y =
                             mfd_scalar atlas (g s) z`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  (* the Cartan pair of the round leaf *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `X:B->real^3`; `V0:B->bool`; `h0:B->real`;
                 `u0:real`; `x0:B`] P2BCL_LEAF_PAIR_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `FS:real^2->B` (X_CHOOSE_THEN `FN:real^2->B` STRIP_ASSUME_TAC)) THEN
  (* the orbits of g(s0) *)
  SUBGOAL_THEN `!r z. z IN topspace top
                      ==> p2bkf_phi (top,atlas) (gs:B->real^3^3) (X:B->real^3) r z =
                          p2bkf_phi (top,atlas) ((g:real->B->real^3^3) s0) X r z`
  (LABEL_TAC "conv") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BCL_PHI_TIME THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN topspace top
        ==> ?r z. z IN lvs_set V0 h0 u0 /\
                  p2bkf_phi (top,atlas) ((g:real->B->real^3^3) s0) (X:B->real^3) r z = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    MP_TAC(MP (SPEC `y:B`
      (ASSUME `!y. y IN topspace top
                   ==> ?r z. z IN lvs_set V0 (h0:B->real) u0 /\
                             p2bkf_phi (top,atlas) (gs:B->real^3^3) (X:B->real^3) r z = y`))
      (ASSUME `(y:B) IN topspace top`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `z:B`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:B) IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ASSUME `lvs_set V0 (h0:B->real) u0 SUBSET topspace top`) THEN
      MP_TAC(ASSUME `(z:B) IN lvs_set V0 h0 u0`) THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "conv" (MP_TAC o C MP (ASSUME `(z:B) IN topspace top`) o
                     SPECL [`r:real`; `z:B`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z z' r r'. z IN lvs_set V0 h0 u0 /\ z' IN lvs_set V0 h0 u0 /\
                p2bkf_phi (top,atlas) ((g:real->B->real^3^3) s0) (X:B->real^3) r z =
                p2bkf_phi (top,atlas) (g s0) X r' z'
                ==> z = z' /\ r = r'`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:B) IN topspace top /\ (z':B) IN topspace top` STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `lvs_set V0 (h0:B->real) u0 SUBSET topspace top`) THEN
      MP_TAC(ASSUME `(z:B) IN lvs_set V0 h0 u0`) THEN
      MP_TAC(ASSUME `(z':B) IN lvs_set V0 h0 u0`) THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`z:B`; `z':B`; `r:real`; `r':real`]
      (ASSUME `!z z' r r'. z IN lvs_set V0 h0 u0 /\ z' IN lvs_set V0 h0 u0 /\
                           p2bkf_phi (top,atlas) (gs:B->real^3^3) (X:B->real^3) r z =
                           p2bkf_phi (top,atlas) gs X r' z'
                           ==> z = z' /\ r = r'`)) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "conv" (fun th ->
      REWRITE_TAC[MP (SPECL [`r:real`; `z:B`] th) (ASSUME `(z:B) IN topspace top`);
                  MP (SPECL [`r':real`; `z':B`] th) (ASSUME `(z':B) IN topspace top`)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the model map of g(s0) *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `X:B->real^3`; `V0:B->bool`; `h0:B->real`;
                 `u0:real`; `mfd_scalar atlas ((g:real->B->real^3^3) s0) x0 / &2`;
                 `FS:real^2->B`; `FN:real^2->B`] P2BCL_MODEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `c = sqrt(inv(mfd_scalar atlas ((g:real->B->real^3^3) s0) x0 / &2))` THEN
  ABBREV_TAC `p = p2bss_p (top,atlas) ((g:real->B->real^3^3) s0) (X:B->real^3) FS FN c` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c /\ mfd_scalar atlas ((g:real->B->real^3^3) s0) x0 * c pow 2 = &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    SUBGOAL_THEN `&0 < inv(mfd_scalar atlas ((g:real->B->real^3^3) s0) x0 / &2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE;
             ASSUME `&0 < inv(mfd_scalar atlas ((g:real->B->real^3^3) s0) x0 / &2)`] THEN
    UNDISCH_TAC `&0 < mfd_scalar atlas ((g:real->B->real^3^3) s0) x0` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  (* the cylinder model *)
  REWRITE_TAC[p2b_cyl_model] THEN
  MAP_EVERY EXISTS_TAC [`p:real^3->B`; `c pow 2 / &2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH; ASSUME `&0 < c`]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `t + s0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `b:real`; `X:B->real^3`; `V0:B->bool`; `h0:B->real`;
                 `u0:real`; `s0:real`; `x0:B`] P2BCL_METRIC_ID) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      USE_THEN "ts" (fun th -> MP_TAC(MP (SPEC `s:real` th) (ASSUME `s < b`))) THEN
      SIMP_TAC[];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t + s0`) THEN
  ASM_REWRITE_TAC[REAL_ARITH `(t + s0) - s0 = t`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `(g:real->B->real^3^3) (t + s0)`; `X:B->real^3`;
                 `p:real^3->B`; `c:real`;
                 `&1 - mfd_scalar atlas ((g:real->B->real^3^3) s0) x0 * t`; `y:real^3`]
                P2BCL_PULLBACK_ID) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC P2BCL_CYL_FORM THEN ASM_REWRITE_TAC[]);;

