(* ========================================================================= *)
(* pc_p2a_l984: MT Lemma 9.84 for one kappa-solution in the length-L form,   *)
(* for COR_9_94_L piece (b) (P2B_PROP_9_85L_ROUTE_STATEMENT, pc_p2b_c994req) *)
(* and other users.  Main theorem P2AL84_LEMMA_9_84L: from THM_9_64,         *)
(* LEMMA_9_65, PROP_9_83K (a) and CYL_MODEL_NECKS (h), for every             *)
(* kappa-solution with p2b_ksep and base point p there is D such that every  *)
(* point outside the ball about p of radius D R(p)^(-1/2) at time 0 is the   *)
(* centre of an evolving eps-neck of length L.  Positivity of the curvature  *)
(* is not needed.  Proof (MT p. 236): by contradiction along points x n      *)
(* with sqrt(R(p)) d(p,x n) >= n + 1 and no neck.  If                        *)
(* R(x n) d(p,x n)^2 is bounded along a subsequence, LEMMA_9_65 at x n       *)
(* bounds R(p) / R(x n), which is impossible.  Otherwise the almost-line     *)
(* pairs of P2BX0_ALMOST_PAIRS pass to the THM_9_64 limit at x n             *)
(* (P2BX0_LIMIT_PAIRS), which then contains a line (P2BX0_LINE_FROM_PAIRS);  *)
(* a parallel unit field (CMPSP_SPLIT_GEN) gives Ric(X,X) = 0, so the        *)
(* limit is not positively curved and (a) makes it the cylinder model; the   *)
(* line excludes the Z/2 alternative (P2A985_ZQ_NO_LINE, pc_p2a_zq), (h)     *)
(* makes its base point an evolving eps-neck centre of length L + 1, and     *)
(* P2B_NECK_OPEN_L with P2BL_NECK_LIMIT moves the neck back to x n.          *)
(* ========================================================================= *)

needs "src/pc_p2b_c994req.ml";;
needs "src/pc_p2b_x0.ml";;
needs "src/pc_p2b_x0r.ml";;
needs "src/pc_cmp_split.ml";;
needs "src/pc_cmp_bg.ml";;
needs "src/pc_rfa_secpres.ml";;
needs "src/pc_p2b_ltr.ml";;
needs "src/pc_p2b_979s.ml";;
needs "src/pc_rfa_c971.ml";;
needs "src/pc_lim_dist.ml";;
needs "src/pc_p2c_views.ml";;
needs "src/pc_p2a_zq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Helpers.  A term search; copies of small lemmas of files outside the load *)
(* closure of this file (the same proofs, renamed): P3S_SECMIN_LE            *)
(* (pc_p3_s13pinch), P2HN_FLOW_LIMIT_ON (pc_p2c_bugq),                       *)
(* P2BX46_CYL_MODEL_SCALAR (pc_p2b_p946c).  Then R > 0 at time 0 on every    *)
(* kappa-solution with p2b_ksep, by (a): positive curvature or the cylinder  *)
(* model, where R = 1 / lam; and a global parallel unit field excludes       *)
(* positive curvature (Ric(X,X) = 0, P2BX0R_PAR_RICCI_ZERO).                 *)
(* ========================================================================= *)

let p2al84_mentions name th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th);;

(* from pc_p3_s13pinch.ml *)
let P2AL84_SECMIN_LE = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x b u v.
     (!u v. ~collinear {vec 0,u,v} ==> b <= mfd_sectional atlas g x u v) /\
     ~collinear {vec 0,u,v}
     ==> mfd_sec_min atlas g x <= mfd_sectional atlas g x u v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sec_min] THEN
  MATCH_MP_TAC REAL_INF_LE THEN
  MAP_EVERY EXISTS_TAC [`b:real`;
    `mfd_sectional (atlas:((A->bool)#(A->real^N))->bool) g x u v`] THEN
  REWRITE_TAC[REAL_LE_REFL; FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`u:real^N`; `v:real^N`] THEN
  ASM_REWRITE_TAC[]);;

(* from pc_p2c_bugq.ml *)
let P2AL84_FLOW_LIMIT_ON = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl Tl.
     p3_flow_limit V x t Q (top,atlas) g xl Tl
     ==> p3_flow_limit_on V x t Q {s | --Tl < s /\ s <= &0} (top,atlas) g xl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_flow_limit; p3_flow_limit_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `ts:num->real`
    (X_CHOOSE_THEN `phi:num->B->A` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "dif") (LABEL_TAC "cl")))))))))) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->A`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `K:B->bool`; `m:num`; `eta:real`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `a <= b` THENL
   [SUBGOAL_THEN `--Tl < a /\ b <= &0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `real_interval[a,b] SUBSET {s | --Tl < s /\ s <= &0}` THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `a:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "cl" (MP_TAC o SPECL [`K:B->bool`; `m:num`; `eta:real`; `a:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
    EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lk"))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "dif" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN USE_THEN "lk" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    USE_THEN "cl" (MP_TAC o SPECL [`K:B->bool`; `m:num`; `eta:real`; `&0`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
    EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

(* from pc_p2b_p946c.ml *)
let P2AL84_CYL_MODEL_SCALAR = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3).
     p2b_cyl_model (top,atlas) g /\ smooth_manifold_atlas top atlas /\
     (!t. t <= &0 ==> riemannian_metric atlas (g t))
     ==> ?lam. &0 < lam /\
               !t x. t <= &0 /\ x IN topspace top
                     ==> mfd_scalar atlas (g t) x = &1 / (lam - t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_cyl_model] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `p:real^3->B` (X_CHOOSE_THEN `lam:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (LABEL_TAC "par") (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pb")))))))
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y. ~(y = vec 0:real^3) /\ x = (p:real^3->B) y`
  (X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
   [UNDISCH_TAC `IMAGE (p:real^3->B) {y | ~(y = vec 0)} = topspace top` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "par" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `t / lam < &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) t`; `ball(y:real^3,r)`; `p:real^3->B`;
                 `&1`; `y:real^3`] P2B9_PARAM_LSCALAR_SCALED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_LT_01]; REWRITE_TAC[REAL_DIV_1]] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `lscalar (\z. &1 %% rfs_pullback atlas (p:real^3->B) ((g:real->B->real^3^3) t) z) y =
    lscalar (\z. lam %% cylinder_flow (t / lam) z) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `ball(y:real^3,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; MATRIX_CMUL_LID] THEN
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    USE_THEN "pb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `dist(y:real^3,z) < r` THEN ASM_REWRITE_TAC[DIST_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (t / lam)`; `lam:real`; `y:real^3`]
    LSCALAR_SCALE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; IN_DELETE; IN_UNIV]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`t / lam`; `y:real^3`] RFB_CYL_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `~(lam = &0) /\ ~(lam - t = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(lam = &0) /\ ~(lam - t = &0)
                           ==> (&1 / (&1 - t / lam)) / lam = &1 / (lam - t)`]);;

(* R > 0 at time 0: (a) gives positive curvature at time 0, where           *)
(* RFA_C971_SCALAR_POS_PT applies, or the cylinder model, where R = 1/lam.  *)

let P2AL84_R_POS = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) x.
     P2B_PROP_9_83K_STATEMENT w /\ p2b_kappa_solution kappa (top,atlas) g /\
     p2b_ksep top atlas /\ x IN topspace top
     ==> &0 < mfd_scalar atlas (g(&0)) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {vec 0:real^3,basis 1,basis 2}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_LEMMA] THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[NOT_EXISTS_THM; CART_EQ; FORALL_3; DIMINDEX_3] THEN
    SIMP_TAC[BASIS_COMPONENT; VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `P2B_PROP_9_83K_STATEMENT (w:B->bool)` THEN
  REWRITE_TAC[P2B_PROP_9_83K_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                             `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MATCH_MP_TAC RFA_C971_SCALAR_POS_PT THEN EXISTS_TAC `top:B topology` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `abs(mfd_sectional atlas ((g:real->B->real^3^3) (&0)) x (basis 1) (basis 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < a ==> &0 < abs a`) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`] P2AL84_CYL_MODEL_SCALAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `lam:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `x:B`]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_SUB_RZERO] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_LT_01]]);;

(* A global parallel field of unit length makes Ric(X,X) = 0, so the slice *)
(* is not positively curved at any point.                                    *)

let P2AL84_NOT_POS_SPLIT = prove
 (`!top atlas (g:B->real^3^3) X p.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\ p IN topspace top /\
     X p dot (g p ** X p) = &1
     ==> ~(!u v. ~collinear {vec 0,u,v} ==> &0 < mfd_sectional atlas g p u v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `X:B->real^3`; `p:B`; `(X:B->real^3) p`] P2BX0R_PAR_RICCI_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`] RFA_SECMIN_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `mfd_sec_min atlas (g:B->real^3^3) p`; `(X:B->real^3) p`]
                CMPZ_MFD_RICCI_SEC_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AL84_SECMIN_LE THEN
    EXISTS_TAC `&0` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* A line selects the one-to-one alternative of p2b_cyl_model               *)
(* (P2A985_ZQ_NO_LINE excludes the Z/2 quotient; this is the bridge from    *)
(* the conjunct form of pc_p2a_zq to the definition), and then (h) makes    *)
(* every point at every time t <= 0 the centre of evolving necks of every   *)
(* length.                                                                  *)
(* ========================================================================= *)

let P2AL84_CYL_MODEL_LINE = prove
 (`!top atlas (g:real->B->real^3^3).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas (g(&0)) /\
     p2b_cyl_model (top,atlas) g /\
     (?l. !s t. l s IN topspace top /\
                mfd_dist (top,atlas) (g(&0)) (l s) (l t) = abs(t - s))
     ==> ?p lam. &0 < lam /\
                 IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
                 (!y. ~(y = vec 0)
                      ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
                 (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) /\
                 (!t y. t <= &0 /\ ~(y = vec 0)
                        ==> rfs_pullback atlas p (g t) y = lam %% cylinder_flow (t / lam) y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
  REWRITE_TAC[p2b_cyl_model] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->B` (X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`p:real^3->B`; `lam:real`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`] P2A985_ZQ_NO_LINE) THEN
  ASM_REWRITE_TAC[]);;

let P2AL84_CYL_LINE_NECK = prove
 (`!(w:B->bool) top atlas (g:real->B->real^3^3).
     P2B_CYL_MODEL_NECKS_STATEMENT w /\
     smooth_manifold_atlas top atlas /\ (!t. t <= &0 ==> riemannian_metric atlas (g t)) /\
     p2b_cyl_model (top,atlas) g /\
     (?l. !s t. l s IN topspace top /\
                mfd_dist (top,atlas) (g(&0)) (l s) (l t) = abs(t - s))
     ==> !delta L t x. &0 < delta /\ &1 <= L /\ t <= &0 /\ x IN topspace top
                       ==> ?e. rfs_evolving_neck (p2b_kview (top,atlas) g) delta x t L e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "line"))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`] P2AL84_CYL_MODEL_LINE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL] THEN USE_THEN "line" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->B` (X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `P2B_CYL_MODEL_NECKS_STATEMENT (w:B->bool)` THEN
  REWRITE_TAC[P2B_CYL_MODEL_NECKS_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                             `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`]) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* THM_9_64 at arbitrary base points.  The theorem asks for R = 1 at the    *)
(* base points; apply it to the parabolic rescalings Q k g(t / Q k)         *)
(* (RFA_C971_KSOL_SCALE) with Q k = R(x k) > 0 (P2AL84_R_POS), and          *)
(* rewrite the limit as a limit of the original views with scales Q k (the  *)
(* slices agree for s <= 0, the pullback is linear in the metric,           *)
(* P2B9_RFS_PULLBACK_CMUL).                                                 *)
(* ========================================================================= *)

let P2AL84_LIMIT_RESCALE = prove
 (`!(top:num->B topology) atlas (g:num->real->B->real^3^3) (x:num->B) Q
    (top':B topology) atlas' g' xl Tl.
     (!k. &0 < Q k) /\
     p3_flow_limit (\k. p2b_kview (top k,atlas k) (\t y. Q k %% g k (t / Q k) y)) x
                   (\k. &0) (\k. &1) (top',atlas') g' xl Tl
     ==> p3_flow_limit (\k. p2b_kview (top k,atlas k) (g k)) x (\k. &0) Q
                       (top',atlas') g' xl Tl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_flow_limit] THEN
  REWRITE_TAC[P2BL_KVIEW_ACCESS; P2B9_RFS_PULLBACK_CMUL; MATRIX_CMUL_LID; REAL_ADD_LID;
              REAL_DIV_1; ETA_AX] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `ts:num->real`; `phi:num->B->B`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `s:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s / (Q:num->real) k <= &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]; ALL_TAC] THEN
  ASM_SIMP_TAC[P2BL_KVIEW_ACCESS] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `s:real`] o
    check (fun th -> is_forall (concl th) && p2al84_mentions "mfd_diffeo" th)) THEN
  ASM_SIMP_TAC[P2BL_KVIEW_ACCESS]);;

let P2AL84_THM964_AT = prove
 (`!(w:B->bool) kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) (x:num->B).
     P2B_THM_9_64_STATEMENT w /\ P2B_PROP_9_83K_STATEMENT w /\
     (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ p2b_ksep (top k) (atlas k) /\
          x k IN topspace (top k))
     ==> ?sub (top':B topology) atlas' g' xl.
           p3_subseq sub /\
           (!Tl. &0 < Tl
                 ==> p3_flow_limit (\k. p2b_kview (top (sub k),atlas (sub k)) (g (sub k)))
                                   (x o sub) (\k. &0)
                                   (\k. mfd_scalar (atlas (sub k)) (g (sub k) (&0)) (x (sub k)))
                                   (top',atlas') g' xl Tl) /\
           p2b_kappa_solution kappa (top',atlas') g' /\ p2b_ksep top' atlas' /\
           mfd_scalar atlas' (g'(&0)) xl = &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "seq"))) THEN
  ABBREV_TAC `Q = \k. mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                                 ((g:num->real->B->real^3^3) k (&0)) ((x:num->B) k)` THEN
  SUBGOAL_THEN `!k. &0 < (Q:num->real) k` (LABEL_TAC "Qpos") THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "Q" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `(top:num->B topology) k`] THEN
    USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[P2B_THM_9_64_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`kappa:real`; `top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
    `\k t y. (Q:num->real) k %% (g:num->real->B->real^3^3) k (t / Q k) y`; `x:num->B`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "seq" (MP_TAC o SPEC `0`) THEN
      REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_C971_KSOL_SCALE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN REWRITE_TAC[GSYM real_div] THEN
    MP_TAC(ISPECL [`(top:num->B topology) k`; `(atlas:num->((B->bool)#(B->real^3))->bool) k`;
                   `(g:num->real->B->real^3^3) k (&0)`; `(Q:num->real) k`; `(x:num->B) k`]
                  RFA_C971_SCALAR_SCALE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL]; DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "Q" THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_DIV_REFL THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN USE_THEN "Qpos" (MP_TAC o SPEC `k:num`) THEN
    EXPAND_TAC "Q" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `xl:B` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                        `xl:B`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `Tl:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\k. (top:num->B topology) ((sub:num->num) k)`;
                 `\k. (atlas:num->((B->bool)#(B->real^3))->bool) ((sub:num->num) k)`;
                 `\k. (g:num->real->B->real^3^3) ((sub:num->num) k)`;
                 `(x:num->B) o (sub:num->num)`;
                 `\k. (Q:num->real) ((sub:num->num) k)`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `Tl:real`] P2AL84_LIMIT_RESCALE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[]; EXPAND_TAC "Q" THEN REWRITE_TAC[o_THM]]);;

(* ========================================================================= *)
(* LEMMA_9_65 in scale-invariant form (R(q) <= Cr R(x) when sqrt(R(x))      *)
(* d(x,q) < r), by the rescaling Q g(t / Q) with Q = R(x)                   *)
(* (MFD_BALL_SCALE, RFA_C971_SCALAR_SCALE); and the bounded case of MT's    *)
(* proof: points x n with sqrt(R(p)) d(p,x n) >= n + 1 cannot have R(x      *)
(* n) d(p,x n)^2 bounded along a subsequence.                               *)
(* ========================================================================= *)

let P2AL84_LEMMA_965_SCALED = prove
 (`!(w:B->bool) kappa r.
     P2B_LEMMA_9_65_STATEMENT w /\ P2B_PROP_9_83K_STATEMENT w /\ &0 < kappa /\ &0 < r
     ==> ?Cr. !top atlas (g:real->B->real^3^3) x q.
                p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                x IN topspace top /\ q IN topspace top /\
                sqrt(mfd_scalar atlas (g(&0)) x) * mfd_dist (top,atlas) (g(&0)) x q < r
                ==> mfd_scalar atlas (g(&0)) q <= Cr * mfd_scalar atlas (g(&0)) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[P2B_LEMMA_9_65_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `r:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cr:real` (LABEL_TAC "Cr")) THEN EXISTS_TAC `Cr:real` THEN
  MAP_EVERY X_GEN_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `x:B`; `q:B`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `connected_space (top:B topology)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) x q` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2b_kappa_solution kappa (top,atlas)
      (\t y. mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x %%
             g (t / mfd_scalar atlas (g(&0)) x) y)` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_C971_KSOL_SCALE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x %%
         g (&0 / mfd_scalar atlas (g(&0)) x) y) =
    (\y. mfd_scalar atlas (g(&0)) x %% g (&0) y)` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN topspace top
        ==> mfd_scalar atlas
              (\y. mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x %% g (&0) y) z =
            mfd_scalar atlas (g(&0)) z / mfd_scalar atlas (g(&0)) x` (LABEL_TAC "sc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_C971_SCALAR_SCALE THEN
    EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ball (top,atlas) (\y. mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x %% g (&0) y) x r =
    mfd_ball (top,atlas) (g(&0)) x (r / sqrt(mfd_scalar atlas (g(&0)) x))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x`;
                   `x:B`; `r:real`] MFD_BALL_SCALE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "Cr" (MP_TAC o SPECL
   [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `\t y. mfd_scalar atlas ((g:real->B->real^3^3) (&0)) x %%
           g (t / mfd_scalar atlas (g(&0)) x) y`; `x:B`; `q:B`]) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "sc" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:B) IN topspace top`);
                                      MATCH_MP th (ASSUME `(q:B) IN topspace top`)]) THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; SQRT_POS_LT; REAL_LE_LDIV_EQ] THEN
  DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]);;

let P2AL84_BOUND_ARITH = prove
 (`!Rp Q d Cr M n.
     &0 < Rp /\ &0 < Q /\ &0 <= d /\ Rp <= Cr * Q /\ Q * d pow 2 <= M /\
     (n + &1) pow 2 <= Rp * d pow 2 /\ Cr * abs M < n + &1 /\ &0 <= n
     ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Cr` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < --Cr * Q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Rp * d pow 2 <= Cr * (Q * d pow 2)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `Cr * (Q * d pow 2) <= Cr * abs M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n + &1 <= (n + &1) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC(REAL_ARITH `&1 * a <= a * a ==> a <= a * a`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2AL84_BOUNDED_CASE = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) p (x:num->B) M.
     P2B_LEMMA_9_65_STATEMENT w /\ P2B_PROP_9_83K_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ p IN topspace top /\
     (!n. x n IN topspace top /\
          &n + &1 <= sqrt(mfd_scalar atlas (g(&0)) p) * mfd_dist (top,atlas) (g(&0)) p (x n)) /\
     (!N. ?n. N <= n /\
              mfd_scalar atlas (g(&0)) (x n) * mfd_dist (top,atlas) (g(&0)) p (x n) pow 2 <= M)
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "far") (LABEL_TAC "bd"))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `connected_space (top:B topology) /\ &0 < kappa` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `sqrt(abs M) + &1`] P2AL84_LEMMA_965_SCALED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `abs M` SQRT_POS_LE) THEN
    REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cr:real` (LABEL_TAC "Cr")) THEN
  MP_TAC(SPEC `Cr * abs M` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
  USE_THEN "bd" (MP_TAC o SPEC `N:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  USE_THEN "far" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p /\
                &0 < mfd_scalar atlas (g(&0)) ((x:num->B) n)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) p ((x:num->B) n)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) p ((x:num->B) n)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p <=
    Cr * mfd_scalar atlas (g(&0)) ((x:num->B) n)` ASSUME_TAC THENL
   [USE_THEN "Cr" MATCH_MP_TAC THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `p:B`; `(x:num->B) n`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= sqrt(abs M) ==> a < sqrt(abs M) + &1`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) ((x:num->B) n) *
                     mfd_dist (top,atlas) (g(&0)) p (x n) pow 2)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[SQRT_MUL; REAL_LT_IMP_LE; REAL_POW_LE; POW_2_SQRT; REAL_LE_REFL];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AL84_BOUND_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p`;
    `mfd_scalar atlas ((g:real->B->real^3^3) (&0)) ((x:num->B) n)`;
    `mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) p ((x:num->B) n)`;
    `Cr:real`; `M:real`; `&n`] THEN
  ASM_REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p) *
                 mfd_dist (top,atlas) (g(&0)) p ((x:num->B) n)) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS; REAL_LE_01];
      ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `N:num <= n` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The split case of MT's proof.  Points x n with d(p,x n) -> infinity      *)
(* and R(x n) d(p,x n)^2 -> infinity: along a subsequence the almost-line   *)
(* pairs of P2BX0_ALMOST_PAIRS give exact pairs in the THM_9_64 limit at x  *)
(* n (P2BX0_LIMIT_PAIRS on LIM_DIST, LIM_BALL), hence a line                *)
(* (P2BX0_LINE_FROM_PAIRS) and a parallel unit field (CMPSP_SPLIT_GEN); the *)
(* limit is not positively curved, so (a) makes it the cylinder model, the  *)
(* line selects the one-to-one alternative, (h) makes its base point an     *)
(* evolving eps-neck centre of length L + 1, and NECK_OPEN_L with           *)
(* P2BL_NECK_LIMIT moves an eps-neck of length L back to x n for n large.   *)
(* ========================================================================= *)

let P2AL84_KVIEW_SLICES = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> (!tau. ~(topspace(rfs_vtop (p2b_kview (top,atlas) g) tau) = {})
                ==> smooth_manifold_atlas (rfs_vtop (p2b_kview (top,atlas) g) tau)
                                          (rfs_vatlas (p2b_kview (top,atlas) g) tau) /\
                    riemannian_metric (rfs_vatlas (p2b_kview (top,atlas) g) tau)
                                      (rfs_vmetric (p2b_kview (top,atlas) g) tau)) /\
         (!tau. hausdorff_space (rfs_vtop (p2b_kview (top,atlas) g) tau))`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  REWRITE_TAC[p2b_kview] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_VIEW_REGULAR THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    MATCH_MP_TAC P2BX0_VIEW_HAUSDORFF THEN ASM_REWRITE_TAC[]]);;

let P2AL84_SPLIT_CASE = prove
 (`!(w:B->bool) eps L kappa top atlas (g:real->B->real^3^3) p (x:num->B).
     P2B_THM_9_64_STATEMENT w /\ P2B_PROP_9_83K_STATEMENT w /\
     P2B_CYL_MODEL_NECKS_STATEMENT w /\
     &0 < eps /\ eps < &1 / &4 /\ &1 <= L /\
     p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ p IN topspace top /\
     (!n. x n IN topspace top) /\
     (!M. ?N. !n. N <= n ==> M < mfd_dist (top,atlas) (g(&0)) p (x n)) /\
     (!M. ?N. !n. N <= n
                  ==> M < mfd_scalar atlas (g(&0)) (x n) *
                          mfd_dist (top,atlas) (g(&0)) p (x n) pow 2)
     ==> ?n e. rfs_evolving_neck (p2b_kview (top,atlas) g) eps (x n) (&0) L e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xin")
    (CONJUNCTS_THEN2 (LABEL_TAC "far") (LABEL_TAC "scale")))))))))))) THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `connected_space (top:B topology) /\
    (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
             ==> &0 <= mfd_sectional atlas ((g:real->B->real^3^3) (&0)) y u v) /\
    riemannian_metric atlas (g(&0))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  (* almost-line pairs along a subsequence *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) (&0)`; `p:B`; `x:num->B`;
                 `\n. mfd_scalar atlas ((g:real->B->real^3^3) (&0)) ((x:num->B) n)`]
                P2BX0_ALMOST_PAIRS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub1:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pairs"))) THEN
  (* the THM_9_64 limit at x o sub1 *)
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `\k:num. (top:B topology)`;
                 `\k:num. (atlas:((B->bool)#(B->real^3))->bool)`;
                 `\k:num. (g:real->B->real^3^3)`; `(x:num->B) o (sub1:num->num)`]
                P2AL84_THM964_AT) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `xl:B`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lim") STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa (top',atlas') (g':real->B->real^3^3)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `connected_space (top':B topology) /\
    (!y u v. y IN topspace top' /\ ~collinear {vec 0,u,v}
             ==> &0 <= mfd_sectional atlas' ((g':real->B->real^3^3) (&0)) y u v) /\
    riemannian_metric atlas' (g'(&0))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top',atlas') (g':real->B->real^3^3)` THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  (* one limit with exposed W, phi on the time set (-1,0] *)
  USE_THEN "lim" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2AL84_FLOW_LIMIT_ON) THEN
  REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B` ASSUME_TAC)) THEN
  SUBGOAL_THEN `(xl:B) IN topspace top'` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> p2al84_mentions "p2c_flow_limit_with" th)) THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    REWRITE_TAC[p2c_flow_limit_with] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`] P2AL84_KVIEW_SLICES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "vreg") (LABEL_TAC "vhaus")) THEN
  (* exact pairs in the limit at time 0 *)
  SUBGOAL_THEN
   `!A. &0 < A
        ==> ?a b. a IN topspace top' /\ b IN topspace top' /\
                  mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) xl a = A /\
                  mfd_dist (top',atlas') (g' (&0)) xl b = A /\
                  mfd_dist (top',atlas') (g' (&0)) a b = &2 * A`
  (LABEL_TAC "lpairs") THENL
   [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`w:B->bool`; `w:B->bool`; `\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`;
      `((x:num->B) o (sub1:num->num)) o (sub2:num->num)`; `\k:num. &0`;
      `\k. mfd_scalar atlas ((g:real->B->real^3^3) (&0))
                      ((x:num->B) ((sub1:num->num) ((sub2:num->num) k)))`;
      `{s:real | --(&1) < s /\ s <= &0}`; `top':B topology`;
      `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
      `W:num->B->bool`; `phi:num->B->B`; `&0`; `A:real`]
     P2BX0_LIMIT_PAIRS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LIM_DIST; LIM_BALL] THEN ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; o_THM] THEN
    ASM_SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "pairs" (MP_TAC o SPECL [`A:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "N" (MP_TAC o SPEC `(sub2:num->num) k`) THEN
    ANTS_TAC THENL
     [MP_TAC(SPEC `sub2:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N <= k:num` THEN ARITH_TAC;
      REWRITE_TAC[]];
    ALL_TAC] THEN
  (* a line and a parallel unit field in the limit at time 0 *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `xl:B`] P2BX0_LINE_FROM_PAIRS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real->B` (LABEL_TAC "line")) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `lam:real->B`] CMPSP_SPLIT_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `X:B->real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `~(!y u v. y IN topspace top' /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas' ((g':real->B->real^3^3) (&0)) y u v)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(g':real->B->real^3^3) (&0)`; `X:B->real^3`; `xl:B`]
                  P2AL84_NOT_POS_SPLIT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* (a): the limit is the cylinder model; (h) with the line: necks at xl *)
  SUBGOAL_THEN `p2b_cyl_model (top',atlas') (g':real->B->real^3^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `P2B_PROP_9_83K_STATEMENT (w:B->bool)` THEN
    REWRITE_TAC[P2B_PROP_9_83K_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `top':B topology`;
                               `atlas':((B->bool)#(B->real^3))->bool`;
                               `g':real->B->real^3^3`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`] P2AL84_CYL_LINE_NECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `lam:real->B` THEN USE_THEN "line" ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`eps:real`; `L + &1`; `&0`; `xl:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^3->B` ASSUME_TAC) THEN
  (* transfer of an eps-neck of length L back to the sequence *)
  MP_TAC(ISPECL [`w:B->bool`; `w:B->bool`] P2B_NECK_OPEN_L) THEN
  REWRITE_TAC[P2B_NECK_OPEN_L_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`p2b_kview (top',atlas') (g':real->B->real^3^3)`; `eps:real`;
                             `xl:B`; `&0`; `L + &1`; `L:real`; `e0:real^3->B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2BL_KVIEW_REGULAR THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "open"))) THEN
  SUBGOAL_THEN
   `p2bl_vslices (\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3))
                 (((x:num->B) o (sub1:num->num)) o (sub2:num->num)) (\k:num. &0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BL_REGULAR_VSLICES THEN REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC P2BL_KVIEW_REGULAR THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `eps < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\k:num. p2b_kview (top,atlas) (g:real->B->real^3^3)`;
                 `((x:num->B) o (sub1:num->num)) o (sub2:num->num)`; `\k:num. &0`;
                 `\k. mfd_scalar atlas ((g:real->B->real^3^3) (&0))
                                 ((x:num->B) ((sub1:num->num) ((sub2:num->num) k)))`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `kappa:real`; `eps:real`; `L + &1`;
                 `e0:real^3->B`;
                 `\V' t' (z:B). ?e':real^3->B. rfs_evolving_neck V' eps z t' L e'`]
                P2BL_NECK_LIMIT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "open" ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[LE_REFL; o_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `e':real^3->B`) THEN
  MAP_EVERY EXISTS_TAC [`(sub1:num->num) ((sub2:num->num) N)`; `e':real^3->B`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The main theorem.  If no D works, choose for each n a point x n outside   *)
(* the ball of radius (n + 1) R(p)^(-1/2) that is no evolving eps-neck       *)
(* centre of length L; then sqrt(R(p)) d(p,x n) >= n+1 and either            *)
(* R(x n) d(p,x n)^2 -> infinity (P2AL84_SPLIT_CASE gives a neck at          *)
(* some x n) or it is bounded along a subsequence (P2AL84_BOUNDED_CASE).     *)
(* ========================================================================= *)

let P2AL84_LEMMA_9_84L = prove
 (`!w:B->bool.
     P2B_THM_9_64_STATEMENT w /\ P2B_LEMMA_9_65_STATEMENT w /\
     P2B_PROP_9_83K_STATEMENT w /\ P2B_CYL_MODEL_NECKS_STATEMENT w
     ==> !eps L kappa top atlas (g:real->B->real^3^3) p.
           &0 < eps /\ eps < &1 / &4 /\ &1 <= L /\
           p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ p IN topspace top
           ==> ?D. &0 < D /\
                   !x. x IN topspace top /\
                       ~(x IN mfd_ball (top,atlas) (g(&0)) p
                                (D * inv(sqrt(mfd_scalar atlas (g(&0)) p))))
                       ==> ?e. rfs_evolving_neck (p2b_kview (top,atlas) g) eps x (&0) L e`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  SUBGOAL_THEN `connected_space (top:B topology) /\
                riemannian_metric atlas ((g:real->B->real^3^3) (&0))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&n + &1` o
    REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`; NOT_FORALL_THM; NOT_IMP]) THEN
  SUBGOAL_THEN `!n. &0 < &n + &1` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LET_ADD THEN REWRITE_TAC[REAL_POS; REAL_LT_01];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->B` (LABEL_TAC "x")) THEN
  SUBGOAL_THEN `!n. (x:num->B) n IN topspace top` (LABEL_TAC "xin") THENL
   [USE_THEN "x" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. &n + &1 <= sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p) *
                   mfd_dist (top,atlas) (g(&0)) p ((x:num->B) n)` (LABEL_TAC "lb") THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "x" (MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) p ((x:num->B) n)`
    (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "xin" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    REWRITE_TAC[REAL_NOT_LT; GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!M. ?N. !n. N <= n ==> M < mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) p ((x:num->B) n)`
  (LABEL_TAC "far") THENL
   [X_GEN_TAC `M:real` THEN
    MP_TAC(SPEC `M * sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p)` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "lb" (MP_TAC o SPEC `n:num`) THEN
    MP_TAC(SPECL [`M:real`;
                  `mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) p ((x:num->B) n)`;
                  `sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p)`]
                 REAL_LT_LMUL_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `N:num <= n` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `M * sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) p) <= &N` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC
   `!M. ?N. !n. N <= n
                ==> M < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) ((x:num->B) n) *
                        mfd_dist (top,atlas) (g(&0)) p (x n) pow 2` THENL
   [MP_TAC(ISPECL [`w:B->bool`; `eps:real`; `L:real`; `kappa:real`; `top:B topology`;
                   `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
                   `x:num->B`] P2AL84_SPLIT_CASE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "x" (MP_TAC o SPEC `n:num`) THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_EXISTS_THM; NOT_IMP; REAL_NOT_LT] o
      check (fun th -> is_neg (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `M:real` ASSUME_TAC) THEN
    MATCH_MP_TAC P2AL84_BOUNDED_CASE THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`;
                          `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                          `p:B`; `x:num->B`; `M:real`] THEN
    ASM_REWRITE_TAC[]]);;

