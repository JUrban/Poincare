(* ========================================================================= *)
(* Unit pc_p2a_s85b: COR_9_94_L piece (b) part (1) at a soul (MT Prop 9.85   *)
(* (1), the soul case).  For eps small and L >= 1 there is D such that for   *)
(* every noncompact kappa-solution with p2b_ksep, positive curvature at time *)
(* 0 and a soul s (every other point regular for d_s, the output of          *)
(* CMP_R5_SOUL), every point outside the ball of radius D R(s)^(-1/2) at     *)
(* time 0 is the centre of an evolving eps-neck of length L.  MT's proof:    *)
(* the THM_9_64 limit at the souls (uniform kappa0 by PROP_9_58) has necks   *)
(* outside a ball (P2AL84_LEMMA_9_84L); they transfer to annuli              *)
(* (P2AS85_UNIF_TRANSFER); a bad point q_k closest to s_k beyond the annulus *)
(* escapes to infinity, has a neck centre y_k nearby with R d^2 -> infinity  *)
(* (LEMMA_9_65); the neck sphere at y_k bounds the soul side                 *)
(* (P2B_SOUL_TOPOLOGY part 2), so split points of minimizing segments from   *)
(* the soul side to a ray give a line in the limit at y_k                    *)
(* (P2AS85_LINE_FROM_SPLITS); the limit is the cylinder (a), the line        *)
(* excludes the Z/2 model, (h) makes all its points necks, and they transfer *)
(* back to q_k.                                                              *)
(* ========================================================================= *)

needs "src/pc_p2a_s85a.ml";;
needs "src/pc_p2b_tubelim2.ml";;
needs "src/pc_cmp_soul.ml";;
needs "src/pc_apx_chain.ml";;
needs "src/pc_rfa_tmaxp.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The uniform kappa0 (PROP_9_58; a noncompact slice is not round,           *)
(* P2AS85_NOT_ROUND) and the choice of an almost closest bad point q beyond  *)
(* the distance c from s, with a good point y on a segment from q towards s  *)
(* at a distance small in the scale of R(q) (the slack is chosen from the    *)
(* maximum of R on a compact ball).                                          *)
(* ========================================================================= *)

let P2AS85_KAPPA0 = prove
 (`!w:B->bool.
     P2B_PROP_9_58_STATEMENT w
     ==> ?kappa0. &0 < kappa0 /\
           !kappa top atlas (g:real->B->real^3^3).
              p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
              ~compact_space top
              ==> p2b_kappa_solution kappa0 (top,atlas) g`,
  GEN_TAC THEN REWRITE_TAC[P2B_PROP_9_58_STATEMENT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `kappa0:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AS85_NOT_ROUND THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  ASM_SIMP_TAC[REAL_LE_REFL] THEN
  UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
  SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol]);;

let P2AS85_SELECT = prove
 (`!top atlas (g:B->real^3^3) s (P:B->bool) c c0 delta.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ s IN topspace top /\
     (!z. z IN topspace top ==> &0 <= mfd_scalar atlas g z) /\
     &0 < c /\ &0 < c0 /\ &0 < delta /\
     (?x. x IN topspace top /\ ~P x /\ c <= mfd_dist (top,atlas) g s x)
     ==> ?q y. q IN topspace top /\ ~P q /\ c <= mfd_dist (top,atlas) g s q /\
               y IN topspace top /\ mfd_dist (top,atlas) g q y <= c0 /\
               sqrt(mfd_scalar atlas g q) * mfd_dist (top,atlas) g q y <= delta /\
               (c + c0 <= mfd_dist (top,atlas) g s q ==> P y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b:B. a IN topspace top /\ b IN topspace top
                        ==> mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) a b`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S = {mfd_dist (top,atlas) (g:B->real^3^3) s z |
                   z | z IN topspace top /\ ~P z /\ c <= mfd_dist (top,atlas) g s z}` THEN
  SUBGOAL_THEN `~(S:real->bool = {}) /\ (!u. u IN S ==> c <= u)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`mfd_dist (top,atlas) (g:B->real^3^3) s x`; `x:B`] THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `S:real->bool` INF) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `m = inf S` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lb") (LABEL_TAC "glb")) THEN
  SUBGOAL_THEN `c <= m` ASSUME_TAC THENL
   [USE_THEN "glb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the maximum of R on a closed ball containing all candidates *)
  MP_TAC(ISPECL [`top:B topology`;
                 `\x:B. --(mfd_scalar atlas (g:B->real^3^3) x)`;
                 `mfd_cball (top,atlas) (g:B->real^3^3) s (m + c0)`] RFA_CMAP_COMPACT_MIN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_complete (top,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)` THEN
      REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `s:B` THEN
      REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_NEG2] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:B` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rmax"))) THEN
  ABBREV_TAC `Cm = abs(mfd_scalar atlas (g:B->real^3^3) x1) + &1` THEN
  SUBGOAL_THEN `&0 < Cm` ASSUME_TAC THENL [EXPAND_TAC "Cm" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt Cm` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `eta = min c0 (delta / sqrt Cm)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= c0 /\ eta <= delta / sqrt Cm` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN
    SUBGOAL_THEN `&0 < delta / sqrt Cm` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt Cm * eta <= delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt Cm * delta / sqrt Cm` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < sqrt Cm` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  (* an almost minimal bad point *)
  SUBGOAL_THEN
   `?q:B. q IN topspace top /\ ~P q /\ c <= mfd_dist (top,atlas) (g:B->real^3^3) s q /\
          mfd_dist (top,atlas) g s q < m + eta / &2`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `m + eta / &2 <= m` MP_TAC THENL
     [USE_THEN "glb" MATCH_MP_TAC THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `z:B` THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC
       `~(?q:B. q IN topspace top /\ ~P q /\
                c <= mfd_dist (top,atlas) (g:B->real^3^3) s q /\
                mfd_dist (top,atlas) g s q < m + eta / &2)` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `z:B` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:B->real^3^3) q <= Cm` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `mfd_scalar atlas (g:B->real^3^3) x1` THEN
    CONJ_TAC THENL
     [USE_THEN "rmax" MATCH_MP_TAC THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
      CONJ_TAC THENL [USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      EXPAND_TAC "Cm" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(mfd_scalar atlas (g:B->real^3^3) q) <= sqrt Cm` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `q:B` THEN
  ASM_CASES_TAC `c + c0 <= mfd_dist (top,atlas) (g:B->real^3^3) s q` THENL
   [ALL_TAC;
    EXISTS_TAC `q:B` THEN ASM_SIMP_TAC[MFD_DIST_REFL; REAL_MUL_RZERO; REAL_LT_IMP_LE]] THEN
  (* a point at distance eta from q on a minimizing segment towards s *)
  SUBGOAL_THEN `~(s:B = q)` ASSUME_TAC THENL
   [DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th])) THEN
    UNDISCH_TAC `c <= mfd_dist (top,atlas) (g:B->real^3^3) s s` THEN
    ASM_SIMP_TAC[MFD_DIST_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `q:B`; `s:B`] APXT_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `q:B`; `u:real^3`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "lip")))) THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:B->real^3^3) s q = mfd_dist (top,atlas) g q s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `eta <= mfd_dist (top,atlas) (g:B->real^3^3) q s` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `y = mfd_geo (top,atlas) (g:B->real^3^3) q u eta` THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:B->real^3^3) q y <= eta` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `mfd_dist (top,atlas) (g:B->real^3^3) (mfd_geo (top,atlas) g q u (&0))
               (mfd_geo (top,atlas) g q u eta) <= abs(eta - &0)` MP_TAC THENL
     [USE_THEN "lip" (fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[ASSUME `mfd_geo (top,atlas) (g:B->real^3^3) q u (&0) = q`;
                  ASSUME `mfd_geo (top,atlas) (g:B->real^3^3) q u eta = y`]] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) (g:B->real^3^3) s y <= mfd_dist (top,atlas) g q s - eta`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `s:B`; `y:B`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `mfd_dist (top,atlas) (g:B->real^3^3) (mfd_geo (top,atlas) g q u eta)
               (mfd_geo (top,atlas) g q u (mfd_dist (top,atlas) g q s)) <=
      abs(mfd_dist (top,atlas) g q s - eta)` MP_TAC THENL
     [USE_THEN "lip" (fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[ASSUME `mfd_geo (top,atlas) (g:B->real^3^3) q u eta = y`;
                  ASSUME `mfd_geo (top,atlas) (g:B->real^3^3) q u
                            (mfd_dist (top,atlas) g q s) = s`]] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt Cm * eta` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `m <= mfd_dist (top,atlas) (g:B->real^3^3) s y` MP_TAC THENL
     [USE_THEN "lb" MATCH_MP_TAC THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `s:B`; `y:B`; `q:B`] MFD_DIST_TRIANGLE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `y:B`; `q:B`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* Necks on annuli about the base points. If the THM_9_64 limit at s k has   *)
(* (eps/4)-necks of length L + 1 at all points at distance at least D' (any  *)
(* real) from its base point, then for every rho and k large, every y with   *)
(* D' + 1 <= sqrt(Q k) d(s k,y) <= rho is the centre of an evolving eps-neck *)
(* of length L.  Proof: one p2c_flow_limit_with on a long enough time set    *)
(* (P2AL84_FLOW_LIMIT_ON), LIM_BALL and LIM_DIST locate y = phi k z with z   *)
(* in a compact ball; the neck at z lies in a fixed compact ball             *)
(* (P2BTL_NECK_IN_BALL with R bounded below there) and P2AS85_UNIF_TRANSFER  *)
(* moves it to y.                                                            *)
(* ========================================================================= *)

let P2AS85_ANNULUS_NECKS = prove
 (`?epsA. &0 < epsA /\
     !(top:num->B topology) atlas (g:num->real->B->real^3^3) (s0:num->B) Q kappa kappa'
      (top':B topology) atlas' g' sl D' eps L.
        (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ s0 k IN topspace (top k)) /\
        (!Tl. &0 < Tl
              ==> p3_flow_limit (\k. p2b_kview (top k,atlas k) (g k)) s0 (\k. &0) Q
                                (top',atlas') g' sl Tl) /\
        p2b_kappa_solution kappa' (top',atlas') g' /\
        (!z. z IN topspace top' ==> &0 < mfd_scalar atlas' (g'(&0)) z) /\
        (!z. z IN topspace top' /\ D' <= mfd_dist (top',atlas') (g'(&0)) sl z
             ==> ?e. rfs_evolving_neck (p2b_kview (top',atlas') g') (eps / &4) z (&0)
                                       (L + &1) e) /\
        &0 < eps /\ eps <= epsA /\ &1 <= L
        ==> !rho. ?k0. !k y.
              k0 <= k /\ y IN topspace (top k) /\
              D' + &1 <= sqrt(Q k) * mfd_dist (top k,atlas k) (g k (&0)) (s0 k) y /\
              sqrt(Q k) * mfd_dist (top k,atlas k) (g k (&0)) (s0 k) y <= rho
              ==> ?e. rfs_evolving_neck (p2b_kview (top k,atlas k) (g k)) eps y (&0) L e`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nib"))
    (INST_TYPE [`:B`,`:A`] P2BTL_NECK_IN_BALL) THEN
  EXISTS_TAC `min (&1 / &8) (&4 * e0)` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "seq") (CONJUNCTS_THEN2 (LABEL_TAC "lim")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rpos")
    (CONJUNCTS_THEN2 (LABEL_TAC "necks") STRIP_ASSUME_TAC))))) THEN
  X_GEN_TAC `rho:real` THEN
  SUBGOAL_THEN `eps < &1 / &4 /\ eps / &4 <= e0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa' (top',atlas') (g':real->B->real^3^3)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `connected_space (top':B topology) /\
                riemannian_metric (atlas':((B->bool)#(B->real^3))->bool)
                                  ((g':real->B->real^3^3) (&0))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa' (top',atlas') (g':real->B->real^3^3)` THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sl:B) IN topspace top'` ASSUME_TAC THENL
   [USE_THEN "lim" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; p3_flow_limit] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  (* a lower bound of R on a compact ball *)
  ABBREV_TAC `Kb = mfd_cball (top',atlas') ((g':real->B->real^3^3) (&0)) sl (rho + &2)` THEN
  SUBGOAL_THEN `compact_in (top':B topology) Kb` ASSUME_TAC THENL
   [EXPAND_TAC "Kb" THEN
    UNDISCH_TAC `mfd_complete (top',atlas') ((g':real->B->real^3^3) (&0))` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?R0. &0 < R0 /\ !z. z IN Kb ==> R0 <= mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) z`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `Kb:B->bool = {}` THENL
     [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`;
                   `mfd_scalar atlas' ((g':real->B->real^3^3) (&0))`; `Kb:B->bool`]
                  RFA_CMAP_COMPACT_MIN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z0:B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) z0` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "rpos" MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `Kb:B->bool`] COMPACT_IN_SUBSET_TOPSPACE) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Tm = (L + &1) / R0 + &1` THEN
  SUBGOAL_THEN `&0 < Tm /\ L + &1 <= R0 * Tm` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Tm" THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN
      SUBGOAL_THEN `R0 * (L + &1) / R0 = L + &1` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < R0` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the flow limit with exposed W, phi on (-(Tm + 1),0] *)
  USE_THEN "lim" (MP_TAC o SPEC `Tm + &1`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2AL84_FLOW_LIMIT_ON) THEN
  REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B` ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(!n tau. ~(topspace(rfs_vtop (p2b_kview ((top:num->B topology) n,atlas n)
                                    ((g:num->real->B->real^3^3) n)) tau) = {})
             ==> smooth_manifold_atlas (rfs_vtop (p2b_kview (top n,atlas n) (g n)) tau)
                                       (rfs_vatlas (p2b_kview (top n,atlas n) (g n)) tau) /\
                 riemannian_metric (rfs_vatlas (p2b_kview (top n,atlas n) (g n)) tau)
                                   (rfs_vmetric (p2b_kview (top n,atlas n) (g n)) tau)) /\
    (!n tau. hausdorff_space (rfs_vtop (p2b_kview (top n,atlas n) (g n)) tau))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `n:num` THEN
    USE_THEN "seq" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL84_KVIEW_SLICES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&0) IN {s:real | --(Tm + &1) < s /\ s <= &0}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* LIM_BALL: the points y lie in images of a compact set *)
  MP_TAC(ISPECL [`\k. p2b_kview ((top:num->B topology) k,atlas k) ((g:num->real->B->real^3^3) k)`;
                 `s0:num->B`; `\k:num. &0`; `Q:num->real`;
                 `{s:real | --(Tm + &1) < s /\ s <= &0}`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `sl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `&0`; `abs rho + &1`]
                (REWRITE_RULE[LIM_BALL_STATEMENT] (ISPECL [`u:B->bool`; `w:B->bool`] LIM_BALL))) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:B->bool` (X_CHOOSE_THEN `k1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ball")))) THEN
  SUBGOAL_THEN `compact_in (top':B topology) (sl INSERT K)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `(a:B) INSERT s = {a} UNION s`] THEN
    MATCH_MP_TAC COMPACT_IN_UNION THEN ASM_REWRITE_TAC[COMPACT_IN_SING];
    ALL_TAC] THEN
  (* LIM_DIST on K and the base point *)
  MP_TAC(ISPECL [`\k. p2b_kview ((top:num->B topology) k,atlas k) ((g:num->real->B->real^3^3) k)`;
                 `s0:num->B`; `\k:num. &0`; `Q:num->real`;
                 `{s:real | --(Tm + &1) < s /\ s <= &0}`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `sl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `&0`; `(sl:B) INSERT K`; `&1 / &2`]
                (REWRITE_RULE[LIM_DIST_STATEMENT] (ISPECL [`u:B->bool`; `w:B->bool`] LIM_DIST))) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num` (LABEL_TAC "dist")) THEN
  (* the compact set holding all neck regions *)
  ABBREV_TAC `C = mfd_cball (top',atlas') ((g':real->B->real^3^3) (&0)) sl
                    (rho + &2 + &12 / &5 * inv(sqrt R0) * inv eps)` THEN
  SUBGOAL_THEN `compact_in (top':B topology) C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    UNDISCH_TAC `mfd_complete (top',atlas') ((g':real->B->real^3^3) (&0))` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k. p2b_kview ((top:num->B topology) k,atlas k) ((g:num->real->B->real^3^3) k)`;
                 `s0:num->B`; `\k:num. &0`; `Q:num->real`;
                 `{s:real | --(Tm + &1) < s /\ s <= &0}`; `kappa':real`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `sl:B`;
                 `W:num->B->bool`; `phi:num->B->B`; `C:B->bool`; `&19 / &10 * (eps / &4)`;
                 `eps:real`; `L + &1`; `L:real`; `R0:real`; `Tm:real`]
                P2AS85_UNIF_TRANSFER) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC) THEN
    TRY(REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k3:num` (LABEL_TAC "tr")) THEN
  EXISTS_TAC `MAX k1 (MAX k2 k3)` THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:B`] THEN
  REWRITE_TAC[ARITH_RULE `MAX a (MAX b c) <= k <=> a <= k /\ b <= k /\ c <= k`] THEN
  STRIP_TAC THEN
  USE_THEN "seq" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
               ((g:num->real->B->real^3^3) k)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `connected_space ((top:num->B topology) k)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
                   ((g:num->real->B->real^3^3) k)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (Q:num->real) k` ASSUME_TAC THENL
   [USE_THEN "lim" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; p3_flow_limit] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  (* y = phi k z with z in K *)
  USE_THEN "ball" (MP_TAC o SPECL [`k:num`; `y:B`]) THEN
  REWRITE_TAC[P2BL_KVIEW_ACCESS; real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  ASM_SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ; SQRT_POS_LT] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:B` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(z:B) IN topspace top'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `K:B->bool`] COMPACT_IN_SUBSET_TOPSPACE) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  (* the distance of z from the base point of the limit *)
  USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `sl:B`; `z:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  REWRITE_TAC[P2BL_KVIEW_ACCESS; real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL] THEN
  SUBGOAL_THEN `(phi:num->B->B) k sl = s0 k` SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> p2al84_mentions "p2c_flow_limit_with" th)) THEN
    SIMP_TAC[p2c_flow_limit_with];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top',atlas':((B->bool)#(B->real^3))->bool) sl z` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `D' <= mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) sl z /\
    mfd_dist (top',atlas') (g'(&0)) sl z < rho + &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the neck at z, its region in C, R(z) >= R0 *)
  USE_THEN "necks" (MP_TAC o SPEC `z:B`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `e:real^3->B`) THEN
  SUBGOAL_THEN `R0 <= mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) z` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "Kb" THEN
    REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `eps / &4`; `z:B`; `L + &1`; `e:real^3->B`]
                P2BL_KVIEW_NECK0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "nib" (MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                                  `(g':real->B->real^3^3) (&0)`; `eps / &4`; `z:B`;
                                  `e:real^3->B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "tr" (MP_TAC o SPECL [`k:num`; `z:B`; `e:real^3->B`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BTL_EVNECK_MONO THEN
      MAP_EVERY EXISTS_TAC [`eps / &4`; `L + &1`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC P2BL_KVIEW_REGULAR THEN EXISTS_TAC `kappa':real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (top',atlas') ((g':real->B->real^3^3) (&0)) z
                  (&3 / &5 * inv(sqrt(mfd_scalar atlas' (g'(&0)) z)) * inv(eps / &4))` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `v:B` THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `z:B` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) sl z +
                mfd_dist (top',atlas') (g'(&0)) z v` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a < r + &1 /\ b <= c ==> a + b <= r + &2 + c`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 / &5 * inv(sqrt(mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) z)) *
                inv(eps / &4)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(sqrt(mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) z)) * inv eps <=
                  inv(sqrt R0) * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_INV_DIV; real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `(phi:num->B->B) k o (e:real^3->B)` THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* ========================================================================= *)
(* Split points at a neck about the soul. For an eps-neck at y whose sphere  *)
(* separates the soul s from the far end of the neck, P2B_SOUL_TOPOLOGY part *)
(* 2 gives a ball chart b with s in the soul side S = b(ball(0,1)) and       *)
(* b(sphere) = the neck sphere.  A C1 curve from S to a point outside S      *)
(* meets the neck sphere (the frontier of S). For r < A < d(y,s), with the   *)
(* neck region in the ball B(y,r): the point a at distance A from y on a     *)
(* segment from y to s lies in S, the point b at distance A on a ray from y  *)
(* lies outside S, and a segment from a to b meets the sphere at a point m   *)
(* with d(a,m) + d(m,b) = d(a,b).                                            *)
(* ========================================================================= *)

let P2AS85_CURVE_CROSS = prove
 (`!top atlas (c:real->B) t0 t1 S Sg.
     mfd_c1_curve (top,atlas:((B->bool)#(B->real^3))->bool) c t0 t1 /\
     open_in top S /\ top closure_of S SUBSET S UNION Sg /\
     (?t. t0 <= t /\ t <= t1 /\ c t IN S) /\ (?t. t0 <= t /\ t <= t1 /\ ~(c t IN S))
     ==> ?t. t0 <= t /\ t <= t1 /\ c t IN Sg`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `t':real` STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GRGD_CURVE_CONTINUOUS) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(c:real->B) o drop`;
                 `subtopology euclidean (interval[lift t0,lift t1])`; `top:B topology`;
                 `interval[lift t0,lift t1]`] CONNECTED_IN_CONTINUOUS_MAP_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL; CONNECTED_IN_EUCLIDEAN;
                    CONNECTED_INTERVAL];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`;
                 `IMAGE ((c:real->B) o drop) (interval[lift t0,lift t1])`; `S:B->bool`]
                CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THENL
     [EXISTS_TAC `(c:real->B) t`; EXISTS_TAC `(c:real->B) t'`] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_IMAGE; o_THM] THENL
     [EXISTS_TAC `lift t`; EXISTS_TAC `lift t'`] THEN
    ASM_REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:B` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `v:real^1` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `drop v` THEN
  UNDISCH_TAC `(v:real^1) IN interval[lift t0,lift t1]` THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `top frontier_of (S:B->bool) SUBSET Sg` MP_TAC THENL
   [REWRITE_TAC[frontier_of] THEN
    MP_TAC(ISPECL [`top:B topology`; `S:B->bool`] INTERIOR_OF_OPEN_IN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* Segments of geodesics in a complete manifold are C1 curves of Lipschitz  *)
(* displacement.                                                             *)

let P2AS85_GEO_SEG = prove
 (`!top atlas (g:B->real^3^3) x u a b.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ x IN topspace top /\ mfd_tnorm g x u = &1 /\
     &0 <= a /\ a <= b
     ==> mfd_c1_curve (top,atlas) (mfd_geo (top,atlas) g x u) a b /\
         mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x u a) (mfd_geo (top,atlas) g x u b)
         <= b - a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `x:B`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[MFD_JOINABLE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` (ASSUME_TAC o CONJUNCT1)) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `u:real^3`; `b:real`] GEOH_RAY_FACTS) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real`; `b:real`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN SIMP_TAC[]);;

(* Split points at a neck that separates the soul from its far end.         *)

let P2AS85_SPLIT_TRIPLE_SEP = prove
 (`!w:B->bool.
     P2B_SOUL_TOPOLOGY_STATEMENT w
     ==> ?epsS. &0 < epsS /\
           !eps top atlas (g:B->real^3^3) s y e r A.
             &0 < eps /\ eps <= epsS /\ hausdorff_space top /\ connected_space top /\
             smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
             mfd_complete (top,atlas) g /\ ~compact_space top /\
             s IN topspace top /\
             (!x. x IN topspace top /\ ~(x = s) ==> p2b_dist_regular (top,atlas) g s x) /\
             rfs_neck (top,atlas) g eps y e /\
             apx_separates top (IMAGE e (sphere(vec 0,&1))) s (e(&4 / &3 % basis 1)) /\
             IMAGE e (rfs_neck_dom eps) SUBSET mfd_ball (top,atlas) g y r /\
             &0 < r /\ r < A /\ A < mfd_dist (top,atlas) g y s
             ==> ?a b m. a IN topspace top /\ b IN topspace top /\ m IN topspace top /\
                         mfd_dist (top,atlas) g y a = A /\ mfd_dist (top,atlas) g y b = A /\
                         mfd_dist (top,atlas) g y m < r /\
                         mfd_dist (top,atlas) g a m + mfd_dist (top,atlas) g m b =
                         mfd_dist (top,atlas) g a b`,
  GEN_TAC THEN REWRITE_TAC[P2B_SOUL_TOPOLOGY_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "soul"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b:B. a IN topspace top /\ b IN topspace top
                        ==> mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) a b`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) eps y e` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->B`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:B. p IN IMAGE (e:real^3->B) (sphere(vec 0,&1))
                      ==> p IN topspace top /\ mfd_dist (top,atlas) (g:B->real^3^3) y p < r`
  (LABEL_TAC "sph") THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN X_GEN_TAC `p:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:B) IN mfd_ball (top,atlas) (g:B->real^3^3) y r` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((s:B) IN IMAGE e (rfs_neck_dom eps))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(s:B) IN mfd_ball (top,atlas) (g:B->real^3^3) y r` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the ball chart of the soul side *)
  REMOVE_THEN "soul" (MP_TAC o SPECL [`eps:real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `s:B`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`y:B`; `e:real^3->B`] o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->B` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `f':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `mfd_ball_chart top atlas (b:real^3->B)` THEN
  REWRITE_TAC[mfd_ball_chart] THEN DISCH_TAC THEN
  ABBREV_TAC `S = IMAGE (b:real^3->B) (ball(vec 0,&1))` THEN
  SUBGOAL_THEN `open_in (top:B topology) S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (top:B topology) (IMAGE (b:real^3->B) (cball(vec 0,&1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
    ASM_REWRITE_TAC[COMPACT_CBALL; SUBSET_BALLS; DIST_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (b:real^3->B) (cball(vec 0,&1)) =
                S UNION IMAGE (e:real^3->B) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && can (find_term (fun t -> t = `sphere(vec 0:real^3,&1)`)) (lhs(concl th)) &&
      p2azq_mentions "IMAGE" th && can (find_term (fun t -> t = `b:real^3->B`)) (concl th))) THEN
    REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of S SUBSET S UNION IMAGE (e:real^3->B) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(lhs(concl th)) = `cball(vec 0:real^3,&1)`)) THEN
    MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
     [EXPAND_TAC "S" THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `IMAGE (b:real^3->B) (cball(vec 0,&1))`; `y:B`] APXT_COMPACT_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `D0:real` (LABEL_TAC "bdd")) THEN
  (* the point a on a segment from y to s *)
  SUBGOAL_THEN `~(s:B = y)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `A < mfd_dist (top,atlas) (g:B->real^3^3) y y` THEN
    ASM_SIMP_TAC[MFD_DIST_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `s:B`] APXT_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `l = mfd_dist (top,atlas) (g:B->real^3^3) y s` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `u:real^3`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gin")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "lip")))) THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t <= l
        ==> mfd_dist (top,atlas) (g:B->real^3^3) y (mfd_geo (top,atlas) g y u t) = t`
  (LABEL_TAC "exact") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `y:B`; `u:real^3`; `&0`; `t:real`] P2AS85_GEO_SEG) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `y:B`; `u:real^3`; `t:real`; `l:real`] P2AS85_GEO_SEG) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `y:B`; `mfd_geo (top,atlas) (g:B->real^3^3) y u t`;
                   `s:B`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `a = mfd_geo (top,atlas) (g:B->real^3^3) y u A` THEN
  SUBGOAL_THEN `(a:B) IN S` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `mfd_geo (top,atlas) (g:B->real^3^3) y u`; `A:real`; `l:real`; `S:B->bool`;
                   `IMAGE (e:real^3->B) (sphere(vec 0,&1))`] P2AS85_CURVE_CROSS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:B->real^3^3`; `y:B`; `u:real^3`; `A:real`; `l:real`]
                      P2AS85_GEO_SEG) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        EXISTS_TAC `l:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXISTS_TAC `A:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "sph" (MP_TAC o SPEC `mfd_geo (top,atlas) (g:B->real^3^3) y u t1`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    USE_THEN "exact" (MP_TAC o SPEC `t1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the point b on a ray from y *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`] CMPSO_RAY_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u':real^3` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `cmp_ray (top,atlas) (g:B->real^3^3) (mfd_geo (top,atlas) g y u')` THEN
  REWRITE_TAC[cmp_ray] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rin") (LABEL_TAC "ray")) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `u':real^3`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `!t. &0 <= t
        ==> mfd_dist (top,atlas) (g:B->real^3^3) y (mfd_geo (top,atlas) g y u' t) = t`
  (LABEL_TAC "rexact") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "ray" (MP_TAC o SPECL [`&0`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `mfd_geo (top,atlas) (g:B->real^3^3) y u' (&0) = y`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `bb = mfd_geo (top,atlas) (g:B->real^3^3) y u' A` THEN
  SUBGOAL_THEN `~((bb:B) IN S)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `mfd_geo (top,atlas) (g:B->real^3^3) y u'`; `A:real`; `abs D0 + A + &1`;
                   `S:B->bool`; `IMAGE (e:real^3->B) (sphere(vec 0,&1))`] P2AS85_CURVE_CROSS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:B->real^3^3`; `y:B`; `u':real^3`; `A:real`; `abs D0 + A + &1`]
                      P2AS85_GEO_SEG) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        EXISTS_TAC `A:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXISTS_TAC `abs D0 + A + &1` THEN REWRITE_TAC[REAL_LE_REFL] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_TAC THEN
        USE_THEN "bdd" (MP_TAC o SPEC `mfd_geo (top,atlas) (g:B->real^3^3) y u' (abs D0 + A + &1)`) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
        USE_THEN "rexact" (MP_TAC o SPEC `abs D0 + A + &1`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "sph" (MP_TAC o SPEC `mfd_geo (top,atlas) (g:B->real^3^3) y u' t1`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    USE_THEN "rexact" (MP_TAC o SPEC `t1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* a segment from a to bb crosses the neck sphere *)
  SUBGOAL_THEN `(a:B) IN topspace top /\ (bb:B) IN topspace top` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN EXPAND_TAC "bb" THEN CONJ_TAC THENL
     [USE_THEN "gin" (fun th -> REWRITE_TAC[th]);
      USE_THEN "rin" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(bb:B = a)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `a:B`; `bb:B`] APXT_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `dab = mfd_dist (top,atlas) (g:B->real^3^3) a bb` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `a:B`; `v:real^3`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "vin") (K ALL_TAC))) THEN
  SUBGOAL_THEN `&0 <= dab` ASSUME_TAC THENL
   [EXPAND_TAC "dab" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) a v`; `&0`; `dab:real`; `S:B->bool`;
                 `IMAGE (e:real^3->B) (sphere(vec 0,&1))`] P2AS85_CURVE_CROSS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `a:B`; `v:real^3`; `&0`; `dab:real`] P2AS85_GEO_SEG) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; SIMP_TAC[]];
      EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      EXISTS_TAC `dab:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`a:B`; `bb:B`; `mfd_geo (top,atlas) (g:B->real^3^3) a v t1`] THEN
  USE_THEN "sph" (MP_TAC o SPEC `mfd_geo (top,atlas) (g:B->real^3^3) a v t1`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `mfd_geo (top,atlas) (g:B->real^3^3) y u A = a`)) THEN
    USE_THEN "exact" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `mfd_geo (top,atlas) (g:B->real^3^3) y u' A = bb`)) THEN
    USE_THEN "rexact" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `a:B`; `v:real^3`; `&0`; `t1:real`] P2AS85_GEO_SEG) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `a:B`; `v:real^3`; `t1:real`; `dab:real`] P2AS85_GEO_SEG) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `a:B`; `mfd_geo (top,atlas) (g:B->real^3^3) a v t1`;
                 `bb:B`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* from pc_apx_class.ml (APX_NECK_DOM_ANNULUS, APX_BEXT_RADIUS) *)
let P2AS85_NECK_DOM_ANNULUS = prove
 (`!eps. rfs_neck_dom eps =
         annulus (exp(--inv eps / sqrt(&2))) (exp(inv eps / sqrt(&2)))`,
  REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab]);;

let P2AS85_BEXT_RADIUS = prove
 (`!eps. &0 < eps /\ eps <= &1 / &8
         ==> &2 < exp(inv eps / sqrt(&2)) /\
             annulus (&1) (exp(inv eps / sqrt(&2))) SUBSET rfs_neck_dom eps /\
             sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&8 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &8`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 <= inv eps / sqrt(&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `inv eps / sqrt(&2)` REAL_EXP_LE_X) THEN DISCH_TAC THEN
  SUBGOAL_THEN `exp(--inv eps / sqrt(&2)) < &1` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LNEG; GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN REWRITE_TAC[REAL_ARITH `--x < &0 <=> &0 < x`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&8 <= x ==> &0 < x`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[P2AS85_NECK_DOM_ANNULUS; SUBSET; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[P2AS85_NECK_DOM_ANNULUS; SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
    ASM_REAL_ARITH_TAC]);;

(* The orientation of the neck: apx_sphere_sep separates e(3/4 e1) from     *)
(* e(4/3 e1); if s lies with e(4/3 e1), the flipped neck apx_rev e (same    *)
(* sphere, same region, e(3/4 e1) as the far point) is used.                 *)

let P2AS85_REV_SPHERE = prove
 (`!e:real^3->B. IMAGE (apx_rev e) (sphere(vec 0,&1)) = IMAGE e (sphere(vec 0,&1))`,
  GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `(!y. y IN s ==> (f:real^3->B) y = h y) ==> IMAGE f s = IMAGE h s`) THEN
  SIMP_TAC[apx_rev; IN_SPHERE_0; REAL_POW_ONE; REAL_INV_1; VECTOR_MUL_LID]);;

let P2AS85_REV_FAR = prove
 (`!e:real^3->B. apx_rev e (&4 / &3 % basis 1) = e(&3 / &4 % basis 1)`,
  GEN_TAC THEN REWRITE_TAC[apx_rev; NORM_MUL; VECTOR_MUL_ASSOC] THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN AP_TERM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let P2AS85_SPLIT_TRIPLE = prove
 (`!w:B->bool.
     P2B_SOUL_TOPOLOGY_STATEMENT w
     ==> ?epsS. &0 < epsS /\
           !eps top atlas (g:B->real^3^3) s y e r A.
             &0 < eps /\ eps <= epsS /\ hausdorff_space top /\ connected_space top /\
             smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
             mfd_complete (top,atlas) g /\ ~compact_space top /\ apx_sphere_sep top atlas /\
             s IN topspace top /\
             (!x. x IN topspace top /\ ~(x = s) ==> p2b_dist_regular (top,atlas) g s x) /\
             rfs_neck (top,atlas) g eps y e /\
             IMAGE e (rfs_neck_dom eps) SUBSET mfd_ball (top,atlas) g y r /\
             &0 < r /\ r < A /\ A < mfd_dist (top,atlas) g y s
             ==> ?a b m. a IN topspace top /\ b IN topspace top /\ m IN topspace top /\
                         mfd_dist (top,atlas) g y a = A /\ mfd_dist (top,atlas) g y b = A /\
                         mfd_dist (top,atlas) g y m < r /\
                         mfd_dist (top,atlas) g a m + mfd_dist (top,atlas) g m b =
                         mfd_dist (top,atlas) g a b`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2AS85_SPLIT_TRIPLE_SEP) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep"))) THEN
  EXISTS_TAC `min e1 (&1 / &8)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `annulus (&1 / &2) (&2) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2AS85_BEXT_RADIUS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[P2AS85_NECK_DOM_ANNULUS; SUBSET; annulus; IN_ELIM_THM] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_EXP_NEG] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ABBREV_TAC `R = exp(inv eps / sqrt(&2))` THEN DISCH_TAC THEN
    SUBGOAL_THEN `inv R < &1 / &2` ASSUME_TAC THENL
     [MP_TAC(SPECL [`&2`; `R:real`] REAL_LT_INV2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `v:real^3` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_neck_chart top atlas (e:real^3->B)` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_neck_chart] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) eps y e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `apx_separates top (IMAGE e (sphere(vec 0,&1))) ((e:real^3->B)(&3 / &4 % basis 1))
                  (e(&4 / &3 % basis 1))` MP_TAC THENL
   [UNDISCH_TAC `apx_sphere_sep top (atlas:((B->bool)#(B->real^3))->bool)` THEN
    REWRITE_TAC[apx_sphere_sep] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[apx_separates] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:B) IN topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_TAC THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(s:B) IN mfd_ball (top,atlas) (g:B->real^3^3) y r` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC
   `connected_component_of (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
                           (s:B) ((e:real^3->B)(&4 / &3 % basis 1))` THENL
   [USE_THEN "sep" (MP_TAC o SPECL [`eps:real`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `s:B`; `y:B`;
      `apx_rev (e:real^3->B)`; `r:real`; `A:real`]) THEN
    REWRITE_TAC[P2AS85_REV_SPHERE; P2AS85_REV_FAR; APX_REV_IMAGE_DOM] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[APX_REV_NECK] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[apx_separates] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        UNDISCH_TAC
         `~connected_component_of (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
                                  ((e:real^3->B)(&3 / &4 % basis 1)) (e(&4 / &3 % basis 1))` THEN
        REWRITE_TAC[] THEN ASM_MESON_TAC[CONNECTED_COMPONENT_OF_SYM;
                                          CONNECTED_COMPONENT_OF_TRANS]];
      SIMP_TAC[]];
    USE_THEN "sep" (MP_TAC o SPECL [`eps:real`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `s:B`; `y:B`;
      `e:real^3->B`; `r:real`; `A:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[apx_separates] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* A line in the limit at the neck centres. Exact split triples from         *)
(* approximate ones on compact sets (the argument of P2BX0_PAIRS_FROM_SUP of *)
(* pc_p2b_x0 on a triple product); then, for a flow limit at points y k with *)
(* split triples in the views at rescaled distance A from y k and split      *)
(* point within c0, LIM_BALL and LIM_DIST give approximate triples in the    *)
(* limit, hence exact ones, and P2AS85_LINE_FROM_SPLITS gives a line at time *)
(* 0.                                                                        *)
(* ========================================================================= *)

let P2AS85_SPLITS_FROM_APPROX = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) xl K Km A.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ connected_space top /\
     xl IN topspace top /\ compact_in top K /\ compact_in top Km /\
     (!e. &0 < e
          ==> ?a b m. a IN K /\ b IN K /\ m IN Km /\
                      abs(mfd_dist (top,atlas) g xl a - A) < e /\
                      abs(mfd_dist (top,atlas) g xl b - A) < e /\
                      mfd_dist (top,atlas) g a m + mfd_dist (top,atlas) g m b <
                      mfd_dist (top,atlas) g a b + e)
     ==> ?a b m. a IN K /\ b IN K /\ m IN Km /\
                 mfd_dist (top,atlas) g xl a = A /\ mfd_dist (top,atlas) g xl b = A /\
                 mfd_dist (top,atlas) g a m + mfd_dist (top,atlas) g m b =
                 mfd_dist (top,atlas) g a b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "appr"))))))) THEN
  SUBGOAL_THEN `(K:B->bool) SUBSET topspace top /\ (Km:B->bool) SUBSET topspace top`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b:B. a IN topspace top /\ b IN topspace top
                        ==> mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) a b`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`] MFD_DIST_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC
   `Fp = \p:B#(B#B).
           mfd_dist (top,atlas) (g:B->real^3^3) (FST p) (SND(SND p)) +
           mfd_dist (top,atlas) g (SND(SND p)) (FST(SND p)) -
           mfd_dist (top,atlas) g (FST p) (FST(SND p)) +
           abs(mfd_dist (top,atlas) g xl (FST p) - A) +
           abs(mfd_dist (top,atlas) g xl (FST(SND p)) - A)` THEN
  SUBGOAL_THEN
   `!f1 f2:B#(B#B)->B.
       continuous_map (prod_topology top (prod_topology top top),top) f1 /\
       continuous_map (prod_topology top (prod_topology top top),top) f2
       ==> continuous_map (prod_topology top (prod_topology top top),euclideanreal)
             (\p. mfd_dist (top,atlas) (g:B->real^3^3) (f1 p) (f2 p))`
  (LABEL_TAC "dcomp") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\p:B#(B#B). mfd_dist (top,atlas) (g:B->real^3^3) (f1 p) (f2 p)) =
                  (\q:B#B. mfd_dist (top,atlas) g (FST q) (SND q)) o (\p. f1 p,f2 p)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `prod_topology (top:B topology) top` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX] THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> p2al84_mentions "prod_topology" th &&
      p2al84_mentions "mfd_dist" th)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (prod_topology top (prod_topology top top),top) (FST:B#(B#B)->B) /\
    continuous_map (prod_topology top (prod_topology top top),top) (\p:B#(B#B). FST(SND p)) /\
    continuous_map (prod_topology top (prod_topology top top),top) (\p:B#(B#B). SND(SND p)) /\
    continuous_map (prod_topology top (prod_topology top top),top) (\p:B#(B#B). xl)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_CONST; TOPSPACE_PROD_TOPOLOGY] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `prod_topology (top:B topology) top` THEN
    REWRITE_TAC[CONTINUOUS_MAP_SND; CONTINUOUS_MAP_FST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (prod_topology top (prod_topology top top),euclideanreal)
                   (Fp:B#(B#B)->real)` ASSUME_TAC THENL
   [EXPAND_TAC "Fp" THEN
    REPEAT((MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD ORELSE MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB) THEN
           CONJ_TAC) THEN
    TRY(MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
        REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST]) THEN
    USE_THEN "dcomp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((K:B->bool) CROSS (K CROSS (Km:B->bool)) = {})` ASSUME_TAC THENL
   [USE_THEN "appr" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; EXISTS_PAIR_THM; IN_CROSS] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`prod_topology (top:B topology) (prod_topology top top)`;
                 `Fp:B#(B#B)->real`;
                 `(K:B->bool) CROSS (K CROSS (Km:B->bool))`] RFA_CMAP_COMPACT_MIN) THEN
  ASM_REWRITE_TAC[COMPACT_IN_CROSS] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; FORALL_PAIR_THM; IN_CROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` (X_CHOOSE_THEN `b:B` (X_CHOOSE_THEN `m:B`
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "min"))))) THEN
  MAP_EVERY EXISTS_TAC [`a:B`; `b:B`; `m:B`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(Fp:B#(B#B)->real) (a,b,m) <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(prove(`!x. (!e. &0 < e ==> x < &3 * e) ==> x <= &0`,
      GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `x / &3`) THEN REAL_ARITH_TAC)) THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "appr" (MP_TAC o C MATCH_MP (ASSUME `&0 < e`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `a1:B` (X_CHOOSE_THEN `b1:B` (X_CHOOSE_THEN `m1:B`
      STRIP_ASSUME_TAC))) THEN
    USE_THEN "min" (MP_TAC o SPECL [`a1:B`; `b1:B`; `m1:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "Fp" THEN REWRITE_TAC[FST; SND] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) (g:B->real^3^3) a b <=
    mfd_dist (top,atlas) g a m + mfd_dist (top,atlas) g m b` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) (g:B->real^3^3) m b = mfd_dist (top,atlas) g b m` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(Fp:B#(B#B)->real) (a,b,m) <= &0` THEN EXPAND_TAC "Fp" THEN
  REWRITE_TAC[FST; SND] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Limits at the neck centres y k.  Split triples in the views at rescaled   *)
(* distance A from x k with split point within r0 give exact triples in the  *)
(* limit (LIM_BALL, LIM_DIST and P2AS85_SPLITS_FROM_APPROX, as in            *)
(* P2BX0_LIMIT_PAIRS of pc_p2b_x0), for every A > r0 a line                  *)
(* (P2AS85_LINE_FROM_SPLITS).  A limit with a line is the cylinder model     *)
(* ((a) after P2AL84_NOT_POS_SPLIT), all its points are necks ((h),          *)
(* P2AL84_CYL_LINE_NECK), and P2AS85_ANNULUS_NECKS with inner radius -1      *)
(* moves them to all points at rescaled distance <= 1 from x k.              *)
(* ========================================================================= *)

let P2AS85_LIMIT_TRIPLES = prove
 (`!(u:A->bool) (w:B->bool)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi s A r0.
     LIM_DIST_STATEMENT u w /\ LIM_BALL_STATEMENT u w /\
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     (!k. hausdorff_space (rfs_vtop (V k) (t k + s / Q k))) /\
     s IN J /\ connected_space top /\ riemannian_metric atlas (g s) /\
     mfd_complete (top,atlas) (g s) /\ &0 < r0 /\ r0 < A /\
     (?N. !k. N <= k
              ==> ?a b m.
                    mfd_joinable (rfs_vtop (V k) (t k + s / Q k),
                                  rfs_vatlas (V k) (t k + s / Q k)) (x k) a /\
                    mfd_joinable (rfs_vtop (V k) (t k + s / Q k),
                                  rfs_vatlas (V k) (t k + s / Q k)) (x k) b /\
                    mfd_joinable (rfs_vtop (V k) (t k + s / Q k),
                                  rfs_vatlas (V k) (t k + s / Q k)) (x k) m /\
                    sqrt(Q k) *
                    mfd_dist (rfs_vtop (V k) (t k + s / Q k),rfs_vatlas (V k) (t k + s / Q k))
                             (rfs_vmetric (V k) (t k + s / Q k)) (x k) a = A /\
                    sqrt(Q k) *
                    mfd_dist (rfs_vtop (V k) (t k + s / Q k),rfs_vatlas (V k) (t k + s / Q k))
                             (rfs_vmetric (V k) (t k + s / Q k)) (x k) b = A /\
                    sqrt(Q k) *
                    mfd_dist (rfs_vtop (V k) (t k + s / Q k),rfs_vatlas (V k) (t k + s / Q k))
                             (rfs_vmetric (V k) (t k + s / Q k)) (x k) m < r0 /\
                    mfd_dist (rfs_vtop (V k) (t k + s / Q k),rfs_vatlas (V k) (t k + s / Q k))
                             (rfs_vmetric (V k) (t k + s / Q k)) a m +
                    mfd_dist (rfs_vtop (V k) (t k + s / Q k),rfs_vatlas (V k) (t k + s / Q k))
                             (rfs_vmetric (V k) (t k + s / Q k)) m b =
                    mfd_dist (rfs_vtop (V k) (t k + s / Q k),rfs_vatlas (V k) (t k + s / Q k))
                             (rfs_vmetric (V k) (t k + s / Q k)) a b)
     ==> ?a b m. a IN topspace top /\ b IN topspace top /\
                 m IN mfd_cball (top,atlas) (g s) xl (r0 + &1) /\
                 mfd_dist (top,atlas) (g s) xl a = A /\ mfd_dist (top,atlas) (g s) xl b = A /\
                 mfd_dist (top,atlas) (g s) a m + mfd_dist (top,atlas) (g s) m b =
                 mfd_dist (top,atlas) (g s) a b`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "L1 L2 flow vreg vhaus sJ conn riem comp r0 r0A (@N. views)" THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology) /\
                smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                xl IN topspace top /\ (!k. &0 < (Q:num->real) k) /\
                (!k. (phi:num->B->A) k xl = x k)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[p2c_flow_limit_with]; ALL_TAC] THEN
  USE_THEN "L2" (MP_TAC o REWRITE_RULE[LIM_BALL_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `s:real`; `A + &1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:B->bool` (X_CHOOSE_THEN `k0:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ball")))) THEN
  ABBREV_TAC `K = {xl:B} UNION K0` THEN
  SUBGOAL_THEN `compact_in (top:B topology) K /\ (xl:B) IN K /\ K0 SUBSET K /\
                K SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IN_UNION THEN ASM_REWRITE_TAC[COMPACT_IN_SING];
      SET_TAC[];
      SET_TAC[];
      REWRITE_TAC[UNION_SUBSET; SING_SUBSET] THEN ASM_MESON_TAC[compact_in]];
    ALL_TAC] THEN
  ABBREV_TAC `Km = mfd_cball (top,atlas) ((g:real->B->real^3^3) s) xl (r0 + &1)` THEN
  SUBGOAL_THEN `compact_in (top:B topology) Km` ASSUME_TAC THENL
   [EXPAND_TAC "Km" THEN
    UNDISCH_TAC `mfd_complete (top,atlas:((B->bool)#(B->real^3))->bool)
                              ((g:real->B->real^3^3) s)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `xl:B`; `K:B->bool`; `Km:B->bool`; `A:real`]
                P2AS85_SPLITS_FROM_APPROX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "L1" (MP_TAC o REWRITE_RULE[LIM_DIST_STATEMENT]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
      `W:num->B->bool`; `phi:num->B->A`; `s:real`; `K:B->bool`; `min (e / &4) (&1 / &2)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "dist")) THEN
    USE_THEN "views" (MP_TAC o SPEC `k0 + k1 + N:num`) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `k = k0 + k1 + N:num` THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` (X_CHOOSE_THEN `m:A`
      STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(k0:num) <= k /\ (k1:num) <= k` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt((Q:num->real) k)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `sqrt((Q:num->real) k) *
      mfd_dist (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) k) (t k + s / Q k),
                rfs_vatlas (V k) (t k + s / Q k))
               (rfs_vmetric (V k) (t k + s / Q k)) (a:A) m +
      sqrt(Q k) *
      mfd_dist (rfs_vtop (V k) (t k + s / Q k),rfs_vatlas (V k) (t k + s / Q k))
               (rfs_vmetric (V k) (t k + s / Q k)) m b =
      sqrt(Q k) *
      mfd_dist (rfs_vtop (V k) (t k + s / Q k),rfs_vatlas (V k) (t k + s / Q k))
               (rfs_vmetric (V k) (t k + s / Q k)) a b`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:A) IN IMAGE ((phi:num->B->A) k) (K0 INTER W k) /\
                  (b:A) IN IMAGE (phi k) (K0 INTER W k) /\
                  (m:A) IN IMAGE (phi k) (K0 INTER W k)`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `y1:B` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `y2:B` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))
        (X_CHOOSE_THEN `y3:B` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`y1:B`; `y2:B`; `y3:B`] THEN
    SUBGOAL_THEN `(y1:B) IN K /\ (y2:B) IN K /\ (y3:B) IN K` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `xl:B`; `y1:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `xl:B`; `y2:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `xl:B`; `y3:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `y1:B`; `y3:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `y3:B`; `y2:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `y1:B`; `y2:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    SUBGOAL_THEN `(y3:B) IN Km` ASSUME_TAC THENL
     [EXPAND_TAC "Km" THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` (X_CHOOSE_THEN `b:B` (X_CHOOSE_THEN `m:B`
    STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`a:B`; `b:B`; `m:B`] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let P2AS85_LIMIT_LINE = prove
 (`!(u:A->bool) (w:B->bool)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi s r0.
     LIM_DIST_STATEMENT u w /\ LIM_BALL_STATEMENT u w /\
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     (!k. hausdorff_space (rfs_vtop (V k) (t k + s / Q k))) /\
     s IN J /\ connected_space top /\ riemannian_metric atlas (g s) /\
     mfd_complete (top,atlas) (g s) /\ &0 < r0 /\
     (!A. r0 < A
          ==> ?N. !k. N <= k
                  ==> ?a b m.
                        mfd_joinable (rfs_vtop (V k) (t k + s / Q k),
                                      rfs_vatlas (V k) (t k + s / Q k)) (x k) a /\
                        mfd_joinable (rfs_vtop (V k) (t k + s / Q k),
                                      rfs_vatlas (V k) (t k + s / Q k)) (x k) b /\
                        mfd_joinable (rfs_vtop (V k) (t k + s / Q k),
                                      rfs_vatlas (V k) (t k + s / Q k)) (x k) m /\
                        sqrt(Q k) *
                        mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                                  rfs_vatlas (V k) (t k + s / Q k))
                                 (rfs_vmetric (V k) (t k + s / Q k)) (x k) a = A /\
                        sqrt(Q k) *
                        mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                                  rfs_vatlas (V k) (t k + s / Q k))
                                 (rfs_vmetric (V k) (t k + s / Q k)) (x k) b = A /\
                        sqrt(Q k) *
                        mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                                  rfs_vatlas (V k) (t k + s / Q k))
                                 (rfs_vmetric (V k) (t k + s / Q k)) (x k) m < r0 /\
                        mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                                  rfs_vatlas (V k) (t k + s / Q k))
                                 (rfs_vmetric (V k) (t k + s / Q k)) a m +
                        mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                                  rfs_vatlas (V k) (t k + s / Q k))
                                 (rfs_vmetric (V k) (t k + s / Q k)) m b =
                        mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                                  rfs_vatlas (V k) (t k + s / Q k))
                                 (rfs_vmetric (V k) (t k + s / Q k)) a b)
     ==> ?l:real->B. !a b. l a IN topspace top /\
                           mfd_dist (top,atlas) (g s) (l a) (l b) = abs(b - a)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "L1 L2 flow vreg vhaus sJ conn riem comp r0 tri" THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology) /\
                smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                (xl:B) IN topspace top`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[p2c_flow_limit_with]; ALL_TAC] THEN
  MATCH_MP_TAC P2AS85_LINE_FROM_SPLITS THEN
  MAP_EVERY EXISTS_TAC [`mfd_cball (top,atlas) ((g:real->B->real^3^3) s) xl (r0 + &1)`;
                        `xl:B`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_complete (top,atlas:((B->bool)#(B->real^3))->bool)
                              ((g:real->B->real^3^3) s)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `R:real` THEN
  MP_TAC(ISPECL [`u:A->bool`; `w:B->bool`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `s:real`; `max R (r0 + &1)`; `r0:real`]
    P2AS85_LIMIT_TRIPLES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; USE_THEN "tri" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` (X_CHOOSE_THEN `b:B` (X_CHOOSE_THEN `m:B`
    STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`a:B`; `b:B`; `m:B`] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The limit at y k has a line: it is the cylinder model and all its points *)
(* are necks, so every q k at rescaled distance <= 1 from y k is the centre  *)
(* of an evolving eps-neck of length L for k large.                          *)

let P2AS85_CYL_TRANSFER = prove
 (`?epsC. &0 < epsC /\
     !(w:B->bool) (top:num->B topology) atlas (g:num->real->B->real^3^3) (y0:num->B) Q kappa
      (top':B topology) atlas' g' yl eps L (q:num->B) N.
        P2B_PROP_9_83K_STATEMENT w /\ P2B_CYL_MODEL_NECKS_STATEMENT w /\
        (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ y0 k IN topspace (top k)) /\
        (!Tl. &0 < Tl
              ==> p3_flow_limit (\k. p2b_kview (top k,atlas k) (g k)) y0 (\k. &0) Q
                                (top',atlas') g' yl Tl) /\
        p2b_kappa_solution kappa (top',atlas') g' /\ p2b_ksep top' atlas' /\
        (?l. !a b. l a IN topspace top' /\
                   mfd_dist (top',atlas') (g'(&0)) (l a) (l b) = abs(b - a)) /\
        &0 < eps /\ eps <= epsC /\ &1 <= L /\
        (!k. q k IN topspace (top k)) /\
        (!k. N <= k
             ==> sqrt(Q k) * mfd_dist (top k,atlas k) (g k (&0)) (y0 k) (q k) <= &1)
        ==> ?k0. !k. k0 <= k
                     ==> ?e. rfs_evolving_neck (p2b_kview (top k,atlas k) (g k)) eps (q k)
                                               (&0) L e`,
  X_CHOOSE_THEN `epsA:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ann"))
    P2AS85_ANNULUS_NECKS THEN
  EXISTS_TAC `epsA:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  INTRO_TAC "pk ch seq lim ksol ksep line ep epA L1 qin qk" THEN
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
  SUBGOAL_THEN `(yl:B) IN topspace top'` ASSUME_TAC THENL
   [USE_THEN "lim" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; p3_flow_limit] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "line" (X_CHOOSE_TAC `lam:real->B`) THEN
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
                   `(g':real->B->real^3^3) (&0)`; `X:B->real^3`; `yl:B`]
                  P2AL84_NOT_POS_SPLIT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_cyl_model (top',atlas') (g':real->B->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "pk" (MP_TAC o REWRITE_RULE[P2B_PROP_9_83K_STATEMENT]) THEN
    DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `top':B topology`;
                               `atlas':((B->bool)#(B->real^3))->bool`;
                               `g':real->B->real^3^3`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:B->bool`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`] P2AL84_CYL_LINE_NECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `lam:real->B` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(LABEL_TAC "cyln")] THEN
  SUBGOAL_THEN
   `!z. z IN topspace top' ==> &0 < mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top':B topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "ann" (MP_TAC o SPECL
    [`top:num->B topology`; `atlas:num->((B->bool)#(B->real^3))->bool`;
     `g:num->real->B->real^3^3`; `y0:num->B`; `Q:num->real`; `kappa:real`; `kappa:real`;
     `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
     `yl:B`; `-- &1`; `eps:real`; `L:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "cyln" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0") o SPEC `&1`) THEN
  EXISTS_TAC `k0 + N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "k0" MATCH_MP_TAC THEN
  SUBGOAL_THEN `k0 <= k /\ N <= k:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `k0 + N <= k:num` THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "qk" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> -- &1 + &1 <= x`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "lim" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; p3_flow_limit] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "seq" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
               ((g:num->real->B->real^3^3) k)`)) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
                 ((g:num->real->B->real^3^3) k)` THEN
  SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol]);;

(* ========================================================================= *)
(* The sequence steps of the soul argument. Arithmetic of rescaled           *)
(* distances; Claim 9.87 (R(y k) d(s k,y k)^2 grows when R(s k) d(s k,y k)^2 *)
(* does, by LEMMA_9_65 at y k); the good points y k are at rescaled distance *)
(* <= 1 from the bad points q k for k large (LEMMA_9_65 at q k); split       *)
(* triples at a good point y with A below sqrt(R y) d(y,s)                   *)
(* (P2BTL_NECK_IN_BALL, the neck viewed as a 19/10 eps-neck,                 *)
(* P2AS85_SPLIT_TRIPLE); the choice of q k, y k by P2AS85_SELECT.            *)
(* ========================================================================= *)

let P2AS85_INV_LE = prove
 (`!a b c. &0 < c ==> (a * inv c <= b <=> a <= c * b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

let P2AS85_LE_INV = prove
 (`!b c. &0 < c ==> (b <= inv c <=> c * b <= &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inv c = &1 / c` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC);;

let P2AS85_SCALE_ARITH = prove
 (`!a b C d r. &0 < a /\ &0 < b /\ &0 <= d /\ a <= C * b /\ sqrt b * d <= r
               ==> sqrt a * d <= sqrt(abs C) * r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt a <= sqrt(abs C) * sqrt b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * b` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(sqrt(abs C) * sqrt b) * d` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_ABS_POS]]);;

let P2AS85_OUT_BALL = prove
 (`!top atlas (g:B->real^3^3) s x D.
     connected_space top /\ smooth_manifold_atlas top atlas /\
     s IN topspace top /\ x IN topspace top /\ &0 < mfd_scalar atlas g s /\
     ~(x IN mfd_ball (top,atlas) g s (D * inv(sqrt(mfd_scalar atlas g s))))
     ==> D <= sqrt(mfd_scalar atlas g s) * mfd_dist (top,atlas) g s x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(mfd_scalar atlas (g:B->real^3^3) s)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM P2AS85_INV_LE] THEN
  UNDISCH_TAC `~((x:B) IN mfd_ball (top,atlas) (g:B->real^3^3) s
                       (D * inv(sqrt(mfd_scalar atlas g s))))` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM; DE_MORGAN_THM; REAL_NOT_LT] THEN
  MATCH_MP_TAC(TAUT `p ==> (~p \/ q ==> q)`) THEN
  MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]);;

(* Claim 9.87 along a sequence. *)

let P2AS85_CLAIM_987 = prove
 (`!(w:B->bool) kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) (s:num->B) y.
     P2B_LEMMA_9_65_STATEMENT w /\ P2B_PROP_9_83K_STATEMENT w /\ &0 < kappa /\
     (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ p2b_ksep (top k) (atlas k) /\
          s k IN topspace (top k) /\ y k IN topspace (top k)) /\
     (!M. ?N. !k. N <= k
                  ==> M < sqrt(mfd_scalar (atlas k) (g k (&0)) (s k)) *
                          mfd_dist (top k,atlas k) (g k (&0)) (s k) (y k))
     ==> !r. ?N. !k. N <= k
                     ==> r < sqrt(mfd_scalar (atlas k) (g k (&0)) (y k)) *
                             mfd_dist (top k,atlas k) (g k (&0)) (y k) (s k)`,
  REPEAT GEN_TAC THEN INTRO_TAC "l965 pk kp seq far" THEN
  SUBGOAL_THEN
   `!r. &0 < r
        ==> ?N. !k. N <= k
                    ==> r < sqrt(mfd_scalar (atlas k) ((g:num->real->B->real^3^3) k (&0))
                                           ((y:num->B) k)) *
                            mfd_dist ((top:num->B topology) k,atlas k) (g k (&0)) (y k)
                                     ((s:num->B) k)`
  (LABEL_TAC "pos") THENL
   [ALL_TAC;
    X_GEN_TAC `r:real` THEN USE_THEN "pos" (MP_TAC o SPEC `max r (&1)`) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "N" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REAL_ARITH_TAC]] THEN
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `&2 * r`] P2AL84_LEMMA_965_SCALED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cr:real` (LABEL_TAC "Cr")) THEN
  USE_THEN "far" (MP_TAC o SPEC `sqrt(abs Cr) * r`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "seq" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
               ((g:num->real->B->real^3^3) k)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `connected_space ((top:num->B topology) k)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
                   ((g:num->real->B->real^3^3) k)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < mfd_scalar (atlas k) ((g:num->real->B->real^3^3) k (&0)) ((s:num->B) k) /\
    &0 < mfd_scalar (atlas k) (g k (&0)) ((y:num->B) k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `(top:num->B topology) k`] THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(top:num->B topology) k`; `(atlas:num->((B->bool)#(B->real^3))->bool) k`;
                 `(g:num->real->B->real^3^3) k (&0)`; `(s:num->B) k`; `(y:num->B) k`]
                MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= mfd_dist ((top:num->B topology) k,atlas k) ((g:num->real->B->real^3^3) k (&0))
                   ((y:num->B) k) ((s:num->B) k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "N" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  USE_THEN "Cr" (MP_TAC o SPECL [`(top:num->B topology) k`;
    `(atlas:num->((B->bool)#(B->real^3))->bool) k`; `(g:num->real->B->real^3^3) k`;
    `(y:num->B) k`; `(s:num->B) k`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`mfd_scalar (atlas k) ((g:num->real->B->real^3^3) k (&0)) ((s:num->B) k)`;
                 `mfd_scalar (atlas k) ((g:num->real->B->real^3^3) k (&0)) ((y:num->B) k)`;
                 `Cr:real`;
                 `mfd_dist ((top:num->B topology) k,atlas k) ((g:num->real->B->real^3^3) k (&0))
                           ((y:num->B) k) ((s:num->B) k)`;
                 `r:real`] P2AS85_SCALE_ARITH) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The good point y k is at rescaled distance <= 1 from q k, eventually. *)

let P2AS85_NEAR = prove
 (`!(w:B->bool) kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) (q:num->B) y K0.
     P2B_LEMMA_9_65_STATEMENT w /\ P2B_PROP_9_83K_STATEMENT w /\ &0 < kappa /\
     (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ p2b_ksep (top k) (atlas k) /\
          q k IN topspace (top k) /\ y k IN topspace (top k)) /\
     (!k. K0 <= k
          ==> sqrt(mfd_scalar (atlas k) (g k (&0)) (q k)) *
              mfd_dist (top k,atlas k) (g k (&0)) (q k) (y k) <= inv(&k + &1))
     ==> ?N. !k. N <= k
                 ==> sqrt(mfd_scalar (atlas k) (g k (&0)) (y k)) *
                     mfd_dist (top k,atlas k) (g k (&0)) (y k) (q k) <= &1`,
  REPEAT GEN_TAC THEN INTRO_TAC "l965 pk kp seq near" THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `&2`] P2AL84_LEMMA_965_SCALED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (LABEL_TAC "C1")) THEN
  X_CHOOSE_TAC `K1:num` (SPEC `sqrt(abs C1)` REAL_ARCH_SIMPLE) THEN
  EXISTS_TAC `K0 + K1:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "seq" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
  USE_THEN "near" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `K0 + K1 <= k:num` THEN ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
               ((g:num->real->B->real^3^3) k)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `connected_space ((top:num->B topology) k)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
                   ((g:num->real->B->real^3^3) k)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < mfd_scalar (atlas k) ((g:num->real->B->real^3^3) k (&0)) ((q:num->B) k) /\
    &0 < mfd_scalar (atlas k) (g k (&0)) ((y:num->B) k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `(top:num->B topology) k`] THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(top:num->B topology) k`; `(atlas:num->((B->bool)#(B->real^3))->bool) k`;
                 `(g:num->real->B->real^3^3) k (&0)`; `(y:num->B) k`; `(q:num->B) k`]
                MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `&0 <= mfd_dist ((top:num->B topology) k,atlas k) ((g:num->real->B->real^3^3) k (&0))
                   ((q:num->B) k) ((y:num->B) k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&k + &1) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "C1" (MP_TAC o SPECL [`(top:num->B topology) k`;
    `(atlas:num->((B->bool)#(B->real^3))->bool) k`; `(g:num->real->B->real^3^3) k`;
    `(q:num->B) k`; `(y:num->B) k`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`mfd_scalar (atlas k) ((g:num->real->B->real^3^3) k (&0)) ((y:num->B) k)`;
                 `mfd_scalar (atlas k) ((g:num->real->B->real^3^3) k (&0)) ((q:num->B) k)`;
                 `C1:real`;
                 `mfd_dist ((top:num->B topology) k,atlas k) ((g:num->real->B->real^3^3) k (&0))
                           ((q:num->B) k) ((y:num->B) k)`;
                 `inv(&k + &1)`] P2AS85_SCALE_ARITH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(abs C1) * inv(&k + &1) <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &k + &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&K1` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `K0 + K1 <= k:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Split triples at a good point y in the R(y)-scale. *)

let P2AS85_TRIPLE_AT = prove
 (`!w:B->bool.
     P2B_SOUL_TOPOLOGY_STATEMENT w /\ P2B_PROP_9_83K_STATEMENT w
     ==> ?epsT. &0 < epsT /\
           !eps L kappa top atlas (g:real->B->real^3^3) s y A.
             &0 < eps /\ eps <= epsT /\
             p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
             ~compact_space top /\ s IN topspace top /\
             (!z. z IN topspace top /\ ~(z = s)
                  ==> p2b_dist_regular (top,atlas) (g(&0)) s z) /\
             (?e. rfs_evolving_neck (p2b_kview (top,atlas) g) eps y (&0) L e) /\
             &3 / &5 * inv eps < A /\
             A < sqrt(mfd_scalar atlas (g(&0)) y) * mfd_dist (top,atlas) (g(&0)) y s
             ==> ?a b m. mfd_joinable (top,atlas) y a /\ mfd_joinable (top,atlas) y b /\
                         mfd_joinable (top,atlas) y m /\
                         sqrt(mfd_scalar atlas (g(&0)) y) *
                         mfd_dist (top,atlas) (g(&0)) y a = A /\
                         sqrt(mfd_scalar atlas (g(&0)) y) *
                         mfd_dist (top,atlas) (g(&0)) y b = A /\
                         sqrt(mfd_scalar atlas (g(&0)) y) *
                         mfd_dist (top,atlas) (g(&0)) y m < &3 / &5 * inv eps /\
                         mfd_dist (top,atlas) (g(&0)) a m + mfd_dist (top,atlas) (g(&0)) m b =
                         mfd_dist (top,atlas) (g(&0)) a b`,
  GEN_TAC THEN INTRO_TAC "soul pk" THEN
  USE_THEN "soul" (X_CHOOSE_THEN `epsS:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tri")) o
    MATCH_MP P2AS85_SPLIT_TRIPLE) THEN
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nib"))
    (INST_TYPE [`:B`,`:A`] P2BTL_NECK_IN_BALL) THEN
  EXISTS_TAC `min (&10 / &19 * epsS) e0` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN INTRO_TAC "ep epT ksol ksep ncpt sin reg (@e. nk) A1 A2" THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `connected_space (top:B topology) /\
                riemannian_metric atlas ((g:real->B->real^3^3) (&0))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `eps:real`; `y:B`; `L:real`; `e:real^3->B`]
                P2BL_KVIEW_NECK0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) ((g:real->B->real^3^3) (&0)) eps y e` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->B`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  USE_THEN "nib" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                  `(g:real->B->real^3^3) (&0)`; `eps:real`; `y:B`;
                                  `e:real^3->B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) ((g:real->B->real^3^3) (&0)) (&19 / &10 * eps) y e`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_MONO_GEN THEN EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sphere_sep top (atlas:((B->bool)#(B->real^3))->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_ksep top (atlas:((B->bool)#(B->real^3))->bool)` THEN
    SIMP_TAC[p2b_ksep];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &19 / &10 * eps /\ &19 / &10 * eps <= epsS` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < &3 / &5 * inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y)) * inv eps /\
    &3 / &5 * inv(sqrt(mfd_scalar atlas (g(&0)) y)) * inv eps <
    A * inv(sqrt(mfd_scalar atlas (g(&0)) y)) /\
    A * inv(sqrt(mfd_scalar atlas (g(&0)) y)) < mfd_dist (top,atlas) (g(&0)) y s`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ];
      SUBGOAL_THEN
       `&3 / &5 * inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y)) * inv eps =
        (&3 / &5 * inv eps) * inv(sqrt(mfd_scalar atlas (g(&0)) y))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ];
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  USE_THEN "tri" (MP_TAC o SPECL [`&19 / &10 * eps`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) (&0)`; `s:B`; `y:B`;
    `e:real^3->B`;
    `&3 / &5 * inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y)) * inv eps`;
    `A * inv(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y))`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` (X_CHOOSE_THEN `b:B` (X_CHOOSE_THEN `m:B`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y) * A *
    inv(sqrt(mfd_scalar atlas (g(&0)) y)) = A /\
    sqrt(mfd_scalar atlas (g(&0)) y) *
    &3 / &5 * inv(sqrt(mfd_scalar atlas (g(&0)) y)) * inv eps = &3 / &5 * inv eps`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y) *
    mfd_dist (top,atlas) (g(&0)) y m < &3 / &5 * inv eps`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `sqrt(mfd_scalar atlas ((g:real->B->real^3^3) (&0)) y) *
                &3 / &5 * inv(sqrt(mfd_scalar atlas (g(&0)) y)) * inv eps` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:B`; `b:B`; `m:B`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]);;

(* The choice of the bad points q k and the good points y k. *)

let P2AS85_FAR_BAD = prove
 (`!(w:B->bool) kappa (top:num->B topology) atlas (g:num->real->B->real^3^3) (s:num->B)
    (x:num->B) D' eps L.
     P2B_PROP_9_83K_STATEMENT w /\ &0 <= D' /\
     (!k. p2b_kappa_solution kappa (top k,atlas k) (g k) /\ p2b_ksep (top k) (atlas k) /\
          s k IN topspace (top k) /\ x k IN topspace (top k) /\
          ~(?e. rfs_evolving_neck (p2b_kview (top k,atlas k) (g k)) eps (x k) (&0) L e) /\
          &k + &1 <= sqrt(mfd_scalar (atlas k) (g k (&0)) (s k)) *
                     mfd_dist (top k,atlas k) (g k (&0)) (s k) (x k)) /\
     (!rho. ?k0. !k y. k0 <= k /\ y IN topspace (top k) /\
                       D' + &1 <= sqrt(mfd_scalar (atlas k) (g k (&0)) (s k)) *
                                  mfd_dist (top k,atlas k) (g k (&0)) (s k) y /\
                       sqrt(mfd_scalar (atlas k) (g k (&0)) (s k)) *
                       mfd_dist (top k,atlas k) (g k (&0)) (s k) y <= rho
                       ==> ?e. rfs_evolving_neck (p2b_kview (top k,atlas k) (g k)) eps y (&0)
                                                 L e)
     ==> ?q y K0.
           (!k. q k IN topspace (top k) /\ y k IN topspace (top k)) /\
           (!k. K0 <= k
                ==> ~(?e. rfs_evolving_neck (p2b_kview (top k,atlas k) (g k)) eps (q k) (&0)
                                            L e) /\
                    sqrt(mfd_scalar (atlas k) (g k (&0)) (q k)) *
                    mfd_dist (top k,atlas k) (g k (&0)) (q k) (y k) <= inv(&k + &1)) /\
           (!M. ?N. !k. N <= k
                        ==> M < sqrt(mfd_scalar (atlas k) (g k (&0)) (s k)) *
                                mfd_dist (top k,atlas k) (g k (&0)) (s k) (y k) /\
                            ?e. rfs_evolving_neck (p2b_kview (top k,atlas k) (g k)) eps (y k)
                                                  (&0) L e)`,
  REPEAT GEN_TAC THEN INTRO_TAC "pk D0 seq ann" THEN
  SUBGOAL_THEN
   `!k. hausdorff_space ((top:num->B topology) k) /\ connected_space (top k) /\
        smooth_manifold_atlas (top k) (atlas k) /\
        riemannian_metric (atlas k) ((g:num->real->B->real^3^3) k (&0)) /\
        mfd_complete (top k,atlas k) (g k (&0)) /\
        (!z. z IN topspace (top k) ==> &0 < mfd_scalar (atlas k) (g k (&0)) z)`
  (LABEL_TAC "facts") THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "seq" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
    MP_TAC(MATCH_MP P2BL_KSOL_FACTS
      (ASSUME `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
                 ((g:num->real->B->real^3^3) k)`)) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `p2b_kappa_solution kappa ((top:num->B topology) k,atlas k)
                     ((g:num->real->B->real^3^3) k)` THEN
      SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AL84_R_POS THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `(top:num->B topology) k`] THEN
      ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  X_CHOOSE_TAC `K0:num` (SPEC `D' + &2` REAL_ARCH_SIMPLE) THEN
  SUBGOAL_THEN
   `!k. ?q y. q IN topspace ((top:num->B topology) k) /\ y IN topspace (top k) /\
              (K0 <= k
               ==> ~(?e. rfs_evolving_neck (p2b_kview (top k,atlas k)
                                            ((g:num->real->B->real^3^3) k)) eps q (&0) L e) /\
                   (D' + &2) * inv(sqrt(mfd_scalar (atlas k) (g k (&0)) ((s:num->B) k))) <=
                   mfd_dist (top k,atlas k) (g k (&0)) (s k) q /\
                   mfd_dist (top k,atlas k) (g k (&0)) q y <=
                   inv(sqrt(mfd_scalar (atlas k) (g k (&0)) (s k))) /\
                   sqrt(mfd_scalar (atlas k) (g k (&0)) q) *
                   mfd_dist (top k,atlas k) (g k (&0)) q y <= inv(&k + &1) /\
                   ((D' + &2) * inv(sqrt(mfd_scalar (atlas k) (g k (&0)) (s k))) +
                    inv(sqrt(mfd_scalar (atlas k) (g k (&0)) (s k))) <=
                    mfd_dist (top k,atlas k) (g k (&0)) (s k) q
                    ==> ?e. rfs_evolving_neck (p2b_kview (top k,atlas k) (g k)) eps y (&0)
                                              L e))`
  MP_TAC THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "seq" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
    ASM_CASES_TAC `K0 <= k:num` THENL
     [ALL_TAC;
      MAP_EVERY EXISTS_TAC [`(s:num->B) k`; `(s:num->B) k`] THEN ASM_REWRITE_TAC[]] THEN
    USE_THEN "facts" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `&0 < sqrt(mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                           ((g:num->real->B->real^3^3) k (&0)) ((s:num->B) k))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < (D' + &2) * inv(sqrt(mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                                          ((g:num->real->B->real^3^3) k (&0)) ((s:num->B) k))) /\
      &0 < inv(sqrt(mfd_scalar (atlas k) (g k (&0)) (s k))) /\ &0 < inv(&k + &1)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_LT_INV_EQ];
        REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!z. z IN topspace ((top:num->B topology) k)
          ==> &0 <= mfd_scalar (atlas k) ((g:num->real->B->real^3^3) k (&0)) z`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&(K0:num) <= &k` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(top:num->B topology) k`; `(atlas:num->((B->bool)#(B->real^3))->bool) k`;
                   `(g:num->real->B->real^3^3) k (&0)`; `(s:num->B) k`;
                   `\z:B. ?e. rfs_evolving_neck (p2b_kview ((top:num->B topology) k,atlas k)
                                                 ((g:num->real->B->real^3^3) k)) eps z (&0) L e`;
                   `(D' + &2) * inv(sqrt(mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                                      ((g:num->real->B->real^3^3) k (&0)) ((s:num->B) k)))`;
                   `inv(sqrt(mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                              ((g:num->real->B->real^3^3) k (&0)) ((s:num->B) k)))`;
                   `inv(&k + &1)`] P2AS85_SELECT) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `(x:num->B) k` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[P2AS85_INV_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&k + &1` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `qq:B` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `yy:B` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->B` (X_CHOOSE_THEN `y:num->B` (LABEL_TAC "qy")) o
             REWRITE_RULE[SKOLEM_THM]) THEN
  MAP_EVERY EXISTS_TAC [`q:num->B`; `y:num->B`; `K0:num`] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "qy" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN USE_THEN "qy" (MP_TAC o SPEC `k:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `M:real` THEN
  USE_THEN "ann" (MP_TAC o SPEC `max M (D' + &3) + &1`) THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0 + K0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k0 <= k /\ K0 <= k:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `k0 + K0 <= k:num` THEN ARITH_TAC; ALL_TAC] THEN
  USE_THEN "qy" (MP_TAC o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "yg"))))) THEN
  USE_THEN "seq" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
  USE_THEN "facts" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 < sqrt(mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                         ((g:num->real->B->real^3^3) k (&0)) ((s:num->B) k))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `D' + &2 <= sqrt(mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                               ((g:num->real->B->real^3^3) k (&0)) ((s:num->B) k)) *
               mfd_dist ((top:num->B topology) k,atlas k) (g k (&0)) (s k) ((q:num->B) k)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM P2AS85_INV_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `max M (D' + &3) + &1 <
    sqrt(mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                    ((g:num->real->B->real^3^3) k (&0)) ((s:num->B) k)) *
    mfd_dist ((top:num->B topology) k,atlas k) (g k (&0)) (s k) ((q:num->B) k)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(?e. rfs_evolving_neck (p2b_kview ((top:num->B topology) k,atlas k)
                                          ((g:num->real->B->real^3^3) k)) eps ((q:num->B) k)
                                          (&0) L e)` THEN
    REWRITE_TAC[] THEN USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    USE_THEN "yg" MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `(D' + &2) * inv(sqrt(mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                                      ((g:num->real->B->real^3^3) k (&0)) ((s:num->B) k))) +
      inv(sqrt(mfd_scalar (atlas k) (g k (&0)) (s k))) =
      (D' + &3) * inv(sqrt(mfd_scalar (atlas k) (g k (&0)) (s k)))`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[P2AS85_INV_LE] THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist ((top:num->B topology) k,atlas k) ((g:num->real->B->real^3^3) k (&0))
             ((y:num->B) k) ((q:num->B) k) =
    mfd_dist (top k,atlas k) (g k (&0)) (q k) (y k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                    ((g:num->real->B->real^3^3) k (&0)) ((s:num->B) k)) *
    mfd_dist ((top:num->B topology) k,atlas k) (g k (&0)) ((y:num->B) k) ((q:num->B) k) <= &1`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM P2AS85_LE_INV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(mfd_scalar ((atlas:num->((B->bool)#(B->real^3))->bool) k)
                    ((g:num->real->B->real^3^3) k (&0)) ((s:num->B) k)) *
    mfd_dist ((top:num->B topology) k,atlas k) (g k (&0)) (s k) ((q:num->B) k) <=
    sqrt(mfd_scalar (atlas k) (g k (&0)) (s k)) *
    mfd_dist (top k,atlas k) (g k (&0)) (s k) ((y:num->B) k) +
    sqrt(mfd_scalar (atlas k) (g k (&0)) (s k)) *
    mfd_dist (top k,atlas k) (g k (&0)) (y k) (q k)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The headline, MT Prop 9.85 (1) at a soul. By contradiction:               *)
(* counterexamples (kappa-solutions with souls s n and points x n outside    *)
(* the ball of radius (n + 1) R(s n)^(-1/2) that are no evolving eps-neck    *)
(* centres of length L); uniform kappa0 (P2AS85_KAPPA0); the THM_9_64 limit  *)
(* at s n has (eps/4)-necks of length L + 1 outside a ball                   *)
(* (P2AL84_LEMMA_9_84L), they transfer to annuli (P2AS85_ANNULUS_NECKS); bad *)
(* points q n and good points y n (P2AS85_FAR_BAD); Claim 9.87 and nearness  *)
(* (LEMMA_9_65); the THM_9_64 limit at y n has a line (split triples,        *)
(* P2AS85_TRIPLE_AT and P2AS85_LIMIT_LINE), so its points are necks and q n  *)
(* is a neck centre for n large (P2AS85_CYL_TRANSFER).                       *)
(* ========================================================================= *)

let P2AS85_DIV_LZERO = prove
 (`!x. &0 / x = &0`,
  REWRITE_TAC[real_div; REAL_MUL_LZERO]);;

let P2AS85_SOUL_NECKS = prove
 (`!w:B->bool.
     P2B_THM_9_64_STATEMENT w /\ P2B_PROP_9_58_STATEMENT w /\ P2B_LEMMA_9_65_STATEMENT w /\
     P2B_PROP_9_83K_STATEMENT w /\ P2B_CYL_MODEL_NECKS_STATEMENT w /\
     P2B_SOUL_TOPOLOGY_STATEMENT w
     ==> ?eps1. &0 < eps1 /\
           !eps L. &0 < eps /\ eps <= eps1 /\ &1 <= L
             ==> ?D. &0 < D /\
                   !kappa top atlas (g:real->B->real^3^3) s x.
                      p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
                      ~compact_space top /\ s IN topspace top /\
                      (!z. z IN topspace top /\ ~(z = s)
                           ==> p2b_dist_regular (top,atlas) (g(&0)) s z) /\
                      x IN topspace top /\
                      ~(x IN mfd_ball (top,atlas) (g(&0)) s
                               (D * inv(sqrt(mfd_scalar atlas (g(&0)) s))))
                      ==> ?e. rfs_evolving_neck (p2b_kview (top,atlas) g) eps x (&0) L e`,
  GEN_TAC THEN INTRO_TAC "t964 p958 l965 pk ch soul" THEN
  USE_THEN "p958" (X_CHOOSE_THEN `kappa0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "k0sol")) o
    MATCH_MP P2AS85_KAPPA0) THEN
  X_CHOOSE_THEN `epsA:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ann"))
    P2AS85_ANNULUS_NECKS THEN
  X_CHOOSE_THEN `epsC:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cyl"))
    P2AS85_CYL_TRANSFER THEN
  MP_TAC(SPEC `w:B->bool` P2AS85_TRIPLE_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `epsT:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tri"))) THEN
  EXISTS_TAC `min (min epsA epsC) (min epsT (&1 / &8))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `L:real`] THEN INTRO_TAC "ep ep1 L1" THEN
  SUBGOAL_THEN `eps <= epsA /\ eps <= epsC /\ eps <= epsT /\ eps <= &1 / &8`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the counterexamples *)
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "neg" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN
   `!n:num. ?kappa top atlas (g:real->B->real^3^3) s x.
       p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
       ~compact_space top /\ s IN topspace top /\
       (!z. z IN topspace top /\ ~(z = s) ==> p2b_dist_regular (top,atlas) (g(&0)) s z) /\
       x IN topspace top /\
       ~(x IN mfd_ball (top,atlas) (g(&0)) s
                ((&n + &1) * inv(sqrt(mfd_scalar atlas (g(&0)) s)))) /\
       ~(?e. rfs_evolving_neck (p2b_kview (top,atlas) g) eps x (&0) L e)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "neg" (MP_TAC o SPEC `&n + &1`) THEN
    REWRITE_TAC[REAL_ARITH `&0 < &n + &1`; NOT_FORALL_THM; NOT_IMP; GSYM CONJ_ASSOC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kp:num->real` (X_CHOOSE_THEN `tpk:num->B topology`
    (X_CHOOSE_THEN `atk:num->((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `gk:num->real->B->real^3^3` (X_CHOOSE_THEN `sk:num->B`
    (X_CHOOSE_THEN `xk:num->B` (LABEL_TAC "cex")))))) o REWRITE_RULE[SKOLEM_THM]) THEN
  SUBGOAL_THEN
   `!n. p2b_kappa_solution kappa0 ((tpk:num->B topology) n,atk n)
                           ((gk:num->real->B->real^3^3) n) /\
        p2b_ksep (tpk n) (atk n) /\ (sk:num->B) n IN topspace (tpk n)`
  (LABEL_TAC "seq0") THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "cex" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "k0sol" MATCH_MP_TAC THEN
    EXISTS_TAC `(kp:num->real) n` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the limit at the souls and its necks *)
  MP_TAC(ISPECL [`w:B->bool`; `kappa0:real`; `tpk:num->B topology`;
                 `atk:num->((B->bool)#(B->real^3))->bool`; `gk:num->real->B->real^3^3`;
                 `sk:num->B`] P2AL84_THM964_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub1:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `sl:B`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lim1")
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN `(sl:B) IN topspace top'` ASSUME_TAC THENL
   [USE_THEN "lim1" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; p3_flow_limit] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `w:B->bool` P2AL84_LEMMA_9_84L) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`eps / &4`; `L + &1`; `kappa0:real`; `top':B topology`;
                             `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                             `sl:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D':real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nk1")) o
    REWRITE_RULE[ASSUME `mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) sl = &1`;
                 SQRT_1; REAL_INV_1; REAL_MUL_RID]) THEN
  SUBGOAL_THEN
   `!z. z IN topspace top' ==> &0 < mfd_scalar atlas' ((g':real->B->real^3^3) (&0)) z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AL84_R_POS THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa0:real`; `top':B topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "ann" (MP_TAC o REWRITE_RULE[o_THM] o SPECL
    [`\k. (tpk:num->B topology) ((sub1:num->num) k)`;
     `\k. (atk:num->((B->bool)#(B->real^3))->bool) ((sub1:num->num) k)`;
     `\k. (gk:num->real->B->real^3^3) ((sub1:num->num) k)`;
     `(sk:num->B) o (sub1:num->num)`;
     `\k. mfd_scalar ((atk:num->((B->bool)#(B->real^3))->bool) ((sub1:num->num) k))
                     ((gk:num->real->B->real^3^3) (sub1 k) (&0)) ((sk:num->B) (sub1 k))`;
     `kappa0:real`; `kappa0:real`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
     `g':real->B->real^3^3`; `sl:B`; `D':real`; `eps:real`; `L:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "nk1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM; DE_MORGAN_THM] THEN DISJ2_TAC THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "ann1")] THEN
  (* the bad points q k and the good points y k on the sub1 sequence *)
  SUBGOAL_THEN
   `!k. p2b_kappa_solution kappa0 ((tpk:num->B topology) ((sub1:num->num) k),atk (sub1 k))
                           ((gk:num->real->B->real^3^3) (sub1 k)) /\
        p2b_ksep (tpk (sub1 k)) (atk (sub1 k)) /\
        (sk:num->B) (sub1 k) IN topspace (tpk (sub1 k)) /\
        (xk:num->B) (sub1 k) IN topspace (tpk (sub1 k)) /\
        ~(?e. rfs_evolving_neck (p2b_kview (tpk (sub1 k),atk (sub1 k)) (gk (sub1 k))) eps
                                (xk (sub1 k)) (&0) L e) /\
        &k + &1 <= sqrt(mfd_scalar (atk (sub1 k)) (gk (sub1 k) (&0)) (sk (sub1 k))) *
                   mfd_dist (tpk (sub1 k),atk (sub1 k)) (gk (sub1 k) (&0)) (sk (sub1 k))
                            (xk (sub1 k))`
  (LABEL_TAC "seq1") THENL
   [X_GEN_TAC `k:num` THEN
    USE_THEN "seq0" (MP_TAC o SPEC `(sub1:num->num) k`) THEN STRIP_TAC THEN
    USE_THEN "cex" (MP_TAC o SPEC `(sub1:num->num) k`) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(MATCH_MP P2BL_KSOL_FACTS
      (ASSUME `p2b_kappa_solution kappa0 ((tpk:num->B topology) ((sub1:num->num) k),
                                          atk (sub1 k)) ((gk:num->real->B->real^3^3) (sub1 k))`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `connected_space ((tpk:num->B topology) ((sub1:num->num) k))` ASSUME_TAC THENL
     [UNDISCH_TAC `p2b_kappa_solution kappa0 ((tpk:num->B topology) ((sub1:num->num) k),
                                              atk (sub1 k)) ((gk:num->real->B->real^3^3) (sub1 k))` THEN
      SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < mfd_scalar ((atk:num->((B->bool)#(B->real^3))->bool) ((sub1:num->num) k))
                      ((gk:num->real->B->real^3^3) (sub1 k) (&0)) ((sk:num->B) (sub1 k))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2AL84_R_POS THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa0:real`;
                            `(tpk:num->B topology) ((sub1:num->num) k)`] THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&((sub1:num->num) k) + &1` THEN CONJ_TAC THENL
     [MP_TAC(SPEC `sub1:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC P2AS85_OUT_BALL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`w:B->bool`; `kappa0:real`;
                 `\k. (tpk:num->B topology) ((sub1:num->num) k)`;
                 `\k. (atk:num->((B->bool)#(B->real^3))->bool) ((sub1:num->num) k)`;
                 `\k. (gk:num->real->B->real^3^3) ((sub1:num->num) k)`;
                 `\k. (sk:num->B) ((sub1:num->num) k)`;
                 `\k. (xk:num->B) ((sub1:num->num) k)`;
                 `D':real`; `eps:real`; `L:real`] P2AS85_FAR_BAD)) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->B` (X_CHOOSE_THEN `y:num->B` (X_CHOOSE_THEN `K0:num`
    (CONJUNCTS_THEN2 (LABEL_TAC "qyin")
      (CONJUNCTS_THEN2 (LABEL_TAC "qbad") (LABEL_TAC "yfar")))))) THEN
  SUBGOAL_THEN
   `!k. p2b_kappa_solution kappa0 ((tpk:num->B topology) ((sub1:num->num) k),atk (sub1 k))
                           ((gk:num->real->B->real^3^3) (sub1 k)) /\
        p2b_ksep (tpk (sub1 k)) (atk (sub1 k)) /\
        (sk:num->B) (sub1 k) IN topspace (tpk (sub1 k)) /\
        (y:num->B) k IN topspace (tpk (sub1 k)) /\ (q:num->B) k IN topspace (tpk (sub1 k))`
  (LABEL_TAC "seq2") THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "seq1" (MP_TAC o SPEC `k:num`) THEN
    USE_THEN "qyin" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* Claim 9.87 and nearness *)
  MP_TAC(BETA_RULE(ISPECL [`w:B->bool`; `kappa0:real`;
                 `\k. (tpk:num->B topology) ((sub1:num->num) k)`;
                 `\k. (atk:num->((B->bool)#(B->real^3))->bool) ((sub1:num->num) k)`;
                 `\k. (gk:num->real->B->real^3^3) ((sub1:num->num) k)`;
                 `\k. (sk:num->B) ((sub1:num->num) k)`; `y:num->B`] P2AS85_CLAIM_987)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `M:real` THEN
    USE_THEN "yfar" (MP_TAC o SPEC `M:real`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MESON_TAC[];
    DISCH_THEN(LABEL_TAC "c987")] THEN
  MP_TAC(BETA_RULE(ISPECL [`w:B->bool`; `kappa0:real`;
                 `\k. (tpk:num->B topology) ((sub1:num->num) k)`;
                 `\k. (atk:num->((B->bool)#(B->real^3))->bool) ((sub1:num->num) k)`;
                 `\k. (gk:num->real->B->real^3^3) ((sub1:num->num) k)`;
                 `q:num->B`; `y:num->B`; `K0:num`] P2AS85_NEAR)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "qbad" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "near"))] THEN
  (* the limit at the good points *)
  MP_TAC(BETA_RULE(ISPECL [`w:B->bool`; `kappa0:real`;
                 `\k. (tpk:num->B topology) ((sub1:num->num) k)`;
                 `\k. (atk:num->((B->bool)#(B->real^3))->bool) ((sub1:num->num) k)`;
                 `\k. (gk:num->real->B->real^3^3) ((sub1:num->num) k)`; `y:num->B`]
                P2AL84_THM964_AT)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `top'':B topology`
    (X_CHOOSE_THEN `atlas'':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g'':real->B->real^3^3` (X_CHOOSE_THEN `yl:B`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lim2")
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))) THEN
  MP_TAC(MATCH_MP P2BL_KSOL_FACTS
    (ASSUME `p2b_kappa_solution kappa0 (top'',atlas'') (g'':real->B->real^3^3)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `connected_space (top'':B topology) /\
    riemannian_metric (atlas'':((B->bool)#(B->real^3))->bool) ((g'':real->B->real^3^3) (&0))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa0 (top'',atlas'') (g'':real->B->real^3^3)` THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  USE_THEN "lim2" (MP_TAC o REWRITE_RULE[P2C_FLOW_LIMIT_ON_WITH] o
                   MATCH_MP P2AL84_FLOW_LIMIT_ON o REWRITE_RULE[REAL_LT_01] o SPEC `&1`) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B` ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(!n tau. ~(topspace(rfs_vtop (p2b_kview ((tpk:num->B topology) ((sub1:num->num)
                                                 ((sub2:num->num) n)),atk (sub1 (sub2 n)))
                                    ((gk:num->real->B->real^3^3) (sub1 (sub2 n)))) tau) = {})
             ==> smooth_manifold_atlas
                   (rfs_vtop (p2b_kview (tpk (sub1 (sub2 n)),atk (sub1 (sub2 n)))
                                        (gk (sub1 (sub2 n)))) tau)
                   (rfs_vatlas (p2b_kview (tpk (sub1 (sub2 n)),atk (sub1 (sub2 n)))
                                          (gk (sub1 (sub2 n)))) tau) /\
                 riemannian_metric
                   (rfs_vatlas (p2b_kview (tpk (sub1 (sub2 n)),atk (sub1 (sub2 n)))
                                          (gk (sub1 (sub2 n)))) tau)
                   (rfs_vmetric (p2b_kview (tpk (sub1 (sub2 n)),atk (sub1 (sub2 n)))
                                           (gk (sub1 (sub2 n)))) tau)) /\
    (!n tau. hausdorff_space (rfs_vtop (p2b_kview (tpk (sub1 (sub2 n)),atk (sub1 (sub2 n)))
                                                  (gk (sub1 (sub2 n)))) tau))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `n:num` THEN
    USE_THEN "seq0" (MP_TAC o SPEC `(sub1:num->num) ((sub2:num->num) n)`) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL84_KVIEW_SLICES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&0) IN {s:real | --(&1) < s /\ s <= &0}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &3 / &5 * inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* a line in the limit at the good points *)
  MP_TAC(REWRITE_RULE[LIM_DIST; LIM_BALL](ISPECL [`w:B->bool`; `w:B->bool`;
     `\k. p2b_kview ((tpk:num->B topology) ((sub1:num->num) ((sub2:num->num) k)),
                     (atk:num->((B->bool)#(B->real^3))->bool) (sub1 (sub2 k)))
                    ((gk:num->real->B->real^3^3) (sub1 (sub2 k)))`;
     `(y:num->B) o (sub2:num->num)`; `\k:num. &0`;
     `\k. mfd_scalar ((atk:num->((B->bool)#(B->real^3))->bool)
                        ((sub1:num->num) ((sub2:num->num) k)))
                     ((gk:num->real->B->real^3^3) (sub1 (sub2 k)) (&0)) ((y:num->B) (sub2 k))`;
     `{s:real | --(&1) < s /\ s <= &0}`; `top'':B topology`;
     `atlas'':((B->bool)#(B->real^3))->bool`; `g'':real->B->real^3^3`; `yl:B`;
     `W:num->B->bool`; `phi:num->B->B`; `&0`; `&3 / &5 * inv eps`] P2AS85_LIMIT_LINE)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[P2AS85_DIV_LZERO; REAL_ADD_RID; o_THM] THEN
    SIMP_TAC[P2BL_KVIEW_ACCESS; REAL_LE_REFL] THEN
    X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "c987" (MP_TAC o SPEC `A:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
    USE_THEN "yfar" (MP_TAC o SPEC `&0`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
    EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `N1 <= (sub2:num->num) k /\ N2 <= sub2 k` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `sub2:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N1 + N2 <= k:num` THEN ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "N1" (MP_TAC o SPEC `(sub2:num->num) k`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    USE_THEN "N2" (MP_TAC o SPEC `(sub2:num->num) k`) THEN
    ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)] THEN
    USE_THEN "cex" (MP_TAC o SPEC `(sub1:num->num) ((sub2:num->num) k)`) THEN STRIP_TAC THEN
    USE_THEN "tri" (MP_TAC o SPECL
      [`eps:real`; `L:real`; `(kp:num->real) ((sub1:num->num) ((sub2:num->num) k))`;
       `(tpk:num->B topology) ((sub1:num->num) ((sub2:num->num) k))`;
       `(atk:num->((B->bool)#(B->real^3))->bool) ((sub1:num->num) ((sub2:num->num) k))`;
       `(gk:num->real->B->real^3^3) ((sub1:num->num) ((sub2:num->num) k))`;
       `(sk:num->B) ((sub1:num->num) ((sub2:num->num) k))`;
       `(y:num->B) ((sub2:num->num) k)`; `A:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    DISCH_TAC] THEN
  (* the cylinder transfer at the bad points *)
  SUBGOAL_THEN
   `!k. N3 <= k
        ==> sqrt(mfd_scalar ((atk:num->((B->bool)#(B->real^3))->bool)
                               ((sub1:num->num) ((sub2:num->num) k)))
                            ((gk:num->real->B->real^3^3) (sub1 (sub2 k)) (&0))
                            ((y:num->B) (sub2 k))) *
            mfd_dist ((tpk:num->B topology) (sub1 (sub2 k)),atk (sub1 (sub2 k)))
                     (gk (sub1 (sub2 k)) (&0)) (y (sub2 k)) ((q:num->B) (sub2 k)) <= &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN USE_THEN "near" MATCH_MP_TAC THEN
    MP_TAC(SPEC `sub2:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N3 <= k:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "cyl" (MP_TAC o REWRITE_RULE[o_THM] o SPECL
    [`w:B->bool`; `\k. (tpk:num->B topology) ((sub1:num->num) ((sub2:num->num) k))`;
     `\k. (atk:num->((B->bool)#(B->real^3))->bool) ((sub1:num->num) ((sub2:num->num) k))`;
     `\k. (gk:num->real->B->real^3^3) ((sub1:num->num) ((sub2:num->num) k))`;
     `(y:num->B) o (sub2:num->num)`;
     `\k. mfd_scalar ((atk:num->((B->bool)#(B->real^3))->bool)
                        ((sub1:num->num) ((sub2:num->num) k)))
                     ((gk:num->real->B->real^3^3) (sub1 (sub2 k)) (&0)) ((y:num->B) (sub2 k))`;
     `kappa0:real`; `top'':B topology`; `atlas'':((B->bool)#(B->real^3))->bool`;
     `g'':real->B->real^3^3`; `yl:B`; `eps:real`; `L:real`; `(q:num->B) o (sub2:num->num)`;
     `N3:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (ASSUME_TAC o REWRITE_RULE[LE_ADD] o SPEC `k0 + K0:num`)) THEN
  USE_THEN "qbad" (MP_TAC o SPEC `(sub2:num->num) (k0 + K0)`) THEN
  ANTS_TAC THENL
   [MP_TAC(SPEC `sub2:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `k0 + K0:num`) THEN ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

