(* ========================================================================= *)
(* Unit pc_p2b_cone2: minimizing geodesics near the end E of a bad tube,     *)
(* rays to E, and the concavity of H(s) = d(q,gamma s)^2 - s^2 along rays    *)
(* (CMPLT_HBARRIER and CMPA_CALABI), which gives the monotonicity of         *)
(* comparison angles at E.  Balls about the farther of two points near E     *)
(* have compact closure because dE stays positive on them and the inner      *)
(* region is far; a second level-set bound d(q,p) <= dE q - dE p + 25 h(p)   *)
(* puts the error at the nearer point.                                       *)
(* ========================================================================= *)

needs "src/pc_p2b_cone.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Compact balls and minimizing geodesics near the end.                      *)
(* ========================================================================= *)

let P2BK_BALL_CLOSURE_COMPACT = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 x r r' c.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ x IN topspace top /\
     &0 < r /\ r < p2bk_dend (top,atlas) g z x /\ &1 < r' /\ r' < &2 /\
     (!w. &1 < norm w /\ norm w <= r' ==> c <= p2bk_dend (top,atlas) g z (H w)) /\
     p2bk_dend (top,atlas) g z x + r < c
     ==> compact_in top (top closure_of mfd_ball (top,atlas) g x r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  ABBREV_TAC `dx = p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `dx - r`] P2BK_DEND_NEAR_END) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `r < dx` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far")))] THEN
  ABBREV_TAC `K = {w:real^3 | r' <= norm w /\ norm w <= max rho r'}` THEN
  SUBGOAL_THEN `compact (K:real^3->bool) /\ K SUBSET annulus (&1) (&2)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{w:real^3 | r' <= norm w /\ norm w <= max rho r'} =
                    cball(vec 0,max rho r') DIFF ball(vec 0,r')` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `annulus (&1) (&2):real^3->bool`; `H:real^3->B`] MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Hi:B->real^3` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `IMAGE (H:real^3->B) K` THEN
  REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (annulus (&1) (&2):real^3->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `{y:B | y IN topspace top /\
                     (\p. mfd_dist (top,atlas) (g:B->real^3^3) x p) y IN {t:real | t <= r}}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `x:B`; `y:B`] MFD_JOINABLE_IN_TOPSPACE) THEN
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `euclideanreal` THEN
      ASM_SIMP_TAC[P2BK_DIST_SECTION_CONTINUOUS; GSYM REAL_CLOSED_IN;
                   REAL_CLOSED_HALFSPACE_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN IMAGE (H:real^3->B) (annulus (&1) (&2))` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; annulus; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `x:B`; `y:B`] P2BK_DEND_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `c:real`)) (concl th))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REWRITE_TAC[]; UNDISCH_TAC `norm(w:real^3) < r'` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs(dx - p2bk_dend (top,atlas) (g:B->real^3^3) z y) <=
                 mfd_dist (top,atlas) g x y` THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x y <= r` THEN
    UNDISCH_TAC `dx + r < c` THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "far" (MP_TAC o SPEC `w:real^3`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `max rho r' < norm(w:real^3)` THEN REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs(dx - p2bk_dend (top,atlas) (g:B->real^3^3) z y) <=
                 mfd_dist (top,atlas) g x y` THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x y <= r` THEN REAL_ARITH_TAC]);;

(* A minimizing geodesic from the farther point. *)

let P2BK_MIN_GEODESIC = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 x y r' c.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ x IN topspace top /\ y IN topspace top /\
     mfd_dist (top,atlas) g x y < p2bk_dend (top,atlas) g z x /\ &1 < r' /\ r' < &2 /\
     (!w. &1 < norm w /\ norm w <= r' ==> c <= p2bk_dend (top,atlas) g z (H w)) /\
     p2bk_dend (top,atlas) g z x + mfd_dist (top,atlas) g x y < c
     ==> ?v. v IN mfd_exp_dom (top,atlas) g x /\ mfd_exp (top,atlas) g x v = y /\
             mfd_tnorm g x v = mfd_dist (top,atlas) g x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) x y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) (g:B->real^3^3) x y` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `dx = p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN
  ABBREV_TAC `dxy = mfd_dist (top,atlas) (g:B->real^3^3) x y` THEN
  ABBREV_TAC `r = dxy + min (dx - dxy) (c - dx - dxy) / &2` THEN
  SUBGOAL_THEN `dxy < r /\ r < dx /\ dx + r < c /\ &0 < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN UNDISCH_TAC `dxy < dx` THEN UNDISCH_TAC `dx + dxy < c` THEN
    UNDISCH_TAC `&0 <= dxy` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `x:B`; `r:real`; `r':real`; `c:real`] P2BK_BALL_CLOSURE_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `r:real`] CMPQ_COMPACT_DOM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `r:real`; `y:B`] MFD_LOCAL_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "mfd_tball" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM]);;

(* ========================================================================= *)
(* The near-end context (inner region at a fixed positive level), neck       *)
(* centres and ray points near E, the second level-set bound with the error  *)
(* at the nearer point, reversal of geodesics, and minimizing geodesics      *)
(* between any two points near E.                                            *)
(* ========================================================================= *)

let p2bk_nearctx = new_definition
 `p2bk_nearctx (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
               (H:real^3->B) (eps:real) (z:num->B) (es:num->real^3->B) (r0:real)
               (c:real) (r1:real) <=>
    p2bk_endchain (top,atlas) g H eps z es r0 /\ &1 < r1 /\ r1 < &2 /\ r0 <= r1 /\ &0 < c /\
    (!w. &1 < norm w /\ norm w <= r1 ==> c <= p2bk_dend (top,atlas) g z (H w))`;;

let P2BK_NEARCTX_EXISTS = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 r1.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ r0 <= r1 /\ r1 < &2
     ==> ?c. p2bk_nearctx (top,atlas) g H eps z es r0 c r1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `r1:real`] P2BK_DEND_INNER_REGION) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[p2bk_nearctx] THEN
  UNDISCH_TAC `p2bk_endchain (top,atlas) (g:B->real^3^3) H eps z es r0` THEN
  REWRITE_TAC[p2bk_endchain] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2BK_NEAR_SEPNECK = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ x IN topspace top /\
     p2bk_dend (top,atlas) g z x < c
     ==> ?e. p2bk_sepneck (top,atlas) g H eps x e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bk_nearctx] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_tube]) THEN
  SUBGOAL_THEN `(x:B) IN IMAGE (H:real^3->B) (annulus (&1) (&2))` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; annulus; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `norm(w:real^3) <= r1` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `c:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x < c` THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `r0:real`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "p2bk_sepneck" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `r0 <= r1` THEN UNDISCH_TAC `~(norm(w:real^3) <= r1)` THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]]]);;

let P2BK_NEAR_RAY_POINT = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x t.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ x IN topspace top /\
     p2bk_dend (top,atlas) g z x < c /\ &0 < t /\ t < p2bk_dend (top,atlas) g z x
     ==> ?y. y IN topspace top /\ mfd_dist (top,atlas) g x y = t /\
             p2bk_dend (top,atlas) g z y = p2bk_dend (top,atlas) g z x - t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bk_nearctx] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BK_DEND_RAY_POINT THEN
  MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`;
                        `r1:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c:real` THEN CONJ_TAC THENL
   [UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x < c` THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The second level-set bound: the error sits at the nearer point. *)

let P2BK_LEVEL_DIST2 = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 q p.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ q IN topspace top /\ p IN topspace top /\
     p2bk_dend (top,atlas) g z p <= p2bk_dend (top,atlas) g z q /\
     p2bk_dend (top,atlas) g z q < c
     ==> mfd_dist (top,atlas) g q p <=
         p2bk_dend (top,atlas) g z q - p2bk_dend (top,atlas) g z p +
         &25 * inv(sqrt(mfd_scalar atlas g p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  (* a point q' at the level of p with d(q,q') = dE q - dE p *)
  SUBGOAL_THEN
   `?q'. q' IN topspace top /\
         mfd_dist (top,atlas) (g:B->real^3^3) q q' =
         p2bk_dend (top,atlas) g z q - p2bk_dend (top,atlas) g z p /\
         p2bk_dend (top,atlas) g z q' = p2bk_dend (top,atlas) g z p`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z p = p2bk_dend (top,atlas) g z q` THENL
     [EXISTS_TAC `q:B` THEN ASM_SIMP_TAC[MFD_DIST_REFL; REAL_SUB_REFL];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                     `c:real`; `r1:real`; `q:B`;
                     `p2bk_dend (top,atlas) (g:B->real^3^3) z q - p2bk_dend (top,atlas) g z p`]
        P2BK_NEAR_RAY_POINT) THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                     `p:B`] P2BK_DEND_POS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `~(p2bk_dend (top,atlas) (g:B->real^3^3) z p = p2bk_dend (top,atlas) g z q)` THEN
        UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z p <= p2bk_dend (top,atlas) g z q` THEN
        UNDISCH_TAC `&0 < p2bk_dend (top,atlas) (g:B->real^3^3) z p` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* q' and p are neck centres at the same level *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `q':B`] P2BK_NEAR_SEPNECK) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `p:B`] P2BK_NEAR_SEPNECK) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p2bk_dend (top,atlas) (g:B->real^3^3) z p < c` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z p <= p2bk_dend (top,atlas) g z q` THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z q < c` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `ep:real^3->B`) THEN DISCH_THEN(X_CHOOSE_TAC `eq:real^3->B`) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `q':B`; `eq:real^3->B`; `p:B`; `ep:real^3->B`] P2BK_LEVEL_DIST) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `q':B`; `eq:real^3->B`; `p:B`; `ep:real^3->B`] P2BK_LEVEL_SCALE) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) p /\ &0 < mfd_scalar atlas g q'`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bk_sepneck; rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(sqrt(mfd_scalar atlas (g:B->real^3^3) p)) /\
                &0 <= inv(sqrt(mfd_scalar atlas (g:B->real^3^3) q'))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_LE_ADD] THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`mfd_scalar atlas (g:B->real^3^3) p`; `mfd_scalar atlas (g:B->real^3^3) q'`]
    P2BK_SCALE_COMPARE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(&2) <= &3 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) p)) <=
                &3 / &2 * inv(sqrt(mfd_scalar atlas g p))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `q:B`; `q':B`; `p:B`] MFD_DIST_TRIANGLE) THEN
  ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Reversal of a geodesic segment: from exp_x v = y to exp_y w = x. *)

let P2BK_EXPREV_ARITH = prove
 (`&1 + -- &1 = &0 /\ -- &1 * &1 = -- &1 /\ &1 + -- &1 * &1 = &0`,
  REAL_ARITH_TAC);;

let P2BK_EXP_REVERSE = prove
 (`!top atlas (g:B->real^3^3) x v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top /\
     v IN mfd_exp_dom (top,atlas) g x
     ==> ?w. w IN mfd_exp_dom (top,atlas) g (mfd_exp (top,atlas) g x v) /\
             mfd_exp (top,atlas) g (mfd_exp (top,atlas) g x v) w = x /\
             mfd_tnorm g (mfd_exp (top,atlas) g x v) w = mfd_tnorm g x v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `v IN mfd_exp_dom (top,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) x` THEN
  REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM; mfd_exp] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `v:real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `y = mfd_geo (top,atlas) (g:B->real^3^3) x v (&1)` THEN
  ABBREV_TAC `u = mfd_vel (atlas:((B->bool)#(B->real^3))->bool)
                    (mfd_geo (top,atlas) (g:B->real^3^3) x v) (&1)` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `v:real^3`; `&1`] MFD_GEO_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "shI") (LABEL_TAC "shG")) THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `mfd_geo (top,atlas) (g:B->real^3^3) x v`;
                   `mfd_geo_maxint (top,atlas) (g:B->real^3^3) x v`; `&0`; `&1`]
      MFD_GEODESIC_C1_CURVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POS] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      UNDISCH_TAC `is_realinterval(mfd_geo_maxint (top,atlas) (g:B->real^3^3) x v)` THEN
      REWRITE_TAC[is_realinterval] THEN DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`; `s:real`]) THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `mfd_geo (top,atlas) (g:B->real^3^3) x v`; `&0`; `&1`; `&1`]
        MFD_C1_CURVE_IN_TOPSPACE) THEN
      ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `u:real^3`; `-- &1`] MFD_GEO_RESCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rsI") (LABEL_TAC "rsG")) THEN
  SUBGOAL_THEN `-- &1 IN mfd_geo_maxint (top,atlas) (g:B->real^3^3) y u` ASSUME_TAC THENL
   [USE_THEN "shI" SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[P2BK_EXPREV_ARITH] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `-- &1 % u:real^3` THEN REPEAT CONJ_TAC THENL
   [USE_THEN "rsI" SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[P2BK_EXPREV_ARITH] THEN ASM_REWRITE_TAC[];
    USE_THEN "rsG" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[P2BK_EXPREV_ARITH] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    USE_THEN "shG" (MP_TAC o SPEC `-- &1`) THEN
    REWRITE_TAC[P2BK_EXPREV_ARITH] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_tnorm] THEN
  REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID; DOT_LNEG; DOT_RNEG; MATRIX_VECTOR_MUL_RNEG;
              REAL_NEG_NEG] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x v`;
                 `mfd_geo_maxint (top,atlas) (g:B->real^3^3) x v`; `&0`; `&1`]
    MFD_GEODESIC_SPEED) THEN
  ASM_REWRITE_TAC[mfd_tnorm] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

(* The farther of two points near E is closer to the nearer one than to E. *)

let P2BK_NEAR_FAR_BOUND = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 q p.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ q IN topspace top /\ p IN topspace top /\
     p2bk_dend (top,atlas) g z p <= p2bk_dend (top,atlas) g z q /\
     p2bk_dend (top,atlas) g z q < c
     ==> mfd_dist (top,atlas) g q p < p2bk_dend (top,atlas) g z q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `q:B`; `p:B`] P2BK_LEVEL_DIST2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `p:B`] P2BK_NEAR_SEPNECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z p <= p2bk_dend (top,atlas) g z q` THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z q < c` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `ep:real^3->B`)] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:B->real^3^3) eps (p:B) ep` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bk_sepneck (top,atlas) (g:B->real^3^3) H eps (p:B) ep` THEN
    SIMP_TAC[p2bk_sepneck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `ep:real^3->B`] P2BK_DEND_NECK_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:B->real^3^3) p))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) eps (p:B) ep` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `inv(sqrt(mfd_scalar atlas (g:B->real^3^3) p))`]
    P2BK_EXIT_FACTOR) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) q p <=
               p2bk_dend (top,atlas) g z q - p2bk_dend (top,atlas) g z p +
               &25 * inv(sqrt(mfd_scalar atlas g p))` THEN
  UNDISCH_TAC `sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) p)) * inv eps <=
               p2bk_dend (top,atlas) g z p` THEN
  UNDISCH_TAC `&99 * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) p)) <=
               sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g p)) * inv eps` THEN
  UNDISCH_TAC `&0 < inv(sqrt(mfd_scalar atlas (g:B->real^3^3) p))` THEN REAL_ARITH_TAC);;

let P2BK_MIN_GEODESIC2 = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x y.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ x IN topspace top /\ y IN topspace top /\
     p2bk_dend (top,atlas) g z x < c / &2 /\ p2bk_dend (top,atlas) g z y < c / &2
     ==> ?v. v IN mfd_exp_dom (top,atlas) g x /\ mfd_exp (top,atlas) g x v = y /\
             mfd_tnorm g x v = mfd_dist (top,atlas) g x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  ASM_CASES_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z y <= p2bk_dend (top,atlas) g z x` THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `x:B`; `y:B`] P2BK_NEAR_FAR_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x < c / &2` THEN
      UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MATCH_MP_TAC P2BK_MIN_GEODESIC THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`;
                          `r0:real`; `r1:real`; `c:real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x y < p2bk_dend (top,atlas) g z x` THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x < c / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `y:B`; `x:B`] P2BK_NEAR_FAR_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(p2bk_dend (top,atlas) (g:B->real^3^3) z y <= p2bk_dend (top,atlas) g z x)` THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z y < c / &2` THEN
    UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `y:B`; `x:B`; `r1:real`; `c:real`] P2BK_MIN_GEODESIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) y x < p2bk_dend (top,atlas) g z y` THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z y < c / &2` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `v':real^3`] P2BK_EXP_REVERSE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^3` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                       `y:B`; `x:B`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Ray segments.  The minimizing geodesic from x to a ray point at distance  *)
(* T < dE(x) is itself a ray segment: along it dE decreases at unit speed.   *)
(* ========================================================================= *)

let P2BK_GEO_SEGMENT_DIST = prove
 (`!top atlas (g:B->real^3^3) x u a b.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top /\ mfd_tnorm g x u = &1 /\
     real_interval[a,b] SUBSET mfd_geo_maxint (top,atlas) g x u /\ a <= b
     ==> mfd_joinable (top,atlas) (mfd_geo (top,atlas) g x u a) (mfd_geo (top,atlas) g x u b) /\
         mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x u a) (mfd_geo (top,atlas) g x u b)
         <= b - a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `u:real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x u`;
                 `mfd_geo_maxint (top,atlas) (g:B->real^3^3) x u`; `a:real`; `b:real`]
    MFD_GEODESIC_C1_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x u`; `a:real`; `b:real`]
    MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_tnorm g (mfd_geo (top,atlas) (g:B->real^3^3) x u a)
                  (mfd_vel atlas (mfd_geo (top,atlas) g x u) a) = &1`
    (fun th -> REWRITE_TAC[th; REAL_MUL_RID]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x u`;
                 `mfd_geo_maxint (top,atlas) (g:B->real^3^3) x u`; `a:real`; `&0`]
    MFD_GEODESIC_SPEED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
      check (fun th -> can (find_term ((=) `real_interval[a,b]`)) (concl th))) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let P2BK_RAY_SEGMENT = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x L.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ x IN topspace top /\
     p2bk_dend (top,atlas) g z x < c / &2 /\ &0 < L /\ L < p2bk_dend (top,atlas) g z x
     ==> ?u. mfd_tnorm g x u = &1 /\
             real_interval[&0,L] SUBSET mfd_geo_maxint (top,atlas) g x u /\
             !s. &0 <= s /\ s <= L
                 ==> mfd_dist (top,atlas) g x (mfd_geo (top,atlas) g x u s) = s /\
                     p2bk_dend (top,atlas) g z (mfd_geo (top,atlas) g x u s) =
                     p2bk_dend (top,atlas) g z x - s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `L:real`] P2BK_NEAR_RAY_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x < c / &2` THEN
    UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `x:B`; `y:B`; `r1:real`; `c:real`] P2BK_MIN_GEODESIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x < c / &2` THEN
    UNDISCH_TAC `L < p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `inv L % v:real^3` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `v:real^3`; `inv L`] MFD_GEO_RESCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rsI") (LABEL_TAC "rsG")) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `v:real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 IN mfd_geo_maxint (top,atlas) (g:B->real^3^3) x v` ASSUME_TAC THENL
   [UNDISCH_TAC `v IN mfd_exp_dom (top,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) x` THEN
    REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_interval[&0,L] SUBSET mfd_geo_maxint (top,atlas) (g:B->real^3^3) x (inv L % v)`
  ASSUME_TAC THENL
   [USE_THEN "rsI" SUBST1_TAC THEN REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `is_realinterval(mfd_geo_maxint (top,atlas) (g:B->real^3^3) x v)` THEN
    REWRITE_TAC[is_realinterval] THEN DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`; `inv L * s`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv L * L` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:B->real^3^3) (x:B) (inv L % v:real^3) = &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `x:B`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < L ==> abs L = L`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `real_interval[&0,L] SUBSET
                 mfd_geo_maxint (top,atlas) (g:B->real^3^3) x (inv L % v)` THEN
    USE_THEN "rsI" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:B->real^3^3) x (inv L % v) L = y` ASSUME_TAC THENL
   [USE_THEN "rsG" (MP_TAC o SPEC `L:real`) THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    UNDISCH_TAC `mfd_exp (top,atlas) (g:B->real^3^3) x v = y` THEN
    REWRITE_TAC[mfd_exp] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `inv L % v:real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_interval[&0,s] SUBSET mfd_geo_maxint (top,atlas) (g:B->real^3^3) x (inv L % v) /\
                real_interval[s,L] SUBSET mfd_geo_maxint (top,atlas) g x (inv L % v)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval[&0,L]` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    UNDISCH_TAC `&0 <= s` THEN UNDISCH_TAC `s <= L` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `p = mfd_geo (top,atlas) (g:B->real^3^3) x (inv L % v) s` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `inv L % v:real^3`; `&0`; `s:real`] P2BK_GEO_SEGMENT_DIST) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "j1") (LABEL_TAC "d1")) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `inv L % v:real^3`; `s:real`; `L:real`] P2BK_GEO_SEGMENT_DIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "j2") (LABEL_TAC "d2")) THEN
  SUBGOAL_THEN `(p:B) IN topspace top` ASSUME_TAC THENL
   [USE_THEN "j1" (MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `x:B`; `p:B`] P2BK_DEND_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "l1") THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `y:B`] P2BK_DEND_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "l2") THEN
  REMOVE_THEN "d1" MP_TAC THEN REMOVE_THEN "d2" MP_TAC THEN
  REMOVE_THEN "l1" MP_TAC THEN REMOVE_THEN "l2" MP_TAC THEN
  UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z y = p2bk_dend (top,atlas) g z x - L` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Rays to the end.  A ray segment of length L from x is a unit geodesic     *)
(* along which d(x,.) and dE change at unit speed.  Segments extend: a ray   *)
(* segment from the end point, joined to the old one, is distance-realizing, *)
(* hence one geodesic (CMPRG_CORE) with the same initial vector (geodesics   *)
(* agreeing near a point have equal velocity there, MFD_GEODESIC_UNIQUE).    *)
(* By dyadic steps one unit vector u gives a ray on [0, dE x).               *)
(* ========================================================================= *)

let P2BK_VEL_LOCAL = prove
 (`!top atlas (g:B->real^3^3) (gamma1:real->B) gamma2 J t d.
     smooth_manifold_atlas top atlas /\ mfd_geodesic (top,atlas) g gamma1 J /\ t IN J /\
     gamma1 t IN topspace top /\ &0 < d /\
     (!s. abs(s - t) < d ==> gamma1 s = gamma2 s)
     ==> mfd_vel atlas gamma1 t = mfd_vel atlas gamma2 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma2:real->B) t = gamma1 t` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(gamma1:real->B) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_geodesic (top,atlas) (g:B->real^3^3) gamma1 J` THEN
  REWRITE_TAC[mfd_geodesic] THEN
  DISCH_THEN(MP_TAC o SPEC `chart_at (atlas:((B->bool)#(B->real^3))->bool) ((gamma1:real->B) t)` o
    CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real->real^3` (MP_TAC o SPEC `t:real`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  REWRITE_TAC[mfd_vel] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(v:real->real^3) t` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC
     [`\s. SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) ((gamma1:real->B) t))
             (gamma1(drop s))`; `d:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2BK_GEO_IN_TOPSPACE = prove
 (`!top atlas (g:B->real^3^3) (x:B) u s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ s IN mfd_geo_maxint (top,atlas) g x u
     ==> mfd_geo (top,atlas) g x u s IN topspace top`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `u:real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[mfd_geodesic] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map" with Failure _ -> false)) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2BK_GEO_AGREE = prove
 (`!top atlas (g:B->real^3^3) (x:B) u u' T0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 < T0 /\
     real_interval[&0,T0] SUBSET mfd_geo_maxint (top,atlas) g x u /\
     real_interval[&0,T0] SUBSET mfd_geo_maxint (top,atlas) g x u' /\
     (!r. &0 <= r /\ r <= T0 ==> mfd_geo (top,atlas) g x u r = mfd_geo (top,atlas) g x u' r)
     ==> u = u'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (l,t) -> LABEL_TAC l t)
    (zip ["haus"; "smooth"; "riem"; "xtop"; "T0pos"; "sub1"; "sub2"; "agree"] (CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `u:real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (l,t) -> LABEL_TAC l t)
    (zip ["o1"; "i1"; "z1"; "g1"; "x1"; "v1"] (CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `u':real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (l,t) -> LABEL_TAC l t)
    (zip ["o2"; "i2"; "z2"; "g2"; "x2"; "v2"] (CONJUNCTS th))) THEN
  SUBGOAL_THEN `T0 / &2 IN mfd_geo_maxint (top,atlas) (g:B->real^3^3) x u /\
                T0 / &2 IN mfd_geo_maxint (top,atlas) g x u'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "sub1" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]);
      USE_THEN "sub2" (MATCH_MP_TAC o REWRITE_RULE[SUBSET])] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN USE_THEN "T0pos" MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_vel atlas (mfd_geo (top,atlas) (g:B->real^3^3) x u) (T0 / &2) =
                mfd_vel atlas (mfd_geo (top,atlas) g x u') (T0 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BK_VEL_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `g:B->real^3^3`;
                          `mfd_geo_maxint (top,atlas) (g:B->real^3^3) x u`; `T0 / &2`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BK_GEO_IN_TOPSPACE THEN ASM_REWRITE_TAC[];
      USE_THEN "T0pos" MP_TAC THEN REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN USE_THEN "agree" MATCH_MP_TAC THEN
      UNDISCH_TAC `abs(s - T0 / &2) < T0 / &2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x u`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x u'`;
                 `mfd_geo_maxint (top,atlas) (g:B->real^3^3) x u`;
                 `mfd_geo_maxint (top,atlas) (g:B->real^3^3) x u'`; `T0 / &2`]
    MFD_GEODESIC_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "agree" MATCH_MP_TAC THEN
    USE_THEN "T0pos" MP_TAC THEN REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "uniq")] THEN
  SUBGOAL_THEN `?d. &0 < d /\
                    !s. abs(s - &0) < d
                        ==> s IN mfd_geo_maxint (top,atlas) (g:B->real^3^3) x u /\
                            s IN mfd_geo_maxint (top,atlas) g x u'`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "o1" (MP_TAC o SPEC `&0` o REWRITE_RULE[real_open]) THEN
    USE_THEN "o2" (MP_TAC o SPEC `&0` o REWRITE_RULE[real_open]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e1 e2` THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < e1` THEN UNDISCH_TAC `&0 < e2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `abs(s - &0) < min e1 e2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x u`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x u'`;
                 `mfd_geo_maxint (top,atlas) (g:B->real^3^3) x u`; `&0`; `d:real`]
    P2BK_VEL_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "uniq" MATCH_MP_TAC THEN REWRITE_TAC[IN_INTER] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let p2bk_rayseg = new_definition
 `p2bk_rayseg (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
              (z:num->B) (x:B) (u:real^3) (L:real) <=>
    mfd_tnorm g x u = &1 /\
    real_interval[&0,L] SUBSET mfd_geo_maxint (top,atlas) g x u /\
    !s. &0 <= s /\ s <= L
        ==> mfd_dist (top,atlas) g x (mfd_geo (top,atlas) g x u s) = s /\
            p2bk_dend (top,atlas) g z (mfd_geo (top,atlas) g x u s) =
            p2bk_dend (top,atlas) g z x - s`;;

let P2BK_RAYSEG_MONO = prove
 (`!top atlas (g:B->real^3^3) z (x:B) u L L'.
     p2bk_rayseg (top,atlas) g z x u L /\ L' <= L
     ==> p2bk_rayseg (top,atlas) g z x u L'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bk_rayseg] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval[&0,L]` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    UNDISCH_TAC `L' <= L` THEN REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `&0 <= s` THEN UNDISCH_TAC `s <= L'` THEN UNDISCH_TAC `L' <= L` THEN
    REAL_ARITH_TAC]);;

let P2BK_RAYSEG_EXISTS = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x L.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ x IN topspace top /\
     p2bk_dend (top,atlas) g z x < c / &2 /\ &0 < L /\ L < p2bk_dend (top,atlas) g z x
     ==> ?u. p2bk_rayseg (top,atlas) g z x u L`,
  REWRITE_TAC[p2bk_rayseg; P2BK_RAY_SEGMENT]);;

(* Extending a ray segment by half the remaining distance. *)

let P2BK_RAY_EXTEND = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x u T0.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ x IN topspace top /\
     p2bk_dend (top,atlas) g z x < c / &2 /\ &0 < T0 /\ T0 < p2bk_dend (top,atlas) g z x /\
     p2bk_rayseg (top,atlas) g z x u T0
     ==> p2bk_rayseg (top,atlas) g z x u (T0 + (p2bk_dend (top,atlas) g z x - T0) / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_X_ASSUM(fun th -> if is_comb(concl th) &&
      (try fst(dest_const(fst(strip_comb(concl th)))) = "p2bk_rayseg" with Failure _ -> false)
    then MP_TAC(GEN_REWRITE_RULE I [p2bk_rayseg] th) else failwith "") THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "un") (CONJUNCTS_THEN2 (LABEL_TAC "sub")
    (LABEL_TAC "rs"))) THEN
  ABBREV_TAC `a = p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN
  ABBREV_TAC `y = mfd_geo (top,atlas) (g:B->real^3^3) x u T0` THEN
  SUBGOAL_THEN `T0 IN mfd_geo_maxint (top,atlas) (g:B->real^3^3) x u` ASSUME_TAC THENL
   [USE_THEN "sub" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    UNDISCH_TAC `&0 < T0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN topspace top /\ mfd_dist (top,atlas) (g:B->real^3^3) x y = T0 /\
                p2bk_dend (top,atlas) g z y = a - T0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BK_GEO_IN_TOPSPACE THEN ASM_REWRITE_TAC[];
      USE_THEN "rs" MATCH_MP_TAC THEN UNDISCH_TAC `&0 < T0` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `y:B`; `(a - T0) / &2`] P2BK_RAYSEG_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `a < c / &2` THEN UNDISCH_TAC `T0 < a` THEN
    UNDISCH_TAC `&0 < T0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2bk_rayseg] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^3` (CONJUNCTS_THEN2 (LABEL_TAC "un'")
    (CONJUNCTS_THEN2 (LABEL_TAC "sub'") (LABEL_TAC "rs'")))) THEN
  ABBREV_TAC `R = T0 + (a - T0) / &2` THEN
  ABBREV_TAC `cc = \r:real. if r <= T0 then mfd_geo (top,atlas) (g:B->real^3^3) x u r
                            else mfd_geo (top,atlas) g y u' (r - T0)` THEN
  SUBGOAL_THEN `(!r. r <= T0 ==> cc r = mfd_geo (top,atlas) (g:B->real^3^3) x u r) /\
                (!r. T0 <= r ==> cc r = mfd_geo (top,atlas) g y u' (r - T0))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `r <= T0` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `r = T0:real` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `u':real^3`] MFD_GEO_MAXIMAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* dE along the joined curve *)
  SUBGOAL_THEN `!r. &0 <= r /\ r <= R
                    ==> (cc:real->B) r IN topspace top /\
                        p2bk_dend (top,atlas) (g:B->real^3^3) z (cc r) = a - r`
    (LABEL_TAC "cdE") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN ASM_CASES_TAC `r <= T0` THENL
     [SUBGOAL_THEN `(cc:real->B) r = mfd_geo (top,atlas) (g:B->real^3^3) x u r` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `r IN mfd_geo_maxint (top,atlas) (g:B->real^3^3) x u` ASSUME_TAC THENL
       [USE_THEN "sub" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2BK_GEO_IN_TOPSPACE THEN ASM_REWRITE_TAC[];
        USE_THEN "rs" (MP_TAC o SPEC `r:real`) THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
      SUBGOAL_THEN `T0 <= r` ASSUME_TAC THENL
       [UNDISCH_TAC `~(r <= T0)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(cc:real->B) r = mfd_geo (top,atlas) (g:B->real^3^3) y u' (r - T0)`
        SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= r - T0 /\ r - T0 <= (a - T0) / &2` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `T0 <= r` THEN UNDISCH_TAC `r <= R` THEN EXPAND_TAC "R" THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `r - T0 IN mfd_geo_maxint (top,atlas) (g:B->real^3^3) y u'` ASSUME_TAC THENL
       [USE_THEN "sub'" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2BK_GEO_IN_TOPSPACE THEN ASM_REWRITE_TAC[];
        USE_THEN "rs'" (MP_TAC o SPEC `r - T0`) THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the joined curve is 1-Lipschitz *)
  SUBGOAL_THEN
   `!s t. &0 <= s /\ s <= t /\ t <= T0
          ==> mfd_joinable (top,atlas) ((cc:real->B) s) (cc t) /\
              mfd_dist (top,atlas) (g:B->real^3^3) (cc s) (cc t) <= t - s`
    (LABEL_TAC "c1") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `s <= T0` ASSUME_TAC THENL
     [UNDISCH_TAC `s <= t` THEN UNDISCH_TAC `t <= T0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(cc:real->B) s = mfd_geo (top,atlas) (g:B->real^3^3) x u s /\
                  cc t = mfd_geo (top,atlas) g x u t` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P2BK_GEO_SEGMENT_DIST THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval[&0,T0]` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t. T0 <= s /\ s <= t /\ t <= R
          ==> mfd_joinable (top,atlas) ((cc:real->B) s) (cc t) /\
              mfd_dist (top,atlas) (g:B->real^3^3) (cc s) (cc t) <= t - s`
    (LABEL_TAC "c2") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `T0 <= t` ASSUME_TAC THENL
     [UNDISCH_TAC `T0 <= s` THEN UNDISCH_TAC `s <= t` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(cc:real->B) s = mfd_geo (top,atlas) (g:B->real^3^3) y u' (s - T0) /\
                  cc t = mfd_geo (top,atlas) g y u' (t - T0)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `u':real^3`; `s - T0`; `t - T0`] P2BK_GEO_SEGMENT_DIST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval[&0,(a - T0) / &2]` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
        UNDISCH_TAC `T0 <= s` THEN UNDISCH_TAC `s <= t` THEN UNDISCH_TAC `t <= R` THEN
        EXPAND_TAC "R" THEN REAL_ARITH_TAC;
        UNDISCH_TAC `s <= t` THEN REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ARITH `(t - T0) - (s - T0) = t - s:real`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t. &0 <= s /\ s <= t /\ t <= R
          ==> mfd_joinable (top,atlas) ((cc:real->B) s) (cc t) /\
              mfd_dist (top,atlas) (g:B->real^3^3) (cc s) (cc t) <= t - s`
    (LABEL_TAC "lip") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC `t <= T0` THENL
     [USE_THEN "c1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `T0 <= s` THENL
     [USE_THEN "c2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "c1" (MP_TAC o SPECL [`s:real`; `T0:real`]) THEN ANTS_TAC THENL
     [UNDISCH_TAC `&0 <= s` THEN UNDISCH_TAC `~(T0 <= s)` THEN REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "c2" (MP_TAC o SPECL [`T0:real`; `t:real`]) THEN ANTS_TAC THENL
     [UNDISCH_TAC `t <= R` THEN UNDISCH_TAC `~(t <= T0)` THEN REAL_ARITH_TAC; STRIP_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(cc:real->B) T0` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `(cc:real->B) s`; `(cc:real->B) T0`; `(cc:real->B) t`] MFD_DIST_TRIANGLE) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) ((cc:real->B) s) (cc T0) <= T0 - s` THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) ((cc:real->B) T0) (cc t) <= t - T0` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the joined curve realizes distances, so it is one geodesic *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `cc:real->B`; `R:real`] CMPRG_CORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "R" THEN UNDISCH_TAC `&0 < T0` THEN UNDISCH_TAC `T0 < a` THEN REAL_ARITH_TAC;
      USE_THEN "cdE" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL
       [EXPAND_TAC "R" THEN UNDISCH_TAC `&0 < T0` THEN UNDISCH_TAC `T0 < a` THEN
        REAL_ARITH_TAC;
        SIMP_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
    USE_THEN "cdE" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cdE" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `(cc:real->B) s`; `(cc:real->B) t`] P2BK_DEND_LIPSCHITZ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISJ_CASES_TAC(REAL_ARITH `s <= t \/ t <= s:real`) THENL
     [USE_THEN "lip" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `abs((a - s) - (a - t)) <= mfd_dist (top,atlas) (g:B->real^3^3)
                     ((cc:real->B) s) (cc t)` THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) ((cc:real->B) s) (cc t) <= t - s` THEN
      UNDISCH_TAC `s <= t:real` THEN REAL_ARITH_TAC;
      USE_THEN "lip" (MP_TAC o SPECL [`t:real`; `s:real`]) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `(cc:real->B) t`; `(cc:real->B) s`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `abs((a - s) - (a - t)) <= mfd_dist (top,atlas) (g:B->real^3^3)
                     ((cc:real->B) s) (cc t)` THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) ((cc:real->B) t) (cc s) <= s - t` THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) ((cc:real->B) t) (cc s) =
                   mfd_dist (top,atlas) g (cc s) (cc t)` THEN
      UNDISCH_TAC `t <= s:real` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(cc:real->B) (&0) = x` ASSUME_TAC THENL
   [SUBGOAL_THEN `(cc:real->B) (&0) = mfd_geo (top,atlas) (g:B->real^3^3) x u (&0)`
      SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `(cc:real->B) r`))
        (concl th) && can (find_term ((=) `r <= T0`)) (concl th))) THEN
      UNDISCH_TAC `&0 < T0` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `x:B`; `u:real^3`] MFD_GEO_MAXIMAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `us:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `u:real^3 = us` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC P2BK_GEO_AGREE THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `x:B`; `T0:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval[&0,R]` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      EXPAND_TAC "R" THEN UNDISCH_TAC `&0 < T0` THEN UNDISCH_TAC `T0 < a` THEN REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `mfd_geo (top,atlas) (g:B->real^3^3) x us r = cc r` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `&0 <= r` THEN UNDISCH_TAC `r <= T0` THEN EXPAND_TAC "R" THEN
        UNDISCH_TAC `T0 < a` THEN REAL_ARITH_TAC;
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[p2bk_rayseg] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:B->real^3^3) x us s = cc s` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "cdE" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "lip" (MP_TAC o SPECL [`&0`; `s:real`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `x:B`; `(cc:real->B) s`] P2BK_DEND_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x ((cc:real->B) s) <= s` THEN
  REAL_ARITH_TAC);;

let P2BK_DYADIC = prove
 (`!a n. &0 < a
         ==> &0 < a - a / &2 pow (SUC n) /\ a - a / &2 pow (SUC n) < a /\
             (a - a / &2 pow (SUC n)) + (a - (a - a / &2 pow (SUC n))) / &2 =
             a - a / &2 pow (SUC(SUC n))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `p = &2 pow (SUC n)` THEN
  SUBGOAL_THEN `&2 pow (SUC(SUC n)) = &2 * p` SUBST1_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[real_pow]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[real_pow] THEN
    MP_TAC(SPECL [`n:num`; `&2`] REAL_POW_LE_1) THEN REWRITE_TAC[REAL_OF_NUM_LE; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL
   [UNDISCH_TAC `&2 <= p` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a / p` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `a / p < a` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `a * &1 < a * p ==> a < a * p`) THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&2 <= p` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `a / p < a` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < a / p` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD]);;

let P2BK_RAY = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ x IN topspace top /\
     p2bk_dend (top,atlas) g z x < c / &2
     ==> ?u. !L. L < p2bk_dend (top,atlas) g z x ==> p2bk_rayseg (top,atlas) g z x u L`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `x:B`]
    P2BK_DEND_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `a = p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `a / &2`] P2BK_RAYSEG_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < a` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^3` THEN DISCH_TAC] THEN
  SUBGOAL_THEN `!n. p2bk_rayseg (top,atlas) (g:B->real^3^3) z x u (a - a / &2 pow (SUC n))`
    ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[real_pow; REAL_POW_1; REAL_MUL_RID] THEN
      SUBGOAL_THEN `a - a / &2 = a / &2` SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`a:real`; `n:num`] P2BK_DYADIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN EXPAND_TAC "a" THEN
    MATCH_MP_TAC P2BK_RAY_EXTEND THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`;
                          `c:real`; `r1:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `L:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `a / (a - L)` REAL_ARCH_POW2) THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MATCH_MP_TAC P2BK_RAYSEG_MONO THEN EXISTS_TAC `a - a / &2 pow (SUC n)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a / &2 pow (SUC n) <= a / &2 pow n /\ a / &2 pow n < a - L`
    (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
  SUBGOAL_THEN `&0 < &2 pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_pow; real_div; REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < a` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> inv(&2) * x <= x`) THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    UNDISCH_TAC `a / (a - L) < &2 pow n` THEN
    SUBGOAL_THEN `&0 < a - L` ASSUME_TAC THENL
     [UNDISCH_TAC `L < a` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Concavity along rays.  With sec >= 0, along a ray gamma(s) = geo(x,u,s)   *)
(* toward E the function H(s) = d(q,gamma s)^2 - s^2 is concave on every     *)
(* [a,b] inside [0,dE x) (CMPLT_HBARRIER at each interior point, using the   *)
(* minimizing geodesic between gamma(t0) and q, and CMPA_CALABI).            *)
(* ========================================================================= *)

(* Facts at one point of a ray. *)

let P2BK_RAY_AT = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 x u s.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ x IN topspace top /\
     (!L. L < p2bk_dend (top,atlas) g z x ==> p2bk_rayseg (top,atlas) g z x u L) /\
     &0 <= s /\ s < p2bk_dend (top,atlas) g z x
     ==> mfd_tnorm g x u = &1 /\
         real_interval[&0,s] SUBSET mfd_geo_maxint (top,atlas) g x u /\
         s IN mfd_geo_maxint (top,atlas) g x u /\
         mfd_geo (top,atlas) g x u s IN topspace top /\
         mfd_dist (top,atlas) g x (mfd_geo (top,atlas) g x u s) = s /\
         p2bk_dend (top,atlas) g z (mfd_geo (top,atlas) g x u s) =
         p2bk_dend (top,atlas) g z x - s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  UNDISCH_TAC `!L. L < p2bk_dend (top,atlas) (g:B->real^3^3) z x
                   ==> p2bk_rayseg (top,atlas) g z x u L` THEN
  DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[p2bk_rayseg] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sub") (LABEL_TAC "rs"))) THEN
  SUBGOAL_THEN `s IN mfd_geo_maxint (top,atlas) (g:B->real^3^3) x u` ASSUME_TAC THENL
   [USE_THEN "sub" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BK_GEO_IN_TOPSPACE THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "rs" (MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL]]);;

let P2BK_H_CONCAVE = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x u q a b.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\
     (!y v w. y IN topspace top /\ ~collinear {vec 0,v,w}
              ==> &0 <= mfd_sectional atlas g y v w) /\
     x IN topspace top /\ p2bk_dend (top,atlas) g z x < c / &2 /\
     (!L. L < p2bk_dend (top,atlas) g z x ==> p2bk_rayseg (top,atlas) g z x u L) /\
     q IN topspace top /\ p2bk_dend (top,atlas) g z q < c / &2 /\
     &0 <= a /\ a < b /\ b < p2bk_dend (top,atlas) g z x
     ==> !s. a <= s /\ s <= b
             ==> (mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g x u a) pow 2 - a pow 2) +
                 (s - a) / (b - a) *
                 ((mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g x u b) pow 2 - b pow 2) -
                  (mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g x u a) pow 2 - a pow 2))
                 <= mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g x u s) pow 2 - s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `x:B`; `u:real^3`; `b:real`] P2BK_RAY_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= a` THEN UNDISCH_TAC `a < b` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`\t. mfd_dist (top,atlas) (g:B->real^3^3) q
                       (mfd_geo (top,atlas) g x u t) pow 2 - t pow 2`;
                 `a:real`; `b:real`] CMPA_CALABI) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMPLT_HCONT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval[&0,b]` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    UNDISCH_TAC `&0 <= a` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `e:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `x:B`; `u:real^3`; `t0:real`] P2BK_RAY_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= a` THEN UNDISCH_TAC `a < t0` THEN
    UNDISCH_TAC `t0 < b` THEN UNDISCH_TAC `b < p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN
    REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `mfd_geo (top,atlas) (g:B->real^3^3) x u t0`; `q:B`]
    P2BK_MIN_GEODESIC2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x < c / &2` THEN
    UNDISCH_TAC `&0 <= a` THEN UNDISCH_TAC `a < t0` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `u:real^3`; `q:B`; `t0:real`; `e:real`] CMPLT_HBARRIER) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN ACCEPT_TAC]);;

(* Through the end: d(p,q) <= dE p + dE q, so |d(q,y) - dE q| <= dE y. *)

let P2BK_DIST_VIA_END = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 p q.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ p IN topspace top /\ q IN topspace top
     ==> mfd_dist (top,atlas) g p q <=
         p2bk_dend (top,atlas) g z p + p2bk_dend (top,atlas) g z q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_endchain]) THEN
  MATCH_MP_TAC(ISPECL [`sequentially:num net`; `\k:num. mfd_dist (top,atlas) (g:B->real^3^3) p q`;
    `\k. mfd_dist (top,atlas) (g:B->real^3^3) p ((z:num->B) k) + mfd_dist (top,atlas) g q (z k)`]
    REALLIM_LE) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY; REALLIM_CONST] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN MATCH_MP_TAC P2BK_DEND_TENDSTO THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `0` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `p:B`; `(z:num->B) k`; `q:B`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `(z:num->B) k`; `q:B`] MFD_DIST_SYM) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

let P2BK_DIST_NEAR_END = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 q y.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ q IN topspace top /\ y IN topspace top
     ==> abs(mfd_dist (top,atlas) g q y - p2bk_dend (top,atlas) g z q) <=
         p2bk_dend (top,atlas) g z y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `q:B`; `y:B`] P2BK_DIST_VIA_END) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `q:B`; `y:B`] P2BK_DEND_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The chord from s1 to the end: H at s2 lies above the line from H(s1) to  *)
(* the value dE(q)^2 - dE(x)^2 taken at the end of the ray.                 *)

let P2BK_H_ENDCHORD = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x u q s1 s2.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\
     (!y v w. y IN topspace top /\ ~collinear {vec 0,v,w}
              ==> &0 <= mfd_sectional atlas g y v w) /\
     x IN topspace top /\ p2bk_dend (top,atlas) g z x < c / &2 /\
     (!L. L < p2bk_dend (top,atlas) g z x ==> p2bk_rayseg (top,atlas) g z x u L) /\
     q IN topspace top /\ p2bk_dend (top,atlas) g z q < c / &2 /\
     &0 <= s1 /\ s1 < s2 /\ s2 < p2bk_dend (top,atlas) g z x
     ==> (s2 - s1) *
         ((p2bk_dend (top,atlas) g z q pow 2 - p2bk_dend (top,atlas) g z x pow 2) -
          (mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g x u s1) pow 2 - s1 pow 2))
         <= (p2bk_dend (top,atlas) g z x - s1) *
            ((mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g x u s2) pow 2 - s2 pow 2) -
             (mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g x u s1) pow 2 - s1 pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  ABBREV_TAC `a = p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN
  ABBREV_TAC `bq = p2bk_dend (top,atlas) (g:B->real^3^3) z q` THEN
  ABBREV_TAC `h1 = mfd_dist (top,atlas) (g:B->real^3^3) q (mfd_geo (top,atlas) g x u s1) pow 2 -
                   s1 pow 2` THEN
  ABBREV_TAC `h2 = mfd_dist (top,atlas) (g:B->real^3^3) q (mfd_geo (top,atlas) g x u s2) pow 2 -
                   s2 pow 2` THEN
  ABBREV_TAC `bb = \n. a - (a - s2) * inv(&n + &2)` THEN
  SUBGOAL_THEN `!n. s2 < (bb:num->real) n /\ bb n < a` (LABEL_TAC "bbr") THENL
   [GEN_TAC THEN EXPAND_TAC "bb" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < inv(&n + &2) /\ inv(&n + &2) < &1` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_INV_LT_1 THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < a - s2` ASSUME_TAC THENL
     [UNDISCH_TAC `s2 < a` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `(a - s2) * i < (a - s2) * &1 ==> s2 < a - (a - s2) * i`) THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `&0 < (a - s2) * i ==> a - (a - s2) * i < a`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* facts along the ray at bb n *)
  SUBGOAL_THEN
   `!n. mfd_geo (top,atlas) (g:B->real^3^3) x u (bb n) IN topspace top /\
        p2bk_dend (top,atlas) g z (mfd_geo (top,atlas) g x u (bb n)) = a - (bb:num->real) n`
    (LABEL_TAC "bbf") THENL
   [GEN_TAC THEN USE_THEN "bbr" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `x:B`; `u:real^3`; `(bb:num->real) n`] P2BK_RAY_AT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= s1` THEN UNDISCH_TAC `s1 < s2` THEN
      UNDISCH_TAC `s2 < (bb:num->real) n` THEN REAL_ARITH_TAC;
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* each chord inequality, multiplied out *)
  SUBGOAL_THEN
   `!n. (s2 - s1) *
        ((mfd_dist (top,atlas) (g:B->real^3^3) q (mfd_geo (top,atlas) g x u (bb n)) pow 2 -
          (bb:num->real) n pow 2) - h1) <= (bb n - s1) * (h2 - h1)`
    (LABEL_TAC "chord") THENL
   [GEN_TAC THEN USE_THEN "bbr" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `x:B`; `u:real^3`; `q:B`; `s1:real`;
                   `(bb:num->real) n`] P2BK_H_CONCAVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `s1 < s2` THEN
      UNDISCH_TAC `s2 < (bb:num->real) n` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s2:real`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `s1 < s2` THEN UNDISCH_TAC `s2 < (bb:num->real) n` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `hb = mfd_dist (top,atlas) (g:B->real^3^3) q
                       (mfd_geo (top,atlas) g x u ((bb:num->real) n)) pow 2 - bb n pow 2` THEN
    SUBGOAL_THEN `&0 < (bb:num->real) n - s1` ASSUME_TAC THENL
     [UNDISCH_TAC `s1 < s2` THEN UNDISCH_TAC `s2 < (bb:num->real) n` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(s2 - s1) * (hb - h1) =
                  ((bb:num->real) n - s1) * ((s2 - s1) / (bb n - s1) * (hb - h1))`
      SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < (bb:num->real) n - s1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < (bb:num->real) n - s1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `h1 + (s2 - s1) / ((bb:num->real) n - s1) * (hb - h1) <= h2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the limits *)
  SUBGOAL_THEN `((bb:num->real) ---> a) sequentially` ASSUME_TAC THENL
   [EXPAND_TAC "bb" THEN
    MP_TAC(ISPECL [`sequentially:num net`; `\n:num. (a:real)`; `\n. (a - s2) * inv(&n + &2)`;
                   `a:real`; `(a - s2) * &0`] REALLIM_SUB) THEN
    REWRITE_TAC[REALLIM_CONST; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPEC `&2` REALLIM_1_OVER_N_OFFSET) THEN
    DISCH_THEN(MP_TAC o SPEC `a - s2` o MATCH_MP REALLIM_LMUL) THEN
    REWRITE_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. mfd_dist (top,atlas) (g:B->real^3^3) q (mfd_geo (top,atlas) g x u ((bb:num->real) n)))
     ---> bq) sequentially` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REALLIM_NULL] THEN MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
    EXISTS_TAC `\n. a - (bb:num->real) n` THEN CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN
      DISCH_TAC THEN USE_THEN "bbf" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                     `q:B`; `mfd_geo (top,atlas) (g:B->real^3^3) x u ((bb:num->real) n)`]
        P2BK_DIST_NEAR_END) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`sequentially:num net`; `\n:num. (a:real)`; `bb:num->real`; `a:real`; `a:real`]
        REALLIM_SUB) THEN
      ASM_REWRITE_TAC[REALLIM_CONST; REAL_SUB_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL [`sequentially:num net`;
    `\n. (s2 - s1) *
         ((mfd_dist (top,atlas) (g:B->real^3^3) q (mfd_geo (top,atlas) g x u ((bb:num->real) n))
           pow 2 - bb n pow 2) - h1)`;
    `\n. ((bb:num->real) n - s1) * (h2 - h1)`] REALLIM_LE) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_SUB THEN REWRITE_TAC[REALLIM_CONST] THEN
    MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THEN MATCH_MP_TAC REALLIM_POW THEN
    ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC REALLIM_MUL THEN REWRITE_TAC[REALLIM_CONST] THEN
    MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[REALLIM_CONST; ETA_AX];
    EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "chord" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[]]);;

(* Monotonicity of the comparison cosine at E along a ray: moving toward E  *)
(* the comparison angle at E with any q does not decrease.                  *)

let P2BK_DIV_LE_CROSS = prove
 (`!a b c d. &0 < b /\ &0 < d /\ a * d <= c * b ==> a / b <= c / d`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `c / d * b = (c * b) / d`] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ]);;

let P2BK_COS_ARITH = prove
 (`!al bq s1 s2 h1 h2.
     &0 <= s1 /\ s1 < s2 /\ s2 < al /\ &0 < bq /\
     (s2 - s1) * ((bq pow 2 - al pow 2) - h1) <= (al - s1) * (h2 - h1)
     ==> ((al - s2) pow 2 + bq pow 2 - (h2 + s2 pow 2)) / (&2 * (al - s2) * bq) <=
         ((al - s1) pow 2 + bq pow 2 - (h1 + s1 pow 2)) / (&2 * (al - s1) * bq)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BK_DIV_LE_CROSS THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((al - s1) pow 2 + bq pow 2 - (h1 + s1 pow 2)) * (&2 * (al - s2) * bq) -
    ((al - s2) pow 2 + bq pow 2 - (h2 + s2 pow 2)) * (&2 * (al - s1) * bq) =
    &2 * bq * ((al - s1) * (h2 - h1) - (s2 - s1) * ((bq pow 2 - al pow 2) - h1))`
  MP_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= &2 * bq * ((al - s1) * (h2 - h1) - (s2 - s1) * ((bq pow 2 - al pow 2) - h1))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let P2BK_COS_MONO = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x u q s1 s2.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\
     (!y v w. y IN topspace top /\ ~collinear {vec 0,v,w}
              ==> &0 <= mfd_sectional atlas g y v w) /\
     x IN topspace top /\ p2bk_dend (top,atlas) g z x < c / &2 /\
     (!L. L < p2bk_dend (top,atlas) g z x ==> p2bk_rayseg (top,atlas) g z x u L) /\
     q IN topspace top /\ p2bk_dend (top,atlas) g z q < c / &2 /\
     &0 <= s1 /\ s1 < s2 /\ s2 < p2bk_dend (top,atlas) g z x
     ==> (p2bk_dend (top,atlas) g z (mfd_geo (top,atlas) g x u s2) pow 2 +
          p2bk_dend (top,atlas) g z q pow 2 -
          mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x u s2) q pow 2) /
         (&2 * p2bk_dend (top,atlas) g z (mfd_geo (top,atlas) g x u s2) *
          p2bk_dend (top,atlas) g z q) <=
         (p2bk_dend (top,atlas) g z (mfd_geo (top,atlas) g x u s1) pow 2 +
          p2bk_dend (top,atlas) g z q pow 2 -
          mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x u s1) q pow 2) /
         (&2 * p2bk_dend (top,atlas) g z (mfd_geo (top,atlas) g x u s1) *
          p2bk_dend (top,atlas) g z q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `q:B`; `s1:real`; `s2:real`]
    P2BK_H_ENDCHORD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `x:B`; `u:real^3`; `s1:real`] P2BK_RAY_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `s1 < s2` THEN
    UNDISCH_TAC `s2 < p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `x:B`; `u:real^3`; `s2:real`] P2BK_RAY_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= s1` THEN UNDISCH_TAC `s1 < s2` THEN
    REAL_ARITH_TAC;
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x u s1`; `q:B`] MFD_DIST_SYM) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x u s2`; `q:B`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `q:B`]
    P2BK_DEND_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`p2bk_dend (top,atlas) (g:B->real^3^3) z x`;
                `p2bk_dend (top,atlas) (g:B->real^3^3) z q`; `s1:real`; `s2:real`;
                `mfd_dist (top,atlas) (g:B->real^3^3) q (mfd_geo (top,atlas) g x u s1) pow 2 -
                 s1 pow 2`;
                `mfd_dist (top,atlas) (g:B->real^3^3) q (mfd_geo (top,atlas) g x u s2) pow 2 -
                 s2 pow 2`]
    P2BK_COS_ARITH) THEN
  ASM_REWRITE_TAC[REAL_SUB_ADD]);;

