(* ========================================================================= *)
(* Unit pc_p2b_cone4: the upper half of MT Claim 10.31 and the main theorem  *)
(* P2BK_END_CONE.  Two points of the central sphere of a neck at the same    *)
(* level give two rays with a positive angle at E; their comparison angles   *)
(* then stay bounded below, so d(gamma s, mu s) >= c s while the level-set   *)
(* bound gives d <= 50 h; hence sqrt(R) dE <= c2 near E.                     *)
(* ========================================================================= *)

needs "src/pc_p2b_cone3.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Two rays with a positive angle at E, and the upper half of Claim 10.31.   *)
(* ========================================================================= *)

(* On the central sphere of a neck, dE takes equal values at some pair of    *)
(* antipodal points (the antipodal difference changes sign on the connected  *)
(* sphere).                                                                  *)

let P2BK_SAME_LEVEL_PAIR = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 (y:B) e.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ rfs_neck (top,atlas) g eps y e
     ==> ?p. p IN sphere(vec 0,&1) /\
             p2bk_dend (top,atlas) g z (e p) = p2bk_dend (top,atlas) g z (e(--p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->B`] MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:B->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`]
    P2BK_DEND_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),top) (e:real^3->B)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `rfs_neck_dom eps:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),
                    subtopology euclidean (sphere(vec 0:real^3,&1))) (\p:real^3. --p)`
    ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
    SIMP_TAC[CONTINUOUS_ON_NEG; CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; NORM_NEG];
    ALL_TAC] THEN
  ABBREV_TAC `psi = \p:real^3. p2bk_dend (top,atlas) (g:B->real^3^3) z (e p) -
                               p2bk_dend (top,atlas) g z (e(--p))` THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),euclideanreal)
                   (psi:real^3->real)`
    ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\p:real^3. p2bk_dend (top,atlas) (g:B->real^3^3) z (e p)) =
                    p2bk_dend (top,atlas) g z o (e:real^3->B)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(\p:real^3. p2bk_dend (top,atlas) (g:B->real^3^3) z (e(--p))) =
                    (p2bk_dend (top,atlas) g z o (e:real^3->B)) o (\p. --p)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^3,&1))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `is_realinterval (IMAGE (psi:real^3->real) (sphere(vec 0,&1)))` MP_TAC THENL
   [REWRITE_TAC[GSYM CONNECTED_IN_EUCLIDEANREAL] THEN
    MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^3,&1))` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL; CONNECTED_IN_EUCLIDEAN] THEN
    MATCH_MP_TAC CONNECTED_SPHERE THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(basis 1:real^3) IN sphere(vec 0,&1) /\ --(basis 1:real^3) IN sphere(vec 0,&1)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_NEG] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^3->real)(--basis 1) = --(psi(basis 1))` ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN REWRITE_TAC[VECTOR_NEG_NEG] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[is_realinterval; IN_IMAGE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?p:real^3. &0 = psi p /\ p IN sphere(vec 0,&1)` MP_TAC THENL
   [ASM_CASES_TAC `(psi:real^3->real)(basis 1) <= &0` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`(psi:real^3->real)(basis 1)`;
                                    `(psi:real^3->real)(--basis 1)`; `&0`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`(psi:real^3->real)(--basis 1)`;
                                    `(psi:real^3->real)(basis 1)`; `&0`])] THEN
    (ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]]) THEN
    REPEAT CONJ_TAC THEN
    TRY(EXISTS_TAC `basis 1:real^3` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(EXISTS_TAC `--basis 1:real^3` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    POP_ASSUM MP_TAC THEN
    UNDISCH_TAC `(psi:real^3->real)(--basis 1) = --(psi(basis 1))` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 = (psi:real^3->real) p` THEN EXPAND_TAC "psi" THEN REAL_ARITH_TAC]);;

(* Distinct points at the same level have a positive comparison angle at E. *)

let P2BK_POS_EANG_SAME_LEVEL = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 p q.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ p IN topspace top /\ q IN topspace top /\
     p2bk_dend (top,atlas) g z p = p2bk_dend (top,atlas) g z q /\ ~(p = q)
     ==> &0 < p2bk_eang (top,atlas) g z p q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  SUBGOAL_THEN `&0 < mfd_dist (top,atlas) (g:B->real^3^3) p q` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `p:B`; `q:B`] MFD_DIST_EQ_0) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `p:B`; `q:B`] MFD_DIST_POS_LE) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `q:B`] P2BK_EANG_COS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `q:B`]
    P2BK_DEND_POS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `L = p2bk_dend (top,atlas) (g:B->real^3^3) z q` THEN
  ABBREV_TAC `D = mfd_dist (top,atlas) (g:B->real^3^3) p q` THEN
  ABBREV_TAC `k = p2bk_eang (top,atlas) (g:B->real^3^3) z p q` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(L pow 2 + L pow 2 - D pow 2) / (&2 * L * L) < &1` MP_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * L * L` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
    MP_TAC(SPECL [`D:real`; `2`] REAL_POW_LT) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `cos k = (L pow 2 + L pow 2 - D pow 2) / (&2 * L * L)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `cos(&0) < &1` THEN REWRITE_TAC[COS_0] THEN REAL_ARITH_TAC);;

(* Two distinct points near E at the same level. *)

let P2BK_TWO_POINTS = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1.
     p2bk_angctx (top,atlas) g H eps z es r0 c r1
     ==> ?a b. a IN topspace top /\ b IN topspace top /\ ~(a = b) /\
               p2bk_dend (top,atlas) g z a = p2bk_dend (top,atlas) g z b /\
               p2bk_dend (top,atlas) g z a < c / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ANGCTX_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c / &4`] P2BK_DEND_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `y0:B` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `y0:B`] P2BK_NEAR_SEPNECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z y0 < c / &4` THEN
    UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `e:real^3->B`)] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:B->real^3^3) eps y0 e` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bk_sepneck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `y0:B`; `e:real^3->B`] P2BK_SAME_LEVEL_PAIR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `--(p:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0; NORM_NEG];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(e:real^3->B) p`; `(e:real^3->B)(--p)`] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `y0:B`; `e:real^3->B`] P2BK_NECK_SCALE_LEVEL) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `y0:B`; `e:real^3->B`; `(e:real^3->B) p`] P2BK_SPHERE_LEVEL) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `y0:B`; `e:real^3->B`; `(e:real^3->B)(--p)`] P2BK_SPHERE_LEVEL) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o
      check (fun th -> concl th = `rfs_neck (top,atlas) (g:B->real^3^3) eps y0 e`)) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->B`] MFD_PARAM_MAPS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:B->real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
     [MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3) = --p` MP_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(e1:B->real^3)((e:real^3->B) p)` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
      UNDISCH_TAC `(p:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
      DISCH_TAC THEN REWRITE_TAC[VECTOR_ARITH `p = --p <=> p:real^3 = vec 0`] THEN
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `norm(vec 0:real^3) = &1` THEN
      REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC];
    UNDISCH_TAC `abs(p2bk_dend (top,atlas) (g:B->real^3^3) z ((e:real^3->B) p) -
                     p2bk_dend (top,atlas) g z y0) <= &5 * inv(sqrt(mfd_scalar atlas g y0))` THEN
    UNDISCH_TAC `&99 * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) y0)) <=
                 p2bk_dend (top,atlas) g z y0` THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z y0 < c / &4` THEN
    UNDISCH_TAC `&0 < inv(sqrt(mfd_scalar atlas (g:B->real^3^3) y0))` THEN REAL_ARITH_TAC]);;

(* Two rays with a positive angle at E. *)

let P2BK_TWO_RAYS = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1.
     p2bk_angctx (top,atlas) g H eps z es r0 c r1
     ==> ?x u y v. p2bk_isray (top,atlas) g z c x u /\ p2bk_isray (top,atlas) g z c y v /\
                   &0 < p2bk_theta (top,atlas) g z x u y v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ANGCTX_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`] P2BK_TWO_POINTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` (X_CHOOSE_THEN `b:B` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `a:B`; `b:B`] P2BK_POS_EANG_SAME_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `a:B`] P2BK_ISRAY_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `ua:real^3`) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `b:B`] P2BK_ISRAY_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z a = p2bk_dend (top,atlas) g z b` THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z a < c / &2` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `ub:real^3`)] THEN
  MAP_EVERY EXISTS_TAC [`a:B`; `ua:real^3`; `b:B`; `ub:real^3`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `p2bk_eang (top,atlas) (g:B->real^3^3) z a b` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `a:B`; `ua:real^3`] P2BK_RPT_TOP) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `b:B`; `ub:real^3`] P2BK_RPT_TOP) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `a:B`; `ua:real^3`; `b:B`; `ub:real^3`] P2BK_THETA_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`p2bk_dend (top,atlas) (g:B->real^3^3) z a`;
                             `p2bk_dend (top,atlas) (g:B->real^3^3) z b`] o CONJUNCT1) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* Points at the same level as x on the two rays are at distance >= kap l,  *)
(* and within 50 h(x) of each other.                                         *)

let P2BK_LEVEL_PAIR_DIST = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x p q.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\
     x IN topspace top /\ p IN topspace top /\ q IN topspace top /\
     p2bk_dend (top,atlas) g z x < c /\
     p2bk_dend (top,atlas) g z p = p2bk_dend (top,atlas) g z x /\
     p2bk_dend (top,atlas) g z q = p2bk_dend (top,atlas) g z x
     ==> mfd_dist (top,atlas) g p q <= &50 * inv(sqrt(mfd_scalar atlas g x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  SUBGOAL_THEN
   `!w:B. w IN topspace top /\ p2bk_dend (top,atlas) (g:B->real^3^3) z w = p2bk_dend (top,atlas) g z x
          ==> mfd_dist (top,atlas) g w x <= &25 * inv(sqrt(mfd_scalar atlas g x)) /\
              mfd_dist (top,atlas) g x w <= &25 * inv(sqrt(mfd_scalar atlas g x))`
    (LABEL_TAC "near") THENL
   [X_GEN_TAC `w:B` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `x:B`] P2BK_NEAR_SEPNECK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `ex:real^3->B`) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `w:B`] P2BK_NEAR_SEPNECK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `ew:real^3->B`) THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) x /\ &0 < mfd_scalar atlas g w`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2bk_sepneck; rfs_neck]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `x:B`; `ex:real^3->B`; `w:B`; `ew:real^3->B`] P2BK_LEVEL_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN MATCH_MP_TAC REAL_LE_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      STRIP_TAC] THEN
    MP_TAC(SPECL [`mfd_scalar atlas (g:B->real^3^3) x`; `mfd_scalar atlas (g:B->real^3^3) w`]
      P2BK_SCALE_COMPARE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `w:B`; `ew:real^3->B`; `x:B`; `ex:real^3->B`] P2BK_LEVEL_DIST) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `x:B`; `w:B`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `sqrt(&2) <= &3 / &2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    UNDISCH_TAC `inv(sqrt(mfd_scalar atlas (g:B->real^3^3) w)) <=
                 sqrt(&2) * inv(sqrt(mfd_scalar atlas g x))` THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) w x <=
                 &10 * (inv(sqrt(mfd_scalar atlas g w)) + inv(sqrt(mfd_scalar atlas g x)))` THEN
    ABBREV_TAC `hx = inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x))` THEN
    ABBREV_TAC `hw = inv(sqrt(mfd_scalar atlas (g:B->real^3^3) w))` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `sqrt(&2) * hx <= &3 / &2 * hx` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `hw <= sqrt(&2) * hx` THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) w x <= &10 * (hw + hx)` THEN
    UNDISCH_TAC `&0 <= hx` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "near" (MP_TAC o SPEC `p:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "near" (MP_TAC o SPEC `q:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `x:B`; `q:B`] MFD_DIST_TRIANGLE) THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) p x <= &25 * inv(sqrt(mfd_scalar atlas g x))` THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x q <= &25 * inv(sqrt(mfd_scalar atlas g x))` THEN
  REAL_ARITH_TAC);;

(* The upper half of MT Claim 10.31: sqrt(R x) dE(x) <= c2 near E. *)

let P2BK_UPPER_1031 = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1.
     p2bk_angctx (top,atlas) g H eps z es r0 c r1
     ==> ?s1 c2. &0 < s1 /\ &0 < c2 /\
                 !x. x IN topspace top /\ p2bk_dend (top,atlas) g z x <= s1
                     ==> sqrt(mfd_scalar atlas g x) * p2bk_dend (top,atlas) g z x <= c2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ANGCTX_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`] P2BK_TWO_RAYS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `xa:B` (X_CHOOSE_THEN `ua:real^3` (X_CHOOSE_THEN `xb:B`
    (X_CHOOSE_THEN `ub:real^3` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `xa:B`; `ua:real^3`; `xb:B`; `ub:real^3`;
                 `p2bk_theta (top,atlas) (g:B->real^3^3) z xa ua xb ub / &2`] P2BK_THETA_APPROX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < p2bk_theta (top,atlas) (g:B->real^3^3) z xa ua xb ub` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `th = p2bk_theta (top,atlas) (g:B->real^3^3) z xa ua xb ub` THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:real` (X_CHOOSE_THEN `m0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "app"))))))) THEN
  ABBREV_TAC `bh = min (th / &2) (&1)` THEN
  SUBGOAL_THEN `&0 < bh /\ bh <= th / &2 /\ bh <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "bh" THEN UNDISCH_TAC `&0 < th` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `bh < pi` ASSUME_TAC THENL
   [MP_TAC PI_APPROX_32 THEN UNDISCH_TAC `bh <= &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cos bh < &1` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM COS_0] THEN MATCH_MP_TAC COS_MONO_LT THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN UNDISCH_TAC `bh < pi` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `kap = sqrt(&2 * (&1 - cos bh))` THEN
  SUBGOAL_THEN `&0 < kap` ASSUME_TAC THENL
   [EXPAND_TAC "kap" THEN MATCH_MP_TAC SQRT_POS_LT THEN UNDISCH_TAC `cos bh < &1` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`min l0 m0`; `&50 / kap`] THEN
  CONJ_TAC THENL [UNDISCH_TAC `&0 < l0` THEN UNDISCH_TAC `&0 < m0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:B` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `x:B`]
    P2BK_DEND_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `l = p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `xa:B`; `ua:real^3`; `l:real`] P2BK_RPT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `l <= min l0 m0` THEN
    UNDISCH_TAC `l0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z xa` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `xb:B`; `ub:real^3`; `l:real`] P2BK_RPT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `l <= min l0 m0` THEN
    UNDISCH_TAC `m0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z xb` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  USE_THEN "app" (MP_TAC o SPECL [`l:real`; `l:real`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `l <= min l0 m0` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `pa = p2bk_rpt (top,atlas) (g:B->real^3^3) z xa ua l` THEN
  ABBREV_TAC `pb = p2bk_rpt (top,atlas) (g:B->real^3^3) z xb ub l` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `pa:B`; `pb:B`; `bh:real`] P2BK_EANG_DIST_LOWER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `th - th / &2 < p2bk_eang (top,atlas) (g:B->real^3^3) z pa pb` THEN
    UNDISCH_TAC `bh <= th / &2` THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `pa:B`; `pb:B`] P2BK_LEVEL_PAIR_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `l <= min l0 m0` THEN
    UNDISCH_TAC `l0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z xa` THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2bk_isray] o
      check (fun th -> concl th = `p2bk_isray (top,atlas) (g:B->real^3^3) z c xa ua`)) THEN
    UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `sqrt(l pow 2 + l pow 2 - &2 * l * l * cos bh) = l * kap` SUBST_ALL_TAC THENL
   [EXPAND_TAC "kap" THEN
    SUBGOAL_THEN `l pow 2 + l pow 2 - &2 * l * l * cos bh = l pow 2 * (&2 * (&1 - cos bh))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SQRT_MUL] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `x:B`] P2BK_NEAR_SEPNECK) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `l <= min l0 m0` THEN
      UNDISCH_TAC `l0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z xa` THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2bk_isray] o
        check (fun th -> concl th = `p2bk_isray (top,atlas) (g:B->real^3^3) z c xa ua`)) THEN
      UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
      MESON_TAC[p2bk_sepneck; rfs_neck]];
    ALL_TAC] THEN
  ABBREV_TAC `sr = sqrt(mfd_scalar atlas (g:B->real^3^3) x)` THEN
  SUBGOAL_THEN `&0 < sr` ASSUME_TAC THENL
   [EXPAND_TAC "sr" THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `sr * (l * kap) < sr * (&50 * inv sr)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `l * kap < mfd_dist (top,atlas) (g:B->real^3^3) pa pb` THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) pa pb <= &50 * inv sr` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sr * &50 * inv sr = &50` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sr` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The main theorem P2BK_END_CONE (MT Secs 10.4, Claims 10.13, 10.31, Lemmas *)
(* 10.21, 10.22, 10.27 in the form stated in pc_p2b_conestmts).  The bad     *)
(* tube with eps gives the tube and the chain of 2 eps necks, dE is the      *)
(* distance to the end, s1 is below the inner region bound and the scale     *)
(* bounds; the angle clause is P2BK_EANG_TRIANGLE_ASYM.                      *)
(* ========================================================================= *)

let P2BK_LOWER_1031 = prove
 (`!eps R d. &0 < eps /\ eps <= &1 / &200 /\ &0 < R /\
             sqrt(&1 - &2 * eps) * inv(sqrt R) * inv(&2 * eps) <= d
             ==> inv(&4 * eps) <= sqrt R * d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt R` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= sqrt(&1 - &2 * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN UNDISCH_TAC `eps <= &1 / &200` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&2 * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN UNDISCH_TAC `&0 < eps` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt R * (sqrt(&1 - &2 * eps) * inv(sqrt R) * inv(&2 * eps)) <= sqrt R * d`
    MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt R * (sqrt(&1 - &2 * eps) * inv(sqrt R) * inv(&2 * eps)) =
                sqrt(&1 - &2 * eps) * inv(&2 * eps)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sqrt R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&4 * eps) = &1 / &2 * inv(&2 * eps)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 * inv(&2 * eps) <= sqrt(&1 - &2 * eps) * inv(&2 * eps)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let P2BK_END_CONE = prove
 (`!w:B->bool. P2BK_END_CONE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2BK_END_CONE_STATEMENT] THEN
  MP_TAC(INST [`UNIV:B->bool`,`u:B->bool`] P2BK_GOOD_EPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "good"))) THEN
  EXISTS_TAC `min (eps1 / &2) (&1 / &200)` THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < eps1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:B->real^3^3`;
                       `V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                          (real->B->real^3^3)`;
                       `H:real^3->B`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= &1 / &200 /\ &2 * eps <= eps1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `eps <= min (eps1 / &2) (&1 / &200)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "good" (MP_TAC o SPEC `&2 * eps`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < eps` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`;
                 `V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
                 `H:real^3->B`] P2BK_TUBE_OF_BAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`;
                 `V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
                 `H:real^3->B`] P2BK_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `&2 * eps`] P2BK_END_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:num->B` (X_CHOOSE_THEN `es:num->real^3->B`
    (X_CHOOSE_TAC `r0:real`))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  SUBGOAL_THEN `&1 < r0 /\ r0 < &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bk_endchain (top,atlas) (g:B->real^3^3) H (&2 * eps) z es r0` THEN
    SIMP_TAC[p2bk_endchain];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `&2 * eps`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `max r0 r1`] P2BK_NEARCTX_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `r0 < &2` THEN UNDISCH_TAC `r1 < &2` THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `cc:real`)] THEN
  SUBGOAL_THEN `p2bk_angctx (top,atlas) (g:B->real^3^3) H (&2 * eps) z es r0 cc (max r0 r1)`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2bk_angctx]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ANGCTX_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `&2 * eps`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `r1:real`] P2BK_DEND_INNER_REGION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ci:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inner"))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `&2 * eps`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `cc:real`; `max r0 r1`] P2BK_UPPER_1031) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `su:real` (X_CHOOSE_THEN `c2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "upper"))))) THEN
  MAP_EVERY EXISTS_TAC [`p2bk_dend (top,atlas) (g:B->real^3^3) z`;
                        `min (min (ci / &2) su) (cc / &4)`; `c2:real`] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&0 < ci` THEN UNDISCH_TAC `&0 < su` THEN UNDISCH_TAC `&0 < cc` THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BK_DEND_POS THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `&2 * eps`; `es:num->real^3->B`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BK_DEND_LIPSCHITZ THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `&2 * eps`; `es:num->real^3->B`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BK_DEND_SMALL THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `&2 * eps`; `es:num->real^3->B`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC;
    ALL_TAC;
    ALL_TAC] THENL
   [(* the neck clauses near E *)
    X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p2bk_dend (top,atlas) (g:B->real^3^3) z x < cc` ASSUME_TAC THENL
     [UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x <= min (min (ci / &2) su) (cc / &4)` THEN
      UNDISCH_TAC `&0 < cc` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `?w. x = (H:real^3->B) w /\ &1 < norm w /\ norm w < &2` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:B) IN topspace top` THEN
        UNDISCH_THEN `IMAGE (H:real^3->B) (annulus (&1) (&2)) = topspace top` (SUBST1_TAC o SYM) THEN
        REWRITE_TAC[IN_IMAGE; annulus; IN_ELIM_THM] THEN MESON_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `norm(w:real^3) <= r1` THENL
       [USE_THEN "inner" (MP_TAC o SPEC `w:real^3`) THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `x = (H:real^3->B) w` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x <= min (min (ci / &2) su) (cc / &4)` THEN
        UNDISCH_TAC `&0 < ci` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_evolving_neck")) (concl th) &&
        is_forall(concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(norm(w:real^3) <= r1)` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `H:real^3->B`; `&2 * eps`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                     `cc:real`; `max r0 r1`; `x:B`] P2BK_NEAR_SEPNECK) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `e:real^3->B`) THEN
      SUBGOAL_THEN `rfs_neck (top,atlas) (g:B->real^3^3) (&2 * eps) x e` ASSUME_TAC THENL
       [ASM_MESON_TAC[p2bk_sepneck]; ALL_TAC] THEN
      MATCH_MP_TAC P2BK_LOWER_1031 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
      MATCH_MP_TAC P2BK_DEND_NECK_LOWER THEN
      MAP_EVERY EXISTS_TAC [`H:real^3->B`; `es:num->real^3->B`; `r0:real`; `e:real^3->B`] THEN
      ASM_REWRITE_TAC[];
      USE_THEN "upper" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x <= min (min (ci / &2) su) (cc / &4)` THEN
      REAL_ARITH_TAC];
    (* ray points *)
    MAP_EVERY X_GEN_TAC [`x:B`; `t:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BK_NEAR_RAY_POINT THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `&2 * eps`; `es:num->real^3->B`; `r0:real`;
                          `cc:real`; `max r0 r1`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `&2 * eps`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `x:B`]
      P2BK_DEND_POS) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x <= min (min (ci / &2) su) (cc / &4)` THEN
    UNDISCH_TAC `t <= p2bk_dend (top,atlas) (g:B->real^3^3) z x / &2` THEN
    UNDISCH_TAC `&0 < cc` THEN REAL_ARITH_TAC;
    (* the asymptotic triangle inequality for comparison angles at E *)
    X_GEN_TAC `dl:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `&2 * eps`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `cc:real`; `max r0 r1`; `dl:real`] P2BK_EANG_TRIANGLE_ASYM) THEN
    ASM_REWRITE_TAC[p2bk_eang]]);;

