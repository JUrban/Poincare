(* ========================================================================= *)
(* L3 and L4 of the limit-geometry layer (the statements LIM_VOL_STATEMENT   *)
(* and LIM_KNC_STATEMENT of pc_lim_stmts).                                   *)
(*   LIM_VOL |- !u w. LIM_VOL_STATEMENT u w: volumes of rescaled balls in   *)
(*     the sandwich form (radii r1 < r2).                                    *)
(*   LIM_KNC |- !u w. LIM_KNC_STATEMENT u w: kappa-noncollapsing of the     *)
(*     views at the scales r0 / sqrt(Q k) passes to the limit flow view.    *)
(* Route: volume comparison under the rescaled pullbacks (P2BC_VOLUME_PB_   *)
(* COMPARE), ball inclusions LIM_BALL_IN and LIM_BALL_OUT (pc_lim_close),   *)
(* uniform curvature transfer LIM_VIEW_RM_BOUND (LCK_CURVATURE_STABILITY   *)
(* with the bound K0 from RFA_LRM_SECTIONAL_BOUND), persistence of the      *)
(* view balls through the diffeomorphisms at all times (LIM_DIFFEO_OPEN_    *)
(* TRANSFER), and the limit r' -> r.                                         *)
(* ========================================================================= *)

needs "src/pc_lim_stmts.ml";;
needs "src/pc_lim_close.ml";;
needs "src/pc_lim_dist.ml";;
needs "src/pc_lim_curv.ml";;
needs "src/pc_cmp_pull.ml";;
needs "src/pc_rfa_sec.ml";;

prioritize_real();;
type_invention_error := true;;
(* Preimages of open sets under a diffeomorphism of open sets are open.     *)

let LIM_DIFFEO_PREIMAGE_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (top':B topology)
    (atlas':((B->bool)#(B->real^M))->bool) U U' psi psi' O.
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ open_in top' O
     ==> open_in top {z | z IN U /\ psi z IN O}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  UNDISCH_TAC `continuous_map (subtopology top (U:A->bool),top') (psi:A->B)` THEN
  REWRITE_TAC[CONTINUOUS_MAP] THEN DISCH_THEN(MP_TAC o SPEC `O:B->bool` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `topspace top INTER (U:A->bool) = U` SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]; SIMP_TAC[]]);;

(* An open set inside a compact set has a volume.                            *)

let LIM_OPEN_VOLUME = prove
 (`!top atlas (g:A->real^N^N) S K.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top S /\ compact_in top K /\ S SUBSET K
     ==> mfd_has_volume (top,atlas) g S (mfd_volume (top,atlas) g S)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `K:A->bool`; `S:A->bool`] MFD_VOLUME_COMPACT_MEASURABLE_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `w:real`) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `S:A->bool`; `K:A->bool`; `w:real`] MFD_HAS_VOLUME_SUBSET) THEN
  ASM_SIMP_TAC[]);;

(* Elementary bounds for the powers (1 +/- d)^(3/2).                         *)

let LIM_POW32_BOUNDS = prove
 (`!d. &0 <= d /\ d <= &1
       ==> (&1 + d) * sqrt(&1 + d) <= &1 + &3 * d /\
           &1 - &2 * d <= (&1 - d) * sqrt(&1 - d)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `d:real` LIM_SQRT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + d) * (&1 + d)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `d * d <= d ==> (&1 + d) * (&1 + d) <= &1 + &3 * d`) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - d) * (&1 - d)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= d * d ==> &1 - &2 * d <= (&1 - d) * (&1 - d)`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]);;
(* Choice of a small closeness parameter.                                   *)

let LIM_SMALL_D = prove
 (`!e a c. &0 < e /\ &0 <= a /\ &0 < c
           ==> ?d. &0 < d /\ d <= &1 / &2 /\
                   !d'. &0 <= d' /\ d' <= d ==> c * d' * a <= e`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `min (&1 / &2) (e / (c * (a + &1)))` THEN
  SUBGOAL_THEN `&0 < e / (c * (a + &1)) /\ c * (e / (c * (a + &1))) * (a + &1) = e`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_LT_MUL; REAL_ARITH `&0 <= a ==> &0 < a + &1`];
      UNDISCH_TAC `&0 < c` THEN UNDISCH_TAC `&0 <= a` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `d':real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c * d' * (a + &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]);;
(* Volume comparison under a diffeomorphism psi whose pullback metric,     *)
(* scaled by c, is within 1 +/- d of g, in the rescaled form c^(3/2)       *)
(* vol'(psi S) versus vol(S).                                                *)

let LIM_VOL_IMAGE_UPPER = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi' S v v' c d.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ S SUBSET U /\
     &0 < c /\ &0 <= d /\ d <= &1 /\
     (!y w. y IN S
            ==> c * (w dot (mfd_pullback_metric atlas atlas' psi g' y ** w)) <=
                (&1 + d) * (w dot (g y ** w))) /\
     mfd_has_volume (top,atlas) g S v /\ mfd_has_volume (top',atlas') g' (IMAGE psi S) v'
     ==> c * sqrt c * v' <= (&1 + &3 * d) * v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `S:A->bool`;
                 `v:real`; `v':real`; `(&1 + d) / c`] P2BC_VOLUME_PB_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `c:real` THEN
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_DIV_LMUL; REAL_LT_IMP_NZ];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `S:A->bool`; `v:real`] MFD_HAS_VOLUME_POS_LE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `d:real` LIM_POW32_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt c` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `c * sqrt c * ((&1 + d) / c * sqrt((&1 + d) / c) * v) =
                ((&1 + d) * sqrt(&1 + d)) * v` ASSUME_TAC THENL
   [REWRITE_TAC[SQRT_DIV] THEN UNDISCH_TAC `&0 < sqrt c` THEN UNDISCH_TAC `&0 < c` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c * sqrt c * ((&1 + d) / c * sqrt((&1 + d) / c) * v)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

let LIM_VOL_IMAGE_LOWER = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi' S v v' c d.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ S SUBSET U /\
     &0 < c /\ &0 <= d /\ d < &1 /\
     (!y w. y IN S
            ==> (&1 - d) * (w dot (g y ** w)) <=
                c * (w dot (mfd_pullback_metric atlas atlas' psi g' y ** w))) /\
     mfd_has_volume (top,atlas) g S v /\ mfd_has_volume (top',atlas') g' (IMAGE psi S) v'
     ==> (&1 - &2 * d) * v <= c * sqrt c * v'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `S:A->bool`;
                 `v:real`; `v':real`; `c / (&1 - d)`] P2BC_VOLUME_PB_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&1 - d` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 - d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_DIV_LMUL; REAL_LT_IMP_NZ];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `S:A->bool`; `v:real`] MFD_HAS_VOLUME_POS_LE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `g':B->real^3^3`; `IMAGE (psi:A->B) S`; `v':real`] MFD_HAS_VOLUME_POS_LE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `d:real` LIM_POW32_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt c /\ &0 < sqrt(&1 - d) /\ &0 < &1 - d` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SQRT_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((&1 - d) * sqrt(&1 - d)) * (c / (&1 - d) * sqrt(c / (&1 - d)) * v') =
                c * sqrt c * v'` ASSUME_TAC THENL
   [REWRITE_TAC[SQRT_DIV] THEN UNDISCH_TAC `&0 < sqrt(&1 - d)` THEN
    UNDISCH_TAC `&0 < &1 - d` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((&1 - d) * sqrt(&1 - d)) * v` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* ========================================================================= *)
(* The volume sandwich (L3).                                                 *)
(* ========================================================================= *)
(* The volume sandwich for one diffeomorphism close to an isometry after    *)
(* the scaling by c.                                                         *)

let LIM_VOL_STEP = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi' Kc y
    r1 r2 rm rho1 rho2 c dd v1 v2 e.
     hausdorff_space top /\ hausdorff_space top' /\
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     compact_in top Kc /\ Kc SUBSET U /\ mfd_cball (top,atlas) g y (r2 + &1) SUBSET Kc /\
     compact_in top (mfd_cball (top,atlas) g y (r2 + &1)) /\
     &0 < c /\ &0 <= dd /\ dd <= &1 / &2 /\
     (!z w. z IN Kc
            ==> abs(c * (w dot (mfd_pullback_metric atlas atlas' psi g' z ** w)) -
                    w dot (g z ** w)) <= dd * (w dot (g z ** w))) /\
     r1 < rm /\ rm < r2 /\
     (!z. z IN mfd_ball (top',atlas') g' (psi y) rho1
          ==> z IN IMAGE psi (mfd_ball (top,atlas) g y rm INTER U)) /\
     (!z. z IN mfd_ball (top',atlas') g' (psi y) rho2
          ==> z IN IMAGE psi (mfd_ball (top,atlas) g y (r2 + &1) INTER U)) /\
     (!z. z IN mfd_ball (top,atlas) g y r1
          ==> psi z IN mfd_ball (top',atlas') g' (psi y) rho2) /\
     mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y r1) v1 /\
     mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y r2) v2 /\
     &3 * dd * v2 <= e /\ &2 * dd * v1 <= e
     ==> ?vk1 vk2.
           mfd_has_volume (top',atlas') g' (mfd_ball (top',atlas') g' (psi y) rho1) vk1 /\
           mfd_has_volume (top',atlas') g' (mfd_ball (top',atlas') g' (psi y) rho2) vk2 /\
           c * sqrt c * vk1 <= v2 + e /\ v1 <= c * sqrt c * vk2 + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  ABBREV_TAC `C1 = mfd_cball (top,atlas) (g:A->real^3^3) y (r2 + &1)` THEN
  ABBREV_TAC `C2 = IMAGE (psi:A->B) C1` THEN
  SUBGOAL_THEN `compact_in top' (C2:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C2" THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology top (U:A->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) (g:A->real^3^3) y rm SUBSET C1 /\
                mfd_ball (top,atlas) g y (r2 + &1) SUBSET C1 /\
                mfd_ball (top,atlas) g y r2 SUBSET C1 /\
                mfd_ball (top,atlas) g y r1 SUBSET C1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C1" THEN REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Bk1 = mfd_ball (top',atlas') (g':B->real^3^3) ((psi:A->B) y) rho1` THEN
  ABBREV_TAC `Bk2 = mfd_ball (top',atlas') (g':B->real^3^3) ((psi:A->B) y) rho2` THEN
  SUBGOAL_THEN `open_in top' (Bk1:B->bool) /\ open_in top' (Bk2:B->bool) /\
                Bk1 SUBSET C2 /\ Bk2 SUBSET C2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Bk1" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "Bk2" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:B` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Bk1:B->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "C2" THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:B` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Bk2:B->bool`)) (concl th) &&
        can (find_term ((=) `r2 + &1`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "C2" THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `Bk1:B->bool`; `C2:B->bool`] LIM_OPEN_VOLUME) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `Bk2:B->bool`; `C2:B->bool`] LIM_OPEN_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  EXISTS_TAC `mfd_volume (top',atlas') (g':B->real^3^3) Bk1` THEN
  EXISTS_TAC `mfd_volume (top',atlas') (g':B->real^3^3) Bk2` THEN
  ASM_REWRITE_TAC[] THEN
  (* the first inequality *)
  ABBREV_TAC `S = mfd_ball (top,atlas) (g:A->real^3^3) y r2 INTER
                  {z | z IN U /\ (psi:A->B) z IN Bk1}` THEN
  SUBGOAL_THEN `open_in top (S:A->bool) /\ S SUBSET U /\ S SUBSET Kc /\
                S SUBSET mfd_ball (top,atlas) (g:A->real^3^3) y r2 /\
                IMAGE (psi:A->B) S = Bk1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "S" THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[MFD_BALL_OPEN] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `U:A->bool`;
                     `U':B->bool`; `psi:A->B`; `psi':B->A`; `Bk1:B->bool`]
                    LIM_DIFFEO_PREIMAGE_OPEN) THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "S" THEN SET_TAC[];
      EXPAND_TAC "S" THEN ASM SET_TAC[];
      EXPAND_TAC "S" THEN SET_TAC[];
      EXPAND_TAC "S" THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `z:B` THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:B` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Bk1:B->bool`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN EXISTS_TAC `w:A` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(w:A) IN mfd_ball (top,atlas) (g:A->real^3^3) y rm` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LT_TRANS];
        UNDISCH_TAC `(z:B) IN Bk1` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `S:A->bool`; `Kc:A->bool`] LIM_OPEN_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `S:A->bool`;
                 `mfd_volume (top,atlas) (g:A->real^3^3) S`;
                 `mfd_volume (top',atlas') (g':B->real^3^3) Bk1`; `c:real`; `dd:real`]
                LIM_VOL_IMAGE_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`z:A`; `w:real^3`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`z:A`; `w:real^3`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `dd:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REAL_ARITH_TAC]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `S:A->bool`; `mfd_ball (top,atlas) (g:A->real^3^3) y r2`;
                 `mfd_volume (top,atlas) (g:A->real^3^3) S`; `v2:real`] MFD_HAS_VOLUME_MONO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + &3 * dd) * mfd_volume (top,atlas) (g:A->real^3^3) S` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + &3 * dd) * v2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the second inequality *)
  ABBREV_TAC `T0 = mfd_ball (top,atlas) (g:A->real^3^3) y r1` THEN
  SUBGOAL_THEN `(T0:A->bool) SUBSET Kc /\ T0 SUBSET U /\ open_in top T0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN ASM_SIMP_TAC[MFD_BALL_OPEN] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `U:A->bool`; `U':B->bool`;
                 `psi:A->B`; `psi':B->A`; `Kc:A->bool`; `T0:A->bool`] LIM_DIFFEO_IMAGE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (psi:A->B) T0 SUBSET C2 /\ IMAGE psi T0 SUBSET Bk2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "C2" THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `T0:A->bool`)) (concl th) &&
        can (find_term ((=) `Bk2:B->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `IMAGE (psi:A->B) T0`; `C2:B->bool`] LIM_OPEN_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `IMAGE (psi:A->B) T0`; `Bk2:B->bool`;
                 `mfd_volume (top',atlas') (g':B->real^3^3) (IMAGE (psi:A->B) T0)`;
                 `mfd_volume (top',atlas') (g':B->real^3^3) Bk2`] MFD_HAS_VOLUME_MONO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `T0:A->bool`;
                 `v1:real`; `mfd_volume (top',atlas') (g':B->real^3^3) (IMAGE (psi:A->B) T0)`;
                 `c:real`; `dd:real`] LIM_VOL_IMAGE_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`z:A`; `w:real^3`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`z:A`; `w:real^3`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `dd:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REAL_ARITH_TAC]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < c * sqrt c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `c * sqrt c * mfd_volume (top',atlas') (g':B->real^3^3) (IMAGE (psi:A->B) T0) <=
                c * sqrt c * mfd_volume (top',atlas') g' Bk2` MP_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_REAL_ARITH_TAC]);;
(* L3: volumes of rescaled balls, sandwich form.                            *)

let LIM_VOL = prove
 (`!u:A->bool w:B->bool. LIM_VOL_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_VOL_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `s:real`; `y:B`; `r1:real`; `r2:real`;
    `v1:real`; `v2:real`; `e:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  SUBGOAL_THEN `&0 <= v1 /\ &0 <= v2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) s`;
                     `mfd_ball (top,atlas) ((g:real->B->real^3^3) s) y r1`;
                     `v1:real`] MFD_HAS_VOLUME_POS_LE);
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) s`;
                     `mfd_ball (top,atlas) ((g:real->B->real^3^3) s) y r2`;
                     `v2:real`] MFD_HAS_VOLUME_POS_LE)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real`; `v2:real`; `&3`] LIM_SMALL_D) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`e:real`; `v1:real`; `&2`] LIM_SMALL_D) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `dd = min d1 d2` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= &1 / &2 /\ &3 * dd * v2 <= e /\ &2 * dd * v1 <= e`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `d1:real`)) (concl th) &&
        is_forall(concl th))) THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `d2:real`)) (concl th) &&
        is_forall(concl th))) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `rm = (r1 + r2) / &2` THEN
  SUBGOAL_THEN `r1 < rm /\ rm < r2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rm" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Kc = mfd_cball (top,atlas) ((g:real->B->real^3^3) s) y (r2 + &2)` THEN
  SUBGOAL_THEN `compact_in top (Kc:B->bool) /\
                compact_in top (mfd_cball (top,atlas) ((g:real->B->real^3^3) s) y (r2 + &1)) /\
                mfd_cball (top,atlas) ((g:real->B->real^3^3) s) y (r2 + &1) SUBSET Kc`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Kc" THEN
      UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) s)` THEN
      REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) s)` THEN
      REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "Kc" THEN REWRITE_TAC[mfd_cball; SUBSET; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `s:real`; `y:B`; `r1:real`; `rm:real`]
                LIM_BALL_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ka:num` (LABEL_TAC "ba")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `s:real`; `y:B`; `r2:real`; `r2 + &1`]
                LIM_BALL_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kb:num` (LABEL_TAC "bb")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `s:real`; `y:B`; `r1:real`; `r2:real`]
                LIM_BALL_OUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kc:num` (LABEL_TAC "bo")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `s:real`; `s:real`; `Kc:B->bool`;
                 `dd:real`] LIM_QF_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET] THEN
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s' = s:real` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kd:num` (LABEL_TAC "qf0")) THEN
  EXISTS_TAC `ka + kb + kc + kd:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "qf0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `s:real`)) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi:A->B`) ASSUME_TAC))) THEN
  MATCH_MP_TAC LIM_VOL_STEP THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                        `(g:real->B->real^3^3) s`; `(W:num->B->bool) k`;
                        `IMAGE ((phi:num->B->A) k) (W k)`; `psi:A->B`; `Kc:B->bool`;
                        `r1:real`; `r2:real`; `rm:real`; `dd:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN USE_THEN "ba" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN USE_THEN "bb" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    USE_THEN "bo" (MP_TAC o SPECL [`k:num`; `z:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* Curvature bounds in the views, persistence and kappa-noncollapsing in the *)
(* limit (L4).                                                               *)
(* ========================================================================= *)

let LIM_NONCOLLINEAR_BASIS = prove
 (`~collinear {vec 0:real^3,basis 1,basis 2}`,
  REWRITE_TAC[COLLINEAR_LEMMA] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[NOT_EXISTS_THM; CART_EQ; FORALL_3; DIMINDEX_3] THEN
  SIMP_TAC[BASIS_COMPONENT; VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH] THEN
  REAL_ARITH_TAC);;

let LIM_RM_NORM_LE = prove
 (`!atlas (g:A->real^3^3) x B.
     (!u v. ~collinear {vec 0,u,v} ==> abs(mfd_sectional atlas g x u v) <= B)
     ==> mfd_rm_norm atlas g x <= B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_rm_norm] THEN MATCH_MP_TAC REAL_SUP_LE THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `abs(mfd_sectional atlas (g:A->real^3^3) x (basis 1) (basis 2))` THEN
    MAP_EVERY EXISTS_TAC [`basis 1:real^3`; `basis 2:real^3`] THEN
    REWRITE_TAC[LIM_NONCOLLINEAR_BASIS];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]);;
(* The reverse direction of LIM_POINT_CURV for sectional curvatures: every *)
(* plane at psi y is close to a plane at y.                                  *)

let LIM_POINT_SEC_REV = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi' Q K0 alpha eta y.
     (!s (G0:real^3->real^3^3) G y.
         metric_field s G0 /\ metric_field s G /\ y IN s /\
         lrm_deriv_norm2 0 G0 y <= K0 pow 2 /\ lck_dist2 2 G0 G y < eta pow 2
         ==> abs(lscalar G y - lscalar G0 y) <= alpha /\
             (!w. abs(lricci G y w w - lricci G0 y w w) <= alpha * (w dot (G0 y ** w))) /\
             (!u v. ~collinear {vec 0,u,v}
                    ==> abs(lsectional G y u v - lsectional G0 y u v) <= alpha)) /\
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\ y IN U /\ &0 < Q /\
     rfa_rmd2 0 atlas g y <= K0 pow 2 /\
     lck_dist2 2 (metric_local atlas (chart_at atlas y) g)
                 (metric_local atlas (chart_at atlas y)
                    (\z. Q %% mfd_pullback_metric atlas atlas' psi g' z))
                 (SND(chart_at atlas y) y) < eta pow 2
     ==> (!u' v'. ~collinear {vec 0,u',v'}
                  ==> ?u v. ~collinear {vec 0,u,v} /\
                            abs(mfd_sectional atlas' g' (psi y) u' v' / Q -
                                mfd_sectional atlas g y u v) <= alpha)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "D") STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `g':B->real^3^3`; `y:A`] P2B9S_PB_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `P:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `g':B->real^3^3`; `y:A`] P2B9S_PB_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `g':B->real^3^3`; `y:A`] P2B9S_PB_SECTIONAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sec" o CONJUNCT2) THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)` THEN
  ABBREV_TAC `p = SND (c:(A->bool)#(A->real^3)) y` THEN
  ABBREV_TAC `Lg = metric_local (atlas:((A->bool)#(A->real^3))->bool) c (g:A->real^3^3)` THEN
  ABBREV_TAC `Lp = metric_local (atlas:((A->bool)#(A->real^3))->bool) c
                     (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3))` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))
                             (Lg:real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "Lg" THEN
    UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s0 = P INTER IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
  SUBGOAL_THEN `(p:real^3) IN s0 /\ metric_field s0 (Lg:real^3->real^3^3) /\
                metric_field s0 (\z. Q %% (Lp:real^3->real^3^3) z) /\
                metric_field s0 (Lp:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))` ASSUME_TAC THENL
     [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    SUBGOAL_THEN `open (s0:real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "s0" THEN MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `metric_field s0 (Lp:real^3->real^3^3)` ASSUME_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `P:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "s0" THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LRG_METRIC_FIELD_SCALE] THEN CONJ_TAC THENL
     [EXPAND_TAC "s0" THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        EXPAND_TAC "p" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "s0" THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "D" (MP_TAC o SPECL [`s0:real^3->bool`; `Lg:real^3->real^3^3`;
                                  `\z. Q %% (Lp:real^3->real^3^3) z`; `p:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfa_rmd2")) (concl th))) THEN
      REWRITE_TAC[rfa_rmd2] THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> not(is_forall(concl th)) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
      REWRITE_TAC[METRIC_LOCAL_CMUL; ETA_AX] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "stab"))) THEN
  MP_TAC(ISPECL [`s0:real^3->bool`; `Lp:real^3->real^3^3`; `Q:real`; `p:real^3`]
                P2C_SCALE_QUANTITIES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) y = lscalar (Lg:real^3->real^3^3) (p:real^3) /\
                mfd_scalar atlas (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3)) y =
                lscalar (Lp:real^3->real^3^3) p`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mfd_scalar] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u':real^3`; `v':real^3`] THEN DISCH_TAC THEN
  USE_THEN "sec" (MP_TAC o C MATCH_MP (ASSUME `~collinear {vec 0,u':real^3,v'}`) o
                  SPECL [`u':real^3`; `v':real^3`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    can (find_term ((=) `u':real^3`)) (concl th) && is_eq(concl th))) THEN
  USE_THEN "stab" (MP_TAC o C MATCH_MP (ASSUME `~collinear {vec 0,u:real^3,v}`) o
                   SPECL [`u:real^3`; `v:real^3`]) THEN
  MP_TAC(ISPECL [`s0:real^3->bool`; `Lp:real^3->real^3^3`; `Q:real`; `p:real^3`;
                 `u:real^3`; `v:real^3`] APX_LSECTIONAL_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[]);;
(* A uniform bound on |Rm| of the views over a compact set and a closed time *)
(* interval, from a bound on the sectional curvatures of the limit.          *)

let LIM_VIEW_RM_BOUND = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi a b K B alpha.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     real_interval[a,b] SUBSET J /\
     (!s. a <= s /\ s <= b ==> riemannian_metric atlas (g s)) /\
     compact_in top K /\ &0 <= B /\ &0 < alpha /\
     (!s z u v. a <= s /\ s <= b /\ z IN K /\ ~collinear {vec 0,u,v}
                ==> abs(mfd_sectional atlas (g s) z u v) <= B)
     ==> ?k0. !k s z. k0 <= k /\ a <= s /\ s <= b /\ z IN K
                      ==> mfd_rm_norm (rfs_vatlas (V k) (t k + s / Q k))
                                      (rfs_vmetric (V k) (t k + s / Q k)) (phi k z)
                          <= Q k * (B + alpha)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] RFA_LRM_SECTIONAL_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rfa"))) THEN
  ABBREV_TAC `K0 = sqrt C * B + &1` THEN
  SUBGOAL_THEN `C * B pow 2 <= K0 pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN
    SUBGOAL_THEN `C * B pow 2 = (sqrt C * B) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K0:real`; `alpha:real`] (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `b:real`; `K:B->bool`; `2`; `eta pow 2 / &8`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN MAP_EVERY X_GEN_TAC [`k:num`; `s:real`; `z:B`] THEN STRIP_TAC THEN
  USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (MP_TAC o SPEC `s:real`)
    (MP_TAC o SPECL [`s:real`; `z:B`]))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  ABBREV_TAC `VT = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VA = rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VG = rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  SUBGOAL_THEN `(z:B) IN W(k:num) /\ z IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:num->B->A) k z IN topspace (VT:A topology)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                   ((W:num->B->bool) k) (VT:A topology) (VA:((A->bool)#(A->real^3))->bool)
                   (IMAGE ((phi:num->B->A) k) (W k)) (phi k) (psi:A->B)` THEN
    REWRITE_TAC[mfd_diffeo] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (VT:A topology) VA /\ riemannian_metric VA (VG:A->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["VT"; "VA"; "VG"] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "riemannian_metric"))
          (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_vtop")) (concl th))) THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfa_rmd2 0 atlas ((g:real->B->real^3^3) s) z <= K0 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * B pow 2` THEN ASM_REWRITE_TAC[rfa_rmd2] THEN
    USE_THEN "rfa" MATCH_MP_TAC THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (z:B)))
                      (FST(chart_at atlas z))` THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `z:B`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM mfd_sectional] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `VT:A topology`;
                 `VA:((A->bool)#(A->real^3))->bool`; `VG:A->real^3^3`; `(W:num->B->bool) k`;
                 `IMAGE ((phi:num->B->A) k) (W k)`; `(phi:num->B->A) k`; `psi:A->B`;
                 `(Q:num->real) k`; `K0:real`; `alpha:real`; `eta:real`; `z:B`]
                LIM_POINT_SEC_REV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(&1 + inv(&1)) pow 2 *
                lck_dist2 2 (metric_local atlas (chart_at atlas (z:B)) ((g:real->B->real^3^3) s))
                  (\w. (Q:num->real) k %%
                       rfs_pullback (VA:((A->bool)#(A->real^3))->bool)
                         ((phi:num->B->A) k o chart_inv (chart_at atlas z)) (VG:A->real^3^3) w)
                  (SND(chart_at atlas z) z)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `VT:A topology`; `VA:((A->bool)#(A->real^3))->bool`;
                     `(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`;
                     `(phi:num->B->A) k`; `psi:A->B`; `(g:real->B->real^3^3) s`;
                     `VG:A->real^3^3`; `&1`; `(Q:num->real) k`; `2`; `z:B`]
                    P2BL_LCK_CHART_CONVERT) THEN
      ASM_REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; MATRIX_CMUL_LID; ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 + inv(&1)) pow 2 = &4` SUBST1_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x < e / &8 /\ &0 < e ==> &4 * x < e`) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(ACCEPT_TAC o check (fun th -> not(is_forall(concl th)) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th)));
      ASM_SIMP_TAC[REAL_POW_LT]];
    DISCH_TAC] THEN
  MATCH_MP_TAC LIM_RM_NORM_LE THEN
  MAP_EVERY X_GEN_TAC [`u':real^3`; `v':real^3`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `~collinear {vec 0,u':real^3,v'}`) o
    SPECL [`u':real^3`; `v':real^3`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `abs(mfd_sectional atlas ((g:real->B->real^3^3) s) z u v) <= B` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `B:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_sectional")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `sk = mfd_sectional (VA:((A->bool)#(A->real^3))->bool) (VG:A->real^3^3)
                                 ((phi:num->B->A) k z) u' v'` THEN
  SUBGOAL_THEN `&0 < (Q:num->real) k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(sk / (Q:num->real) k) <= B + alpha` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < q ==> abs q = q`; REAL_LE_LDIV_EQ] THEN
  REAL_ARITH_TAC);;
(* A set open in one target slice and inside the image of a map that is a  *)
(* diffeomorphism onto two target slices is open in the other slice.        *)

let LIM_DIFFEO_OPEN_TRANSFER = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) U (top1:B topology)
    (atlas1:((B->bool)#(B->real^M))->bool) U1 (top2:B topology)
    (atlas2:((B->bool)#(B->real^M))->bool) U2 f g1 g2 S.
     mfd_diffeo top atlas U top1 atlas1 U1 f g1 /\
     mfd_diffeo top atlas U top2 atlas2 U2 f g2 /\
     hausdorff_space top2 /\ open_in top1 S /\ S SUBSET U1
     ==> open_in top2 S`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top1:B topology`;
                 `atlas1:((B->bool)#(B->real^M))->bool`; `U:A->bool`; `U1:B->bool`;
                 `f:A->B`; `g1:B->A`; `S:B->bool`] LIM_DIFFEO_PREIMAGE_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS o check (fun th ->
    can (find_term ((=) `U1:B->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `top2:B topology`;
                 `atlas2:((B->bool)#(B->real^M))->bool`; `U:A->bool`; `U2:B->bool`;
                 `f:A->B`; `g2:B->A`; `{}:A->bool`; `{z | z IN U /\ (f:A->B) z IN S}`]
                LIM_DIFFEO_IMAGE_FACTS) THEN
  ASM_REWRITE_TAC[COMPACT_IN_EMPTY; EMPTY_SUBSET] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `w:B` THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:B) IN IMAGE (f:A->B) U` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:A` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
(* Unfolding noncollapsing for a general view V.                             *)

let LIM_KNC_VIEW = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    kappa r0.
     rfs_kappa_noncollapsed V kappa r0 <=>
     !t x r. x IN topspace(rfs_vtop V t) /\ &0 < r /\ r <= r0 /\
             (!s. t - r pow 2 < s /\ s <= t
                  ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
                      open_in (rfs_vtop V s)
                        (mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x r)) /\
             (!s y. t - r pow 2 < s /\ s <= t /\
                    y IN mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x r
                    ==> mfd_rm_norm (rfs_vatlas V s) (rfs_vmetric V s) y <= inv(r pow 2))
             ==> ?v. mfd_has_volume (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t)
                       (mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x r) v /\
                     kappa * r pow 3 <= v`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[P2BL_VIEW_TRIPLE] THEN
  REWRITE_TAC[rfs_kappa_noncollapsed; rfs_parabolic_exists; rfs_persists; rfs_vball;
              rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  REWRITE_TAC[REAL_ARITH `t - r pow 2 < s <=> t - r pow 2 < s`]);;
(* Change of time variable for rescaled views.                              *)

let LIM_TIME_CHANGE = prove
 (`!q t0 a b sg. &0 < q /\ t0 + a / q < sg /\ sg <= t0 + b / q
                 ==> ?s. a < s /\ s <= b /\ sg = t0 + s / q`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `(sg - t0) * q` THEN
  SUBGOAL_THEN `a / q < sg - t0 /\ sg - t0 <= b / q` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `a / q < sg - t0` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ];
    UNDISCH_TAC `sg - t0 <= b / q` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
    UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD]);;

(* The rescaled radius: (r inv(sqrt q))^2 = r^2 / q and q sqrt q (r inv(sqrt q))^3 = r^3. *)

let LIM_RHO_FACTS = prove
 (`!q r. &0 < q
         ==> (r * inv(sqrt q)) pow 2 = r pow 2 / q /\
             q * sqrt q * (r * inv(sqrt q)) pow 3 = r pow 3 /\
             inv((r * inv(sqrt q)) pow 2) = q * inv(r pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt q /\ sqrt q pow 2 = q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN ASM_REWRITE_TAC[real_div];
    UNDISCH_TAC `sqrt q pow 2 = q` THEN UNDISCH_TAC `&0 < sqrt q` THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV; REAL_INV_MUL; REAL_INV_INV] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;
(* L4 core: for r' < r and d in (0,1/2], kappa r'^3 <= (1 + 3 d) times the  *)
(* volume of the limit ball B_tt(xx,r).                                      *)

let LIM_KNC_APPROX = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi kappa r0 tt xx r r' d.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     (!k tau. hausdorff_space (rfs_vtop (V k) tau)) /\
     (!s. s IN J ==> riemannian_metric atlas (g s) /\ mfd_complete (top,atlas) (g s)) /\
     (!k. rfs_kappa_noncollapsed (V k) kappa (r0 * inv(sqrt(Q k)))) /\
     tt IN J /\ xx IN topspace top /\ &0 <= kappa /\ &0 < r' /\ r' < r /\ r <= r0 /\
     &0 < d /\ d <= &1 / &2 /\
     (!s. tt - r pow 2 < s /\ s <= tt ==> s IN J) /\
     (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN mfd_ball (top,atlas) (g tt) xx r
            ==> mfd_rm_norm atlas (g s) y <= inv(r pow 2))
     ==> kappa * r' pow 3 <=
         (&1 + &3 * d) * mfd_volume (top,atlas) (g tt) (mfd_ball (top,atlas) (g tt) xx r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) tt) /\
                mfd_complete (top,atlas) ((g:real->B->real^3^3) tt)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `r'' = (r' + r) / &2` THEN
  SUBGOAL_THEN `r' < r'' /\ r'' < r /\ &0 < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r''" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r' pow 2 < r pow 2 /\ &0 < r' pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ARITH_TAC;
      ASM_SIMP_TAC[REAL_POW_LT]];
    ALL_TAC] THEN
  ABBREV_TAC `alpha = inv(r' pow 2) - inv(r pow 2)` THEN
  SUBGOAL_THEN `&0 < alpha` ASSUME_TAC THENL
   [EXPAND_TAC "alpha" THEN REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_interval[tt - r' pow 2,tt] SUBSET J` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Kb = mfd_cball (top,atlas) ((g:real->B->real^3^3) tt) xx r''` THEN
  ABBREV_TAC `Kq = mfd_cball (top,atlas) ((g:real->B->real^3^3) tt) xx (r + &1)` THEN
  SUBGOAL_THEN `compact_in top (Kb:B->bool) /\ compact_in top (Kq:B->bool) /\ Kb SUBSET Kq /\
                Kb SUBSET mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r /\
                mfd_ball (top,atlas) (g tt) xx r SUBSET Kq`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Kb"; "Kq"] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) tt)` THEN
      REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) tt)` THEN
      REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[mfd_cball; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the view curvature bound on [tt - r'^2, tt] over Kb *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `tt - r' pow 2`; `tt:real`; `Kb:B->bool`;
                 `inv(r pow 2)`; `alpha:real`] LIM_VIEW_RM_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(s:real) IN J` (fun th -> ASM_SIMP_TAC[th]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tt - r pow 2`)) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm"))
                            (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `z:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_rm_norm atlas ((g:real->B->real^3^3) s) z` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(s:real) IN J` (fun th -> ASM_SIMP_TAC[th]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) (concl th) &&
        can (find_term ((=) `inv(r pow 2)`)) (concl th))) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `kb:num` (LABEL_TAC "rmb"))] THEN
  (* the view ball inside the image of B(xx,r'') *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `tt:real`; `xx:B`; `r':real`; `r'':real`]
                LIM_BALL_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ka:num` (LABEL_TAC "bin")) THEN
  (* closeness on Kq at time tt *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `tt:real`; `tt:real`; `Kq:B->bool`;
                 `d:real`] LIM_QF_CLOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET] THEN
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s' = tt:real` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kc:num` (LABEL_TAC "qf0")) THEN
  (* the diffeomorphisms at all times of [tt - r'^2, tt] *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`tt - r' pow 2`; `tt:real`; `Kq:B->bool`; `0`; `&1`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kd:num` (LABEL_TAC "dif")) THEN
  ABBREV_TAC `k = ka + kb + kc + kd:num` THEN
  USE_THEN "qf0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
   [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `tt:real`)) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi0:A->B`) (LABEL_TAC "qfk")))) THEN
  USE_THEN "dif" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
   [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "difk") (K ALL_TAC))) THEN
  SUBGOAL_THEN `&0 < (Q:num->real) k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`(Q:num->real) k`; `r':real`] LIM_RHO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `rho = r' * inv(sqrt((Q:num->real) k))` THEN
  SUBGOAL_THEN `&0 < rho /\ rho <= r0 * inv(sqrt((Q:num->real) k))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN
    SUBGOAL_THEN `&0 < inv(sqrt((Q:num->real) k))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `VT0 = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + tt / Q k)` THEN
  ABBREV_TAC `VA0 = rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + tt / Q k)` THEN
  ABBREV_TAC `VG0 = rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + tt / Q k)` THEN
  ABBREV_TAC `Bk = mfd_ball (VT0:A topology,VA0:((A->bool)#(A->real^3))->bool)
                            (VG0:A->real^3^3) ((phi:num->B->A) k xx) rho` THEN
  SUBGOAL_THEN `!z:A. z IN Bk
                      ==> z IN IMAGE ((phi:num->B->A) k)
                                (mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r'' INTER
                                 W k)` (LABEL_TAC "bink") THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN USE_THEN "bin" MATCH_MP_TAC THEN
    CONJ_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["VT0"; "VA0"; "VG0"; "Bk"; "rho"] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Bk:A->bool) SUBSET IMAGE ((phi:num->B->A) k) (W k) /\
                (phi:num->B->A) k xx IN topspace (VT0:A topology) /\
                hausdorff_space (VT0:A topology)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      USE_THEN "bink" (MP_TAC o C MATCH_MP (ASSUME `(z:A) IN Bk`)) THEN SET_TAC[];
      UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                     ((W:num->B->bool) k) (VT0:A topology) (VA0:((A->bool)#(A->real^3))->bool)
                     (IMAGE ((phi:num->B->A) k) (W k)) (phi k) (psi0:A->B)` THEN
      REWRITE_TAC[mfd_diffeo] THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
      SUBGOAL_THEN `(xx:B) IN W(k:num)` MP_TAC THENL
       [SUBGOAL_THEN `(xx:B) IN Kq` MP_TAC THENL
         [EXPAND_TAC "Kq" THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
          ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN ASM_REAL_ARITH_TAC;
          ASM SET_TAC[]];
        SET_TAC[]];
      EXPAND_TAC "VT0" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (VT0:A topology) Bk` ASSUME_TAC THENL
   [EXPAND_TAC "Bk" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* times in (t' - rho^2, t'] are t k + s / Q k with s in (tt - r'^2, tt] *)
  SUBGOAL_THEN
   `!sg. (t k + tt / Q k) - rho pow 2 < sg /\ sg <= t k + tt / Q k
         ==> ?s. tt - r' pow 2 < s /\ s <= tt /\ sg = t k + s / (Q:num->real) k`
  (LABEL_TAC "tch") THENL
   [X_GEN_TAC `sg:real` THEN STRIP_TAC THEN MATCH_MP_TAC LIM_TIME_CHANGE THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `t k + (tt - r' pow 2) / (Q:num->real) k = (t k + tt / Q k) - rho pow 2`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < (Q:num->real) k` THEN CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* noncollapsing of V k at (t k + tt / Q k, phi k xx, rho) *)
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_kappa_noncollapsed"))
        (concl th))) THEN
  REWRITE_TAC[LIM_KNC_VIEW] THEN
  DISCH_THEN(MP_TAC o SPECL [`t k + tt / (Q:num->real) k`; `(phi:num->B->A) k xx`; `rho:real`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `sg:real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "tch" (MP_TAC o C MATCH_MP (ASSUME
        `(t k + tt / (Q:num->real) k) - rho pow 2 < sg /\ sg <= t k + tt / Q k`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "difk" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `psis:A->B`) THEN
      SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                      (t k + s / Q k)) (rfs_vatlas (V k) (t k + s / Q k))`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `t k + s / (Q:num->real) k`] o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "riemannian_metric"))
              (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_vtop")) (concl th))) THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(phi:num->B->A) k xx` THEN
        UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                       ((W:num->B->bool) k)
                       (rfs_vtop ((V:num->(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                         (t k + s / Q k))
                       (rfs_vatlas (V k) (t k + s / Q k))
                       (IMAGE ((phi:num->B->A) k) (W k)) (phi k) (psis:A->B)` THEN
        REWRITE_TAC[mfd_diffeo] THEN
        DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
        SUBGOAL_THEN `(phi:num->B->A) k xx IN IMAGE (phi k) (W k)` MP_TAC THENL
         [UNDISCH_TAC `(phi:num->B->A) k xx IN topspace (VT0:A topology)` THEN
          UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                         ((W:num->B->bool) k) (VT0:A topology)
                         (VA0:((A->bool)#(A->real^3))->bool)
                         (IMAGE ((phi:num->B->A) k) (W k)) (phi k) (psi0:A->B)` THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(K ALL_TAC) THEN
          MATCH_MP_TAC FUN_IN_IMAGE THEN
          SUBGOAL_THEN `(xx:B) IN Kq` MP_TAC THENL
           [EXPAND_TAC "Kq" THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
            ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN ASM_REAL_ARITH_TAC;
            ASM SET_TAC[]];
          SET_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(W:num->B->bool) k`; `VT0:A topology`;
                     `VA0:((A->bool)#(A->real^3))->bool`;
                     `IMAGE ((phi:num->B->A) k) (W k)`;
                     `rfs_vtop ((V:num->(real->A topology)#
                       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                       (t k + s / Q k)`;
                     `rfs_vatlas ((V:num->(real->A topology)#
                       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                       (t k + s / Q k)`;
                     `IMAGE ((phi:num->B->A) k) (W k)`; `(phi:num->B->A) k`;
                     `psi0:A->B`; `psis:A->B`; `Bk:A->bool`] LIM_DIFFEO_OPEN_TRANSFER) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`sg:real`; `y':A`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y':A) IN Bk` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["Bk"; "VT0"; "VA0"; "VG0"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "tch" (MP_TAC o C MATCH_MP (CONJ (ASSUME
      `(t k + tt / (Q:num->real) k) - rho pow 2 < sg`) (ASSUME `sg <= t k + tt / (Q:num->real) k`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "bink" (MP_TAC o C MATCH_MP (ASSUME `(y':A) IN Bk`)) THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Q:num->real) k * (inv(r pow 2) + alpha)` THEN CONJ_TAC THENL
     [USE_THEN "rmb" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "k" THEN ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        EXPAND_TAC "Kb" THEN
        UNDISCH_TAC `(z:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r''` THEN
        REWRITE_TAC[mfd_ball; mfd_cball; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "alpha" THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `vk:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `P = mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r INTER
                  {z | z IN W(k:num) /\ (phi:num->B->A) k z IN Bk}` THEN
  SUBGOAL_THEN `open_in top (P:B->bool) /\ P SUBSET W(k:num) /\ P SUBSET Kq /\
                P SUBSET mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r /\
                IMAGE ((phi:num->B->A) k) P = Bk`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "P" THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[MFD_BALL_OPEN] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `VT0:A topology`; `VA0:((A->bool)#(A->real^3))->bool`;
                     `(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`;
                     `(phi:num->B->A) k`; `psi0:A->B`; `Bk:A->bool`]
                    LIM_DIFFEO_PREIMAGE_OPEN) THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "P" THEN SET_TAC[];
      EXPAND_TAC "P" THEN ASM SET_TAC[];
      EXPAND_TAC "P" THEN SET_TAC[];
      EXPAND_TAC "P" THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `w:A` THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
      USE_THEN "bink" (MP_TAC o C MATCH_MP (ASSUME `(w:A) IN Bk`)) THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC) THEN EXISTS_TAC `z:B` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(z:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r''` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(w:A) IN Bk` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) tt`; `P:B->bool`; `Kq:B->bool`] LIM_OPEN_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) tt`;
                 `mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r`; `Kq:B->bool`]
                LIM_OPEN_VOLUME) THEN
  ASM_SIMP_TAC[MFD_BALL_OPEN] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) tt`; `VT0:A topology`;
                 `VA0:((A->bool)#(A->real^3))->bool`; `VG0:A->real^3^3`; `(W:num->B->bool) k`;
                 `IMAGE ((phi:num->B->A) k) (W k)`; `(phi:num->B->A) k`; `psi0:A->B`;
                 `P:B->bool`; `mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) P`;
                 `vk:real`; `(Q:num->real) k`; `d:real`] LIM_VOL_IMAGE_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    MAP_EVERY X_GEN_TAC [`z:B`; `w:real^3`] THEN DISCH_TAC THEN
    USE_THEN "qfk" (MP_TAC o SPECL [`z:B`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) tt`; `P:B->bool`;
                 `mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r`;
                 `mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) P`;
                 `mfd_volume (top,atlas) ((g:real->B->real^3^3) tt)
                    (mfd_ball (top,atlas) (g tt) xx r)`] MFD_HAS_VOLUME_MONO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (Q:num->real) k * sqrt(Q k)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `kappa * r' pow 3 <= (Q:num->real) k * sqrt(Q k) * vk` ASSUME_TAC THENL
   [UNDISCH_TAC `(Q:num->real) k * sqrt(Q k) * rho pow 3 = r' pow 3` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(kappa * ((Q:num->real) k * sqrt(Q k) * rho pow 3) =
                   (Q k * sqrt(Q k)) * (kappa * rho pow 3)) /\
                  ((Q:num->real) k * sqrt(Q k) * vk = (Q k * sqrt(Q k)) * vk)`
    (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + &3 * d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + &3 * d) * mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) P` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;
(* Elementary bounds used in the limit r' -> r.                             *)

let LIM_POW3 = prove
 (`!x. x pow 3 = x * x * x`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `3 = 2 + 1`; REAL_POW_ADD; REAL_POW_2; REAL_POW_1] THEN
  REAL_ARITH_TAC);;

let LIM_CUBE_LOWER = prove
 (`!h. &0 <= h /\ h <= &1 ==> &1 - &3 * h / &4 <= (&1 - h / &4) pow 3`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_POW3] THEN
  SUBGOAL_THEN `&0 <= (h / &4 * h / &4) * (&3 - h / &4)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;
(* L4: kappa-noncollapsing passes to the limit.                             *)

let LIM_KNC = prove
 (`!u:A->bool w:B->bool. LIM_KNC_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_KNC_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `kappa:real`; `r0:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  REWRITE_TAC[rfs_flow_view; rfs_kappa_noncollapsed; rfs_parabolic_exists; rfs_persists;
              rfs_vball] THEN
  MAP_EVERY X_GEN_TAC [`tt:real`; `xx:B`; `r:real`] THEN
  ASM_CASES_TAC `(tt:real) IN J` THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) tt) /\
                mfd_complete (top,atlas) ((g:real->B->real^3^3) tt)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(xx:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. tt - r pow 2 < s /\ s <= tt ==> s IN J` (LABEL_TAC "inJ") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Bl = mfd_ball (top,atlas) ((g:real->B->real^3^3) tt) xx r` THEN
  SUBGOAL_THEN `mfd_has_volume (top,atlas) ((g:real->B->real^3^3) tt) Bl
                  (mfd_volume (top,atlas) (g tt) Bl)` ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_OPEN_VOLUME THEN
    EXISTS_TAC `mfd_cball (top,atlas) ((g:real->B->real^3^3) tt) xx (r + &1)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Bl" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) tt)` THEN
      REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "Bl" THEN REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[REAL_ARITH `x < r ==> x <= r + &1`]];
    ALL_TAC] THEN
  EXISTS_TAC `mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) Bl` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) Bl` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) tt`; `Bl:B->bool`;
                   `mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) Bl`]
                  MFD_HAS_VOLUME_POS_LE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r pow 3` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_CASES_TAC `kappa <= &0` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `k * p <= &0 <=> &0 <= --k * p`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_LE_LIMIT THEN
  EXISTS_TAC `mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) Bl / &2 + kappa * r pow 3` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `kappa:real`; `r0:real`; `tt:real`; `xx:B`;
                 `r:real`; `r * (&1 - h / &4)`; `h / &6`] LIM_KNC_APPROX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < r /\ &0 < r * h / &4 ==> r * (&1 - h / &4) < r`) THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `h:real` LIM_CUBE_LOWER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `kappa * r pow 3 * (&1 - &3 * h / &4) <=
                kappa * (r * (&1 - h / &4)) pow 3` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `k * p * c = (k * p) * c:real`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= kappa * r pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + &3 * h / &6) * mfd_volume (top,atlas) ((g:real->B->real^3^3) tt) Bl =
                mfd_volume (top,atlas) (g tt) Bl +
                (mfd_volume (top,atlas) (g tt) Bl / &2) * h` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `kappa * r pow 3 * (&1 - &3 * h / &4) =
                kappa * r pow 3 - (&3 / &4) * (kappa * r pow 3) * h` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &4) * (kappa * r pow 3) * h <= (kappa * r pow 3) * h` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `(&3 / &4) * a * h = (&3 / &4) * (a * h)`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> (&3 / &4) * x <= x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

