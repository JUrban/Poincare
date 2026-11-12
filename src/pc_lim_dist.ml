(* ========================================================================= *)
(* L1 and L2 of the limit-geometry layer (statements of pc_lim_stmts).       *)
(*   LIM_DIST |- !u w. LIM_DIST_STATEMENT u w: rescaled distances converge  *)
(*     uniformly on compact sets.                                           *)
(*   LIM_BALL |- !u w. LIM_BALL_STATEMENT u w: bounded rescaled balls about *)
(*     x k lie in images of a compact set.                                  *)
(* The comparison of distances under a diffeomorphism close to an isometry  *)
(* on a large ball is LIM_DIST_COMPARE.                                      *)
(* ========================================================================= *)

needs "src/pc_lim_stmts.ml";;
needs "src/pc_lim_close.ml";;

prioritize_real();;
type_invention_error := true;;
(* Distances from a fixed point are bounded on a compact set.              *)

let LIM_COMPACT_DIST_BOUND = prove
 (`!top atlas (g:A->real^N^N) x0 K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x0 IN topspace top /\ compact_in top K
     ==> ?D. &0 < D /\ !y. y IN K ==> mfd_dist (top,atlas) g x0 y < D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (top,euclideanreal) (\y:A. mfd_dist (top,atlas) (g:A->real^N^N) x0 y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`]
                  MFD_DIST_CONTINUOUS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\y:A. mfd_dist (top,atlas) (g:A->real^N^N) x0 y) =
                  (\(x,y). mfd_dist (top,atlas) g x y) o (\y. x0,y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `prod_topology top (top:A topology)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_ID] THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_bounded (IMAGE (\y:A. mfd_dist (top,atlas) (g:A->real^N^N) x0 y) K)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN REWRITE_TAC[real_compact_def] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `abs B + &1` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Elementary real facts for the comparison of distances.                  *)

let LIM_SQRT_BOUNDS = prove
 (`!d. &0 <= d /\ d <= &1 ==> &1 - d <= sqrt(&1 - d) /\ sqrt(&1 + d) <= &1 + d`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= d * (&1 - d) ==> (&1 - d) pow 2 <= &1 - d`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= d * (&1 + d) ==> &1 + d <= (&1 + d) pow 2`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

let LIM_LE_LIMIT = prove
 (`!a b m. &0 <= m /\ (!h. &0 < h /\ h <= &1 ==> a <= b + m * h) ==> a <= b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `~(b < a) ==> a <= b`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (&1) ((a - b) / (&2 * (m + &1)))`) THEN
  SUBGOAL_THEN `&0 < (a - b) / (&2 * (m + &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m * min (&1) ((a - b) / (&2 * (m + &1))) <= m * (a - b) / (&2 * (m + &1))`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(a - b) / &2 - m * (a - b) / (&2 * (m + &1)) = (a - b) / (&2 * (m + &1))`
  MP_TAC THENL
   [SUBGOAL_THEN `~(m + &1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ASM_REAL_ARITH_TAC]);;
(* Distances under a diffeomorphism that is close to an isometry after the  *)
(* scaling by c, on a large ball B(x0, 10 (D0 + 1) + 1) of a complete       *)
(* manifold: for y, z in B(x0,D0), |sqrt c d'(psi y,psi z) - d(y,z)| <=     *)
(* dd d(y,z).                                                                *)

let LIM_DIST_COMPARE = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi' x0 D0 c dd y z.
     hausdorff_space top /\ hausdorff_space top' /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
     mfd_complete (top,atlas) g /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     x0 IN topspace top /\ &0 < D0 /\
     mfd_ball (top,atlas) g x0 (&10 * (D0 + &1) + &1) SUBSET U /\
     &0 < c /\ &0 <= dd /\ dd <= &1 / &2 /\
     (!w v. w IN U
            ==> abs(c * (v dot (mfd_pullback_metric atlas atlas' psi g' w ** v)) -
                    v dot (g w ** v)) <= dd * (v dot (g w ** v))) /\
     y IN mfd_ball (top,atlas) g x0 D0 /\ z IN mfd_ball (top,atlas) g x0 D0
     ==> mfd_joinable (top',atlas') (psi y) (psi z) /\
         abs(sqrt c * mfd_dist (top',atlas') g' (psi y) (psi z) -
             mfd_dist (top,atlas) g y z) <= dd * mfd_dist (top,atlas) g y z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = &10 * (D0 + &1)` THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) (g:A->real^3^3) y z` THEN
  UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) (g:A->real^3^3) x0 D0` THEN
  UNDISCH_TAC `(z:A) IN mfd_ball (top,atlas) (g:A->real^3^3) x0 D0` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) y z` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d /\ d < &2 * D0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`; `x0:A`; `z:A`] MFD_DIST_TRIANGLE) THEN
    ASM_SIMP_TAC[MFD_JOINABLE_SYM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x0:A`; `y:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `(y:A) IN U /\ (z:A) IN U` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `U:A->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_ball")) (concl th))) THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w v. w IN U
                      ==> c * (v dot (mfd_pullback_metric atlas atlas' (psi:A->B)
                                        (g':B->real^3^3) w ** v)) <=
                          (&1 + dd) * (v dot ((g:A->real^3^3) w ** v)) /\
                          (&1 - dd) * (v dot (g w ** v)) <=
                          c * (v dot (mfd_pullback_metric atlas atlas' psi g' w ** v))`
  (LABEL_TAC "qf2") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w:A`; `v:real^3`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `dd:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `dd:real` LIM_SQRT_BOUNDS) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt c /\ &0 < sqrt(&1 + dd) /\ &0 < sqrt(&1 - dd)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the upper bound *)
  SUBGOAL_THEN
   `!h. &0 < h /\ h <= &1
        ==> (psi:A->B) z IN mfd_ball (top',atlas') (g':B->real^3^3) (psi y)
                              (sqrt((&1 + dd) / c) * (d + h))`
  (LABEL_TAC "up") THENL
   [X_GEN_TAC `h:real` THEN STRIP_TAC THEN MATCH_MP_TAC LIM_PB_BALL_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `U:A->bool`; `U':B->bool`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `w:A` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `U:A->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_ball")) (concl th))) THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x0 w` ASSUME_TAC THENL
       [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ASM_REWRITE_TAC[]] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `x0:A`; `y:A`; `w:A`] MFD_DIST_TRIANGLE) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[];
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top',atlas':((B->bool)#(B->real^3))->bool) ((psi:A->B) y) (psi z)`
  ASSUME_TAC THENL
   [USE_THEN "up" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; REAL_LE_REFL] THEN
    SIMP_TAC[mfd_ball; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d' = mfd_dist (top',atlas') (g':B->real^3^3) ((psi:A->B) y) (psi z)` THEN
  SUBGOAL_THEN `sqrt c * d' <= sqrt(&1 + dd) * d` ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_LE_LIMIT THEN EXISTS_TAC `sqrt(&1 + dd)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    X_GEN_TAC `h:real` THEN STRIP_TAC THEN
    USE_THEN "up" (MP_TAC o SPEC `h:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `sqrt c * sqrt((&1 + dd) / c) = sqrt(&1 + dd)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM SQRT_MUL] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `sqrt c * (sqrt((&1 + dd) / c) * (d + h))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the lower bound *)
  SUBGOAL_THEN `sqrt(&1 - dd) * d <= sqrt c * d'` ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_LE_LIMIT THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_POS] THEN
    X_GEN_TAC `h:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                   `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `x0:A`; `y:A`;
                   `R:real`; `D0:real`; `c:real`; `dd:real`; `d' + h / sqrt c`;
                   `(psi:A->B) z`] LIM_PB_BALL_PREIMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `x0:A`; `mfd_ball (top,atlas) (g:A->real^3^3) x0 R`;
                       `R:real`] P2BL_BOUNDED_CLOSURE_COMPACT) THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
        MESON_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^3^3) x0 R` THEN CONJ_TAC THENL
         [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
          REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^3^3) x0 (R + &1)` THEN
          ASM_REWRITE_TAC[] THEN REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
          MESON_TAC[REAL_ARITH `x <= R ==> x < R + &1`]];
        ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "qf2" (MP_TAC o SPECL [`y':A`; `v:real^3`]) THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
        ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 * D0 + &1` THEN CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `x <= &3 * D0 /\ h <= &1 ==> x + h <= &3 * D0 + &1`) THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `sqrt(&1 + dd) * d` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + dd) * d` THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
            MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&3 / &2) * (&2 * D0)` THEN
            CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - dd) * (R - D0)` THEN CONJ_TAC THENL
           [EXPAND_TAC "R" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC `(&1 / &2) * (&10 * (D0 + &1) - D0)` THEN CONJ_TAC THENL
             [ASM_REAL_ARITH_TAC;
              MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
            MATCH_MP_TAC REAL_LE_RMUL THEN EXPAND_TAC "R" THEN ASM_REAL_ARITH_TAC]];
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < h ==> d' < d' + h`) THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `(psi':B->A) ((psi:A->B) z) IN
                 mfd_ball (top,atlas) (g:A->real^3^3) y (sqrt(c / (&1 - dd)) * (d' + h / sqrt c))` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `sqrt(&1 - dd) * sqrt(c / (&1 - dd)) * (d' + h / sqrt c) = sqrt c * d' + h`
    ASSUME_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC; GSYM SQRT_MUL] THEN
      SUBGOAL_THEN `(&1 - dd) * c / (&1 - dd) = c` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < sqrt(&1 - dd)` THEN UNDISCH_TAC `&1 - dd <= sqrt(&1 - dd)` THEN
        ASM_CASES_TAC `&1 - dd = &0` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `~(&1 - dd = &0)` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      UNDISCH_TAC `&0 < sqrt c` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `sqrt(&1 - dd) * sqrt(c / (&1 - dd)) * (d' + h / sqrt c)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* combine *)
  MATCH_MP_TAC(REAL_ARITH `(&1 - dd) * d <= x /\ x <= (&1 + dd) * d ==> abs(x - d) <= dd * d`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1 - dd) * d` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1 + dd) * d` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The theorems L1 (LIM_DIST) and L2 (LIM_BALL).                             *)
(* ========================================================================= *)
(* L1: rescaled distances converge uniformly on compact sets.               *)

let LIM_DIST = prove
 (`!u:A->bool w:B->bool. LIM_DIST_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_DIST_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `s:real`; `K:B->bool`; `e:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `xl:B`; `K:B->bool`] LIM_COMPACT_DIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `D0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y:B. y IN K ==> y IN mfd_ball (top,atlas) ((g:real->B->real^3^3) s) xl D0`
  (LABEL_TAC "inK") THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `Kc = mfd_cball (top,atlas) ((g:real->B->real^3^3) s) xl (&10 * (D0 + &1) + &1)` THEN
  SUBGOAL_THEN `compact_in top (Kc:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN
    UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) s)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `dd = min (&1 / &2) (e / (&2 * D0 + &1))` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= &1 / &2 /\ dd * (&2 * D0 + &1) <= e` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < e / (&2 * D0 + &1) /\ e / (&2 * D0 + &1) * (&2 * D0 + &1) = e`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "dd" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e / (&2 * D0 + &1) * (&2 * D0 + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
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
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN MAP_EVERY X_GEN_TAC [`k:num`; `y:B`; `z:B`] THEN STRIP_TAC THEN
  USE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `s:real`)) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  ABBREV_TAC `VT = rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VA = rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  ABBREV_TAC `VG = rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) k) (t k + s / Q k)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi:A->B`) (LABEL_TAC "qf")))) THEN
  SUBGOAL_THEN `hausdorff_space (VT:A topology)` ASSUME_TAC THENL
   [EXPAND_TAC "VT" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `U = mfd_ball (top,atlas) ((g:real->B->real^3^3) s) xl (&10 * (D0 + &1) + &1)` THEN
  SUBGOAL_THEN `open_in top (U:B->bool) /\ U SUBSET Kc` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "Kc"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:B->bool) SUBSET W(k:num)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(W:num->B->bool) k`;
                 `VT:A topology`; `VA:((A->bool)#(A->real^3))->bool`;
                 `IMAGE ((phi:num->B->A) k) (W k)`; `(phi:num->B->A) k`; `psi:A->B`;
                 `U:B->bool`] MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `VT:A topology`;
                 `VA:((A->bool)#(A->real^3))->bool`; `VG:A->real^3^3`; `U:B->bool`;
                 `IMAGE ((phi:num->B->A) k) U`; `(phi:num->B->A) k`; `psi:A->B`;
                 `xl:B`; `D0:real`; `(Q:num->real) k`; `dd:real`; `y:B`; `z:B`]
                LIM_DIST_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`w:B`; `v:real^3`] THEN DISCH_TAC THEN
      USE_THEN "qf" MATCH_MP_TAC THEN ASM SET_TAC[];
      USE_THEN "inK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "inK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `dd * mfd_dist (top,atlas) ((g:real->B->real^3^3) s) y z` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) ((g:real->B->real^3^3) s) y z < &2 * D0 + &1` ASSUME_TAC THENL
   [USE_THEN "inK" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:B) IN K`)) THEN
                              MP_TAC(MATCH_MP th (ASSUME `(z:B) IN K`))) THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `y:B`; `xl:B`; `z:B`] MFD_DIST_TRIANGLE) THEN
    ASM_SIMP_TAC[MFD_JOINABLE_SYM] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `xl:B`; `y:B`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `dd * (&2 * D0 + &1)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]);;
(* L2: bounded rescaled balls about x k lie in images of a compact set.    *)

let LIM_BALL = prove
 (`!u:A->bool w:B->bool. LIM_BALL_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_BALL_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `s:real`; `r:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `s:real`; `xl:B`; `r:real`; `r + &1`]
                LIM_BALL_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN
  EXISTS_TAC `mfd_cball (top,atlas) ((g:real->B->real^3^3) s) xl (r + &1)` THEN
  EXISTS_TAC `k0:num` THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->B->real^3^3) s)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `z:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `z:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(s:B->bool) SUBSET t ==> (z:A) IN IMAGE (f:B->A) (s INTER w) ==> z IN IMAGE f (t INTER w)`) THEN
  REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]);;

