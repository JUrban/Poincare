(* ========================================================================= *)
(* Unit pc_p2b_avrz (Part 2B): the proof of the A6 route of pc_p2b_avrreq,   *)
(*   P2B_AVR_ZERO_ROUTE |- !w. P2B_AVR_ZERO_ROUTE_STATEMENT w               *)
(* (MT Thm 9.59 gives the FIX form of the asymptotic volume ratio            *)
(* statement): noncompact case by Thm 9.59 with eta = eps / 2; compact case  *)
(* because every ball lies in the manifold, whose volume V is finite, and V  *)
(* < eps A^3 for A = V/eps + 1.                                              *)
(* ========================================================================= *)

needs "src/pc_p2b_avrreq.ml";;
needs "src/pc_grg_vol.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The time-0 slice of a kappa-solution, and the route.                      *)
(* ========================================================================= *)

let P2BAV_KSOL_SLICE0_FACTS = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g
     ==> hausdorff_space top /\ smooth_manifold_atlas top atlas /\
         riemannian_metric atlas (g(&0)) /\ mfd_complete (top,atlas) (g(&0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2B_KSOL_SLICE0) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
  REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC);;

let P2BAV_BALL_SUBSET = prove
 (`!top atlas (g:A->real^N^N) x r.
     mfd_ball (top,atlas) g x r SUBSET topspace top`,
  REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]);;

let P2B_AVR_ZERO_ROUTE = prove
 (`!w:B->bool. P2B_AVR_ZERO_ROUTE_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_AVR_ZERO_ROUTE_STATEMENT; P2B_THM_9_59_STATEMENT; P2B_AVR_ZERO_FIX_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "t959") THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `x:B`; `eps:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BAV_KSOL_SLICE0_FACTS) THEN
  SUBGOAL_THEN
   `!r. mfd_has_volume (top,atlas) ((g:real->B->real^3^3)(&0)) (mfd_ball (top,atlas) (g(&0)) x r)
          (mfd_volume (top,atlas) (g(&0)) (mfd_ball (top,atlas) (g(&0)) x r))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3)(&0)`; `x:B`; `r:real`] MFD_HAS_VOLUME_BALL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `compact_space (top:B topology)` THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3)(&0)`; `topspace top:B->bool`] MFD_HAS_VOLUME_COMPACT) THEN
    ASM_REWRITE_TAC[GSYM compact_space] THEN
    DISCH_THEN(X_CHOOSE_TAC `V:real`) THEN
    SUBGOAL_THEN `&0 <= V` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `(g:real->B->real^3^3)(&0)`; `topspace top:B->bool`; `V:real`]
                           MFD_HAS_VOLUME_POS_LE) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= V / eps` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`V / eps + &1`;
      `mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0))
                  (mfd_ball (top,atlas) (g(&0)) x (V / eps + &1))`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `V:real` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `(g:real->B->real^3^3)(&0)`;
                            `mfd_ball (top,atlas) ((g:real->B->real^3^3)(&0)) x (V / eps + &1)`;
                            `topspace top:B->bool`;
                            `mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0))
                               (mfd_ball (top,atlas) (g(&0)) x (V / eps + &1))`; `V:real`]
                           MFD_HAS_VOLUME_MONO) THEN
      ASM_REWRITE_TAC[P2BAV_BALL_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `V / eps + &1 <= (V / eps + &1) pow 3` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(V / eps + &1) pow 1` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_1; REAL_LE_REFL];
        MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ARITH_TAC]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `eps * (V / eps + &1)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_ADD_LDISTRIB; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    USE_THEN "t959" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                     `atlas:((B->bool)#(B->real^3))->bool`;
                                     `g:real->B->real^3^3`; `x:B`; `eps / &2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` (LABEL_TAC "r0")) THEN
    MAP_EVERY EXISTS_TAC
     [`abs r0 + &1`;
      `mfd_volume (top,atlas) ((g:real->B->real^3^3)(&0))
                  (mfd_ball (top,atlas) (g(&0)) x (abs r0 + &1))`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `eps / &2 * (abs r0 + &1) pow 3` THEN
    CONJ_TAC THENL
     [USE_THEN "r0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < (abs r0 + &1) pow 3` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SPEC_TAC(`(abs r0 + &1) pow 3`,`q:real`) THEN GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e * q ==> e / &2 * q < e * q`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]]]);;

