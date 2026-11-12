(* ========================================================================= *)
(* pc_p2b_c994 (Part 2B, piece (f) of pc_p2b_c994req): MT Cor 9.94 in the   *)
(* length-L form from its noncompact and compact cases.  Headline:          *)
(*   P2B_COR_9_94_L_CASES_ROUTE |- !w. P2B_COR_9_94_L_CASES_ROUTE_STATEMENT w *)
(* (KSOL_NONCOMPACT_CANON_L /\ KSOL_COMPACT_CANON_L ==> P2B_COR_9_94_L):    *)
(* C = max C0 C1 and the monotonicity of p2b_canon_L in C, from the cap and *)
(* C-component lemmas P2B_RFS_CAP_MONO_C, P2B_RFS_C_COMPONENT_MONO_C of     *)
(* pc_p2b_lim.                                                               *)
(* ========================================================================= *)

needs "src/pc_p2b_c994req.ml";;
needs "src/pc_p2b_lim.ml";;

prioritize_real();;
type_invention_error := true;;

(* Piece (f): P2B_COR_9_94_L from its noncompact and compact cases (the      *)
(* statements of pc_p2b_c994req); monotonicity of p2b_canon_L in C.          *)

let P2BC94_CANON_L_MONO_C = prove
 (`!(V:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3))
    C C' eps L (x:B) t.
     &1 < C /\ C <= C' /\
     riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t) /\
     p2b_canon_L V C eps L x t
     ==> p2b_canon_L V C' eps L x t`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->B topology`; `AT:real->((B->bool)#(B->real^3))->bool`;
                       `G:real->B->real^3^3`; `C:real`; `C':real`; `eps:real`; `L:real`;
                       `x:B`; `t:real`] THEN
  REWRITE_TAC[rfs_vtop; rfs_vatlas; rfs_vmetric; p2b_canon_L] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[P2B_RFS_CAP_MONO_C; P2B_RFS_C_COMPONENT_MONO_C]);;

let P2B_COR_9_94_L_CASES_ROUTE = prove
 (`!w:B->bool. P2B_COR_9_94_L_CASES_ROUTE_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_COR_9_94_L_CASES_ROUTE_STATEMENT; P2B_KSOL_NONCOMPACT_CANON_L_STATEMENT;
              P2B_KSOL_COMPACT_CANON_L_STATEMENT; P2B_COR_9_94_L_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h2")))
    (X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h3")))) THEN
  EXISTS_TAC `min eps2 eps3` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `L:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "h2" (MP_TAC o SPECL [`eps:real`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c0"))) THEN
  REMOVE_THEN "h3" (MP_TAC o SPECL [`eps:real`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1"))) THEN
  EXISTS_TAC `max C0 C1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `kappa:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                       `x:B`] THEN
  STRIP_TAC THEN MATCH_MP_TAC P2BC94_CANON_L_MONO_C THEN
  REWRITE_TAC[P2B_KVIEW_SLICE0] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3)(&0))` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2B_KSOL_SLICE0]; ALL_TAC] THEN
  ASM_CASES_TAC `compact_space (top:B topology)` THENL
   [EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "c1" MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `C0:real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "c0" MATCH_MP_TAC THEN EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[]]);;

