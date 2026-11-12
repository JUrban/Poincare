(* ========================================================================= *)
(* Unit pc_p2b_ksolcyl: shared by the routes of COR_9_94_L piece (a)         *)
(* (P2B_PROP_9_83K_ROUTE, unit pc_p2b_p983k) and of A5L                      *)
(* (P2B_KAPPA_NECKS_ROUND_L_ROUTE, unit pc_p2b_a5l).  A kappa-solution with  *)
(* p2b_ksep is a p2b_ancflow on s < 0: dR/dt >= 0 is the theorem             *)
(* P2B_KSOL_DRDT (P2B_KSOL_DRDT_FROM_HARNACK with the Harnack theorem        *)
(* RFA_P2B_REQ_RFA_HARNACK), and the noncollapsing passes to the open view   *)
(* (P2BX2_KNC_VIEW_MONO).  With a zero plane at every s0 < 0, X1             *)
(* (P2B_SPLIT_CYL) gives the cylinder model of every shift g(t + s0), and    *)
(* P2BX2_MODEL_AT_ZERO turns these into one model of g itself, time 0        *)
(* included (P2BKC_CYL_ALL).                                                 *)
(* ========================================================================= *)

needs "src/pc_p2b_x2.ml";;
needs "src/pc_rfa_htrace.ml";;

prioritize_real();;
type_invention_error := true;;



(* ------------------------------------------------------------------------- *)
(* Kappa-solutions as ancient flows, and the global cylinder model from zero *)
(* planes at all negative times.                                             *)
(* ------------------------------------------------------------------------- *)

let P2BKC_KSOL_DRDT = prove
 (`!w:B->bool. P2B_KSOL_DRDT_STATEMENT w`,
  GEN_TAC THEN MATCH_MP_TAC P2B_KSOL_DRDT_FROM_HARNACK THEN
  REWRITE_TAC[RFA_P2B_REQ_RFA_HARNACK]);;

let P2BKC_KSOL_ANCFLOW = prove
 (`!kappa top atlas (g:real->B->real^3^3).
     p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas
     ==> p2b_ancflow kappa (top,atlas) g (&0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ks") ASSUME_TAC) THEN
  USE_THEN "ks" (LABEL_TAC "drdt" o MATCH_MP
    (REWRITE_RULE[P2B_KSOL_DRDT_STATEMENT] (SPEC `UNIV:B->bool` P2BKC_KSOL_DRDT))) THEN
  USE_THEN "ks" (STRIP_ASSUME_TAC o REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol]) THEN
  ASM_REWRITE_TAC[p2b_ancflow; p2b_ancflow0] THEN
  REPEAT CONJ_TAC THEN
  FIRST [GEN_TAC THEN MATCH_MP_TAC P2BX2_KNC_VIEW_MONO THEN ASM_REWRITE_TAC[];
         ASM_MESON_TAC[rfs_flow_upto; REAL_LT_IMP_LE]]);;

let P2BKC_CYL_ALL = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3).
     P2B_SPLIT_CYL_STATEMENT w /\
     p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
     (!s. s < &0 ==> ?x0 u v. x0 IN topspace top /\ ~collinear {vec 0,u,v} /\
                              mfd_sectional atlas (g s) x0 u v = &0)
     ==> p2b_cyl_model (top,atlas) g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "x1") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "zp")))) THEN
  MATCH_MP_TAC P2BX2_MODEL_AT_ZERO THEN CONJ_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    X_GEN_TAC `s0:real` THEN DISCH_TAC THEN
    USE_THEN "zp" (MP_TAC o C MP (ASSUME `s0 < &0`) o SPEC `s0:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:B` (X_CHOOSE_THEN `u:real^3`
      (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC))) THEN
    USE_THEN "x1" (MATCH_MP_TAC o REWRITE_RULE[P2B_SPLIT_CYL_STATEMENT]) THEN
    MAP_EVERY EXISTS_TAC [`kappa:real`; `&0`; `x0:B`; `u:real^3`; `v:real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BKC_KSOL_ANCFLOW THEN ASM_REWRITE_TAC[]]);;

