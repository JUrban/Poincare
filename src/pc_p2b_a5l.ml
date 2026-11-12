(* ========================================================================= *)
(* Unit pc_p2b_a5l: the A5L route P2B_KAPPA_NECKS_ROUND_L_ROUTE_STATEMENT of *)
(* pc_p2b_chainstmts (X1 ==> the FIX form of pc_p2b_kreq).  Headline         *)
(* P2BA5_KAPPA_NECKS_ROUND_L_ROUTE.                                          *)
(*                                                                           *)
(* Route: for eps below the eps0 of piece (g) (P2BAN_ALL_NECK_LINE), every   *)
(* slice of a kappa-solution with ksep all of whose points are eps-neck      *)
(* centres contains a line; a line and sec >= 0 give a parallel unit field  *)
(* (CMPSP_SPLIT_GEN), hence zero planes (P2BX0_PAR_SEC_ZERO) at all times;   *)
(* P2BKC_CYL_ALL (X1 and P2BX2_MODEL_AT_ZERO) gives the cylinder model.  Its *)
(* twisted alternative has no line (P2A985_ZQ_NO_LINE), against the line at *)
(* time 0; the one-to-one model has evolving delta-necks of every length at *)
(* every point and time ((h): P2BCY_CYL_MODEL_NECKS).                        *)
(* ========================================================================= *)

needs "src/pc_p2b_ksolcyl.ml";;
needs "src/pc_p2b_allneck.ml";;
needs "src/pc_p2b_cylnecks.ml";;
needs "src/pc_p2a_zq.ml";;
needs "src/pc_cmp_split.ml";;

prioritize_real();;
type_invention_error := true;;



(* ------------------------------------------------------------------------- *)
(* Lines in all slices, zero planes, and the route.                          *)
(* ------------------------------------------------------------------------- *)

let P2BA5_SLICE_LINES = prove
 (`?eps0. &0 < eps0 /\
     !eps kappa top atlas (g:real->B->real^3^3).
       &0 < eps /\ eps <= eps0 /\
       p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\
       (!t x. t <= &0 /\ x IN topspace top ==> ?e. rfs_neck (top,atlas) (g t) eps x e)
       ==> !s. s <= &0
               ==> ?lam:real->B. !a b. lam a IN topspace top /\
                                       mfd_dist (top,atlas) (g s) (lam a) (lam b) = abs(b - a)`,
  MP_TAC(REWRITE_RULE[P2B_ALL_NECK_LINE_STATEMENT] (SPEC `UNIV:B->bool` P2BAN_ALL_NECK_LINE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "an"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol] o
              check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                   "p2b_kappa_solution" with Failure _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2b_ksep] o
              check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                   "p2b_ksep" with Failure _ -> false)) THEN
  USE_THEN "an" (MP_TAC o SPECL [`eps:real`; `top:B topology`;
                                 `atlas:((B->bool)#(B->real^3))->bool`;
                                 `(g:real->B->real^3^3) s`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT2)]);;

let P2BA5_LINE_ZERO_PLANE = prove
 (`!top atlas (h:B->real^3^3) (lam:real->B).
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas h /\ mfd_complete (top,atlas) h /\ ~(topspace top = {}) /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas h x u v) /\
     (!s t. lam s IN topspace top /\ mfd_dist (top,atlas) h (lam s) (lam t) = abs(t - s))
     ==> ?x0 u v. x0 IN topspace top /\ ~collinear {vec 0,u,v} /\
                  mfd_sectional atlas h x0 u v = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `h:B->real^3^3`;
                 `lam:real->B`] CMPSP_SPLIT_GEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:B->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "unit") (K ALL_TAC))) o CONJUNCT2) THEN
  SUBGOAL_THEN `?x0:B. x0 IN topspace top` (X_CHOOSE_TAC `x0:B`) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((X:B->real^3) x0 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "unit" (MP_TAC o C MP (ASSUME `(x0:B) IN topspace top`) o SPEC `x0:B`) THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `(X:B->real^3) x0` P2BX0_NONCOLLINEAR_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `u:real^3`) THEN
  MAP_EVERY EXISTS_TAC [`x0:B`; `u:real^3`; `(X:B->real^3) x0`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BX0_PAR_SEC_ZERO THEN
  EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[]);;

let P2BA5_FIX_FROM_X1 = prove
 (`!w:B->bool. P2B_SPLIT_CYL_STATEMENT w ==> P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT w`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "x1") THEN
  REWRITE_TAC[P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT] THEN
  X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sl")) P2BA5_SLICE_LINES THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `kappa:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`] THEN
  STRIP_TAC THEN
  USE_THEN "sl" (MP_TAC o SPECL [`eps:real`; `kappa:real`; `top:B topology`;
                                 `atlas:((B->bool)#(B->real^3))->bool`;
                                 `g:real->B->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "lines")] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol] o
              check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                   "p2b_kappa_solution" with Failure _ -> false)) THEN
  SUBGOAL_THEN `p2b_cyl_model (top,atlas) (g:real->B->real^3^3)` MP_TAC THENL
   [MATCH_MP_TAC P2BKC_CYL_ALL THEN MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "lines" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `lam:real->B`) THEN
    MATCH_MP_TAC P2BA5_LINE_ZERO_PLANE THEN EXISTS_TAC `lam:real->B` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[p2b_cyl_model] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->B` (X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC)) THENL
   [MP_TAC(SPEC `w:B->bool` P2BCY_CYL_MODEL_NECKS) THEN
    REWRITE_TAC[P2B_CYL_MODEL_NECKS_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                               `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`]) THEN
    ASM_SIMP_TAC[p2b_kview];
    USE_THEN "lines" (MP_TAC o SPEC `&0`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`] P2A985_ZQ_NO_LINE) THEN
    ASM_SIMP_TAC[REAL_LE_REFL] THEN MESON_TAC[]]);;



(* ------------------------------------------------------------------------- *)
(* The headline.                                                             *)
(* ------------------------------------------------------------------------- *)

let P2BA5_KAPPA_NECKS_ROUND_L_ROUTE = prove
 (`!w:B->bool. P2B_KAPPA_NECKS_ROUND_L_ROUTE_STATEMENT w`,
  REWRITE_TAC[P2B_KAPPA_NECKS_ROUND_L_ROUTE_STATEMENT; P2BA5_FIX_FROM_X1]);;

