(* ========================================================================= *)
(* pc_p2b_p983k: piece (a) of COR_9_94_L, the route                          *)
(* P2B_PROP_9_83K_ROUTE_STATEMENT of pc_p2b_c994req (X1 ==> PROP_9_83K).     *)
(* Main theorem P2BPK_PROP_9_83K_ROUTE.                                      *)
(*                                                                           *)
(* Route (the last step is P2BKC_CYL_ALL of pc_p2b_ksolcyl): if some plane   *)
(* has sectional curvature 0 at time 0, the strong maximum principle         *)
(* (RFA_P2B_REQ_SMP_SPLIT_PT) makes every earlier slice flat or locally      *)
(* split; a local parallel unit field gives a zero plane                     *)
(* (P2BPK_PAR_SEC_ZERO_LOCAL); so there are zero planes at all s < 0 and the *)
(* solution is the cylinder model.                                           *)
(* ========================================================================= *)

needs "src/pc_p2b_ksolcyl.ml";;
needs "src/pc_p2b_c994req.ml";;
needs "src/pc_rfa_splitend.ml";;

prioritize_real();;
type_invention_error := true;;



(* ------------------------------------------------------------------------- *)
(* A parallel field on an open set kills the planes containing it (the local *)
(* form of P2BX0_PAR_SEC_ZERO), and the route.                               *)
(* ------------------------------------------------------------------------- *)

let P2BPK_PAR_SEC_ZERO_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W X p u.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ p2b_parallel_on atlas g W X /\ p IN W
     ==> mfd_sectional atlas g p u (X p) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (p:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `U = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)` THEN
  SUBGOAL_THEN `open (U:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^3)) p IN U` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (U:real^3->bool) (metric_local atlas c (g:A->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; EXPAND_TAC "U" THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `p2b_parallel_on atlas (g:A->real^3^3) W X` THEN
  REWRITE_TAC[p2b_parallel_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `c:(A->bool)#(A->real^3)`)
    (MP_TAC o SPEC `c:(A->bool)#(A->real^3)`)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`;
                 `metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)`;
                 `mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3))`;
                 `SND (c:(A->bool)#(A->real^3)) p`; `u:real^3`;
                 `mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3)) (SND c p)`]
                P2BX0_LRIEMANN_PARALLEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `X:A->real^3`; `p:A`]
                P2BX0_VREP_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[mfd_sectional; lsectional; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO;
                  real_div; REAL_MUL_LZERO]);;

let P2BPK_PROP_9_83K_ROUTE = prove
 (`!w:B->bool. P2B_PROP_9_83K_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_PROP_9_83K_ROUTE_STATEMENT; P2B_PROP_9_83K_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "x1") THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                         ==> &0 < mfd_sectional atlas ((g:real->B->real^3^3) (&0)) x u v` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:B` (X_CHOOSE_THEN `u:real^3`
    (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BL_KSOL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[p2b_kappa_solution; p2c_kappa_sol] o
              check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                   "p2b_kappa_solution" with Failure _ -> false)) THEN
  SUBGOAL_THEN `mfd_sectional atlas ((g:real->B->real^3^3) (&0)) x u v = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ ~(&0 < a) ==> a = &0`) THEN ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BKC_CYL_ALL THEN
  MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `s - &1`; `&0`; `x:B`; `&0`]
         (REWRITE_RULE[P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT]
           (SPEC `w:B->bool` (INST_TYPE [`:B`,`:A`] RFA_P2B_REQ_SMP_SPLIT_PT)))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                    ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`x:B`; `u:real^3`; `v:real^3`] THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `x:B` o REWRITE_RULE[p2b_locally_split]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `W:B->bool` (X_CHOOSE_THEN `X:B->real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `~((X:B->real^3) x = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(x:B) IN W`) o SPEC `x:B`) THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `(X:B->real^3) x` P2BX0_NONCOLLINEAR_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `u':real^3`) THEN
    MAP_EVERY EXISTS_TAC [`x:B`; `u':real^3`; `(X:B->real^3) x`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BPK_PAR_SEC_ZERO_LOCAL THEN
    EXISTS_TAC `top:B topology` THEN EXISTS_TAC `W:B->bool` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

