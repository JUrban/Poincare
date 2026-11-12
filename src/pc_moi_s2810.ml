(* ========================================================================= *)
(* pc_moi_s2810: Moise 28.10.  Main theorem                                  *)
(* MOISE_2810 : |- MOISE_2810_STATEMENT (pc_moi_core_stmt.ml).  A PL circle  *)
(* j in the boundary torus of a PL solid torus s that misses a set k         *)
(* carrying H_1(s) and bounds no PL 2-cell in the torus is essential there   *)
(* (MOI_S8C_INESSENTIAL_DISK), so loops in k are homotopic in the torus to   *)
(* loops in j (pc_moi_s34_torus.ml), and j carries H_1(s).                   *)
(* ========================================================================= *)

needs "src/pc_moi_s288_cov.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* MOISE_2810.                                                              *)
(* ------------------------------------------------------------------------- *)

let MOISE_2810 = prove
 (`MOISE_2810_STATEMENT`,
  REWRITE_TAC[MOISE_2810_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `k:real^3->bool`; `j:real^3->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4U_PL_SOLID_TORUS_FACTS) THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET frontier s` ASSUME_TAC THENL
   [UNDISCH_TAC `(j:real^3->bool) SUBSET frontier s DIFF k` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) homeomorphic sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4U_PL_SPHERE1_CIRCLE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* j is essential in the torus *)
  SUBGOAL_THEN
   `?k0. path k0 /\ pathfinish k0 = pathstart k0 /\ path_image k0 SUBSET j /\
         ~homotopic_loops (frontier s) k0
            (linepath(pathstart k0,pathstart (k0:real^1->real^3)))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM;
      TAUT `~(a /\ b /\ c /\ ~d) <=> a /\ b /\ c ==> d`]) THEN
    UNDISCH_TAC `~(?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d (j:real^3->bool))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8C_INESSENTIAL_DISK THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the H_1 image of k in the torus lies in that of j *)
  SUBGOAL_THEN
   `group_image (homology_group(&1,subtopology euclidean k),
                 homology_group(&1,subtopology euclidean (frontier s)))
                (hom_induced (&1) (subtopology euclidean k,{})
                                  (subtopology euclidean (frontier s),{}) (\x:real^3. x)) SUBSET
    group_image (homology_group(&1,subtopology euclidean j),
                 homology_group(&1,subtopology euclidean (frontier s)))
                (hom_induced (&1) (subtopology euclidean j,{})
                                  (subtopology euclidean (frontier s),{}) (\x:real^3. x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4U_H1_IMAGE_LOOPS THEN ASM_REWRITE_TAC[MOI_S4U_IMAGE_SUBGROUP] THEN
    X_GEN_TAC `g:real^1->real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`frontier s:real^3->bool`; `j:real^3->bool`; `g:real^1->real^3`]
      MOI_S4U_CURVE_LOOPS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `k0:real^1->real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`path_image (g:real^1->real^3) SUBSET k`;
                             `(j:real^3->bool) SUBSET frontier s DIFF k`;
                             `(k:real^3->bool) SUBSET frontier s`] THEN
      SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `g':real^1->real^3` STRIP_ASSUME_TAC)] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_FH1_LOOP_CLASS_HOMOTOPIC) THEN
    MATCH_MP_TAC MOI_S4U_LOOP_CLASS_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* compose with the inclusion of the torus in s *)
  UNDISCH_TAC `carries_h1 (k:real^3->bool) s` THEN REWRITE_TAC[carries_h1] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `frontier s:real^3->bool`; `s:real^3->bool`]
    MOI_S4U_IMAGE_COMPOSE) THEN
  MP_TAC(ISPECL [`j:real^3->bool`; `frontier s:real^3->bool`; `s:real^3->bool`]
    MOI_S4U_IMAGE_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[homology_group; HOM_INDUCED];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    FIRST_ASSUM ACCEPT_TAC]);;

