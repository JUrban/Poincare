(* ========================================================================= *)
(* pc_top_smooth: the two statements S1 and S2 of the algebraic topology     *)
(* layer that are specific to Part 4, and their proofs.                      *)
(*   S2 (ATOP_SUSPENSION_STATEMENT): every map of S^3 is p4_susp of a       *)
(*   continuous family of maps of S^2 with constant end slices and values   *)
(*   among its values, and homotopies of such families through families     *)
(*   with constant end slices suspend to homotopies of maps of S^3.         *)
(*   S1 (ATOP_SWEEPOUT_SMOOTHING_STATEMENT): a continuous family with       *)
(*   constant end slices in a compact smooth manifold is homotopic, through *)
(*   such families, to a C^1 sweepout (p4_sweepout).                        *)
(* S2: the suspension point smo_spt y t = (sqrt(1-(2t-1)^2) y, 2t-1) and    *)
(* its inverse smo_desusp (the parametrization used by p4_susp); homotopies *)
(* descend along the quotient map I x S^2 x [0,1] -> I x S^3 (compact onto  *)
(* Hausdorff) because they are constant on the end slices.                  *)
(* S1: embedding into real^K (MFD_EMBEDDING_EXISTS), polynomial             *)
(* approximation (STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION), a linear   *)
(* correction in t making the end slices exactly constant, the smooth       *)
(* retraction of the tubular neighbourhood (MFD_TUBULAR_NEIGHBOURHOOD) and  *)
(* the straight-line homotopy inside the tube.                              *)
(* Depends on the library, pc_p4_defs and pc_mfd_tube (with the ns_ files    *)
(* from the Navier_Stokes development,                                       *)
(* github.com/hol-light-family/Navier_Stokes).                               *)
(*                                                                           *)
(* The statements, and S2.                                                   *)
(* ========================================================================= *)

needs "src/pc_p4_defs.ml";;
needs "src/pc_mfd_tube.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The statements.                                                           *)
(* ------------------------------------------------------------------------- *)

let ATOP_SWEEPOUT_SMOOTHING_STATEMENT = new_definition
 `ATOP_SWEEPOUT_SMOOTHING_STATEMENT (u:A->bool) (v:N->bool) <=>
    !top atlas (sigma:real^3->real->A).
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_space top /\
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),top)
          (\(y,t). sigma y t) /\
        (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                ==> sigma y (&0) = sigma y' (&0) /\ sigma y (&1) = sigma y' (&1))
        ==> ?sigma'. p4_sweepout (top,atlas) sigma' /\
                     homotopic_with
                       (\f. !y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                                   ==> f(y,&0) = f(y',&0) /\ f(y,&1) = f(y',&1))
                       (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                                      (subtopology euclideanreal (real_interval[&0,&1])),
                        top)
                       (\(y,t). sigma y t) (\(y,t). sigma' y t)`;;

let ATOP_SUSPENSION_STATEMENT = new_definition
 `ATOP_SUSPENSION_STATEMENT (u:A->bool) <=>
    (!top (f:real^4->A).
        continuous_map (subtopology euclidean (sphere(vec 0:real^4,&1)),top) f
        ==> ?sigma. continuous_map
                      (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                                     (subtopology euclideanreal (real_interval[&0,&1])),
                       top)
                      (\(y,t). sigma y t) /\
                    (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                            ==> sigma y (&0) = sigma y' (&0) /\
                                sigma y (&1) = sigma y' (&1)) /\
                    (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                           ==> ?x. x IN sphere(vec 0,&1) /\ sigma y t = f x) /\
                    !x. x IN sphere(vec 0,&1) ==> p4_susp sigma x = f x) /\
    (!top (sigma:real^3->real->A) sigma'.
        homotopic_with
          (\f. !y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                      ==> f(y,&0) = f(y',&0) /\ f(y,&1) = f(y',&1))
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),top)
          (\(y,t). sigma y t) (\(y,t). sigma' y t)
        ==> homotopic_with (\h. T)
              (subtopology euclidean (sphere(vec 0:real^4,&1)),top)
              (p4_susp sigma) (p4_susp sigma'))`;;

(* ------------------------------------------------------------------------- *)
(* S2. The suspension point and its inverse.                                 *)
(* ------------------------------------------------------------------------- *)

let smo_spt = new_definition
 `smo_spt (y:real^3) (t:real) =
    vector[sqrt(&1 - (&2 * t - &1) pow 2) * y$1;
           sqrt(&1 - (&2 * t - &1) pow 2) * y$2;
           sqrt(&1 - (&2 * t - &1) pow 2) * y$3;
           &2 * t - &1]:real^4`;;

let smo_desusp = new_definition
 `smo_desusp (x:real^4) =
    (if (lambda i. x$i):real^3 = vec 0 then basis 1:real^3
     else inv(norm((lambda i. x$i):real^3)) % ((lambda i. x$i):real^3)),
    (x$4 + &1) / &2`;;

let SMO_P4_SUSP = prove
 (`!(sigma:real^3->real->A) x.
        p4_susp sigma x = sigma (FST(smo_desusp x)) (SND(smo_desusp x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p4_susp; smo_desusp; FST; SND] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let SMO_PAIRED_APPLY = prove
 (`!(f:real^3->real->A) p. (\(y,t). f y t) p = f (FST p) (SND p)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM]);;

let SMO_SQRT_TERM = prove
 (`!t. t IN real_interval[&0,&1]
       ==> &0 <= &1 - (&2 * t - &1) pow 2 /\
           sqrt(&1 - (&2 * t - &1) pow 2) pow 2 = &1 - (&2 * t - &1) pow 2 /\
           (&0 < t /\ t < &1 ==> &0 < sqrt(&1 - (&2 * t - &1) pow 2))`,
  GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 - (&2 * t - &1) pow 2 = &4 * (t * (&1 - t))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &4 * (t * (&1 - t))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2] THEN STRIP_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let SMO_SPT_SPHERE = prove
 (`!y t. y IN sphere(vec 0:real^3,&1) /\ t IN real_interval[&0,&1]
         ==> smo_spt y t IN sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SMO_SQRT_TERM) THEN
  UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; smo_spt; DOT_3; DOT_4; VECTOR_4] THEN
  UNDISCH_TAC `sqrt(&1 - (&2 * t - &1) pow 2) pow 2 = &1 - (&2 * t - &1) pow 2` THEN
  SPEC_TAC(`sqrt(&1 - (&2 * t - &1) pow 2)`,`s:real`) THEN
  CONV_TAC REAL_RING);;

let SMO_SPT_ENDS = prove
 (`!y. smo_spt y (&0) = vector[&0;&0;&0;-- &1] /\
       smo_spt y (&1) = vector[&0;&0;&0;&1]`,
  GEN_TAC THEN REWRITE_TAC[smo_spt] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[SQRT_0; REAL_MUL_LZERO]);;

let SMO_SPT_DESUSP = prove
 (`!x:real^4. x IN sphere(vec 0,&1)
        ==> FST(smo_desusp x) IN sphere(vec 0,&1) /\
            SND(smo_desusp x) IN real_interval[&0,&1] /\
            smo_spt (FST(smo_desusp x)) (SND(smo_desusp x)) = x`,
  GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0; smo_desusp; FST; SND] THEN DISCH_TAC THEN
  ABBREV_TAC `z:real^3 = lambda i. (x:real^4)$i` THEN
  SUBGOAL_THEN `(z:real^3)$1 = (x:real^4)$1 /\ z$2 = x$2 /\ z$3 = x$3`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^4)$1 * x$1 + x$2 * x$2 + x$3 * x$3 + x$4 * x$4 = &1`
  ASSUME_TAC THENL
   [UNDISCH_TAC `norm(x:real^4) = &1` THEN REWRITE_TAC[NORM_EQ_1; DOT_4]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:real^3) pow 2 = (x:real^4)$1 * x$1 + x$2 * x$2 + x$3 * x$3`
  ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_3] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (((x:real^4)$4 + &1) / &2) - &1 = x$4` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 - (x:real^4)$4 pow 2) = norm(z:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^4)$1 * x$1 + x$2 * x$2 + x$3 * x$3 + x$4 * x$4 = &1` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN
    ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
                 REAL_MUL_LINV; NORM_EQ_0];
    MP_TAC(ISPECL [`x:real^4`; `4`] COMPONENT_LE_NORM) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[smo_spt] THEN
    GEN_REWRITE_TAC I [CART_EQ] THEN REWRITE_TAC[DIMINDEX_4; FORALL_4; VECTOR_4] THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `(x:real^4)$1 = &0 /\ x$2 = &0 /\ x$3 = &0` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(z:real^3)$1 = (x:real^4)$1` THEN
        UNDISCH_TAC `(z:real^3)$2 = (x:real^4)$2` THEN
        UNDISCH_TAC `(z:real^3)$3 = (x:real^4)$3` THEN
        ASM_REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[NORM_0; REAL_MUL_LZERO];
      ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0;
                   REAL_MUL_LID]]]);;

let SMO_DESUSP_SPT = prove
 (`!y t. y IN sphere(vec 0:real^3,&1) /\ t IN real_interval[&0,&1]
         ==> SND(smo_desusp(smo_spt y t)) = t /\
             (&0 < t /\ t < &1 ==> FST(smo_desusp(smo_spt y t)) = y) /\
             (t = &0 \/ t = &1 ==> FST(smo_desusp(smo_spt y t)) = basis 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SMO_SQRT_TERM) THEN
  SUBGOAL_THEN
   `(lambda i. (smo_spt y t)$i):real^3 = sqrt(&1 - (&2 * t - &1) pow 2) % y`
  ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH; smo_spt; VECTOR_4; VECTOR_MUL_COMPONENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[smo_desusp; FST; SND] THEN
  CONJ_TAC THENL [REWRITE_TAC[smo_spt; VECTOR_4] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `&0 < sqrt(&1 - (&2 * t - &1) pow 2)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
      ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(y:real^3) = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `abs(sqrt(&1 - (&2 * t - &1) pow 2)) = sqrt(&1 - (&2 * t - &1) pow 2)`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; NORM_MUL; REAL_MUL_RID;
                 VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID];
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[SQRT_0; VECTOR_MUL_LZERO]]);;

let SMO_RCONT_TAC ths =
  let etas = map (CONV_RULE (TRY_CONV (DEPTH_CONV ETA_CONV))) ths in
  let base = CONTINUOUS_MAP_REAL_CONST :: (ths @ etas) in
  let rec tac g =
    (FIRST (map MATCH_ACCEPT_TAC base) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN CONJ_TAC THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_POW THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_SQRT THEN tac)) g in
  tac;;

let SMO_SPT_COMPONENTS =
  let th = BETA_RULE(MATCH_MP CONTINUOUS_MAP_EUCLIDEAN_COMPONENT
             (ISPECL [`euclidean:(real^3)topology`; `euclideanreal`] CONTINUOUS_MAP_FST)) in
  ISPECL [`euclidean:(real^3)topology`; `euclideanreal`] CONTINUOUS_MAP_SND ::
  map (fun i -> SPEC (mk_small_numeral i) th) [1;2;3];;

let SMO_SPT_CONTINUOUS = prove
 (`continuous_map
     (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                    (subtopology euclideanreal (real_interval[&0,&1])),
      subtopology euclidean (sphere(vec 0:real^4,&1)))
     (\z. smo_spt (FST z) (SND z))`,
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUBTOPOLOGY_CROSS] THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_REAL; DIMINDEX_4; FORALL_4] THEN
    REWRITE_TAC[smo_spt; VECTOR_4] THEN REPEAT CONJ_TAC THEN
    SMO_RCONT_TAC SMO_SPT_COMPONENTS;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM; IN_CROSS;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    SIMP_TAC[SMO_SPT_SPHERE]]);;

let SMO_SUSP_HOMOTOPY = prove
 (`!top (sigma:real^3->real->A) sigma'.
        homotopic_with
          (\f. !y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                      ==> f(y,&0) = f(y',&0) /\ f(y,&1) = f(y',&1))
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),top)
          (\(y,t). sigma y t) (\(y,t). sigma' y t)
        ==> homotopic_with (\h. T)
              (subtopology euclidean (sphere(vec 0:real^4,&1)),top)
              (p4_susp sigma) (p4_susp sigma')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with; SMO_PAIRED_APPLY] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real#(real^3#real)->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:real#real^4. (H:real#(real^3#real)->A) (FST z,smo_desusp(SND z))` THEN
  ASM_REWRITE_TAC[SMO_P4_SUSP] THEN
  SUBGOAL_THEN
   `compact_space (subtopology euclideanreal (real_interval[&0,&1])) /\
    compact_space (subtopology euclidean (sphere(vec 0:real^3,&1)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL; COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE];
    ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:real#(real^3#real)`,`:A`; `:real#real^4`,`:B`; `:A`,`:C`]
                CONTINUOUS_COMPOSE_QUOTIENT_MAP) THEN
  EXISTS_TAC
   `prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
     (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                    (subtopology euclideanreal (real_interval[&0,&1])))` THEN
  EXISTS_TAC `\z:real#(real^3#real). FST z,smo_spt (FST(SND z)) (SND(SND z))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_QUOTIENT_MAP THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[COMPACT_SPACE_PROD_TOPOLOGY];
      REWRITE_TAC[HAUSDORFF_SPACE_PROD_TOPOLOGY] THEN DISJ2_TAC THEN CONJ_TAC THEN
      MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
      REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEANREAL; HAUSDORFF_SPACE_EUCLIDEAN];
      REWRITE_TAC[CONTINUOUS_MAP_PAIRED] THEN CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX; CONTINUOUS_MAP_FST];
        SUBGOAL_THEN
         `(\z:real#(real^3#real). smo_spt (FST(SND z)) (SND(SND z))) =
          (\w. smo_spt (FST w) (SND w)) o SND`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
        EXISTS_TAC
         `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                        (subtopology euclideanreal (real_interval[&0,&1]))` THEN
        REWRITE_TAC[CONTINUOUS_MAP_SND; SMO_SPT_CONTINUOUS]];
      GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[FORALL_PAIR_THM; IN_IMAGE; EXISTS_PAIR_THM; TOPSPACE_PROD_TOPOLOGY;
                  IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; PAIR_EQ; FST; SND] THEN
      MAP_EVERY X_GEN_TAC [`s:real`; `x:real^4`] THEN EQ_TAC THENL
       [STRIP_TAC THEN ASM_SIMP_TAC[SMO_SPT_SPHERE];
        STRIP_TAC THEN
        MAP_EVERY EXISTS_TAC
         [`s:real`; `FST(smo_desusp x)`; `SND(smo_desusp x)`] THEN
        ASM_SIMP_TAC[SMO_SPT_DESUSP]]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC `H:real#(real^3#real)->A` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM; IN_CROSS; o_THM;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`; `t:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`y:real^3`; `t:real`] SMO_DESUSP_SPT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 < t /\ t < &1` THENL
   [SUBGOAL_THEN `smo_desusp(smo_spt y t) = (y:real^3,t)` SUBST1_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM PAIR] THEN ASM_SIMP_TAC[PAIR_EQ]; ALL_TAC] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t = &0 \/ t = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `~(&0 < t /\ t < &1)` THEN UNDISCH_TAC `t IN real_interval[&0,&1]` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smo_desusp(smo_spt y t) = (basis 1:real^3,t)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM PAIR] THEN ASM_SIMP_TAC[PAIR_EQ]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `basis 1:real^3`]) THEN
  ASM_SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN SIMP_TAC[]);;

let ATOP_SUSPENSION = prove
 (`ATOP_SUSPENSION_STATEMENT (:A)`,
  REWRITE_TAC[ATOP_SUSPENSION_STATEMENT; SMO_SUSP_HOMOTOPY] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `f:real^4->A`] THEN DISCH_TAC THEN
  EXISTS_TAC `\y t. (f:real^4->A)(smo_spt y t)` THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\(y,t). (f:real^4->A)(smo_spt y t)) = f o (\z. smo_spt (FST z) (SND z))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^4,&1))` THEN
    ASM_REWRITE_TAC[SMO_SPT_CONTINUOUS];
    REWRITE_TAC[SMO_SPT_ENDS];
    REPEAT STRIP_TAC THEN EXISTS_TAC `smo_spt y t` THEN ASM_SIMP_TAC[SMO_SPT_SPHERE];
    SIMP_TAC[SMO_P4_SUSP; SMO_SPT_DESUSP]]);;

(* ------------------------------------------------------------------------- *)
(* Polynomials are smooth, and a continuous map on                           *)
(* S^2 x [0,1] with constant end slices is uniformly approximated by a      *)
(* smooth map on real^(3,1) with exactly the same end slices.               *)
(* ------------------------------------------------------------------------- *)

let SMO_REAL_POLYNOMIAL_SMOOTH = prove
 (`!f:real^M->real.
        real_polynomial_function f ==> smooth_map_on (:real^M) (\x. lift(f x))`,
  MATCH_MP_TAC real_polynomial_function_INDUCT THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE; OPEN_UNIV];
    REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    MAP_EVERY X_GEN_TAC [`f:real^M->real`; `g:real^M->real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(:real^M)`; `\x:real^M. lift(f x)`; `\x:real^M. lift(g x)`]
                  SMOOTH_MAP_ON_LIFT_ADD) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP];
    MAP_EVERY X_GEN_TAC [`f:real^M->real`; `g:real^M->real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(:real^M)`; `\x:real^M. lift(f x)`; `\x:real^M. lift(g x)`]
                  SMOOTH_MAP_ON_LIFT_MUL) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP]]);;

let SMO_VECTOR_POLYNOMIAL_SMOOTH = prove
 (`!g:real^M->real^N. vector_polynomial_function g ==> smooth_map_on (:real^M) g`,
  GEN_TAC THEN REWRITE_TAC[vector_polynomial_function] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `g:real^M->real^N`] SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\x:real^M. (g:real^M->real^N) x$k` SMO_REAL_POLYNOMIAL_SMOOTH) THEN
  ASM_SIMP_TAC[]);;

let SMO_SMOOTH_COMPOSE_UNIV = prove
 (`!(f:real^M->real^N) (g:real^N->real^P).
        smooth_map_on (:real^M) f /\ smooth_map_on (:real^N) g
        ==> smooth_map_on (:real^M) (\x. g(f x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `(:real^N)`; `f:real^M->real^N`; `g:real^N->real^P`]
                SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; o_DEF]);;

let SMO_SMOOTH_FSTCART_SNDCART = prove
 (`smooth_map_on (:real^(M,N)finite_sum) fstcart /\
   smooth_map_on (:real^(M,N)finite_sum) sndcart`,
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^(M,N)finite_sum)`; `\x:real^(M,N)finite_sum. x`]
                  SMOOTH_MAP_ON_FSTCART_OPEN);
    MP_TAC(ISPECL [`(:real^(M,N)finite_sum)`; `\x:real^(M,N)finite_sum. x`]
                  SMOOTH_MAP_ON_SNDCART_OPEN)] THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

let SMO_APPROX_ENDS = prove
 (`!(f:real^(3,1)finite_sum->real^K) a b e.
        f continuous_on (sphere(vec 0,&1) PCROSS interval[vec 0,vec 1]) /\ &0 < e /\
        (!y. y IN sphere(vec 0,&1)
             ==> f(pastecart y (vec 0)) = a /\ f(pastecart y (vec 1)) = b)
        ==> ?g. smooth_map_on (:real^(3,1)finite_sum) g /\
                (!z. z IN sphere(vec 0,&1) PCROSS interval[vec 0,vec 1]
                     ==> norm(g z - f z) < e) /\
                (!y. g(pastecart y (vec 0)) = a /\ g(pastecart y (vec 1)) = b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(3,1)finite_sum->real^K`;
                 `sphere(vec 0:real^3,&1) PCROSS interval[vec 0:real^1,vec 1]`; `e / &2`]
                STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION) THEN
  ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_SPHERE; COMPACT_INTERVAL; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^(3,1)finite_sum->real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `\z:real^(3,1)finite_sum.
      (p:real^(3,1)finite_sum->real^K) z +
      (&1 - drop(sndcart z)) % ((a:real^K) - p(pastecart (fstcart z) (vec 0))) +
      drop(sndcart z) % ((b:real^K) - p(pastecart (fstcart z) (vec 1)))` THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `smooth_map_on (:real^(3,1)finite_sum) (p:real^(3,1)finite_sum->real^K)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[SMO_VECTOR_POLYNOMIAL_SMOOTH]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!c:real^1. smooth_map_on (:real^(3,1)finite_sum)
                   (\z:real^(3,1)finite_sum. pastecart (fstcart z) c)`
    ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; ETA_AX; SMO_SMOOTH_FSTCART_SNDCART];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!c:real^1 q:real^K.
        smooth_map_on (:real^(3,1)finite_sum)
          (\z:real^(3,1)finite_sum. q - (p:real^(3,1)finite_sum->real^K)
                                         (pastecart (fstcart z) c))`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
      MATCH_MP_TAC SMO_SMOOTH_COMPOSE_UNIV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (:real^(3,1)finite_sum)
        (\z:real^(3,1)finite_sum. lift(&1 - drop(sndcart z)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`(:real^(3,1)finite_sum)`; `\z:real^(3,1)finite_sum. lift(&1)`;
                     `sndcart:real^(3,1)finite_sum->real^1`] SMOOTH_MAP_ON_LIFT_SUB) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; LIFT_DROP; SMO_SMOOTH_FSTCART_SNDCART];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^(3,1)finite_sum)`;
                     `\z:real^(3,1)finite_sum. lift(&1 - drop(sndcart z))`;
                     `\z:real^(3,1)finite_sum. a - (p:real^(3,1)finite_sum->real^K)
                                                       (pastecart (fstcart z) (vec 0))`]
                    SMOOTH_MAP_ON_MUL_DROP_OPEN);
      MP_TAC(ISPECL [`(:real^(3,1)finite_sum)`;
                     `sndcart:real^(3,1)finite_sum->real^1`;
                     `\z:real^(3,1)finite_sum. b - (p:real^(3,1)finite_sum->real^K)
                                                       (pastecart (fstcart z) (vec 1))`]
                    SMOOTH_MAP_ON_MUL_DROP_OPEN)] THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP; SMO_SMOOTH_FSTCART_SNDCART];
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`y:real^3`; `t:real^1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= drop t /\ drop t <= &1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `norm((p:real^(3,1)finite_sum->real^K)(pastecart y t) - f(pastecart y t)) < e / &2 /\
      norm(a - p(pastecart y (vec 0))) < e / &2 /\
      norm(b - p(pastecart y (vec 1))) < e / &2`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
      REPEAT CONJ_TAC THENL [ONCE_REWRITE_TAC[NORM_SUB]; ALL_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_VEC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC
     `norm((p:real^(3,1)finite_sum->real^K)(pastecart y t) - f(pastecart y t)) +
      (&1 - drop t) * norm(a - p(pastecart y (vec 0))) +
      drop t * norm(b - p(pastecart y (vec 1)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `norm(v:real^K) = r /\ norm(w:real^K) = s
        ==> norm((u + v + w) - q) <= norm(u - q) + r + s`) THEN
      REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(&1 - drop t) * norm(a - (p:real^(3,1)finite_sum->real^K)(pastecart y (vec 0))) <=
      (&1 - drop t) * e / &2 /\
      drop t * norm(b - p(pastecart y (vec 1))) <= drop t * e / &2`
    MP_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC
     `norm((p:real^(3,1)finite_sum->real^K)(pastecart y t) - f(pastecart y t)) < e / &2` THEN
    REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
    CONJ_TAC THEN VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The smooth retraction of the tubular neighbourhood of                     *)
(* an embedded compact manifold (continuity, left inverse, smoothness in     *)
(* charts), and C^1 regularity in charts of retracted smooth families.      *)
(* ------------------------------------------------------------------------- *)

let SMO_EMB_INV_CONTINUOUS = prove
 (`!top atlas (e:A->real^K).
        mfd_embedding (top,atlas:((A->bool)#(A->real^N))->bool) e
        ==> continuous_map (top,euclidean) e /\
            continuous_map (subtopology euclidean (IMAGE e (topspace top)),top)
                           (mfd_emb_inv top e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_embedding]) THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; homeomorphic_maps] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^K->A` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
   [UNDISCH_TAC `continuous_map
                   (top,subtopology euclidean (IMAGE (e:A->real^K) (topspace top))) e` THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `g:real^K->A` THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC GRGE_EMB_INV_LEFT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]]);;

let SMO_TUBE = prove
 (`!top atlas (e:A->real^K).
     hausdorff_space top /\
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     compact_space top /\ mfd_embedding (top,atlas) e
     ==> ?d. &0 < d /\
             continuous_map
               (subtopology euclidean
                  {z | ?p. p IN IMAGE e (topspace top) /\ dist(z,p) < d},top)
               (\z. mfd_emb_inv top e (closest_point (IMAGE e (topspace top)) z)) /\
             (!x. x IN topspace top
                  ==> mfd_emb_inv top e (closest_point (IMAGE e (topspace top)) (e x)) = x) /\
             (!c. c IN atlas
                  ==> open {z | z IN {z | ?p. p IN IMAGE e (topspace top) /\ dist(z,p) < d} /\
                                mfd_emb_inv top e (closest_point (IMAGE e (topspace top)) z)
                                IN FST c} /\
                      smooth_map_on
                        {z | z IN {z | ?p. p IN IMAGE e (topspace top) /\ dist(z,p) < d} /\
                             mfd_emb_inv top e (closest_point (IMAGE e (topspace top)) z)
                             IN FST c}
                        (\z. SND c (mfd_emb_inv top e
                                     (closest_point (IMAGE e (topspace top)) z))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `e:A->real^K`]
                MFD_TUBULAR_NEIGHBOURHOOD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `e:A->real^K`]
                SMO_EMB_INV_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `continuous_map
      (subtopology euclidean
         {z | ?p. p IN IMAGE (e:A->real^K) (topspace top) /\ dist(z,p) < d},top)
      (\z. mfd_emb_inv top e (closest_point (IMAGE e (topspace top)) z))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\z. mfd_emb_inv top (e:A->real^K) (closest_point (IMAGE e (topspace top)) z)) =
      mfd_emb_inv top e o closest_point (IMAGE e (topspace top))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (e:A->real^K) (topspace top))` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^K` THEN DISCH_THEN(X_CHOOSE_THEN `q:real^K` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^K`; `q:real^K`]) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CLOSEST_POINT_SELF o rand o lhand o snd) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC GRGE_EMB_INV_LEFT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  ABBREV_TAC `tb = {z | ?p. p IN IMAGE (e:A->real^K) (topspace top) /\ dist(z,p) < d}` THEN
  SUBGOAL_THEN
   `open {z | z IN tb /\
              mfd_emb_inv top (e:A->real^K) (closest_point (IMAGE e (topspace top)) z)
              IN FST(c:(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `tb:real^K->bool` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`\z. mfd_emb_inv top (e:A->real^K) (closest_point (IMAGE e (topspace top)) z)`;
        `subtopology euclidean (tb:real^K->bool)`; `top:A topology`;
        `FST(c:(A->bool)#(A->real^N))`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                    SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
      EXPAND_TAC "tb" THEN REWRITE_TAC[GRGE_TUBE_OPEN]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `SND(c:(A->bool)#(A->real^N)) o
    (\z. mfd_emb_inv top (e:A->real^K) (closest_point (IMAGE e (topspace top)) z)) o
    chart_inv (tb:real^K->bool,(\x:real^K. x))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[GRGE_OPEN_SET_CHART_INV];
    ALL_TAC] THEN
  UNDISCH_TAC
   `mfd_smooth_map (open_set_atlas tb) (atlas:((A->bool)#(A->real^N))->bool) tb
      (\z. mfd_emb_inv top (e:A->real^K) (closest_point (IMAGE e (topspace top)) z))` THEN
  REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING; FORALL_PAIR_THM; PAIR_EQ] THEN
  DISCH_THEN(MP_TAC o SPECL [`tb:real^K->bool`; `\x:real^K. x`;
                             `FST(c:(A->bool)#(A->real^N))`;
                             `SND(c:(A->bool)#(A->real^N))`]) THEN
  ASM_REWRITE_TAC[PAIR; FST; SND; IMAGE_ID; INTER_IDEMPOT]);;

let SMO_PASTECART_LIFT_CONTINUOUS = prove
 (`!s t. continuous_map
           (prod_topology (subtopology euclidean s) (subtopology euclideanreal t),euclidean)
           (\z:real^M#real. pastecart (FST z) (lift(SND z)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUBTOPOLOGY_CROSS] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  SUBGOAL_THEN
   `(\z:real^M#real. pastecart (FST z) (lift(SND z))) =
    (\(x,y). pastecart x y) o (\z. FST z,lift(SND z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (euclidean:(real^M)topology) (euclidean:(real^1)topology)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_PASTECART; CONTINUOUS_MAP_PAIRED] THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX; CONTINUOUS_MAP_FST];
    SUBGOAL_THEN `(\z:real^M#real. lift(SND z)) = lift o SND` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclideanreal` THEN
    REWRITE_TAC[CONTINUOUS_MAP_SND; CONTINUOUS_MAP_LIFT]]);;

let SMO_CHART_C1 = prove
 (`!(G:real^(3,1)finite_sum->real^K) (R:real^K->A) (phi:A->real^N) U W.
        smooth_map_on (:real^(3,1)finite_sum) G /\
        open W /\ smooth_map_on W (\z. phi(R z)) /\
        (!x. ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1] /\
             R(G(pastecart (inv(norm(fstcart x)) % fstcart x) (sndcart x))) IN U
             ==> G(pastecart (inv(norm(fstcart x)) % fstcart x) (sndcart x)) IN W)
        ==> continuously_differentiable 1
              {x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1] /\
                   R(G(pastecart (inv(norm(fstcart x)) % fstcart x) (sndcart x))) IN U}
              (\x. phi(R(G(pastecart (inv(norm(fstcart x)) % fstcart x) (sndcart x)))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `oo = {x:real^(3,1)finite_sum | ~(fstcart x = vec 0)}` THEN
  SUBGOAL_THEN `open (oo:real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "oo" THEN
    SUBGOAL_THEN
     `{x:real^(3,1)finite_sum | ~(fstcart x = vec 0)} =
      {x | fstcart x IN (:real^3) DELETE vec 0}`
    SUBST1_TAC THENL [REWRITE_TAC[IN_DELETE; IN_UNIV]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    SIMP_TAC[OPEN_DELETE; OPEN_UNIV; LINEAR_CONTINUOUS_AT; LINEAR_FSTCART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on oo (fstcart:real^(3,1)finite_sum->real^3) /\
    smooth_map_on oo (sndcart:real^(3,1)finite_sum->real^1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `(:real^(3,1)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV; SMO_SMOOTH_FSTCART_SNDCART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (oo:real^(3,1)finite_sum->bool)
      (\x. pastecart (inv(norm(fstcart x)) % fstcart x) (sndcart x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`oo:real^(3,1)finite_sum->bool`;
                   `\x:real^(3,1)finite_sum. lift(inv(norm(fstcart x)))`;
                   `fstcart:real^(3,1)finite_sum->real^3`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`oo:real^(3,1)finite_sum->bool`;
                   `\x:real^(3,1)finite_sum. lift(norm(fstcart x))`] SMOOTH_MAP_ON_LIFT_INV) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`oo:real^(3,1)finite_sum->bool`; `fstcart:real^(3,1)finite_sum->real^3`]
                    SMOOTH_MAP_ON_LIFT_NORM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      EXPAND_TAC "oo" THEN SIMP_TAC[IN_ELIM_THM];
      EXPAND_TAC "oo" THEN SIMP_TAC[IN_ELIM_THM; NORM_EQ_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (oo:real^(3,1)finite_sum->bool)
      (\x. (G:real^(3,1)finite_sum->real^K)
             (pastecart (inv(norm(fstcart x)) % fstcart x) (sndcart x)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`oo:real^(3,1)finite_sum->bool`; `(:real^(3,1)finite_sum)`;
                   `\x:real^(3,1)finite_sum.
                       pastecart (inv(norm(fstcart x)) % fstcart x) (sndcart x)`;
                   `G:real^(3,1)finite_sum->real^K`] SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; o_DEF];
    ALL_TAC] THEN
  ABBREV_TAC
   `oo' = {x | x IN oo /\
               (G:real^(3,1)finite_sum->real^K)
                 (pastecart (inv(norm(fstcart x)) % fstcart x) (sndcart x)) IN W}` THEN
  SUBGOAL_THEN `open (oo':real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "oo'" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (oo':real^(3,1)finite_sum->bool)
      (\x. (phi:A->real^N)(R((G:real^(3,1)finite_sum->real^K)
             (pastecart (inv(norm(fstcart x)) % fstcart x) (sndcart x)))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`oo':real^(3,1)finite_sum->bool`; `W:real^K->bool`;
                   `\x:real^(3,1)finite_sum. (G:real^(3,1)finite_sum->real^K)
                         (pastecart (inv(norm(fstcart x)) % fstcart x) (sndcart x))`;
                   `\z:real^K. (phi:A->real^N)(R z)`] SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [EXPAND_TAC "oo'" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `oo:real^(3,1)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "oo'" THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
  EXISTS_TAC `oo':real^(3,1)finite_sum->bool` THEN CONJ_TAC THENL
   [EXPAND_TAC "oo'" THEN EXPAND_TAC "oo" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `1` o REWRITE_RULE[smooth_map_on]) THEN REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Smoothing of families in an embedded compact manifold                     *)
(* (approximate, retract, straight-line homotopy in the tube), and S1.      *)
(* ------------------------------------------------------------------------- *)

let SMO_SMOOTHING_EMBEDDED = prove
 (`!top atlas (e:A->real^K) (sigma:real^3->real->A).
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_space top /\ mfd_embedding (top,atlas) e /\
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),top)
          (\(y,t). sigma y t) /\
        (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                ==> sigma y (&0) = sigma y' (&0) /\ sigma y (&1) = sigma y' (&1))
        ==> ?sigma'. p4_sweepout (top,atlas) sigma' /\
                     homotopic_with
                       (\f. !y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                                   ==> f(y,&0) = f(y',&0) /\ f(y,&1) = f(y',&1))
                       (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                                      (subtopology euclideanreal (real_interval[&0,&1])),
                        top)
                       (\(y,t). sigma y t) (\(y,t). sigma' y t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `e:A->real^K`]
                SMO_TUBE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Rc")
      (CONJUNCTS_THEN2 (LABEL_TAC "Re") (LABEL_TAC "Rs"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `e:A->real^K`]
                SMO_EMB_INV_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `EM = IMAGE (e:A->real^K) (topspace top)` THEN
  ABBREV_TAC `tb = {z:real^K | ?p. p IN EM /\ dist(z,p) < d}` THEN
  ABBREV_TAC
   `ff = \z:real^(3,1)finite_sum. (e:A->real^K)(sigma (fstcart z) (drop(sndcart z)))` THEN
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0:real^3,&1) /\ t IN real_interval[&0,&1]
          ==> (sigma:real^3->real->A) y t IN topspace top`
  (LABEL_TAC "St") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `(y:real^3,t:real)` o CONJUNCT1 o
      GEN_REWRITE_RULE I [continuous_map]) THEN
    ASM_REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                    TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0:real^3,&1) /\ t IN real_interval[&0,&1]
          ==> pastecart y (lift t) IN sphere(vec 0,&1) PCROSS interval[vec 0,vec 1]`
  (LABEL_TAC "D0") THENL
   [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DROP_VEC;
                IN_REAL_INTERVAL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(ff:real^(3,1)finite_sum->real^K) continuous_on
      (sphere(vec 0,&1) PCROSS interval[vec 0,vec 1])`
  (LABEL_TAC "F1") THENL
   [EXPAND_TAC "ff" THEN REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
    SUBGOAL_THEN
     `(\z:real^(3,1)finite_sum. (e:A->real^K)(sigma (fstcart z) (drop(sndcart z)))) =
      e o (\(y,t). sigma y t) o (\z. fstcart z,drop(sndcart z))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC
     `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                    (subtopology euclideanreal (real_interval[&0,&1]))` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONTINUOUS_MAP_PAIRED] THEN CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX; CONTINUOUS_MAP_EUCLIDEAN2] THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
        SIMP_TAC[];
        REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `(\z:real^(3,1)finite_sum. drop(sndcart z)) = drop o sndcart`
          SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
          MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
          EXISTS_TAC `euclidean:(real^1)topology` THEN
          REWRITE_TAC[CONTINUOUS_MAP_DROP; CONTINUOUS_MAP_EUCLIDEAN] THEN
          SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART;
                      TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_INTERVAL_1; DROP_VEC;
                      IN_REAL_INTERVAL] THEN
          SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN sphere(vec 0,&1) PCROSS interval[vec 0,vec 1]
        ==> (ff:real^(3,1)finite_sum->real^K) z IN EM`
  (LABEL_TAC "F2") THENL
   [EXPAND_TAC "ff" THEN EXPAND_TAC "EM" THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`y:real^3`; `t:real^1`] THEN STRIP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN USE_THEN "St" MATCH_MP_TAC THEN
    UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; IN_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN sphere(vec 0:real^3,&1)
        ==> (ff:real^(3,1)finite_sum->real^K)(pastecart y (vec 0)) =
            ff(pastecart (basis 1) (vec 0)) /\
            ff(pastecart y (vec 1)) = ff(pastecart (basis 1) (vec 1))`
  (LABEL_TAC "F3") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXPAND_TAC "ff" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `basis 1:real^3`]) THEN
    ASM_SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0:real^3,&1) /\ t IN real_interval[&0,&1]
          ==> mfd_emb_inv top (e:A->real^K)
                (closest_point EM ((ff:real^(3,1)finite_sum->real^K)
                                     (pastecart y (lift t)))) =
              (sigma:real^3->real->A) y t`
  (LABEL_TAC "F4") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "ff" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    USE_THEN "Re" MATCH_MP_TAC THEN USE_THEN "St" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ff:real^(3,1)finite_sum->real^K`;
                 `(ff:real^(3,1)finite_sum->real^K)(pastecart (basis 1) (vec 0))`;
                 `(ff:real^(3,1)finite_sum->real^K)(pastecart (basis 1) (vec 1))`;
                 `d / &2`] SMO_APPROX_ENDS) THEN
  ASM_SIMP_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `gg:real^(3,1)finite_sum->real^K`
    (CONJUNCTS_THEN2 (LABEL_TAC "G1")
      (CONJUNCTS_THEN2 (LABEL_TAC "G2") (LABEL_TAC "G3")))) THEN
  SUBGOAL_THEN
   `!s z. s IN real_interval[&0,&1] /\
          z IN sphere(vec 0,&1) PCROSS interval[vec 0,vec 1]
          ==> (&1 - s) % (ff:real^(3,1)finite_sum->real^K) z + s % gg z IN tb`
  (LABEL_TAC "T1") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "tb" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `(ff:real^(3,1)finite_sum->real^K) z` THEN
    USE_THEN "F2" (fun th -> ASM_SIMP_TAC[th]) THEN
    REWRITE_TAC[dist; VECTOR_ARITH
     `((&1 - s) % a + s % b) - a:real^N = s % (b - a)`] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `norm((gg:real^(3,1)finite_sum->real^K) z - ff z) < d / &2`
    ASSUME_TAC THENL [USE_THEN "G2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= s /\ s <= &1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `s IN real_interval[&0,&1]` THEN REWRITE_TAC[IN_REAL_INTERVAL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm((gg:real^(3,1)finite_sum->real^K) z - ff z)` THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      UNDISCH_TAC `&0 <= s` THEN UNDISCH_TAC `s <= &1` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `norm((gg:real^(3,1)finite_sum->real^K) z - ff z) < d / &2` THEN
      UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN sphere(vec 0,&1) PCROSS interval[vec 0,vec 1]
        ==> (gg:real^(3,1)finite_sum->real^K) z IN tb`
  (LABEL_TAC "T2") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "T1" (MP_TAC o SPECL [`&1`; `z:real^(3,1)finite_sum`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map
      (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                     (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
      (\w. (ff:real^(3,1)finite_sum->real^K) (pastecart (FST w) (lift(SND w)))) /\
    continuous_map
      (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                     (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
      (\w. (gg:real^(3,1)finite_sum->real^K) (pastecart (FST w) (lift(SND w))))`
  (CONJUNCTS_THEN2 (LABEL_TAC "Cf") (LABEL_TAC "Cg")) THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\w. (ff:real^(3,1)finite_sum->real^K) (pastecart (FST w) (lift(SND w)))) =
        ff o (\w:real^3#real. pastecart (FST w) (lift(SND w)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean
                    (sphere(vec 0:real^3,&1) PCROSS interval[vec 0:real^1,vec 1])` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN; CONTINUOUS_MAP_IN_SUBTOPOLOGY;
                      SMO_PASTECART_LIFT_CONTINUOUS] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY;
                  IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      USE_THEN "D0" (fun th -> SIMP_TAC[th]);
      SUBGOAL_THEN
       `(\w. (gg:real^(3,1)finite_sum->real^K) (pastecart (FST w) (lift(SND w)))) =
        gg o (\w:real^3#real. pastecart (FST w) (lift(SND w)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `euclidean:(real^(3,1)finite_sum)topology` THEN
      REWRITE_TAC[SMO_PASTECART_LIFT_CONTINUOUS] THEN
      MP_TAC(ISPECL [`gg:real^(3,1)finite_sum->real^K`; `(:real^(3,1)finite_sum)`]
                    CONTINUOUS_MAP_EUCLIDEAN) THEN
      REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "G1" (fun th -> REWRITE_TAC[MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON th])];
    ALL_TAC] THEN
  EXISTS_TAC
   `\y t. mfd_emb_inv top (e:A->real^K)
            (closest_point EM ((gg:real^(3,1)finite_sum->real^K) (pastecart y (lift t))))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[p4_sweepout] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\(y,t). mfd_emb_inv top (e:A->real^K)
                   (closest_point EM ((gg:real^(3,1)finite_sum->real^K)
                                        (pastecart y (lift t))))) =
        (\z. mfd_emb_inv top e (closest_point EM z)) o
        (\w. gg(pastecart (FST w) (lift(SND w))))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean (tb:real^K->bool)` THEN
      USE_THEN "Rc" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "Cg" (fun th -> REWRITE_TAC[th; CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY;
                  IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      REPEAT STRIP_TAC THEN USE_THEN "T2" MATCH_MP_TAC THEN
      USE_THEN "D0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_NUM] THEN USE_THEN "G3" (fun th -> REWRITE_TAC[th]);
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      REWRITE_TAC[LIFT_DROP] THEN
      MP_TAC(ISPECL
       [`gg:real^(3,1)finite_sum->real^K`;
        `\z:real^K. mfd_emb_inv top (e:A->real^K) (closest_point EM z)`;
        `SND(c:(A->bool)#(A->real^N))`; `FST(c:(A->bool)#(A->real^N))`;
        `{z | z IN tb /\
              mfd_emb_inv top (e:A->real^K) (closest_point EM z) IN
              FST(c:(A->bool)#(A->real^N))}`]
       SMO_CHART_C1) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "Rs" (fun th -> MP_TAC(MP (SPEC `c:(A->bool)#(A->real^N)` th)
                                (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real^(3,1)finite_sum` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN USE_THEN "T2" MATCH_MP_TAC THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_SPHERE_0; NORM_MUL; REAL_ABS_INV;
                  REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0] THEN
      UNDISCH_TAC `drop(sndcart(x:real^(3,1)finite_sum)) IN real_interval[&0,&1]` THEN
      REWRITE_TAC[IN_REAL_INTERVAL; IN_INTERVAL_1; DROP_VEC]];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  EXISTS_TAC
   `\(y,t). mfd_emb_inv top (e:A->real^K)
              (closest_point EM ((ff:real^(3,1)finite_sum->real^K) (pastecart y (lift t))))` THEN
  EXISTS_TAC
   `\(y,t). mfd_emb_inv top (e:A->real^K)
              (closest_point EM ((gg:real^(3,1)finite_sum->real^K) (pastecart y (lift t))))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[homotopic_with] THEN
    EXISTS_TAC
     `\w:real#(real^3#real).
        mfd_emb_inv top (e:A->real^K)
          (closest_point EM
            ((&1 - FST w) % (ff:real^(3,1)finite_sum->real^K)
                              (pastecart (FST(SND w)) (lift(SND(SND w)))) +
             FST w % (gg:real^(3,1)finite_sum->real^K)
                       (pastecart (FST(SND w)) (lift(SND(SND w))))))` THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_MUL_LID;
                VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `continuous_map
          (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
            (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                           (subtopology euclideanreal (real_interval[&0,&1]))),
           euclideanreal) FST`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL
         [`subtopology euclideanreal (real_interval[&0,&1])`;
          `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1]))`]
         CONTINUOUS_MAP_FST) THEN
        SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(\w:real#(real^3#real). mfd_emb_inv top (e:A->real^K) (closest_point EM
           ((&1 - FST w) % (ff:real^(3,1)finite_sum->real^K)
                             (pastecart (FST(SND w)) (lift(SND(SND w)))) +
            FST w % (gg:real^(3,1)finite_sum->real^K)
                      (pastecart (FST(SND w)) (lift(SND(SND w))))))) =
        (\z. mfd_emb_inv top e (closest_point EM z)) o
        (\w. (&1 - FST w) % ff (pastecart (FST(SND w)) (lift(SND(SND w)))) +
             FST w % gg (pastecart (FST(SND w)) (lift(SND(SND w)))))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean (tb:real^K->bool)` THEN
      USE_THEN "Rc" (fun th -> REWRITE_TAC[th; CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
          ASM_REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST; ETA_AX];
          SUBGOAL_THEN
           `(\w:real#(real^3#real). (ff:real^(3,1)finite_sum->real^K)
                (pastecart (FST(SND w)) (lift(SND(SND w))))) =
            (\v. ff(pastecart (FST v) (lift(SND v)))) o SND`
          SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
          MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
          EXISTS_TAC
           `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                          (subtopology euclideanreal (real_interval[&0,&1]))` THEN
          USE_THEN "Cf" (fun th -> REWRITE_TAC[th; CONTINUOUS_MAP_SND]);
          ASM_REWRITE_TAC[ETA_AX];
          SUBGOAL_THEN
           `(\w:real#(real^3#real). (gg:real^(3,1)finite_sum->real^K)
                (pastecart (FST(SND w)) (lift(SND(SND w))))) =
            (\v. gg(pastecart (FST v) (lift(SND v)))) o SND`
          SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
          MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
          EXISTS_TAC
           `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                          (subtopology euclideanreal (real_interval[&0,&1]))` THEN
          USE_THEN "Cg" (fun th -> REWRITE_TAC[th; CONTINUOUS_MAP_SND])];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY;
                    IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                    TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; FST; SND] THEN
        REPEAT STRIP_TAC THEN USE_THEN "T1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "D0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`y:real^3`; `y':real^3`] THEN STRIP_TAC THEN
      REWRITE_TAC[LIFT_NUM] THEN USE_THEN "G3" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "F3" (fun th -> ASM_SIMP_TAC[th])];
    REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "F4" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`h:real^3#real->A`; `k:real^3#real->A`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `!y. y IN sphere(vec 0:real^3,&1)
          ==> (h:real^3#real->A)(y,&0) = k(y,&0) /\ h(y,&1) = k(y,&1)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                      TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
      REAL_ARITH_TAC;
      MESON_TAC[]]]);;

let ATOP_SWEEPOUT_SMOOTHING = prove
 (`ATOP_SWEEPOUT_SMOOTHING_STATEMENT (:A) (:N)`,
  REWRITE_TAC[ATOP_SWEEPOUT_SMOOTHING_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `sigma:real^3->real->A`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
    (INST_TYPE [`:((N,N)finite_sum,1)finite_sum`,`:K`] MFD_EMBEDDING_EXISTS)) THEN
  ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `e:A->real^((N,N)finite_sum,1)finite_sum`) THEN
  MATCH_MP_TAC(INST_TYPE [`:((N,N)finite_sum,1)finite_sum`,`:K`] SMO_SMOOTHING_EMBEDDED) THEN
  EXISTS_TAC `e:A->real^((N,N)finite_sum,1)finite_sum` THEN ASM_REWRITE_TAC[]);;

