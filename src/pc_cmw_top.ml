(* ========================================================================= *)
(* Unit pc_cmw_top: topology for the width unit pc_cm_width.  Essentiality   *)
(* (nonzero on H_3) of the suspension of a family of maps of S^2 with        *)
(* constant end slices is invariant under homotopies of such families and    *)
(* under reparametrization of the slices by a continuous family of           *)
(* bijections of S^2; families with constant slices are inessential.  The    *)
(* embedded picture: homotopies of sweepouts inside f(M) (cm_shomotopic)     *)
(* stay in the image of a component and pull back to homotopies in the       *)
(* component.                                                                *)
(*                                                                           *)
(* Suspensions and essentiality.                                             *)
(* ========================================================================= *)

needs "src/pc_cm_target.ml";;
needs "src/pc_top_smooth.ml";;

prioritize_real();;
type_invention_error := true;;

(* End-slice and value properties of maps on S^2 x [0,1].                   *)

let cmw_endp = new_definition
 `cmw_endp (f:real^3#real->B) <=>
    !y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
           ==> f(y,&0) = f(y',&0) /\ f(y,&1) = f(y',&1)`;;

let cmw_ins = new_definition
 `cmw_ins (S:B->bool) (f:real^3#real->B) <=>
    !y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> f(y,t) IN S`;;

let CMW_ENDP_ALT = prove
 (`cmw_endp:(real^3#real->B)->bool =
   \f. !y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
             ==> f(y,&0) = f(y',&0) /\ f(y,&1) = f(y',&1)`,
  REWRITE_TAC[FUN_EQ_THM; cmw_endp]);;

let CMW_ENDP_PAIRED = prove
 (`!sigma:real^3->real->B.
        cmw_endp (\(y,t). sigma y t) <=>
        !y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
               ==> sigma y (&0) = sigma y' (&0) /\ sigma y (&1) = sigma y' (&1)`,
  REWRITE_TAC[cmw_endp]);;

let CMW_INS_PAIRED = prove
 (`!S sigma:real^3->real->B.
        cmw_ins S (\(y,t). sigma y t) <=>
        !y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> sigma y t IN S`,
  REWRITE_TAC[cmw_ins]);;

let CMW_ENDP_EQ = prove
 (`!h k:real^3#real->B.
        (!x. x IN topspace
                 (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                                (subtopology euclideanreal (real_interval[&0,&1])))
             ==> h x = k x)
        ==> (cmw_endp h <=> cmw_endp k)`,
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM; IN_CROSS;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmw_endp] THEN
  SUBGOAL_THEN `&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let CMW_INS_EQ = prove
 (`!S h k:real^3#real->B.
        (!x. x IN topspace
                 (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                                (subtopology euclideanreal (real_interval[&0,&1])))
             ==> h x = k x)
        ==> (cmw_ins S h <=> cmw_ins S k)`,
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM; IN_CROSS;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmw_ins] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The suspension of a continuous family with constant ends is continuous,  *)
(* and essentiality is a homotopy invariant of such families.                *)
(* ------------------------------------------------------------------------- *)

let CMW_FAM_SUSP_CONT = prove
 (`!top (sigma:real^3->real->A).
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),top)
          (\(y,t). sigma y t) /\
        (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                ==> sigma y (&0) = sigma y' (&0) /\ sigma y (&1) = sigma y' (&1))
        ==> continuous_map (subtopology euclidean (sphere(vec 0:real^4,&1)),top)
                           (p4_susp sigma)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `sigma:real^3->real->A`; `sigma:real^3->real->A`]
                SMO_SUSP_HOMOTOPY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HOMOTOPIC_WITH_REFL; SMO_PAIRED_APPLY; FST; SND] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS) THEN
    SIMP_TAC[]]);;

let CMW_ESSENTIAL_HOMOTOPIC = prove
 (`!top (sigma:real^3->real->A) sigma'.
        homotopic_with cmw_endp
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),top)
          (\(y,t). sigma y t) (\(y,t). sigma' y t)
        ==> (p4_essential top (p4_susp sigma) <=> p4_essential top (p4_susp sigma'))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `sigma:real^3->real->A`; `sigma':real^3->real->A`]
                SMO_SUSP_HOMOTOPY) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[CMW_ENDP_ALT]) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS) THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `&3:int` o MATCH_MP HOMOLOGY_HOMOTOPY_EMPTY) THEN
  ASM_REWRITE_TAC[p4_essential]);;

(* Essentiality depends only on the values on S^3.                            *)

let CMW_ESSENTIAL_EQ = prove
 (`!top (f:real^4->A) g.
        (!x. x IN sphere(vec 0,&1) ==> f x = g x)
        ==> (p4_essential top f <=> p4_essential top g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_essential] THEN
  SUBGOAL_THEN
   `!x. x IN topspace(subtopology euclidean (sphere(vec 0:real^4,&1)))
        ==> (f:real^4->A) x = (g:real^4->A) x`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`&3:int`; `subtopology euclidean (sphere(vec 0:real^4,&1))`;
                 `{}:real^4->bool`; `top:A topology`; `{}:A->bool`;
                 `f:real^4->A`; `g:real^4->A`] HOM_INDUCED_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (sphere(vec 0:real^4,&1)),top) (f:real^4->A) <=>
    continuous_map (subtopology euclidean (sphere(vec 0:real^4,&1)),top) g`
  (fun th -> REWRITE_TAC[th]) THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  ASM_MESON_TAC[]);;

(* Families with constant slices are inessential: their suspension factors  *)
(* through the interval, which is contractible.                              *)

let CMW_SUSP_CONST_SLICES = prove
 (`!(c:real->A) x. p4_susp (\y:real^3 t. c t) x = c((x$4 + &1) / &2)`,
  REWRITE_TAC[p4_susp; COND_ID]);;

let CMW_SUSP_SPT = prove
 (`!(sigma:real^3->real->A) y t.
        y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] /\
        (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                ==> sigma y (&0) = sigma y' (&0) /\ sigma y (&1) = sigma y' (&1))
        ==> p4_susp sigma (smo_spt y t) = sigma y t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SMO_P4_SUSP] THEN
  MP_TAC(ISPECL [`y:real^3`; `t:real`] SMO_DESUSP_SPT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `&0 < t /\ t < &1` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t = &0 \/ t = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `~(&0 < t /\ t < &1)` THEN UNDISCH_TAC `t IN real_interval[&0,&1]` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `t = &0 \/ t = &1`)]) THEN
  SUBGOAL_THEN `basis 1 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_MESON_TAC[]);;

let CMW_ESSENTIAL_CONST_SLICES = prove
 (`!top (c:real->A). ~p4_essential top (p4_susp (\y:real^3 t. c t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p4_essential] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (sphere(vec 0:real^4,&1)),
                    subtopology euclideanreal (real_interval[&0,&1]))
                   (\x:real^4. (x$4 + &1) / &2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_EUCLIDEAN_COMPONENT THEN
      REWRITE_TAC[CONTINUOUS_MAP_ID];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_SPHERE_0; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`x:real^4`; `4`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[DIMINDEX_4; ARITH] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`x:real^4`; `4`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[DIMINDEX_4; ARITH] THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top) (c:real->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `p4_susp (\y:real^3 t. (c:real->A) t) o (\t. smo_spt (basis 1) t)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; o_THM] THEN
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC(INST_TYPE [`:A`,`:A`] CMW_SUSP_SPT) THEN
      ASM_SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^4,&1))` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\t. smo_spt (basis 1) t) =
      (\z:real^3#real. smo_spt (FST z) (SND z)) o (\t. (basis 1:real^3,t))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC
     `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                    (subtopology euclideanreal (real_interval[&0,&1]))` THEN
    REWRITE_TAC[SMO_SPT_CONTINUOUS] THEN
    REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_CONST; CONTINUOUS_MAP_ID] THEN
    SIMP_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hom_induced (&3) (subtopology euclidean (sphere(vec 0:real^4,&1)),{}) (top,{})
                (p4_susp (\y:real^3 t. (c:real->A) t)) =
    hom_induced (&3) (subtopology euclideanreal (real_interval[&0,&1]),{}) (top,{}) c o
    hom_induced (&3) (subtopology euclidean (sphere(vec 0:real^4,&1)),{})
                     (subtopology euclideanreal (real_interval[&0,&1]),{})
                     (\x:real^4. (x$4 + &1) / &2)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&3:int`; `subtopology euclidean (sphere(vec 0:real^4,&1))`;
                   `subtopology euclideanreal (real_interval[&0,&1])`; `top:A topology`;
                   `\x:real^4. (x$4 + &1) / &2`; `c:real->A`]
                  HOM_INDUCED_COMPOSE_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC HOM_INDUCED_EQ THEN REWRITE_TAC[o_THM; CMW_SUSP_CONST_SLICES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `trivial_group(homology_group(&3,subtopology euclideanreal (real_interval[&0,&1])))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TRIVIAL_HOMOLOGY_GROUP_CONTRACTIBLE_SPACE THEN
    REWRITE_TAC[CONTRACTIBLE_SPACE_SUBTOPOLOGY_EUCLIDEANREAL; IS_REALINTERVAL_INTERVAL] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hom_induced (&3) (subtopology euclidean (sphere(vec 0:real^4,&1)),{})
                     (subtopology euclideanreal (real_interval[&0,&1]),{})
                     (\x:real^4. (x$4 + &1) / &2) z =
    group_id(homology_group(&3,subtopology euclideanreal (real_interval[&0,&1])))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&3:int`; `subtopology euclidean (sphere(vec 0:real^4,&1))`;
                   `subtopology euclideanreal (real_interval[&0,&1])`;
                   `\x:real^4. (x$4 + &1) / &2`] GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
    REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `z:((num->real)->real^4)frag->bool` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `trivial_group(homology_group(&3,subtopology euclideanreal (real_interval[&0,&1])))` THEN
    REWRITE_TAC[trivial_group] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  UNDISCH_TAC
   `~(hom_induced (&3) (subtopology euclidean (sphere(vec 0:real^4,&1)),{}) (top,{})
                  (p4_susp (\y:real^3 t. (c:real->A) t)) z =
      group_id(homology_group(&3,top)))` THEN
  ASM_REWRITE_TAC[o_THM] THEN
  MP_TAC(ISPECL [`&3:int`; `subtopology euclideanreal (real_interval[&0,&1])`;
                 `top:A topology`; `c:real->A`] GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
  SIMP_TAC[group_homomorphism]);;

(* ------------------------------------------------------------------------- *)
(* Reparametrization of the slices by a continuous family k of maps of S^2. *)
(* If sigma o k is essential, so is sigma (the induced map of S^3 factors).  *)
(* For bijective k t the inverse family is continuous (compactness), so the *)
(* two are equivalent.                                                       *)
(* ------------------------------------------------------------------------- *)

let CMW_SPT_QUOTIENT = prove
 (`quotient_map
     (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                    (subtopology euclideanreal (real_interval[&0,&1])),
      subtopology euclidean (sphere(vec 0:real^4,&1)))
     (\z. smo_spt (FST z) (SND z))`,
  MATCH_MP_TAC CONTINUOUS_IMP_QUOTIENT_MAP THEN REWRITE_TAC[SMO_SPT_CONTINUOUS] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPACT_SPACE_PROD_TOPOLOGY] THEN DISJ2_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL; COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE];
    MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_IMAGE; EXISTS_PAIR_THM; TOPSPACE_PROD_TOPOLOGY;
                IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; FST; SND] THEN
    X_GEN_TAC `x:real^4` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC[SMO_SPT_SPHERE];
      DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`FST(smo_desusp x)`; `SND(smo_desusp x)`] THEN
      ASM_SIMP_TAC[SMO_SPT_DESUSP]]]);;

let CMW_SPT_ENDS_EQ = prove
 (`!y y' t. (t = &0 \/ t = &1) ==> smo_spt y t = smo_spt y' t`,
  REPEAT GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[SMO_SPT_ENDS]);;

let CMW_REPARAM_MAP = prove
 (`!(k:real->real^3->real^3).
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),
           subtopology euclidean (sphere(vec 0:real^3,&1)))
          (\(y,t). k t y)
        ==> continuous_map (subtopology euclidean (sphere(vec 0:real^4,&1)),
                            subtopology euclidean (sphere(vec 0:real^4,&1)))
              (\x. smo_spt (k (SND(smo_desusp x)) (FST(smo_desusp x)))
                           (SND(smo_desusp x))) /\
            !y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                  ==> smo_spt (k (SND(smo_desusp(smo_spt y t)))
                                 (FST(smo_desusp(smo_spt y t))))
                              (SND(smo_desusp(smo_spt y t))) =
                      smo_spt (k t y) t`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
          ==> smo_spt ((k:real->real^3->real^3) (SND(smo_desusp(smo_spt y t)))
                         (FST(smo_desusp(smo_spt y t))))
                      (SND(smo_desusp(smo_spt y t))) =
              smo_spt (k t y) t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`y:real^3`; `t:real`] SMO_DESUSP_SPT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `&0 < t /\ t < &1` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CMW_SPT_ENDS_EQ THEN
    UNDISCH_TAC `~(&0 < t /\ t < &1)` THEN UNDISCH_TAC `t IN real_interval[&0,&1]` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(INST_TYPE [`:real^3#real`,`:A`; `:real^4`,`:B`; `:real^4`,`:C`]
                CONTINUOUS_COMPOSE_QUOTIENT_MAP) THEN
  EXISTS_TAC
   `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                  (subtopology euclideanreal (real_interval[&0,&1]))` THEN
  EXISTS_TAC `\z:real^3#real. smo_spt (FST z) (SND z)` THEN
  REWRITE_TAC[CMW_SPT_QUOTIENT] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC
   `(\z:real^3#real. smo_spt (FST z) (SND z)) o
    (\z:real^3#real. (k:real->real^3->real^3) (SND z) (FST z),SND z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM; IN_CROSS; o_THM;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC
   `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                  (subtopology euclideanreal (real_interval[&0,&1]))` THEN
  REWRITE_TAC[SMO_SPT_CONTINUOUS; CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_SND] THEN
  FIRST_X_ASSUM(K ALL_TAC) THEN
  FIRST_X_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let CMW_ESSENTIAL_REPARAM_IMP = prove
 (`!top (sigma:real^3->real->A) (k:real->real^3->real^3).
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),top)
          (\(y,t). sigma y t) /\
        (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                ==> sigma y (&0) = sigma y' (&0) /\ sigma y (&1) = sigma y' (&1)) /\
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),
           subtopology euclidean (sphere(vec 0:real^3,&1)))
          (\(y,t). k t y) /\
        p4_essential top (p4_susp (\y t. sigma (k t y) t))
        ==> p4_essential top (p4_susp sigma)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "k") MP_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMW_REPARAM_MAP) THEN
  ABBREV_TAC
   `km = \x. smo_spt ((k:real->real^3->real^3) (SND(smo_desusp x)) (FST(smo_desusp x)))
                     (SND(smo_desusp x))` THEN
  SUBGOAL_THEN
   `!x. x IN sphere(vec 0:real^4,&1)
        ==> p4_susp (\y t. (sigma:real^3->real->A) ((k:real->real^3->real^3) t y) t) x =
            (p4_susp sigma o km) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN
    MP_TAC(SPEC `x:real^4` SMO_SPT_DESUSP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `(sigma:real^3->real->A)
        ((k:real->real^3->real^3) (SND(smo_desusp x)) (FST(smo_desusp x)))
        (SND(smo_desusp x))` THEN
    CONJ_TAC THENL [REWRITE_TAC[SMO_P4_SUSP]; ALL_TAC] THEN
    EXPAND_TAC "km" THEN REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC(GSYM CMW_SUSP_SPT) THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "k" (MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM;
                IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (sphere(vec 0:real^4,&1)),top)
                   (p4_susp (sigma:real^3->real->A))`
  ASSUME_TAC THENL [MATCH_MP_TAC CMW_FAM_SUSP_CONT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `hom_induced (&3) (subtopology euclidean (sphere(vec 0:real^4,&1)),{}) (top,{})
                (p4_susp (\y t. (sigma:real^3->real->A) ((k:real->real^3->real^3) t y) t)) =
    hom_induced (&3) (subtopology euclidean (sphere(vec 0:real^4,&1)),{}) (top,{})
                (p4_susp sigma) o
    hom_induced (&3) (subtopology euclidean (sphere(vec 0:real^4,&1)),{})
                     (subtopology euclidean (sphere(vec 0:real^4,&1)),{}) km`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `hom_induced (&3) (subtopology euclidean (sphere(vec 0:real^4,&1)),{}) (top,{})
                  (p4_susp (sigma:real^3->real->A) o km)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOM_INDUCED_EQ THEN ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
      MATCH_MP_TAC HOM_INDUCED_COMPOSE_EMPTY THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p4_essential] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC
   `hom_induced (&3) (subtopology euclidean (sphere(vec 0:real^4,&1)),{})
                     (subtopology euclidean (sphere(vec 0:real^4,&1)),{}) km z` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`&3:int`; `subtopology euclidean (sphere(vec 0:real^4,&1))`;
                   `subtopology euclidean (sphere(vec 0:real^4,&1))`; `km:real^4->real^4`]
                  GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
    REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    UNDISCH_TAC
     `~(hom_induced (&3) (subtopology euclidean (sphere(vec 0:real^4,&1)),{}) (top,{})
                    (p4_susp (\y t. (sigma:real^3->real->A) ((k:real->real^3->real^3) t y) t))
                    z =
        group_id(homology_group(&3,top)))` THEN
    ASM_REWRITE_TAC[o_THM]]);;

(* ========================================================================= *)
(* Bijective reparametrizations, homotopies of embedded                      *)
(* sweepouts (cm_shomotopic) as homotopic_with, and the transfer to a        *)
(* component of the manifold.                                               *)
(* ========================================================================= *)

let CMW_S2I_COMPACT_HAUSDORFF = prove
 (`compact_space
     (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                    (subtopology euclideanreal (real_interval[&0,&1]))) /\
   hausdorff_space
     (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                    (subtopology euclideanreal (real_interval[&0,&1])))`,
  REWRITE_TAC[COMPACT_SPACE_PROD_TOPOLOGY; HAUSDORFF_SPACE_PROD_TOPOLOGY] THEN
  CONJ_TAC THEN DISJ2_TAC THEN CONJ_TAC THEN
  TRY(MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
      REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL; COMPACT_IN_EUCLIDEAN;
                  COMPACT_SPHERE] THEN NO_TAC) THEN
  MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
  REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEANREAL; HAUSDORFF_SPACE_EUCLIDEAN]);;

let CMW_PHI_HOMEO = prove
 (`!(k:real->real^3->real^3).
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),
           subtopology euclidean (sphere(vec 0:real^3,&1)))
          (\(y,t). k t y) /\
        (!t x. t IN real_interval[&0,&1] /\ x IN sphere(vec 0,&1)
               ==> ?!y. y IN sphere(vec 0,&1) /\ k t y = x)
        ==> homeomorphic_map
              (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                             (subtopology euclideanreal (real_interval[&0,&1])),
               prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                             (subtopology euclideanreal (real_interval[&0,&1])))
              (\z. k (SND z) (FST z),SND z)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c") (LABEL_TAC "b")) THEN
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
          ==> (k:real->real^3->real^3) t y IN sphere(vec 0,&1)`
  (LABEL_TAC "s") THENL
   [USE_THEN "c" (MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM;
                IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_HOMEOMORPHIC_MAP THEN
  REWRITE_TAC[CMW_S2I_COMPACT_HAUSDORFF] THEN
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_SND] THEN
    USE_THEN "c" MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM];
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real`] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC[]; STRIP_TAC] THEN
    USE_THEN "b" (MP_TAC o REWRITE_RULE[EXISTS_UNIQUE_THM] o
                  SPECL [`t:real`; `x:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    MAP_EVERY EXISTS_TAC [`y:real^3`; `t:real`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`y:real^3`; `t:real`; `y':real^3`; `t':real`] THEN
    STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN REWRITE_TAC[] THEN
    USE_THEN "b" (MP_TAC o REWRITE_RULE[EXISTS_UNIQUE_THM] o
                  SPECL [`t':real`; `(k:real->real^3->real^3) t' y`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]]);;

let CMW_INVERSE_FAMILY = prove
 (`!(k:real->real^3->real^3).
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),
           subtopology euclidean (sphere(vec 0:real^3,&1)))
          (\(y,t). k t y) /\
        (!t x. t IN real_interval[&0,&1] /\ x IN sphere(vec 0,&1)
               ==> ?!y. y IN sphere(vec 0,&1) /\ k t y = x)
        ==> ?kinv:real->real^3->real^3.
              continuous_map
                (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                               (subtopology euclideanreal (real_interval[&0,&1])),
                 subtopology euclidean (sphere(vec 0:real^3,&1)))
                (\(x,t). kinv t x) /\
              !x t. x IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                    ==> kinv t x IN sphere(vec 0,&1) /\ k t (kinv t x) = x`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CMW_PHI_HOMEO) THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; homeomorphic_maps] THEN
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3#real->real^3#real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\t x. FST((psi:real^3#real->real^3#real) (x,t))` THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\(x,t). (\t x. FST((psi:real^3#real->real^3#real) (x,t))) t x) = FST o psi`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC
     `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                    (subtopology euclideanreal (real_interval[&0,&1]))` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_FST];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real`] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `continuous_map
     (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                    (subtopology euclideanreal (real_interval[&0,&1])),
      prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                    (subtopology euclideanreal (real_interval[&0,&1])))
     (psi:real^3#real->real^3#real)` THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `t:real`]) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x:real^3,t:real)`) THEN
  ASM_REWRITE_TAC[IN_CROSS] THEN
  SPEC_TAC(`(psi:real^3#real->real^3#real) (x,t)`,`w:real^3#real`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; IN_CROSS] THEN MESON_TAC[]);;

let CMW_ESSENTIAL_REPARAM = prove
 (`!top (sigma:real^3->real->A) (k:real->real^3->real^3).
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),top)
          (\(y,t). sigma y t) /\
        (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                ==> sigma y (&0) = sigma y' (&0) /\ sigma y (&1) = sigma y' (&1)) /\
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),
           subtopology euclidean (sphere(vec 0:real^3,&1)))
          (\(y,t). k t y) /\
        (!t x. t IN real_interval[&0,&1] /\ x IN sphere(vec 0,&1)
               ==> ?!y. y IN sphere(vec 0,&1) /\ k t y = x)
        ==> (p4_essential top (p4_susp (\y t. sigma (k t y) t)) <=>
             p4_essential top (p4_susp sigma))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  EQ_TAC THENL [ASM_MESON_TAC[CMW_ESSENTIAL_REPARAM_IMP]; DISCH_TAC] THEN
  MP_TAC(SPEC `k:real->real^3->real^3` CMW_INVERSE_FAMILY) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kinv:real->real^3->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
          ==> (k:real->real^3->real^3) t y IN sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `continuous_map
       (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                      (subtopology euclideanreal (real_interval[&0,&1])),
        subtopology euclidean (sphere(vec 0:real^3,&1)))
       (\(y,t). (k:real->real^3->real^3) t y)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM;
                IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CMW_ESSENTIAL_REPARAM_IMP THEN
  EXISTS_TAC `kinv:real->real^3->real^3` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\(y,t). (sigma:real^3->real->A) ((k:real->real^3->real^3) t y) t) =
      (\(y,t). sigma y t) o (\z. k (SND z) (FST z),SND z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC
     `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                    (subtopology euclideanreal (real_interval[&0,&1]))` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_SND] THEN
    UNDISCH_TAC
     `continuous_map
       (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                      (subtopology euclideanreal (real_interval[&0,&1])),
        subtopology euclidean (sphere(vec 0:real^3,&1)))
       (\(y,t). (k:real->real^3->real^3) t y)` THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]`
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];
    UNDISCH_TAC `p4_essential top (p4_susp (sigma:real^3->real->A))` THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CMW_ESSENTIAL_EQ THEN
    X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN REWRITE_TAC[SMO_P4_SUSP] THEN
    MP_TAC(SPEC `x:real^4` SMO_SPT_DESUSP) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* cm_shomotopic as homotopic_with; the transfer of homotopies               *)
(* of embedded sweepouts to a component of the manifold; separation of the *)
(* image of a component.                                                    *)
(* ========================================================================= *)

let CMW_S2I_CONNECTED = prove
 (`connected_space
     (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
        (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                       (subtopology euclideanreal (real_interval[&0,&1]))))`,
  SUBGOAL_THEN `connected_space (subtopology euclideanreal (real_interval[&0,&1]))`
  ASSUME_TAC THENL
   [MP_TAC(CONJUNCT1 CONNECTED_IN_EUCLIDEANREAL_INTERVAL) THEN
    SIMP_TAC[connected_in];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_space (subtopology euclidean (sphere(vec 0:real^3,&1)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONNECTED_SPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    MATCH_MP_TAC CONNECTED_SPHERE THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CONNECTED_SPACE_PROD_TOPOLOGY]);;

let CMW_SHOMOTOPIC = prove
 (`!S (s1:real^3->real->real^K) s2.
        cm_shomotopic S s1 s2 <=>
        homotopic_with (\f. cmw_ins S f /\ cmw_endp f)
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
          (\(y,t). s1 y t) (\(y,t). s2 y t)`,
  REPEAT GEN_TAC THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) HOMOTOPIC_WITH (rand w))) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN BETA_TAC THEN BINOP_TAC THENL
     [MATCH_MP_TAC CMW_INS_EQ; MATCH_MP_TAC CMW_ENDP_EQ] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[cm_shomotopic; cmw_ins; cmw_endp; TOPSPACE_PROD_TOPOLOGY;
              FORALL_PAIR_THM; IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `H:real->real^3->real->real^K` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\(s,(y,t)). (H:real->real^3->real->real^K) s y t` THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `h:real#(real^3#real)->real^K` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\s y t. (h:real#(real^3#real)->real^K) (s,(y,t))` THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC
       `continuous_map
         (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
           (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                          (subtopology euclideanreal (real_interval[&0,&1]))),
          euclidean) (h:real#(real^3#real)->real^K)` THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM];
      ASM_MESON_TAC[]]]);;

let CMW_SHOMOTOPIC_SYM = prove
 (`!S (s1:real^3->real->real^K) s2.
        cm_shomotopic S s1 s2 <=> cm_shomotopic S s2 s1`,
  REWRITE_TAC[CMW_SHOMOTOPIC] THEN MESON_TAC[HOMOTOPIC_WITH_SYM]);;

let CMW_SHOMOTOPIC_TRANS = prove
 (`!S (s1:real^3->real->real^K) s2 s3.
        cm_shomotopic S s1 s2 /\ cm_shomotopic S s2 s3 ==> cm_shomotopic S s1 s3`,
  REWRITE_TAC[CMW_SHOMOTOPIC] THEN MESON_TAC[HOMOTOPIC_WITH_TRANS]);;

let CMW_SHOMOTOPIC_REFL = prove
 (`!S (s:real^3->real->real^K).
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
          (\(y,t). s y t) /\
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> s y t IN S) /\
        (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                ==> s y (&0) = s y' (&0) /\ s y (&1) = s y' (&1))
        ==> cm_shomotopic S s s`,
  REWRITE_TAC[CMW_SHOMOTOPIC; HOMOTOPIC_WITH_REFL; CMW_INS_PAIRED; CMW_ENDP_PAIRED]);;

let CMW_SWEEP_SHOMOTOPIC_REFL = prove
 (`!S (s:real^3->real->real^K). cm_sweep S s ==> cm_shomotopic S s s`,
  REWRITE_TAC[cm_sweep; cm_smap] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CMW_SHOMOTOPIC_REFL THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Components: open and closed; the image of a component is compact and at *)
(* positive distance from the image of the rest.                            *)
(* ------------------------------------------------------------------------- *)

let CMW_COMPONENT_CLOPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) U.
        smooth_manifold_atlas top atlas /\ U IN connected_components_of top
        ==> open_in top U /\ closed_in top U`,
  MESON_TAC[P4_COMPONENT_OPEN; CLOSED_IN_CONNECTED_COMPONENTS_OF]);;

let CMW_COMPONENT_IMAGE = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) G d U.
        cm_emb (top,atlas) g f G d /\ U IN connected_components_of top
        ==> compact(IMAGE f U) /\ IMAGE f U SUBSET IMAGE f (topspace top) /\
            ?r. &0 < r /\
                !z p. z IN IMAGE f (topspace top) /\ p IN IMAGE f U /\ dist(z,p) < r
                      ==> z IN IMAGE f U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`]
                CMW_COMPONENT_CLOPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (top,euclidean) (f:A->real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`] SMO_EMB_INV_CONTINUOUS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN topspace top /\ y IN topspace top /\ (f:A->real^K) x = f y ==> x = y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_embedding (top,atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)` THEN
    REWRITE_TAC[mfd_embedding; homeomorphic_map] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. closed_in top c ==> compact(IMAGE (f:A->real^K) c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:A->real^K) U`; `IMAGE (f:A->real^K) (topspace top DIFF U)`]
                SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`z:real^K`; `p:real^K`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM DE_MORGAN_THM] THEN
  ASM_CASES_TAC `(z:real^K) IN IMAGE f (U:A->bool)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:real^K) IN IMAGE f (topspace top DIFF (U:A->bool))` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^K`; `z:real^K`]) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC);;

(* The embedding inverse on the image.                                       *)

let CMW_EMB_INV_F = prove
 (`!top atlas (f:A->real^K) x.
        mfd_embedding (top,atlas:((A->bool)#(A->real^N))->bool) f /\ x IN topspace top
        ==> mfd_emb_inv top f (f x) = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_embedding; homeomorphic_map] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `f:A->real^K`; `(f:A->real^K) x`] CMT_EMB_INV_RIGHT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* Homotopies of embedded sweepouts inside f(M) that start in the image of *)
(* a component stay there and pull back to homotopies in the component.    *)

let CMW_EMB_HOMOTOPY = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) G d U W W'.
        cm_emb (top,atlas) g f G d /\ U IN connected_components_of top /\
        cm_shomotopic (IMAGE f (topspace top)) W W' /\
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> W y t IN IMAGE f U)
        ==> (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                   ==> W' y t IN IMAGE f U) /\
            homotopic_with cmw_endp
              (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                             (subtopology euclideanreal (real_interval[&0,&1])),
               subtopology top U)
              (\(y,t). mfd_emb_inv top f (W y t)) (\(y,t). mfd_emb_inv top f (W' y t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`]
                CMW_COMPONENT_CLOPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `f:A->real^K`]
                CMT_EMB_INV_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `cm_shomotopic (IMAGE (f:A->real^K) (topspace (top:A topology)))
                             (W:real^3->real->real^K) W'` THEN
  REWRITE_TAC[CMW_SHOMOTOPIC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) HOMOTOPIC_WITH (lhand w))) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN BETA_TAC THEN BINOP_TAC THENL
     [MATCH_MP_TAC CMW_INS_EQ; MATCH_MP_TAC CMW_ENDP_EQ] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[cmw_ins; TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; FORALL_PAIR_THM; IN_CROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real#(real^3#real)->real^K` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `kk = (mfd_emb_inv top (f:A->real^K)) o (h:real#(real^3#real)->real^K)` THEN
  ABBREV_TAC
   `TT = prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])))` THEN
  SUBGOAL_THEN
   `!z. z IN topspace TT <=>
        FST z IN real_interval[&0,&1] /\ FST(SND z) IN sphere(vec 0:real^3,&1) /\
        SND(SND z) IN real_interval[&0,&1]`
  ASSUME_TAC THENL
   [EXPAND_TAC "TT" THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; FORALL_PAIR_THM; IN_CROSS];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (TT,top) (kk:real#(real^3#real)->A)` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (f:A->real^K) (topspace top))` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    EXPAND_TAC "TT" THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; FORALL_PAIR_THM; IN_CROSS] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
          ==> (kk:real#(real^3#real)->A) (&0,(y,t)) IN U`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "kk" THEN REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `t:real`] o
      check (fun th -> can (find_term ((=) `W:real^3->real->real^K`)) (concl th) &&
                       can (find_term ((=) `U:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `x:A`] CMW_EMB_INV_F) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN topspace TT ==> (kk:real#(real^3#real)->A) z IN U`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `connected_space (TT:(real#(real^3#real))topology)` MP_TAC THENL
     [EXPAND_TAC "TT" THEN REWRITE_TAC[CMW_S2I_CONNECTED];
      REWRITE_TAC[CONNECTED_SPACE_CLOPEN_IN]] THEN
    DISCH_THEN(MP_TAC o SPEC
     `{z | z IN topspace TT /\ (kk:real#(real^3#real)->A) z IN U}`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE;
        MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE] THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `(&0,(basis 1:real^3,&0))`) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `basis 1 IN sphere(vec 0:real^3,&1) /\ &0 IN real_interval[&0,&1]`
      STRIP_ASSUME_TAC THENL
       [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH; IN_REAL_INTERVAL] THEN
        REAL_ARITH_TAC;
        ASM_SIMP_TAC[]];
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^3`; `t:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(kk:real#(real^3#real)->A) (&1,(y,t)) IN U` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "kk" THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN
     `(h:real#(real^3#real)->real^K) (&1,(y,t)) = W' y t /\
      W' y t IN IMAGE (f:A->real^K) (topspace (top:A topology))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&1` o
        check (fun th -> can (find_term (fun u -> is_const u && fst(dest_const u) = "cmw_endp")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `t:real`] o CONJUNCT1) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CMT_EMB_INV_RIGHT) THEN SET_TAC[];
    ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) HOMOTOPIC_WITH w)) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMW_ENDP_EQ THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  EXISTS_TAC `kk:real#(real^3#real)->A` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; FORALL_PAIR_THM; IN_CROSS] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "kk" THEN ASM_SIMP_TAC[o_THM];
    EXPAND_TAC "kk" THEN ASM_SIMP_TAC[o_THM];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[cmw_endp] THEN
    EXPAND_TAC "kk" THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o
      check (fun th -> can (find_term (fun u -> is_const u && fst(dest_const u) = "cmw_endp")) (concl th))) THEN
    ASM_REWRITE_TAC[cmw_endp] THEN MESON_TAC[]]);;

let CMW_ESSENTIAL_SLICES_EQ = prove
 (`!top (sigma:real^3->real->A) sigma'.
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
               ==> sigma y t = sigma' y t)
        ==> (p4_essential top (p4_susp sigma) <=> p4_essential top (p4_susp sigma'))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMW_ESSENTIAL_EQ THEN
  X_GEN_TAC `x:real^4` THEN DISCH_TAC THEN REWRITE_TAC[SMO_P4_SUSP] THEN
  MP_TAC(SPEC `x:real^4` SMO_SPT_DESUSP) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let CMW_EMB_ESSENTIAL_HOMOTOPIC = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) G d U W W'.
        cm_emb (top,atlas) g f G d /\ U IN connected_components_of top /\
        cm_shomotopic (IMAGE f (topspace top)) W W' /\
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> W y t IN IMAGE f U)
        ==> (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                   ==> W' y t IN IMAGE f U) /\
            (p4_essential (subtopology top U)
               (p4_susp (\y t. mfd_emb_inv top f (W y t))) <=>
             p4_essential (subtopology top U)
               (p4_susp (\y t. mfd_emb_inv top f (W' y t))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CMW_EMB_HOMOTOPY) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology (top:A topology) U`;
                 `\y t. mfd_emb_inv (top:A topology) (f:A->real^K)
                          ((W:real^3->real->real^K) y t)`;
                 `\y t. mfd_emb_inv (top:A topology) (f:A->real^K)
                          ((W':real^3->real->real^K) y t)`]
                CMW_ESSENTIAL_HOMOTOPIC) THEN
  ASM_REWRITE_TAC[]);;

(* A sweepout of the manifold and its embedded copy f o sigma.               *)

let CMW_EMB_SELF = prove
 (`!top atlas (f:A->real^K) (sigma:real^3->real->A) U.
        mfd_embedding (top,atlas:((A->bool)#(A->real^N))->bool) f /\
        U SUBSET topspace top /\
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> sigma y t IN U)
        ==> (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                   ==> f(sigma y t) IN IMAGE f U /\
                       mfd_emb_inv top f (f(sigma y t)) = sigma y t) /\
            (p4_essential (subtopology top U)
               (p4_susp (\y t. mfd_emb_inv top f (f(sigma y t)))) <=>
             p4_essential (subtopology top U) (p4_susp sigma))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
          ==> (f:A->real^K)((sigma:real^3->real->A) y t) IN IMAGE f U /\
              mfd_emb_inv top f (f(sigma y t)) = sigma y t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CMW_EMB_INV_F THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMW_ESSENTIAL_SLICES_EQ THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Uniformly close sweepouts in the target are homotopic, by                 *)
(* the straight-line homotopy followed by the nearest-point projection.     *)
(* ========================================================================= *)

let CMW_TUBE_CLOSEST_CONTINUOUS = prove
 (`!S (G:real^K->real^K^K) d.
        cm_target S G d
        ==> continuous_map (subtopology euclidean (cm_tube S d),euclidean)
                           (closest_point S) /\
            (!z. z IN cm_tube S d ==> closest_point S z IN S) /\
            (!z. z IN S ==> z IN cm_tube S d /\ closest_point S z = z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_target] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o REWRITE_RULE[smooth_map_on] o
      check (fun th -> can (find_term ((=) `cm_tube (S:real^K->bool) d`)) (concl th) &&
                       can (find_term (fun u -> is_const u &&
                                         fst(dest_const u) = "smooth_map_on")) (concl th))) THEN
    REWRITE_TAC[continuously_differentiable];
    X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN ASM_SIMP_TAC[CLOSEST_POINT_SELF] THEN
    REWRITE_TAC[cm_tube; IN_ELIM_THM] THEN EXISTS_TAC `z:real^K` THEN
    ASM_REWRITE_TAC[DIST_REFL]]);;

let CMW_CLOSE_SHOMOTOPIC = prove
 (`!S (G:real^K->real^K^K) d (W1:real^3->real->real^K) W2.
        cm_target S G d /\
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
          (\(y,t). W1 y t) /\
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
          (\(y,t). W2 y t) /\
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
               ==> W1 y t IN S /\ W2 y t IN S /\ norm(W1 y t - W2 y t) < d) /\
        (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                ==> W1 y (&0) = W1 y' (&0) /\ W1 y (&1) = W1 y' (&1)) /\
        (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                ==> W2 y (&0) = W2 y' (&0) /\ W2 y (&1) = W2 y' (&1))
        ==> cm_shomotopic S W1 W2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tg") STRIP_ASSUME_TAC) THEN
  USE_THEN "tg" (STRIP_ASSUME_TAC o MATCH_MP CMW_TUBE_CLOSEST_CONTINUOUS) THEN
  REWRITE_TAC[CMW_SHOMOTOPIC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) HOMOTOPIC_WITH w)) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN BETA_TAC THEN BINOP_TAC THENL
     [MATCH_MP_TAC CMW_INS_EQ; MATCH_MP_TAC CMW_ENDP_EQ] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  EXISTS_TAC
   `\z:real#(real^3#real).
      closest_point S ((&1 - FST z) % (W1:real^3->real->real^K) (FST(SND z)) (SND(SND z)) +
                       FST z % (W2:real^3->real->real^K) (FST(SND z)) (SND(SND z)))` THEN
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; FORALL_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[cmw_ins; cmw_endp] THEN
  SUBGOAL_THEN
   `!s y t. s IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) /\
            t IN real_interval[&0,&1]
            ==> (&1 - s) % (W1:real^3->real->real^K) y t + s % W2 y t IN cm_tube S d`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[cm_tube; IN_ELIM_THM] THEN
    EXISTS_TAC `(W1:real^3->real->real^K) y t` THEN ASM_SIMP_TAC[dist] THEN
    SUBGOAL_THEN
     `((&1 - s) % (W1:real^3->real->real^K) y t + s % W2 y t) - W1 y t =
      s % (W2 y t - W1 y t)` SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL] THEN
    TRANS_TAC REAL_LET_TRANS `norm((W2:real^3->real->real^K) y t - W1 y t)` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      UNDISCH_TAC `s IN real_interval[&0,&1]` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_MAP_COMPOSE) THEN
    EXISTS_TAC `subtopology euclidean (cm_tube S d:real^K->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
        EXISTS_TAC `real_interval[&0,&1]` THEN REWRITE_TAC[CONTINUOUS_MAP_FST];
        SUBGOAL_THEN
         `(\z:real#(real^3#real). (W1:real^3->real->real^K) (FST(SND z)) (SND(SND z))) =
          (\(y,t). W1 y t) o SND` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
        EXISTS_TAC
         `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                        (subtopology euclideanreal (real_interval[&0,&1]))` THEN
        ASM_REWRITE_TAC[CONTINUOUS_MAP_SND];
        MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
        EXISTS_TAC `real_interval[&0,&1]` THEN REWRITE_TAC[CONTINUOUS_MAP_FST];
        SUBGOAL_THEN
         `(\z:real#(real^3#real). (W2:real^3->real->real^K) (FST(SND z)) (SND(SND z))) =
          (\(y,t). W2 y t) o SND` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
        EXISTS_TAC
         `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                        (subtopology euclideanreal (real_interval[&0,&1]))` THEN
        ASM_REWRITE_TAC[CONTINUOUS_MAP_SND]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM;
                  IN_CROSS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[]]]);;

(* ========================================================================= *)
(* Slices of jointly C^1 maps on (R^3 - 0) x [0,1].                          *)
(* ========================================================================= *)

let CMW_CD1 = prove
 (`!s (f:real^M->real^N).
        continuously_differentiable 1 s f <=>
        ?f'. (!x. x IN s ==> (f has_derivative f' x) (at x within s)) /\
             !h. (\x. f' x h) continuous_on s`,
  REWRITE_TAC[ONE; continuously_differentiable]);;

let CMW_C1_SLICE = prove
 (`!(FF:real^(3,1)finite_sum->real^K) t.
        continuously_differentiable 1
          {x:real^(3,1)finite_sum |
             ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]} FF /\
        t IN real_interval[&0,&1]
        ==> continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
              (\z. FF(pastecart z (lift t)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CMW_CD1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `FD:real^(3,1)finite_sum->real^(3,1)finite_sum->real^K`
    STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `ss = {x:real^(3,1)finite_sum |
            ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}` THEN
  SUBGOAL_THEN
   `!z:real^3. ~(z = vec 0) ==> pastecart z (lift t) IN ss`
  ASSUME_TAC THENL
   [EXPAND_TAC "ss" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  EXISTS_TAC
   `\z:real^3 h:real^3.
      (FD:real^(3,1)finite_sum->real^(3,1)finite_sum->real^K)
        (pastecart z (lift t)) (pastecart h (vec 0))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\z:real^3. (FF:real^(3,1)finite_sum->real^K) (pastecart z (lift t))) =
      FF o (\z. pastecart z (lift t))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h:real^3. (FD:real^(3,1)finite_sum->real^(3,1)finite_sum->real^K)
                    (pastecart z (lift t)) (pastecart h (vec 0))) =
      FD (pastecart z (lift t)) o (\h. pastecart h (vec 0))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN BETA_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
      MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `ss:real^(3,1)finite_sum->bool` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o
          check (fun th -> can (find_term ((=) `FD:real^(3,1)finite_sum->real^(3,1)finite_sum->real^K`)) (concl th) && is_forall(concl th) &&
                           can (find_term (fun u -> is_const u && fst(dest_const u) = "has_derivative")) (concl th))) THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_SIMP_TAC[]]];
    X_GEN_TAC `h:real^3` THEN BETA_TAC THEN
    SUBGOAL_THEN
     `(\z:real^3. (FD:real^(3,1)finite_sum->real^(3,1)finite_sum->real^K)
                    (pastecart z (lift t)) (pastecart h (vec 0))) =
      (\x. FD x (pastecart h (vec 0))) o (\z. pastecart z (lift t))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ss:real^(3,1)finite_sum->bool` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `pastecart h (vec 0):real^(3,1)finite_sum` o
          check (fun th -> can (find_term ((=) `FD:real^(3,1)finite_sum->real^(3,1)finite_sum->real^K`)) (concl th) && is_forall(concl th) &&
                           can (find_term (fun u -> is_const u && fst(dest_const u) = "continuous_on")) (concl th))) THEN
        REWRITE_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_SIMP_TAC[]]]]);;

let CMW_SWEEP_C1_SLICE = prove
 (`!(W:real^3->real->real^K) t.
        continuously_differentiable 1
          {x:real^(3,1)finite_sum |
             ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
          (\x. W (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))) /\
        t IN real_interval[&0,&1]
        ==> continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
              (wan_rext (\y. W y t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^(3,1)finite_sum.
                    (W:real^3->real->real^K) (inv(norm(fstcart x)) % fstcart x)
                                             (drop(sndcart x))`; `t:real`]
                CMW_C1_SLICE) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; wan_rext]);;

(* ========================================================================= *)
(* Sequential criteria for continuity on S^2 x [0,1] and on                  *)
(* [0,1] x S^2 x [0,1] (the domains of sweepouts and of their homotopies).  *)
(* ========================================================================= *)

let CMW_LIM_COMPONENTS3 = prove
 (`!(x:num->real^(1,(3,1)finite_sum)finite_sum) a.
        (x --> a) sequentially
        ==> ((\n. lift(drop(fstcart(x n)))) --> lift(drop(fstcart a))) sequentially /\
            ((\n. fstcart(sndcart(x n))) --> fstcart(sndcart a)) sequentially /\
            ((\n. lift(drop(sndcart(sndcart(x n))))) --> lift(drop(sndcart(sndcart a))))
            sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN REPEAT CONJ_TAC THEN
  REPEAT(MATCH_MP_TAC LIM_LINEAR THEN
         REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART] THEN
         TRY(FIRST_ASSUM ACCEPT_TAC)) THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  REPEAT(MATCH_MP_TAC LIM_LINEAR THEN
         REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART] THEN
         TRY(FIRST_ASSUM ACCEPT_TAC)));;

let CMW_PROD3_SEQ_CONT = prove
 (`!H:real#(real^3#real)->real^K.
        (!s y t (sn:num->real) (yn:num->real^3) (tn:num->real).
            s IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) /\
            t IN real_interval[&0,&1] /\
            (!n. sn n IN real_interval[&0,&1] /\ yn n IN sphere(vec 0,&1) /\
                 tn n IN real_interval[&0,&1]) /\
            ((\n. lift(sn n)) --> lift s) sequentially /\ (yn --> y) sequentially /\
            ((\n. lift(tn n)) --> lift t) sequentially
            ==> ((\n. H(sn n,(yn n,tn n))) --> H(s,(y,t))) sequentially)
        ==> continuous_map
              (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                 (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                                (subtopology euclideanreal (real_interval[&0,&1]))),
               euclidean) H`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC
   `E = {x:real^(1,(3,1)finite_sum)finite_sum |
           drop(fstcart x) IN real_interval[&0,&1] /\
           fstcart(sndcart x) IN sphere(vec 0,&1) /\
           drop(sndcart(sndcart x)) IN real_interval[&0,&1]}` THEN
  SUBGOAL_THEN
   `(\x:real^(1,(3,1)finite_sum)finite_sum.
       (H:real#(real^3#real)->real^K)
         (drop(fstcart x),(fstcart(sndcart x),drop(sndcart(sndcart x)))))
    continuous_on E`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY; o_DEF] THEN
    MAP_EVERY X_GEN_TAC [`x:num->real^(1,(3,1)finite_sum)finite_sum`;
                         `a:real^(1,(3,1)finite_sum)finite_sum`] THEN
    EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`drop(fstcart(a:real^(1,(3,1)finite_sum)finite_sum))`;
      `fstcart(sndcart(a:real^(1,(3,1)finite_sum)finite_sum))`;
      `drop(sndcart(sndcart(a:real^(1,(3,1)finite_sum)finite_sum)))`;
      `\n. drop(fstcart((x:num->real^(1,(3,1)finite_sum)finite_sum) n))`;
      `\n. fstcart(sndcart((x:num->real^(1,(3,1)finite_sum)finite_sum) n))`;
      `\n. drop(sndcart(sndcart((x:num->real^(1,(3,1)finite_sum)finite_sum) n)))`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`x:num->real^(1,(3,1)finite_sum)finite_sum`;
                   `a:real^(1,(3,1)finite_sum)finite_sum`] CMW_LIM_COMPONENTS3) THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC
   `(\x:real^(1,(3,1)finite_sum)finite_sum.
       (H:real#(real^3#real)->real^K)
         (drop(fstcart x),(fstcart(sndcart x),drop(sndcart(sndcart x))))) o
    (\z:real#(real^3#real). pastecart (lift(FST z)) (pastecart (FST(SND z)) (lift(SND(SND z)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (E:real^(1,(3,1)finite_sum)finite_sum->bool)` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "E" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM; IN_CROSS;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `(\z:real#(real^3#real). pastecart (lift(FST z)) (pastecart (FST(SND z)) (lift(SND(SND z))))) =
    (\(a,b). pastecart a b) o
    (\z. lift(FST z),((\(a,b). pastecart a b) o (\w. FST w,lift(SND w))) (SND z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (euclidean:(real^1)topology)
                            (euclidean:(real^(3,1)finite_sum)topology)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_PASTECART; CONTINUOUS_MAP_PAIRED] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `euclideanreal` THEN REWRITE_TAC[CONTINUOUS_MAP_LIFT] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN REWRITE_TAC[CONTINUOUS_MAP_FST];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                            (subtopology euclideanreal (real_interval[&0,&1]))` THEN
  REWRITE_TAC[CONTINUOUS_MAP_SND] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (euclidean:(real^3)topology) (euclidean:(real^1)topology)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_PASTECART; CONTINUOUS_MAP_PAIRED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN REWRITE_TAC[CONTINUOUS_MAP_FST];
    GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `euclideanreal` THEN REWRITE_TAC[CONTINUOUS_MAP_LIFT] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN REWRITE_TAC[CONTINUOUS_MAP_SND]]);;

