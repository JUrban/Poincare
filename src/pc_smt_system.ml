(* ========================================================================= *)
(* pc_smt_system: M11, the endgame sphere system RFS_SPHERE_SYSTEM_STATEMENT *)
(* (pc_rfs_top): a smooth 3-manifold X whose components are simply          *)
(* connected, cut along finitely many disjoint neck spheres and capped to   *)
(* Z (mfd_cut_cap); if every component of Z is S^3 then so is every         *)
(* component of X (Morgan-Tian, Corollary 15.4 (2) and Section 18.1).       *)
(* Induction on the number of necks (MSY_SYSTEM): a leaf side D of a neck   *)
(* i0 meets no other neck (LSP_LEAF, pc_smt_leafsep); after reflecting the  *)
(* neck, D is the inner side (MSY_LEAF_INNER); ff(D) plus the cap cm i0 is  *)
(* a component Zc of Z (MSY_ZC), hence S^3, so D is a ball of X             *)
(* (MSY_LEAF_BALL: SMT_SPHERE_SUM_INNER, SMT_CAP_BALL_CHART); the cut data  *)
(* of X with the neck i0 removed map onto Z minus Zc, with ff glued to      *)
(* cp i0 o b^-1 across the ball (MSY_NEW_DIFFEO, MSY_NEW_CUT); the empty    *)
(* cut is a diffeomorphism of the whole spaces (MSY_S3_DIFFEO).             *)
(*                                                                           *)
(* The reflection of a neck.                                                *)
(* ========================================================================= *)

needs "src/pc_rfs_top.ml";;
needs "src/pc_apx_event.ml";;
needs "src/pc_smt_disc.ml";;
needs "src/pc_smt_leafsep.ml";;
needs "src/pc_rfs_assembly.ml";;

prioritize_real();;
type_invention_error := true;;

(* Reflecting a neck chart through the unit sphere.                         *)

let MSY_INV_IMAGE = prove
 (`!r1 r2. &0 < r1 /\ r1 <= r2
           ==> IMAGE (\x:real^3. inv(norm x pow 2) % x) (annulus r1 r2) =
               annulus (inv r2) (inv r1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r1:real`; `r2:real`] (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_INVERSION_ANNULUS)) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN SIMP_TAC[]);;

let MSY_NECK_REFLECT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) e.
        smooth_manifold_atlas top atlas /\ mfd_neck_chart top atlas e
        ==> mfd_neck_chart top atlas (\x. e(inv(norm x pow 2) % x)) /\
            IMAGE (\x. e(inv(norm x pow 2) % x)) (annulus (&1 / &2) (&2)) =
            IMAGE e (annulus (&1 / &2) (&2)) /\
            IMAGE (\x. e(inv(norm x pow 2) % x)) (sphere(vec 0,&1)) =
            IMAGE e (sphere(vec 0,&1)) /\
            IMAGE (\x. e(inv(norm x pow 2) % x)) (annulus (&1 / &2) (&1)) =
            IMAGE e (annulus (&1) (&2)) /\
            IMAGE (\x. e(inv(norm x pow 2) % x)) (annulus (&1) (&2)) =
            IMAGE e (annulus (&1 / &2) (&1)) /\
            (\x. e(inv(norm x pow 2) % x)) (&3 / &4 % basis 1) = e(&4 / &3 % basis 1) /\
            (!x. ~(x = vec 0)
                 ==> (\x. e(inv(norm x pow 2) % x)) (inv(norm x pow 2) % x) = e x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_neck_chart] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^3. (e:real^3->A)(inv(norm x pow 2) % x)) =
                e o (\x. inv(norm x pow 2) % x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o; o_THM] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^3. inv(norm x pow 2) % x) (annulus (&1 / &2) (&2)) =
      annulus (&1 / &2) (&2) /\
    IMAGE (\x:real^3. inv(norm x pow 2) % x) (annulus (&1 / &2) (&1)) = annulus (&1) (&2) /\
    IMAGE (\x:real^3. inv(norm x pow 2) % x) (annulus (&1) (&2)) = annulus (&1 / &2) (&1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`&1 / &2`; `&2`] MSY_INV_IMAGE);
      MP_TAC(SPECL [`&1 / &2`; `&1`] MSY_INV_IMAGE);
      MP_TAC(SPECL [`&1`; `&2`] MSY_INV_IMAGE)] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. ~(x = vec 0)
                           ==> inv(norm(inv(norm x pow 2) % x) pow 2) %
                               (inv(norm x pow 2) % x) = x /\
                               norm(inv(norm x pow 2) % x) = inv(norm x)`
  ASSUME_TAC THENL
   [SIMP_TAC[SMT_INVERSION_INVOLUTION; SMT_INVERSION_NORM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`annulus (&1 / &2) (&2):real^3->bool`;
                          `annulus (&1 / &2) (&2):real^3->bool`;
                          `\x:real^3. inv(norm x pow 2) % x`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MP_TAC(ISPECL [`&1 / &2`; `&2`] (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_INVERSION_ANNULUS)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `norm(x:real^3) = &1` THEN
        ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_INV_1; REAL_POW_ONE; VECTOR_MUL_LID]];
      DISCH_TAC THEN EXISTS_TAC `inv(norm y pow 2) % (y:real^3)` THEN
      SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `norm(y:real^3) = &1` THEN
        ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_INV_1; REAL_POW_ONE; VECTOR_MUL_LID]]];
    AP_TERM_TAC THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[]]);;

(* Reflecting the neck i0 of a cut and swapping its caps.                    *)

let MSY_CUT_REFLECT = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topZ (atlasZ:((B->bool)#(B->real^3))->bool) J e cp cm ff gg i0.
        smooth_manifold_atlas topX atlasX /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm ff gg /\ i0 IN J
        ==> mfd_cut_cap topX atlasX topZ atlasZ J
              (\i. if i = i0 then (\x. e i0 (inv(norm x pow 2) % x)) else e i)
              (\i. if i = i0 then cm i0 else cp i)
              (\i. if i = i0 then cp i0 else cm i) ff gg`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_cut_cap] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "charts")
     (CONJUNCTS_THEN2 (LABEL_TAC "ndisj") (CONJUNCTS_THEN2 (LABEL_TAC "bdisj")
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cout")
     (LABEL_TAC "cin"))))))) ASSUME_TAC)) THEN
  USE_THEN "charts" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(i0:num) IN J`))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `(e:num->real^3->A) i0`] MSY_NECK_REFLECT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i IN J
        ==> IMAGE (if i = i0 then (\x. (e:num->real^3->A) i0 (inv(norm x pow 2) % x))
                   else e i) (annulus (&1 / &2) (&2)) =
            IMAGE (e i) (annulus (&1 / &2) (&2))`
  (LABEL_TAC "nimg") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x:real^3. x IN annulus (&1) (&2) ==> inv(norm x pow 2) % x IN annulus (&1 / &2) (&1)) /\
    (!x:real^3. x IN annulus (&1 / &2) (&1) ==> inv(norm x pow 2) % x IN annulus (&1) (&2)) /\
    (!x:real^3. x IN annulus (&1 / &2) (&2)
                ==> ~(x = vec 0) /\
                    inv(norm(inv(norm x pow 2) % x) pow 2) % (inv(norm x pow 2) % x) = x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THENL
     [MP_TAC(SPECL [`&1`; `&2`] MSY_INV_IMAGE);
      MP_TAC(SPECL [`&1 / &2`; `&1`] MSY_INV_IMAGE);
      ALL_TAC] THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
      CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `(x:real^3) IN annulus (&1 / &2) (&2)` THEN
        ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_0] THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[SMT_INVERSION_INVOLUTION]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_cut_spheres J
      (\i. if i = i0 then (\x. (e:num->real^3->A) i0 (inv(norm x pow 2) % x)) else e i) =
    mfd_cut_spheres J e /\
    mfd_cut_cores J (\i. if i = i0 then (cm:num->real^3->B) i0 else cp i)
                    (\i. if i = i0 then cp i0 else cm i) =
    mfd_cut_cores J cp cm`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[mfd_cut_spheres] THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `s:A->bool` THEN
      EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[EXTENSION; IN_MFD_CUT_CORES] THEN X_GEN_TAC `p:B` THEN
      EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `x:real^3`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`i:num`; `x:real^3`] THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i:num = i0` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        concl th = `i:num = i0`)) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "charts" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    USE_THEN "nimg" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(i:num) IN J`)]) THEN
    USE_THEN "nimg" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(j:num) IN J`)]) THEN
    USE_THEN "ndisj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!a b. a IN J /\ b IN J
            ==> DISJOINT (IMAGE ((cp:num->real^3->B) a) (ball(vec 0,&2)))
                         (IMAGE ((cm:num->real^3->B) b) (ball(vec 0,&2))) /\
                DISJOINT (IMAGE (cm b) (ball(vec 0,&2))) (IMAGE (cp a) (ball(vec 0,&2)))`
    (LABEL_TAC "pm") THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      USE_THEN "bdisj" (MP_TAC o SPECL [`a:num`; `b:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[DISJOINT_SYM]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!a b. a IN J /\ b IN J /\ ~(a = b)
            ==> DISJOINT (IMAGE ((cp:num->real^3->B) a) (ball(vec 0,&2)))
                         (IMAGE (cp b) (ball(vec 0,&2))) /\
                DISJOINT (IMAGE ((cm:num->real^3->B) a) (ball(vec 0,&2)))
                         (IMAGE (cm b) (ball(vec 0,&2)))`
    (LABEL_TAC "pp") THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      USE_THEN "bdisj" (MP_TAC o SPECL [`a:num`; `b:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `i:num = i0` THEN ASM_CASES_TAC `j:num = i0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY DISCH_TAC THEN
    REPEAT CONJ_TAC THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `x:real^3`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "cin" (MP_TAC o SPECL [`i0:num`; `inv(norm x pow 2) % (x:real^3)`]) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC SMT_INVERSION_INVOLUTION THEN
      DISCH_TAC THEN UNDISCH_TAC `(x:real^3) IN annulus (&1) (&2)` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_0] THEN REAL_ARITH_TAC;
      USE_THEN "cout" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`i:num`; `x:real^3`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "cout" (MP_TAC o SPECL [`i0:num`; `inv(norm x pow 2) % (x:real^3)`]) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
      USE_THEN "cin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The cut map and the leaf component.  ff is a diffeomorphism               *)
(* of X minus the spheres onto Z minus the cores; the image of the leaf      *)
(* side D together with the cap cm i0 is a component Zc of Z containing no  *)
(* other cap.                                                                *)
(* ------------------------------------------------------------------------- *)

let MSY_CUT_BASIC = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topZ (atlasZ:((B->bool)#(B->real^3))->bool) J e cp cm ff gg.
        hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\
        hausdorff_space topZ /\ smooth_manifold_atlas topZ atlasZ /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm ff gg
        ==> open_in topX (topspace topX DIFF mfd_cut_spheres J e) /\
            open_in topZ (topspace topZ DIFF mfd_cut_cores J cp cm) /\
            (!x. x IN topspace topX DIFF mfd_cut_spheres J e
                 ==> ff x IN topspace topZ DIFF mfd_cut_cores J cp cm /\ gg(ff x) = x) /\
            (!z. z IN topspace topZ DIFF mfd_cut_cores J cp cm
                 ==> gg z IN topspace topX DIFF mfd_cut_spheres J e /\ ff(gg z) = z) /\
            (!U. open_in topX U /\ U SUBSET topspace topX DIFF mfd_cut_spheres J e
                 ==> open_in topZ (IMAGE ff U)) /\
            (!U. connected_in topX U /\ U SUBSET topspace topX DIFF mfd_cut_spheres J e
                 ==> connected_in topZ (IMAGE ff U)) /\
            (!i. i IN J
                 ==> IMAGE (e i) (annulus (&1 / &2) (&1)) SUBSET
                     topspace topX DIFF mfd_cut_spheres J e /\
                     IMAGE (e i) (annulus (&1) (&2)) SUBSET
                     topspace topX DIFF mfd_cut_spheres J e) /\
            (!i. i IN J
                 ==> IMAGE (cp i) (cball(vec 0,&1)) SUBSET mfd_cut_cores J cp cm /\
                     IMAGE (cm i) (cball(vec 0,&1)) SUBSET mfd_cut_cores J cp cm)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_cut_cap]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_MAPS o check (fun th ->
    can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_diffeo")) (concl th))) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo] o check (fun th ->
    can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_diffeo")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (ff:A->B) (topspace topX DIFF mfd_cut_spheres J e) SUBSET
                   topspace topZ DIFF mfd_cut_cores J cp cm` THEN
      UNDISCH_TAC `(x:A) IN topspace topX DIFF mfd_cut_spheres J e` THEN SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:B` THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (gg:B->A) (topspace topZ DIFF mfd_cut_cores J cp cm) SUBSET
                   topspace topX DIFF mfd_cut_spheres J e` THEN
      UNDISCH_TAC `(z:B) IN topspace topZ DIFF mfd_cut_cores J cp cm` THEN SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `U:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)`;
                   `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                   `topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm`;
                   `ff:A->B`; `gg:B->A`; `U:A->bool`] MFD_DIFFEO_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[mfd_diffeo];
    X_GEN_TAC `U:A->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology topX (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A))` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `mfd_neck_chart topX atlasX ((e:num->real^3->A) i)` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_neck_chart"))
            (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `(e:num->real^3->A) i`] LSP_NECK_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `mfd_neck_chart topX (atlasX:((A->bool)#(A->real^3))->bool) (e(i:num))` THEN
    REWRITE_TAC[mfd_neck_chart] THEN DISCH_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    SUBGOAL_THEN
     `!y. y IN annulus (&1 / &2) (&2) /\ ~(norm y = &1)
          ==> (e:num->real^3->A) i y IN topspace topX DIFF mfd_cut_spheres J e`
    ASSUME_TAC THENL
     [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      REWRITE_TAC[IN_DIFF; IN_MFD_CUT_SPHERES; NOT_EXISTS_THM] THEN CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)) SUBSET
                     topspace topX` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        MAP_EVERY X_GEN_TAC [`j:num`; `u:real^3`] THEN STRIP_TAC THEN
        ASM_CASES_TAC `j:num = i` THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN
          SUBGOAL_THEN `(y:real^3) = u` (fun th -> ASM_MESON_TAC[th]) THEN
          FIRST_X_ASSUM(MP_TAC o AP_TERM `e':A->real^3`) THEN
          SUBGOAL_THEN `(u:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
           [ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ASM_SIMP_TAC[]];
          FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o check (fun th ->
            is_forall(concl th) &&
            can (find_term (fun u -> is_const u && fst(dest_const u) = "DISJOINT")) (concl th) &&
            can (find_term (fun u -> is_const u && fst(dest_const u) = "annulus")) (concl th))) THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `mfd_neck_chart topX atlasX ((e:num->real^3->A) j)` ASSUME_TAC THENL
           [FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
              can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_neck_chart"))
                  (concl th))) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
            ALL_TAC] THEN
          MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                         `(e:num->real^3->A) j`] LSP_NECK_FACTS) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
          REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
          DISCH_THEN(MP_TAC o SPEC `(e:num->real^3->A) i y`) THEN
          REWRITE_TAC[] THEN CONJ_TAC THENL
           [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
            ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
            ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC]]];
      ALL_TAC] THEN
    CONJ_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_MFD_CUT_CORES; IN_CBALL_0] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `x:real^3`] THEN ASM_REWRITE_TAC[]]);;

(* The leaf component.                                                       *)

let MSY_ZC = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topZ (atlasZ:((B->bool)#(B->real^3))->bool) J e cp cm ff gg i0 D Zc.
        hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\
        hausdorff_space topZ /\ smooth_manifold_atlas topZ atlasZ /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm ff gg /\ i0 IN J /\
        open_in topX D /\ connected_in topX D /\
        D SUBSET topspace topX DIFF IMAGE (e i0) (sphere(vec 0,&1)) /\
        open_in topX ((topspace topX DIFF IMAGE (e i0) (sphere(vec 0,&1))) DIFF D) /\
        IMAGE (e i0) (annulus (&1 / &2) (&1)) SUBSET D /\
        DISJOINT (IMAGE (e i0) (annulus (&1) (&2))) D /\
        (!j. j IN J /\ ~(j = i0) ==> DISJOINT (IMAGE (e j) (annulus (&1 / &2) (&2))) D) /\
        Zc = IMAGE ff D UNION IMAGE (cm i0) (ball(vec 0,&2))
        ==> D SUBSET topspace topX DIFF mfd_cut_spheres J e /\
            connected_in topZ Zc /\ open_in topZ Zc /\ closed_in topZ Zc /\
            cm i0 (vec 0) IN Zc /\
            IMAGE ff D = Zc DIFF IMAGE (cm i0) (cball(vec 0,&1)) /\
            (!j. j IN J ==> DISJOINT (IMAGE (cp j) (ball(vec 0,&2))) Zc) /\
            (!j. j IN J /\ ~(j = i0) ==> DISJOINT (IMAGE (cm j) (ball(vec 0,&2))) Zc)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `Zc:B->bool`)) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->B`;
                 `cm:num->real^3->B`; `ff:A->B`; `gg:B->A`] MSY_CUT_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ffinv") (CONJUNCTS_THEN2 (LABEL_TAC "gginv")
    (CONJUNCTS_THEN2 (LABEL_TAC "openimg") (CONJUNCTS_THEN2 (LABEL_TAC "connimg")
    (CONJUNCTS_THEN2 (LABEL_TAC "halves") (LABEL_TAC "cores")))))))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_cut_cap] o check (fun th ->
    can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_cut_cap")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "charts")
    (CONJUNCTS_THEN2 (LABEL_TAC "ndisj") (CONJUNCTS_THEN2 (LABEL_TAC "bdisj")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cout") (LABEL_TAC "cin"))))))) THEN
  SUBGOAL_THEN
   `!i. i IN J ==> mfd_neck_chart topX atlasX ((e:num->real^3->A) i) /\
                   mfd_ball_chart topZ atlasZ ((cp:num->real^3->B) i) /\
                   mfd_ball_chart topZ atlasZ ((cm:num->real^3->B) i)`
  (LABEL_TAC "ch") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "charts" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "ch" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(i0:num) IN J`))) THEN
  SUBGOAL_THEN `(D:A->bool) SUBSET topspace topX` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  (* D misses all spheres *)
  SUBGOAL_THEN `(D:A->bool) SUBSET topspace topX DIFF mfd_cut_spheres J e` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; IN_MFD_CUT_SPHERES; NOT_EXISTS_THM] THEN
    X_GEN_TAC `p:A` THEN DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `u:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `p:A`)) THEN
    ASM_CASES_TAC `j:num = i0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(e:num->real^3->A) i0 u IN IMAGE (e i0) (sphere(vec 0,&1))` MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(e:num->real^3->A) i0 u IN D`;
        `(D:A->bool) SUBSET topspace topX DIFF IMAGE ((e:num->real^3->A) i0)
                                                     (sphere(vec 0,&1))`] THEN
      SET_TAC[];
      SUBGOAL_THEN `(e:num->real^3->A) j u IN IMAGE (e j) (annulus (&1 / &2) (&2))`
      MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `D:A->bool`)) (concl th) &&
        can (find_term (fun u -> is_const u && fst(dest_const u) = "DISJOINT")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(e:num->real^3->A) j u IN D` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the image of D *)
  SUBGOAL_THEN `open_in topZ (IMAGE (ff:A->B) D) /\ connected_in topZ (IMAGE ff D) /\
                IMAGE ff D SUBSET topspace topZ DIFF mfd_cut_cores J cp cm`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "openimg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "connimg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
      USE_THEN "ffinv" (MP_TAC o SPEC `p:A`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in topZ (IMAGE ((cm:num->real^3->B) i0) (ball(vec 0,&2))) /\
                connected_in topZ (IMAGE (cm i0) (ball(vec 0,&2)))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_ball_chart topZ (atlasZ:((B->bool)#(B->real^3))->bool)
                                ((cm:num->real^3->B) i0)` THEN
    REWRITE_TAC[mfd_ball_chart] THEN
    DISCH_THEN(X_CHOOSE_THEN `c':B->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,&2))` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_ABSOLUTE; CONNECTED_IN_EUCLIDEAN; CONNECTED_BALL];
    ALL_TAC] THEN
  (* inversion facts *)
  SUBGOAL_THEN
   `!y:real^3. y IN annulus (&1) (&2)
               ==> inv(norm y pow 2) % y IN annulus (&1 / &2) (&1) /\
                   inv(norm(inv(norm y pow 2) % y) pow 2) % (inv(norm y pow 2) % y) = y`
  (LABEL_TAC "inv") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(y:real^3) IN annulus (&1) (&2)` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_INVERSION_INVOLUTION] THEN
    MP_TAC(SPECL [`&1`; `&2`] MSY_INV_IMAGE) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the outer collar of the cap cm i0 lies in the image of D *)
  SUBGOAL_THEN `!y. y IN annulus (&1) (&2) ==> (cm:num->real^3->B) i0 y IN IMAGE (ff:A->B) D`
  (LABEL_TAC "collar") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "inv" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(y:real^3) IN annulus (&1) (&2)`))) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(e:num->real^3->A) i0 (inv(norm y pow 2) % y)` THEN CONJ_TAC THENL
     [USE_THEN "cin" (MP_TAC o SPECL [`i0:num`; `inv(norm y pow 2) % (y:real^3)`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE ((e:num->real^3->A) i0) (annulus (&1 / &2) (&1)) SUBSET D` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* points of Z minus the cores in a cap lie on its collar *)
  SUBGOAL_THEN
   `!(c:real^3->B) y. (?i. i IN J /\ (c = cp i \/ c = cm i)) /\ norm y < &2 /\
                      c y IN topspace topZ DIFF mfd_cut_cores J cp cm
                      ==> y IN annulus (&1) (&2)`
  (LABEL_TAC "oncollar") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `(c:real^3->B) y IN topspace topZ DIFF mfd_cut_cores J cp cm` THEN
    REWRITE_TAC[IN_DIFF; IN_MFD_CUT_CORES] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `y:real^3`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* disjointness of the other caps *)
  SUBGOAL_THEN `!j. j IN J ==> DISJOINT (IMAGE ((cp:num->real^3->B) j) (ball(vec 0,&2))) Zc`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXPAND_TAC "Zc" THEN
    REWRITE_TAC[SET_RULE `DISJOINT (s:B->bool) (t UNION u) <=>
                          DISJOINT s t /\ DISJOINT s u`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_BALL_0] THEN
      X_GEN_TAC `z:B` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(z:B) IN topspace topZ DIFF mfd_cut_cores J cp cm` ASSUME_TAC THENL
       [UNDISCH_TAC `IMAGE (ff:A->B) D SUBSET topspace topZ DIFF mfd_cut_cores J cp cm` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^3) IN annulus (&1) (&2)` ASSUME_TAC THENL
       [USE_THEN "oncollar" MATCH_MP_TAC THEN
        EXISTS_TAC `(cp:num->real^3->B) j` THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(e:num->real^3->A) j y = p` ASSUME_TAC THENL
       [USE_THEN "ffinv" (MP_TAC o SPEC `(e:num->real^3->A) j y`) THEN
        ANTS_TAC THENL
         [USE_THEN "halves" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(j:num) IN J`))) THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
          ALL_TAC] THEN
        USE_THEN "cout" (MP_TAC o SPECL [`j:num`; `y:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        USE_THEN "ffinv" (MP_TAC o SPEC `p:A`) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `j:num = i0` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        UNDISCH_TAC `DISJOINT (IMAGE ((e:num->real^3->A) i0) (annulus (&1) (&2))) D` THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `p:A`) THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
          `(e:num->real^3->A) i0 y = p`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `D:A->bool`)) (concl th) &&
          can (find_term (fun u -> is_const u && fst(dest_const u) = "DISJOINT")) (concl th))) THEN
        ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `p:A`) THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
          `(e:num->real^3->A) j y = p`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `(y:real^3) IN annulus (&1) (&2)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
      USE_THEN "bdisj" (MP_TAC o SPECL [`j:num`; `i0:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j IN J /\ ~(j = i0) ==> DISJOINT (IMAGE ((cm:num->real^3->B) j) (ball(vec 0,&2))) Zc`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN EXPAND_TAC "Zc" THEN
    REWRITE_TAC[SET_RULE `DISJOINT (s:B->bool) (t UNION u) <=>
                          DISJOINT s t /\ DISJOINT s u`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_BALL_0] THEN
      X_GEN_TAC `z:B` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(z:B) IN topspace topZ DIFF mfd_cut_cores J cp cm` ASSUME_TAC THENL
       [UNDISCH_TAC `IMAGE (ff:A->B) D SUBSET topspace topZ DIFF mfd_cut_cores J cp cm` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^3) IN annulus (&1) (&2)` ASSUME_TAC THENL
       [USE_THEN "oncollar" MATCH_MP_TAC THEN
        EXISTS_TAC `(cm:num->real^3->B) j` THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      USE_THEN "inv" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `(y:real^3) IN annulus (&1) (&2)`))) THEN
      SUBGOAL_THEN `(e:num->real^3->A) j (inv(norm y pow 2) % y) = p` ASSUME_TAC THENL
       [USE_THEN "ffinv" (MP_TAC o SPEC `(e:num->real^3->A) j (inv(norm y pow 2) % y)`) THEN
        ANTS_TAC THENL
         [USE_THEN "halves" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(j:num) IN J`))) THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
          ALL_TAC] THEN
        USE_THEN "cin" (MP_TAC o SPECL [`j:num`; `inv(norm y pow 2) % (y:real^3)`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "ffinv" (MP_TAC o SPEC `p:A`) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `D:A->bool`)) (concl th) &&
        can (find_term (fun u -> is_const u && fst(dest_const u) = "DISJOINT")) (concl th))) THEN
      ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `p:A`) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `(e:num->real^3->A) j (inv(norm y pow 2) % y) = p`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `inv(norm y pow 2) % (y:real^3) IN annulus (&1 / &2) (&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      USE_THEN "bdisj" (MP_TAC o SPECL [`i0:num`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[DISJOINT_SYM]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(cm:num->real^3->B) i0 (&4 / &3 % basis 1) IN IMAGE (ff:A->B) D /\
                cm i0 (&4 / &3 % basis 1) IN IMAGE (cm i0) (ball(vec 0,&2)) /\
                cm i0 (vec 0) IN IMAGE (cm i0) (ball(vec 0,&2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "collar" MATCH_MP_TAC THEN
      SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      SIMP_TAC[IN_BALL_0; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[CENTRE_IN_BALL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_in topZ (Zc:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Zc" THEN MATCH_MP_TAC CONNECTED_IN_UNION THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in topZ (Zc:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Zc" THEN MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(cm:num->real^3->B) i0 (vec 0) IN Zc` ASSUME_TAC THENL
   [EXPAND_TAC "Zc" THEN ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ff:A->B) D = Zc DIFF IMAGE ((cm:num->real^3->B) i0) (cball(vec 0,&1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Zc" THEN REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION] THEN
    X_GEN_TAC `z:B` THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `IMAGE (ff:A->B) D SUBSET topspace topZ DIFF mfd_cut_cores J cp cm` THEN
      REWRITE_TAC[SUBSET; IN_DIFF] THEN DISCH_THEN(MP_TAC o SPEC `z:B`) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "cores" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(i0:num) IN J`))) THEN
      ASM SET_TAC[];
      DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN ASSUME_TAC) ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:B) IN IMAGE ((cm:num->real^3->B) i0) (ball(vec 0,&2))` THEN
      REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[GSYM IN_IMAGE] THEN
      USE_THEN "collar" MATCH_MP_TAC THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((cm:num->real^3->B) i0 y IN IMAGE (cm i0) (cball(vec 0,&1)))` THEN
      REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
      REWRITE_TAC[GSYM REAL_NOT_LE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in topZ (Zc:B->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[closed_in] THEN CONJ_TAC THENL [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `z:B` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(z:B) IN mfd_cut_cores J cp cm` THENL
     [UNDISCH_TAC `(z:B) IN mfd_cut_cores J cp cm` THEN REWRITE_TAC[IN_MFD_CUT_CORES] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THENL
       [EXISTS_TAC `IMAGE ((cp:num->real^3->B) j) (ball(vec 0,&2))` THEN
        USE_THEN "ch" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(j:num) IN J`))) THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
          MAP_EVERY EXISTS_TAC [`atlasZ:((B->bool)#(B->real^3))->bool`;
                                `ball(vec 0:real^3,&2)`] THEN
          ASM_REWRITE_TAC[GSYM mfd_ball_chart; OPEN_BALL; SUBSET_REFL];
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
          REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `!j. j IN J ==> DISJOINT (IMAGE ((cp:num->real^3->B) j)
                                                       (ball(vec 0,&2))) Zc` THEN
          DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(SET_RULE
           `(s:B->bool) SUBSET t ==> DISJOINT s a ==> s SUBSET t DIFF a`) THEN
          MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
          MAP_EVERY EXISTS_TAC [`atlasZ:((B->bool)#(B->real^3))->bool`;
                                `ball(vec 0:real^3,&2)`] THEN
          ASM_REWRITE_TAC[GSYM mfd_ball_chart; SUBSET_REFL]];
        ASM_CASES_TAC `j:num = i0` THENL
         [UNDISCH_TAC `~((z:B) IN Zc)` THEN EXPAND_TAC "Zc" THEN
          FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[IN_UNION] THEN
          MATCH_MP_TAC(TAUT `b ==> ~(a \/ b) ==> c`) THEN
          MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        EXISTS_TAC `IMAGE ((cm:num->real^3->B) j) (ball(vec 0,&2))` THEN
        USE_THEN "ch" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(j:num) IN J`))) THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
          MAP_EVERY EXISTS_TAC [`atlasZ:((B->bool)#(B->real^3))->bool`;
                                `ball(vec 0:real^3,&2)`] THEN
          ASM_REWRITE_TAC[GSYM mfd_ball_chart; OPEN_BALL; SUBSET_REFL];
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
          REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `!j. j IN J /\ ~(j = i0)
                           ==> DISJOINT (IMAGE ((cm:num->real^3->B) j) (ball(vec 0,&2))) Zc` THEN
          DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(SET_RULE
           `(s:B->bool) SUBSET t ==> DISJOINT s a ==> s SUBSET t DIFF a`) THEN
          MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
          MAP_EVERY EXISTS_TAC [`atlasZ:((B->bool)#(B->real^3))->bool`;
                                `ball(vec 0:real^3,&2)`] THEN
          ASM_REWRITE_TAC[GSYM mfd_ball_chart; SUBSET_REFL]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:B) IN topspace topZ DIFF mfd_cut_cores J cp cm` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
    USE_THEN "gginv" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(z:B) IN topspace topZ DIFF mfd_cut_cores J cp cm`))) THEN
    ABBREV_TAC `O' = (topspace topX DIFF IMAGE ((e:num->real^3->A) i0) (sphere(vec 0,&1)))
                     DIFF D` THEN
    EXISTS_TAC `IMAGE (ff:A->B) (O' INTER (topspace topX DIFF mfd_cut_spheres J e))` THEN
    SUBGOAL_THEN `~((gg:B->A) z IN D)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((z:B) IN Zc)` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (ff:A->B) D = Zc DIFF IMAGE ((cm:num->real^3->B) i0) (cball(vec 0,&1))` THEN
      REWRITE_TAC[EXTENSION; IN_DIFF; IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `z:B`) THEN MATCH_MP_TAC(TAUT `a ==> (a <=> b /\ c) ==> b`) THEN
      EXISTS_TAC `(gg:B->A) z` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "openimg" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(gg:B->A) z` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      EXPAND_TAC "O'" THEN REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(gg:B->A) z IN topspace topX DIFF mfd_cut_spheres J e` THEN
      REWRITE_TAC[IN_DIFF; IN_MFD_CUT_SPHERES] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~(?i x. i IN J /\ norm x = &1 /\ (gg:B->A) z = (e:num->real^3->A) i x)` THEN
      REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`i0:num`; `u:real^3`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `q:A` THEN
      STRIP_TAC THEN
      USE_THEN "ffinv" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `(q:A) IN topspace topX DIFF mfd_cut_spheres J e`))) THEN
      REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(ff:A->B) q IN topspace topZ DIFF mfd_cut_cores J cp cm` THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(ff:A->B) q IN IMAGE ff D` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_DIFF] THEN
        UNDISCH_TAC `(ff:A->B) q IN topspace topZ DIFF mfd_cut_cores J cp cm` THEN
        USE_THEN "cores" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(i0:num) IN J`))) THEN
        SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `d:A` STRIP_ASSUME_TAC) THEN
      USE_THEN "ffinv" (MP_TAC o SPEC `d:A`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(ff:A->B) q = ff d`)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(d:A) IN O'` THEN EXPAND_TAC "O'" THEN
      UNDISCH_TAC `(d:A) IN D` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The leaf side is a ball.  Zc is S^3, so D is a ball                      *)
(* (SMT_SPHERE_SUM_INNER) and capping gives a ball chart b of X with        *)
(* b = e i0 on the collar and b(ball(0,1)) = D (SMT_CAP_BALL_CHART).        *)
(* ------------------------------------------------------------------------- *)

let MSY_LEAF_BALL = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topZ (atlasZ:((B->bool)#(B->real^3))->bool) J e cp cm ff gg i0 D Zc.
        hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\
        hausdorff_space topZ /\ smooth_manifold_atlas topZ atlasZ /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm ff gg /\ i0 IN J /\
        D SUBSET topspace topX DIFF mfd_cut_spheres J e /\ open_in topX D /\
        IMAGE (e i0) (annulus (&1 / &2) (&1)) SUBSET D /\
        DISJOINT (IMAGE (e i0) (annulus (&1) (&2))) D /\
        DISJOINT D (IMAGE (e i0) (sphere(vec 0,&1))) /\
        open_in topZ Zc /\ IMAGE (cm i0) (ball(vec 0,&2)) SUBSET Zc /\
        IMAGE ff D = Zc DIFF IMAGE (cm i0) (cball(vec 0,&1)) /\
        mfd_diffeomorphic (subtopology topZ Zc) (restrict_atlas atlasZ Zc)
          (subtopology euclidean (sphere(vec 0,&1))) sphere3_atlas
        ==> ?b. mfd_ball_chart topX atlasX b /\
                (!x. x IN annulus (&2 / &3) (&2) ==> b x = e i0 x) /\
                IMAGE b (ball(vec 0,&1)) = D /\
                IMAGE b (sphere(vec 0,&1)) = IMAGE (e i0) (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_cut_cap] o check (fun th ->
    can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_cut_cap")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "charts")
    (CONJUNCTS_THEN2 (LABEL_TAC "ndisj") (CONJUNCTS_THEN2 (LABEL_TAC "bdisj")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cout") (LABEL_TAC "cin"))))))) THEN
  USE_THEN "charts" (MP_TAC o SPEC `i0:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(Zc:B->bool) SUBSET topspace topZ` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo topX (atlasX:((A->bool)#(A->real^3))->bool) D
               topZ (atlasZ:((B->bool)#(B->real^3))->bool) (IMAGE (ff:A->B) D) ff gg`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)`;
                          `topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:B`,`:C`] (MATCH_MP SMT_SPHERE_SUM_INNER SMT_S3_BALL_COMPLEMENT_ALL)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
    `subtopology topZ (Zc:B->bool)`;
    `restrict_atlas (atlasZ:((B->bool)#(B->real^3))->bool) Zc`;
    `(e:num->real^3->A) i0`; `D:A->bool`; `(cm:num->real^3->B) i0`; `ff:A->B`; `gg:B->A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[mfd_ball_chart] THEN
      MP_TAC(ISPECL [`topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                     `Zc:B->bool`; `ball(vec 0:real^3,&2)`; `(cm:num->real^3->B) i0`]
        APX_PARAM_RESTRICT_EQ) THEN
      ASM_REWRITE_TAC[GSYM mfd_ball_chart];
      SUBGOAL_THEN `topspace (subtopology topZ Zc) DIFF
                    IMAGE ((cm:num->real^3->B) i0) (cball(vec 0,&1)) = IMAGE (ff:A->B) D`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
        UNDISCH_TAC `(Zc:B->bool) SUBSET topspace topZ` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `D:A->bool`;
                     `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                     `Zc:B->bool`; `IMAGE (ff:A->B) D`; `ff:A->B`; `gg:B->A`]
        APX_MFD_DIFFEO_RESTRICT_TARGET) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `IMAGE (ff:A->B) D = Zc DIFF IMAGE ((cm:num->real^3->B) i0) (cball(vec 0,&1))` THEN
      SET_TAC[];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "cin" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->A` (X_CHOOSE_THEN `psi':A->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `(e:num->real^3->A) i0`; `D:A->bool`; `psi:real^3->A`; `psi':A->real^3`]
    SMT_CAP_BALL_CHART) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The new cut map.  ff on X minus the spheres and the closed                *)
(* ball b(cball(0,1)), glued with cp i0 o b^-1 on b(ball(0,2)), is a        *)
(* diffeomorphism of X minus the remaining spheres onto Z minus Zc minus    *)
(* the remaining cores.                                                      *)
(* ------------------------------------------------------------------------- *)

let MSY_NEW_DIFFEO = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topZ (atlasZ:((B->bool)#(B->real^3))->bool) J e cp cm ff gg i0 D Zc b.
        hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\
        hausdorff_space topZ /\ smooth_manifold_atlas topZ atlasZ /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm ff gg /\ i0 IN J /\
        D SUBSET topspace topX DIFF mfd_cut_spheres J e /\
        IMAGE (cm i0) (ball(vec 0,&2)) SUBSET Zc /\
        IMAGE ff D = Zc DIFF IMAGE (cm i0) (cball(vec 0,&1)) /\
        (!j. j IN J ==> DISJOINT (IMAGE (cp j) (ball(vec 0,&2))) Zc) /\
        Zc SUBSET topspace topZ /\
        mfd_ball_chart topX atlasX b /\
        (!x. x IN annulus (&2 / &3) (&2) ==> b x = e i0 x) /\
        IMAGE b (ball(vec 0,&1)) = D /\
        IMAGE b (sphere(vec 0,&1)) = IMAGE (e i0) (sphere(vec 0,&1))
        ==> ?ff' gg'.
              mfd_diffeo topX atlasX (topspace topX DIFF mfd_cut_spheres (J DELETE i0) e)
                         topZ atlasZ
                         ((topspace topZ DIFF Zc) DIFF mfd_cut_cores (J DELETE i0) cp cm)
                         ff' gg' /\
              (!x. x IN topspace topX DIFF IMAGE b (ball(vec 0,&2)) ==> ff' x = ff x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->B`;
                 `cm:num->real^3->B`; `ff:A->B`; `gg:B->A`] MSY_CUT_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ffinv") (CONJUNCTS_THEN2 (LABEL_TAC "gginv")
    (CONJUNCTS_THEN2 (LABEL_TAC "openimg") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "halves") (LABEL_TAC "cores")))))))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_cut_cap] o check (fun th ->
    can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_cut_cap")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "charts")
    (CONJUNCTS_THEN2 (LABEL_TAC "ndisj") (CONJUNCTS_THEN2 (LABEL_TAC "bdisj")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cout") (LABEL_TAC "cin"))))))) THEN
  USE_THEN "charts" (MP_TAC o SPEC `i0:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "halves" (MP_TAC o SPEC `i0:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "cores" (MP_TAC o SPEC `i0:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `mfd_ball_chart topX (atlasX:((A->bool)#(A->real^3))->bool) b` THEN
  REWRITE_TAC[mfd_ball_chart] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  UNDISCH_TAC `mfd_ball_chart topZ (atlasZ:((B->bool)#(B->real^3))->bool)
                              ((cp:num->real^3->B) i0)` THEN
  REWRITE_TAC[mfd_ball_chart] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c':B->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS o
    check (fun th -> can (find_term ((=) `(cp:num->real^3->B) i0`)) (concl th) &&
                     can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_param"))
                         (concl th))) THEN
  ABBREV_TAC `Xo = topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)` THEN
  ABBREV_TAC `W1 = (Xo:A->bool) DIFF IMAGE (b:real^3->A) (cball(vec 0,&1))` THEN
  SUBGOAL_THEN `(Xo:A->bool) SUBSET topspace topX` ASSUME_TAC THENL
   [EXPAND_TAC "Xo" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. p IN IMAGE (b:real^3->A) (ball(vec 0,&2)) <=>
        p IN D \/ p IN IMAGE ((e:num->real^3->A) i0) (sphere(vec 0,&1)) \/
        p IN IMAGE (e i0) (annulus (&1) (&2))`
  (LABEL_TAC "bmem") THENL
   [REWRITE_TAC[GSYM IN_UNION] THEN REWRITE_TAC[GSYM EXTENSION] THEN
    SUBGOAL_THEN `ball(vec 0:real^3,&2) =
                  ball(vec 0,&1) UNION sphere(vec 0,&1) UNION annulus (&1) (&2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_UNION] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> (f:real^3->A) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^3) IN annulus (&1) (&2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in topX (IMAGE (b:real^3->A) (cball(vec 0,&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
    ASM_REWRITE_TAC[COMPACT_CBALL; SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in topX (W1:A->bool) /\ W1 SUBSET Xo` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W1" THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN
      EXPAND_TAC "Xo" THEN ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo topX (atlasX:((A->bool)#(A->real^3))->bool) W1
               topZ (atlasZ:((B->bool)#(B->real^3))->bool) (IMAGE (ff:A->B) W1) ff gg`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`Xo:A->bool`;
                          `topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Xo" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo topX (atlasX:((A->bool)#(A->real^3))->bool) (IMAGE (b:real^3->A) (ball(vec 0,&2)))
               topZ (atlasZ:((B->bool)#(B->real^3))->bool)
               (IMAGE ((cp:num->real^3->B) i0) (ball(vec 0,&2)))
               (cp i0 o b') (b o c')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:real^3`,`:B`; `:3`,`:N`] MFD_DIFFEO_COMPOSE) THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas(:real^3)`;
                          `ball(vec 0:real^3,&2)`] THEN
    ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS] THEN
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (b:real^3->A) (cball(vec 0,&1)) SUBSET IMAGE b (ball(vec 0,&2)) /\
                IMAGE (b:real^3->A) (ball(vec 0,&2)) SUBSET topspace topX /\
                IMAGE ((cp:num->real^3->B) i0) (ball(vec 0,&2)) SUBSET topspace topZ`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[OPEN_IN_SUBSET];
      ASM_SIMP_TAC[OPEN_IN_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN ball(vec 0,&2) /\ ~(y IN cball(vec 0,&1))
                           ==> y IN annulus (&1) (&2) /\ y IN annulus (&2 / &3) (&2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0; IN_CBALL_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN W1 /\ x IN IMAGE (b:real^3->A) (ball(vec 0,&2))
          ==> (cp:num->real^3->B) i0 (b' x) = ff x`
  (LABEL_TAC "h1") THENL
   [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    UNDISCH_TAC `(x:A) IN IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~((y:real^3) IN cball(vec 0,&1))` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(b:real^3->A) y IN W1` THEN EXPAND_TAC "W1" THEN
      REWRITE_TAC[IN_DIFF] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "cball")) (concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "annulus")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    USE_THEN "cout" (MP_TAC o SPECL [`i0:num`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:B. z IN IMAGE (ff:A->B) W1 /\ z IN IMAGE ((cp:num->real^3->B) i0) (ball(vec 0,&2))
          ==> (b:real^3->A) (c' z) = gg z`
  (LABEL_TAC "k1") THENL
   [X_GEN_TAC `z:B` THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:B) IN IMAGE ((cp:num->real^3->B) i0) (ball(vec 0,&2))` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(cp:num->real^3->B) i0 u IN topspace topZ DIFF mfd_cut_cores J cp cm`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(cp:num->real^3->B) i0 u IN IMAGE (ff:A->B) W1` THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "ffinv" (MP_TAC o SPEC `x:A`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(x:A) IN W1` THEN UNDISCH_TAC `(W1:A->bool) SUBSET Xo` THEN
        EXPAND_TAC "Xo" THEN SET_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((u:real^3) IN cball(vec 0,&1))` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `(cp:num->real^3->B) i0 u IN topspace topZ DIFF mfd_cut_cores J cp cm` THEN
      REWRITE_TAC[IN_DIFF] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE ((cp:num->real^3->B) i0) (cball(vec 0,&1)) SUBSET
                   mfd_cut_cores J cp cm` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "cball")) (concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "annulus")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    USE_THEN "cout" (MP_TAC o SPECL [`i0:num`; `u:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    CONV_TAC SYM_CONV THEN USE_THEN "ffinv" (MP_TAC o SPEC `(e:num->real^3->A) i0 u`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `IMAGE ((e:num->real^3->A) i0) (annulus (&1) (&2)) SUBSET Xo` THEN
      EXPAND_TAC "Xo" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* the X side: X minus the remaining spheres is W1 union b(ball(0,2)) *)
  SUBGOAL_THEN
   `topspace topX DIFF mfd_cut_spheres (J DELETE i0) (e:num->real^3->A) =
    W1 UNION IMAGE (b:real^3->A) (ball(vec 0,&2))`
  (LABEL_TAC "setX") THENL
   [REWRITE_TAC[EXTENSION; IN_UNION] THEN X_GEN_TAC `p:A` THEN EQ_TAC THENL
     [REWRITE_TAC[IN_DIFF; IN_MFD_CUT_SPHERES; IN_DELETE] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(p:A) IN IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "W1" THEN EXPAND_TAC "Xo" THEN
  REWRITE_TAC[IN_DIFF; IN_MFD_CUT_SPHERES] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC `i:num = i0` THENL
     [UNDISCH_TAC `~((p:A) IN IMAGE (b:real^3->A) (ball(vec 0,&2)))` THEN
      ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN DISJ1_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
      ASM_MESON_TAC[]];
    UNDISCH_TAC `~((p:A) IN IMAGE (b:real^3->A) (ball(vec 0,&2)))` THEN
    UNDISCH_TAC `IMAGE (b:real^3->A) (cball(vec 0,&1)) SUBSET IMAGE b (ball(vec 0,&2))` THEN
    SET_TAC[]];
      STRIP_TAC THENL
       [UNDISCH_TAC `(p:A) IN W1` THEN EXPAND_TAC "W1" THEN EXPAND_TAC "Xo" THEN
  REWRITE_TAC[IN_DIFF; IN_MFD_CUT_SPHERES; IN_DELETE] THEN MESON_TAC[];
  REWRITE_TAC[IN_DIFF; IN_MFD_CUT_SPHERES; IN_DELETE] THEN CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2)) SUBSET topspace topX` THEN
    UNDISCH_TAC `(p:A) IN IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `p:A`)) THEN
  SUBGOAL_THEN `(e:num->real^3->A) i x IN mfd_cut_spheres J e` ASSUME_TAC THENL
   [REWRITE_TAC[IN_MFD_CUT_SPHERES] THEN MAP_EVERY EXISTS_TAC [`i:num`; `x:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(e:num->real^3->A) i x IN IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(e:num->real^3->A) i x IN mfd_cut_spheres J e`;
                           `(e:num->real^3->A) i x IN D`; `(D:A->bool) SUBSET Xo`] THEN
    EXPAND_TAC "Xo" THEN SET_TAC[];
    USE_THEN "ndisj" (MP_TAC o SPECL [`i0:num`; `i:num`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:num->real^3->A) i x`) THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!(y:A) s t. y IN s /\ s SUBSET t ==> y IN t`) THEN
      EXISTS_TAC `IMAGE ((e:num->real^3->A) i0) (sphere(vec 0,&1))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    MAP_EVERY UNDISCH_TAC [`(e:num->real^3->A) i x IN mfd_cut_spheres J e`;
                           `(e:num->real^3->A) i x IN IMAGE (e i0) (annulus (&1) (&2))`;
                           `IMAGE ((e:num->real^3->A) i0) (annulus (&1) (&2)) SUBSET Xo`] THEN
    EXPAND_TAC "Xo" THEN SET_TAC[]]]];
    ALL_TAC] THEN
  (* the Z side: Z minus Zc minus the remaining cores is ff(W1) union cp i0(ball(0,2)) *)
  REMOVE_THEN "bmem" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `(topspace topZ DIFF Zc) DIFF mfd_cut_cores (J DELETE i0) (cp:num->real^3->B) cm =
    IMAGE (ff:A->B) W1 UNION IMAGE (cp i0) (ball(vec 0,&2))`
  (LABEL_TAC "setZ") THENL
   [SUBGOAL_THEN `!p:A. p IN IMAGE (b:real^3->A) (cball(vec 0,&1)) <=>
                      p IN D \/ p IN IMAGE ((e:num->real^3->A) i0) (sphere(vec 0,&1))`
  (LABEL_TAC "bcb") THENL
   [REWRITE_TAC[GSYM IN_UNION] THEN REWRITE_TAC[GSYM EXTENSION] THEN
    REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((e:num->real^3->A) i0) (sphere(vec 0,&1)) SUBSET mfd_cut_spheres J e`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; IN_MFD_CUT_SPHERES] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`i0:num`; `x:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_cut_cores (J DELETE i0) (cp:num->real^3->B) cm SUBSET mfd_cut_cores J cp cm`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_MFD_CUT_CORES; IN_DELETE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:B. z IN mfd_cut_cores (J DELETE i0) cp cm
                      ==> ~(z IN IMAGE ((cp:num->real^3->B) i0) (ball(vec 0,&2)))`
  (LABEL_TAC "cpdisj") THENL
   [X_GEN_TAC `z:B` THEN REWRITE_TAC[IN_MFD_CUT_CORES; IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `y:real^3`
      (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
    SUBGOAL_THEN `(y:real^3) IN ball(vec 0,&2)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(i0:num = j)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "bdisj" (MP_TAC o SPECL [`i0:num`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(z:B) = (cp:num->real^3->B) j y \/ z = (cm:num->real^3->B) j y`;
                           `(y:real^3) IN ball(vec 0,&2)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF] THEN X_GEN_TAC `z:B` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    ASM_CASES_TAC `(z:B) IN IMAGE ((cp:num->real^3->B) i0) (ball(vec 0,&2))` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:B) IN topspace topZ DIFF mfd_cut_cores J cp cm` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF; IN_MFD_CUT_CORES] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `y:real^3`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
      SUBGOAL_THEN `(y:real^3) IN ball(vec 0,&2)` ASSUME_TAC THENL
       [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `j:num = i0` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        MAP_EVERY UNDISCH_TAC
         [`(z:B) = (cp:num->real^3->B) i0 y \/ z = (cm:num->real^3->B) i0 y`;
          `(y:real^3) IN ball(vec 0,&2)`;
          `~((z:B) IN IMAGE ((cp:num->real^3->B) i0) (ball(vec 0,&2)))`;
          `~((z:B) IN Zc)`; `IMAGE ((cm:num->real^3->B) i0) (ball(vec 0,&2)) SUBSET Zc`] THEN
        SET_TAC[];
        UNDISCH_TAC `~((z:B) IN mfd_cut_cores (J DELETE i0) cp cm)` THEN
        REWRITE_TAC[IN_MFD_CUT_CORES; IN_DELETE] THEN
        MAP_EVERY EXISTS_TAC [`j:num`; `y:real^3`] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "gginv" (MP_TAC o SPEC `z:B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `~((gg:B->A) z IN D)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((z:B) IN Zc)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(ff:A->B)((gg:B->A) z) IN IMAGE ff D` MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((gg:B->A) z IN IMAGE ((e:num->real^3->A) i0) (sphere(vec 0,&1)))`
    ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(gg:B->A) z IN Xo`;
        `IMAGE ((e:num->real^3->A) i0) (sphere(vec 0,&1)) SUBSET mfd_cut_spheres J e`] THEN
      EXPAND_TAC "Xo" THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(gg:B->A) z` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "W1" THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    USE_THEN "bcb" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `(z:B) IN IMAGE (ff:A->B) W1` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x:A) IN Xo` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:A) IN W1` THEN UNDISCH_TAC `(W1:A->bool) SUBSET Xo` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "ffinv" (MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(ff:A->B) x IN IMAGE ff D` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_TAC THEN
        UNDISCH_TAC `~((ff:A->B) x IN mfd_cut_cores J cp cm)` THEN REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`(ff:A->B) x IN IMAGE ((cm:num->real^3->B) i0) (cball(vec 0,&1))`;
          `IMAGE ((cm:num->real^3->B) i0) (cball(vec 0,&1)) SUBSET mfd_cut_cores J cp cm`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `d:A` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(d:A) IN Xo` ASSUME_TAC THENL
       [UNDISCH_TAC `(d:A) IN D` THEN UNDISCH_TAC `(D:A->bool) SUBSET Xo` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:A) = d` SUBST_ALL_TAC THENL
       [USE_THEN "ffinv" (MP_TAC o SPEC `d:A`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o CONJUNCT2) THEN
        UNDISCH_TAC `(gg:B->A)((ff:A->B) x) = x` THEN
        UNDISCH_TAC `(ff:A->B) x = ff d` THEN MESON_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(d:A) IN W1` THEN EXPAND_TAC "W1" THEN
      REWRITE_TAC[IN_DIFF] THEN USE_THEN "bcb" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC [`~((ff:A->B) x IN mfd_cut_cores J cp cm)`;
        `mfd_cut_cores (J DELETE i0) (cp:num->real^3->B) cm SUBSET mfd_cut_cores J cp cm`] THEN
      SET_TAC[]];
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(z:B) IN IMAGE ((cp:num->real^3->B) i0) (ball(vec 0,&2))` THEN
      UNDISCH_TAC `IMAGE ((cp:num->real^3->B) i0) (ball(vec 0,&2)) SUBSET topspace topZ` THEN
      SET_TAC[];
      MP_TAC(MATCH_MP (ASSUME `!j. j IN J ==> DISJOINT (IMAGE ((cp:num->real^3->B) j)
                                                   (ball(vec 0,&2))) Zc`)
                      (ASSUME `(i0:num) IN J`)) THEN
      UNDISCH_TAC `(z:B) IN IMAGE ((cp:num->real^3->B) i0) (ball(vec 0,&2))` THEN SET_TAC[];
      USE_THEN "cpdisj" (MP_TAC o SPEC `z:B`) THEN
      UNDISCH_TAC `(z:B) IN IMAGE ((cp:num->real^3->B) i0) (ball(vec 0,&2))` THEN
      CONV_TAC TAUT]];
    ALL_TAC] THEN
  (* glue ff on W1 with cp i0 o b^-1 on b(ball(0,2)) *)
  MAP_EVERY EXISTS_TAC
   [`\x:A. if x IN IMAGE (b:real^3->A) (ball(vec 0,&2))
           then (cp:num->real^3->B) i0 ((b':A->real^3) x) else (ff:A->B) x`;
    `\z:B. if z IN IMAGE ((cp:num->real^3->B) i0) (ball(vec 0,&2))
           then (b:real^3->A) ((c':B->real^3) z) else (gg:B->A) z`] THEN
  USE_THEN "setX" SUBST1_TAC THEN USE_THEN "setZ" SUBST1_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_GLUE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`ff:A->B`; `gg:B->A`;
                          `(cp:num->real^3->B) i0 o (b':A->real^3)`;
                          `(b:real^3->A) o (c':B->real^3)`] THEN
    ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "h1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:B` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "k1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:B` THEN DISCH_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The new cut data.  With the neck i0 removed, X is cut along               *)
(* the remaining necks and capped to Z minus the component Zc, by the glued *)
(* map of MSY_NEW_DIFFEO; on the other collars it is still ff.              *)
(* ------------------------------------------------------------------------- *)

let MSY_BALL2_SPLIT = prove
 (`!(b:real^3->A) e D.
        (!x. x IN annulus (&2 / &3) (&2) ==> b x = e x) /\
        IMAGE b (ball(vec 0,&1)) = D /\
        IMAGE b (sphere(vec 0,&1)) = IMAGE e (sphere(vec 0,&1))
        ==> IMAGE b (ball(vec 0,&2)) =
            D UNION IMAGE e (sphere(vec 0,&1)) UNION IMAGE e (annulus (&1) (&2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ball(vec 0:real^3,&2) =
                ball(vec 0,&1) UNION sphere(vec 0,&1) UNION annulus (&1) (&2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_UNION] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> (f:real^3->A) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `(x:real^3) IN annulus (&1) (&2)` THEN
  REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* The other necks miss the ball b(ball(0,2)) = D + sphere + outer half.     *)

let MSY_NECK_OFF_BALL = prove
 (`!J (e:num->real^3->A) i0 D B i x.
        (!j. j IN J /\ ~(j = i0) ==> DISJOINT (IMAGE (e j) (annulus (&1 / &2) (&2))) D) /\
        (!i j. i IN J /\ j IN J /\ ~(i = j)
               ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                            (IMAGE (e j) (annulus (&1 / &2) (&2)))) /\
        B = D UNION IMAGE (e i0) (sphere(vec 0,&1)) UNION IMAGE (e i0) (annulus (&1) (&2)) /\
        i0 IN J /\ i IN J /\ ~(i = i0) /\ x IN annulus (&1 / &2) (&2)
        ==> ~(e i x IN B)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dd") (CONJUNCTS_THEN2 (LABEL_TAC "nd")
    (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC))) THEN
  USE_THEN "dd" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "nd" (MP_TAC o SPECL [`i:num`; `i0:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2) /\
                (annulus (&1) (&2):real^3->bool) SUBSET annulus (&1 / &2) (&2)`
  MP_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(x:real^3) IN annulus (&1 / &2) (&2)`;
    `DISJOINT (IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2))) D`;
    `DISJOINT (IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)))
              (IMAGE (e i0) (annulus (&1 / &2) (&2)))`] THEN
  SET_TAC[]);;

(* A ball chart missing a closed set K is a ball chart of the complement.   *)

let MSY_BALL_CHART_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) K (c:real^N->A).
        smooth_manifold_atlas top atlas /\ closed_in top K /\
        mfd_ball_chart top atlas c /\ DISJOINT (IMAGE c (ball(vec 0,&2))) K
        ==> mfd_ball_chart (subtopology top (topspace top DIFF K))
                           (restrict_atlas atlas (topspace top DIFF K)) c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_ball_chart] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `topspace top DIFF K:A->bool`; `ball(vec 0:real^N,&2)`; `c:real^N->A`]
    APX_PARAM_RESTRICT_EQ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET u /\ DISJOINT s k ==> s SUBSET u DIFF k`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `ball(vec 0:real^N,&2)`] THEN
    ASM_REWRITE_TAC[GSYM mfd_ball_chart; SUBSET_REFL];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[GSYM mfd_ball_chart]]);;

(* The new cut data: X cut along the necks other than i0, capped to Z minus *)
(* Zc.                                                                       *)

let MSY_NEW_CUT = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topZ (atlasZ:((B->bool)#(B->real^3))->bool) J e cp cm ff gg i0 D Zc b.
        hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\
        hausdorff_space topZ /\ smooth_manifold_atlas topZ atlasZ /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm ff gg /\ i0 IN J /\
        D SUBSET topspace topX DIFF mfd_cut_spheres J e /\
        (!j. j IN J /\ ~(j = i0) ==> DISJOINT (IMAGE (e j) (annulus (&1 / &2) (&2))) D) /\
        closed_in topZ Zc /\ IMAGE (cm i0) (ball(vec 0,&2)) SUBSET Zc /\
        IMAGE ff D = Zc DIFF IMAGE (cm i0) (cball(vec 0,&1)) /\
        (!j. j IN J ==> DISJOINT (IMAGE (cp j) (ball(vec 0,&2))) Zc) /\
        (!j. j IN J /\ ~(j = i0) ==> DISJOINT (IMAGE (cm j) (ball(vec 0,&2))) Zc) /\
        mfd_ball_chart topX atlasX b /\
        (!x. x IN annulus (&2 / &3) (&2) ==> b x = e i0 x) /\
        IMAGE b (ball(vec 0,&1)) = D /\
        IMAGE b (sphere(vec 0,&1)) = IMAGE (e i0) (sphere(vec 0,&1))
        ==> ?ff' gg'. mfd_cut_cap topX atlasX
                        (subtopology topZ (topspace topZ DIFF Zc))
                        (restrict_atlas atlasZ (topspace topZ DIFF Zc))
                        (J DELETE i0) e cp cm ff' gg'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Zc:B->bool) SUBSET topspace topZ` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->B`;
                 `cm:num->real^3->B`; `ff:A->B`; `gg:B->A`; `i0:num`; `D:A->bool`;
                 `Zc:B->bool`; `b:real^3->A`] MSY_NEW_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff':A->B` (X_CHOOSE_THEN `gg':B->A`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agree")))) THEN
  MAP_EVERY EXISTS_TAC [`ff':A->B`; `gg':B->A`] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_cut_cap] o check (fun th ->
    can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_cut_cap")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "charts")
    (CONJUNCTS_THEN2 (LABEL_TAC "ndisj") (CONJUNCTS_THEN2 (LABEL_TAC "bdisj")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "cout") (LABEL_TAC "cin"))))))) THEN
  MP_TAC(ISPECL [`b:real^3->A`; `(e:num->real^3->A) i0`; `D:A->bool`] MSY_BALL2_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!i x. i IN J /\ ~(i = i0) /\ x IN annulus (&1 / &2) (&2)
          ==> (ff':A->B) ((e:num->real^3->A) i x) = ff (e i x)`
  (LABEL_TAC "off") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "agree" MATCH_MP_TAC THEN REWRITE_TAC[IN_DIFF] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!(y:A) s t. y IN s /\ s SUBSET t ==> y IN t`) THEN
      EXISTS_TAC `IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2))` THEN
      CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`;
                            `annulus (&1 / &2) (&2):real^3->bool`] THEN
      REWRITE_TAC[SUBSET_REFL; GSYM mfd_neck_chart] THEN
      USE_THEN "charts" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      MATCH_MP_TAC MSY_NECK_OFF_BALL THEN
      MAP_EVERY EXISTS_TAC [`J:num->bool`; `i0:num`; `D:A->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_cut_cap] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[FINITE_DELETE];
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    USE_THEN "charts" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MSY_BALL_CHART_RESTRICT THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[IN_DELETE] THEN REPEAT STRIP_TAC THEN USE_THEN "ndisj" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_DELETE] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "bdisj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `topspace topZ INTER (topspace topZ DIFF Zc) = topspace topZ DIFF (Zc:B->bool)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `topspace topX DIFF mfd_cut_spheres (J DELETE i0) (e:num->real^3->A)`;
                   `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                   `topspace topZ DIFF (Zc:B->bool)`;
                   `(topspace topZ DIFF Zc) DIFF
                    mfd_cut_cores (J DELETE i0) (cp:num->real^3->B) cm`;
                   `ff':A->B`; `gg':B->A`] APX_MFD_DIFFEO_RESTRICT_TARGET) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_DELETE] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN annulus (&1) (&2)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "off" (MP_TAC o SPECL [`i:num`; `x:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "cout" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_DELETE] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN annulus (&1 / &2) (&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "off" (MP_TAC o SPECL [`i:num`; `x:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "cin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Components.  Removing a clopen set keeps the manifold                     *)
(* structure and the S^3 components; a diffeomorphism of the whole spaces   *)
(* carries S^3 components back (the base case); the complement of a side in *)
(* the complement of a closed set is open.                                   *)
(* ------------------------------------------------------------------------- *)

let MSY_COMPONENT_CLOPEN_SUB = prove
 (`!top W (U:A->bool).
        open_in top W /\ closed_in top W /\ U IN connected_components_of (subtopology top W)
        ==> U IN connected_components_of top /\ U SUBSET W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(U:A->bool) IN connected_components_of (subtopology top W)` THEN
  REWRITE_TAC[connected_components_of; IN_ELIM_THM; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC)) THEN
  SUBGOAL_THEN `connected_component_of top (x:A) SUBSET W` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `connected_component_of top (x:A)`; `W:A->bool`]
      CONNECTED_IN_CLOPEN_CASES) THEN
    ASM_REWRITE_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_component_of (subtopology top W) (x:A) = connected_component_of top x`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_SUBTOPOLOGY_EQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]);;

let MSY_REMOVE_CLOPEN = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) K.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        rfs_components_s3 top atlas /\ open_in top K /\ closed_in top K
        ==> hausdorff_space (subtopology top (topspace top DIFF K)) /\
            smooth_manifold_atlas (subtopology top (topspace top DIFF K))
                                  (restrict_atlas atlas (topspace top DIFF K)) /\
            rfs_components_s3 (subtopology top (topspace top DIFF K))
                              (restrict_atlas atlas (topspace top DIFF K))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (topspace top DIFF K:A->bool) /\
                closed_in top (topspace top DIFF K:A->bool)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_DIFF; CLOSED_IN_DIFF; OPEN_IN_TOPSPACE; CLOSED_IN_TOPSPACE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY];
    MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_components_s3 top (atlas:((A->bool)#(A->real^3))->bool)` THEN
  REWRITE_TAC[rfs_components_s3] THEN DISCH_TAC THEN
  X_GEN_TAC `U:A->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `topspace top DIFF K:A->bool`; `U:A->bool`]
    MSY_COMPONENT_CLOPEN_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; RFS_RESTRICT_ATLAS_RESTRICT] THEN
  SUBGOAL_THEN `(topspace top DIFF K) INTER U = U:A->bool` SUBST1_TAC THENL
   [UNDISCH_TAC `U SUBSET topspace top DIFF (K:A->bool)` THEN SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The base case: a diffeomorphism of the whole spaces.                      *)

let MSY_S3_DIFFEO = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topZ (atlasZ:((B->bool)#(B->real^3))->bool) ff gg.
        smooth_manifold_atlas topX atlasX /\ smooth_manifold_atlas topZ atlasZ /\
        mfd_diffeo topX atlasX (topspace topX) topZ atlasZ (topspace topZ) ff gg /\
        rfs_components_s3 topZ atlasZ
        ==> rfs_components_s3 topX atlasX`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_components_s3] THEN X_GEN_TAC `U:A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `homeomorphic_map (topX,topZ) (ff:A->B)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_diffeo topX (atlasX:((A->bool)#(A->real^3))->bool) (topspace topX)
                            topZ (atlasZ:((B->bool)#(B->real^3))->bool) (topspace topZ)
                            ff gg` THEN
    REWRITE_TAC[mfd_diffeo; SUBTOPOLOGY_TOPSPACE] THEN MESON_TAC[HOMEOMORPHIC_MAPS_IMP_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ff:A->B) U IN connected_components_of topZ` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP HOMEOMORPHIC_MAP_CONNECTED_COMPONENTS_OF th]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in topX (U:A->bool) /\ open_in topZ (IMAGE (ff:A->B) U)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] APX_COMPONENT_OPEN) THENL
     [EXISTS_TAC `atlasX:((A->bool)#(A->real^3))->bool`;
      EXISTS_TAC `atlasZ:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_DIFFEOMORPHIC_TRANS) THEN
  MAP_EVERY EXISTS_TAC [`subtopology topZ (IMAGE (ff:A->B) U)`;
                        `restrict_atlas (atlasZ:((B->bool)#(B->real^3))->bool)
                                        (IMAGE (ff:A->B) U)`] THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; SPHERE3_ATLAS] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:A)`; `(:B)`] APX_DIFFEO_SUBSPACE) THEN
    REWRITE_TAC[APX_DIFFEO_SUBSPACE_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ff:A->B`; `gg:B->A`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`topspace topX:A->bool`; `topspace topZ:B->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET];
    UNDISCH_TAC `rfs_components_s3 topZ (atlasZ:((B->bool)#(B->real^3))->bool)` THEN
    REWRITE_TAC[rfs_components_s3] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The rest of the complement of a closed set, off one of its components.    *)

let MSY_SIDE_REST_OPEN = prove
 (`!top S (p:A).
        closed_in top S
        ==> open_in top ((topspace top DIFF S) DIFF
                         connected_component_of (subtopology top (topspace top DIFF S)) p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
  EXISTS_TAC `topspace top DIFF S:A->bool` THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN
  MP_TAC(ISPECL [`subtopology top (topspace top DIFF S:A->bool)`; `p:A`]
    CLOSED_IN_CONNECTED_COMPONENT_OF) THEN
  REWRITE_TAC[closed_in; TOPSPACE_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `topspace top INTER (topspace top DIFF S) = topspace top DIFF S:A->bool`
  SUBST1_TAC THENL [SET_TAC[]; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The induction.  A leaf side meets no other neck (LSP_LEAF);              *)
(* reflecting the neck makes it the inner side; Zc = ff(D) + cap is a       *)
(* component of Z, so S^3, D is a ball, and the cut data with the neck      *)
(* removed map X onto Z minus Zc.  Induction on the number of necks; the    *)
(* empty cut is a diffeomorphism of the whole spaces.                        *)
(* ------------------------------------------------------------------------- *)

let MSY_LEAF_INNER = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topZ (atlasZ:((B->bool)#(B->real^3))->bool) J e cp cm ff gg.
        hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\
        apx_sphere_sep topX atlasX /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm ff gg /\ ~(J = {})
        ==> ?i0 e' cp' cm'.
              i0 IN J /\ mfd_cut_cap topX atlasX topZ atlasZ J e' cp' cm' ff gg /\
              !j. j IN J /\ ~(j = i0)
                  ==> DISJOINT (IMAGE (e' j) (annulus (&1 / &2) (&2)))
                               (lsp_side topX (e' i0) (&3 / &4))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_cut_cap] o check (fun th ->
    can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_cut_cap")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "charts")
    (CONJUNCTS_THEN2 (LABEL_TAC "ndisj") (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`] LSP_LEAF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "charts" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i0:num` (X_CHOOSE_THEN `r:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "leaf"))))) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [MAP_EVERY EXISTS_TAC [`i0:num`; `e:num->real^3->A`; `cp:num->real^3->B`;
                          `cm:num->real^3->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->B`;
                 `cm:num->real^3->B`; `ff:A->B`; `gg:B->A`; `i0:num`] MSY_CUT_REFLECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`i0:num`;
    `\i. if i = i0 then (\x. (e:num->real^3->A) i0 (inv(norm x pow 2) % x)) else e i`;
    `\i. if i = i0 then (cm:num->real^3->B) i0 else (cp:num->real^3->B) i`;
    `\i. if i = i0 then (cp:num->real^3->B) i0 else (cm:num->real^3->B) i`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `lsp_side topX (\x. (e:num->real^3->A) i0 (inv(norm x pow 2) % x)) (&3 / &4) =
    lsp_side topX (e i0) (&4 / &3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[lsp_side] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `(e:num->real^3->A) i0`] MSY_NECK_REFLECT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "charts" (MP_TAC o SPEC `i0:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      DISCH_THEN(STRIP_ASSUME_TAC o BETA_RULE)] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "leaf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* One step: remove the leaf neck and the component Zc.                      *)

let MSY_STEP = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topZ (atlasZ:((B->bool)#(B->real^3))->bool) J e cp cm ff gg.
        hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\
        apx_sphere_sep topX atlasX /\
        hausdorff_space topZ /\ smooth_manifold_atlas topZ atlasZ /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm ff gg /\ ~(J = {}) /\
        rfs_components_s3 topZ atlasZ
        ==> ?topZ' (atlasZ':((B->bool)#(B->real^3))->bool) J' e' cp' cm' ff' gg'.
              J' PSUBSET J /\
              hausdorff_space topZ' /\ smooth_manifold_atlas topZ' atlasZ' /\
              mfd_cut_cap topX atlasX topZ' atlasZ' J' e' cp' cm' ff' gg' /\
              rfs_components_s3 topZ' atlasZ'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->B`;
                 `cm:num->real^3->B`; `ff:A->B`; `gg:B->A`] MSY_LEAF_INNER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i0:num` (X_CHOOSE_THEN `e1:num->real^3->A`
    (X_CHOOSE_THEN `cp1:num->real^3->B` (X_CHOOSE_THEN `cm1:num->real^3->B`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "leaf"))))))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_cut_cap] o check (fun th ->
    can (find_term ((=) `e1:num->real^3->A`)) (concl th) &&
    can (find_term (fun u -> is_const u && fst(dest_const u) = "mfd_cut_cap")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "charts") (K ALL_TAC))) THEN
  USE_THEN "charts" (MP_TAC o SPEC `i0:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `D = lsp_side topX ((e1:num->real^3->A) i0) (&3 / &4)` THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `(e1:num->real^3->A) i0`] LSP_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `(e1:num->real^3->A) i0`] LSP_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `&3 / &4` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `(e1:num->real^3->A) i0`] LSP_SIDE_HALVES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in topX ((topspace topX DIFF IMAGE ((e1:num->real^3->A) i0) (sphere(vec 0,&1)))
                  DIFF D)`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[lsp_side] THEN MATCH_MP_TAC MSY_SIDE_REST_OPEN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Zc = IMAGE (ff:A->B) D UNION IMAGE ((cm1:num->real^3->B) i0) (ball(vec 0,&2))` THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e1:num->real^3->A`; `cp1:num->real^3->B`;
                 `cm1:num->real^3->B`; `ff:A->B`; `gg:B->A`; `i0:num`; `D:A->bool`;
                 `Zc:B->bool`] MSY_ZC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(Zc:B->bool) IN connected_components_of topZ` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_CLOPEN_COMPONENT THEN ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `(cm1:num->real^3->B) i0 (vec 0)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeomorphic (subtopology topZ Zc)
                      (restrict_atlas (atlasZ:((B->bool)#(B->real^3))->bool) Zc)
                      (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_components_s3 topZ (atlasZ:((B->bool)#(B->real^3))->bool)` THEN
    REWRITE_TAC[rfs_components_s3] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (D:A->bool) (IMAGE ((e1:num->real^3->A) i0) (sphere(vec 0,&1))) /\
    IMAGE ((cm1:num->real^3->B) i0) (ball(vec 0,&2)) SUBSET Zc`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(D:A->bool) SUBSET
                   topspace topX DIFF IMAGE ((e1:num->real^3->A) i0) (sphere(vec 0,&1))` THEN
      SET_TAC[];
      EXPAND_TAC "Zc" THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e1:num->real^3->A`; `cp1:num->real^3->B`;
                 `cm1:num->real^3->B`; `ff:A->B`; `gg:B->A`; `i0:num`; `D:A->bool`;
                 `Zc:B->bool`] MSY_LEAF_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `b:real^3->A` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e1:num->real^3->A`; `cp1:num->real^3->B`;
                 `cm1:num->real^3->B`; `ff:A->B`; `gg:B->A`; `i0:num`; `D:A->bool`;
                 `Zc:B->bool`; `b:real^3->A`] MSY_NEW_CUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff':A->B` (X_CHOOSE_THEN `gg':B->A` ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`; `Zc:B->bool`]
    MSY_REMOVE_CLOPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`subtopology topZ (topspace topZ DIFF Zc:B->bool)`;
    `restrict_atlas (atlasZ:((B->bool)#(B->real^3))->bool) (topspace topZ DIFF Zc)`;
    `J DELETE (i0:num)`; `e1:num->real^3->A`; `cp1:num->real^3->B`; `cm1:num->real^3->B`;
    `ff':A->B`; `gg':B->A`] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(i0:num) IN J` THEN SET_TAC[]);;

(* The induction on the number of necks.                                     *)

let MSY_SYSTEM = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topZ (atlasZ:((B->bool)#(B->real^3))->bool) J e cp cm ff gg.
        hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\
        apx_sphere_sep topX atlasX /\
        hausdorff_space topZ /\ smooth_manifold_atlas topZ atlasZ /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm ff gg /\
        rfs_components_s3 topZ atlasZ
        ==> rfs_components_s3 topX atlasX`,
  GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN
   `!n topZ (atlasZ:((B->bool)#(B->real^3))->bool) J (e:num->real^3->A) cp cm ff gg.
      CARD J = n /\
      hausdorff_space topX /\
      smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
      apx_sphere_sep topX atlasX /\
      hausdorff_space topZ /\ smooth_manifold_atlas topZ atlasZ /\
      mfd_cut_cap topX atlasX topZ atlasZ J e cp cm ff gg /\
      rfs_components_s3 topZ atlasZ
      ==> rfs_components_s3 topX atlasX`
  (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(J:num->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_cut_cap topX (atlasX:((A->bool)#(A->real^3))->bool)
                             topZ (atlasZ:((B->bool)#(B->real^3))->bool)
                             J e cp cm (ff:A->B) gg` THEN
    SIMP_TAC[mfd_cut_cap];
    ALL_TAC] THEN
  ASM_CASES_TAC `J:num->bool = {}` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                   `ff:A->B`; `gg:B->A`] MSY_S3_DIFFEO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `mfd_cut_cap topX (atlasX:((A->bool)#(A->real^3))->bool)
                             topZ (atlasZ:((B->bool)#(B->real^3))->bool)
                             {} e cp cm (ff:A->B) gg` THEN
    REWRITE_TAC[MFD_CUT_CAP_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->B`;
                 `cm:num->real^3->B`; `ff:A->B`; `gg:B->A`] MSY_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `topZ':B topology`
    (X_CHOOSE_THEN `atlasZ':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `J':num->bool` (X_CHOOSE_THEN `e':num->real^3->A`
    (X_CHOOSE_THEN `cp':num->real^3->B` (X_CHOOSE_THEN `cm':num->real^3->B`
    (X_CHOOSE_THEN `ff':A->B` (X_CHOOSE_THEN `gg':B->A` STRIP_ASSUME_TAC)))))))) THEN
  USE_THEN "ih" (MP_TAC o SPEC `CARD(J':num->bool)`) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "n" THEN MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`topZ':B topology`; `atlasZ':((B->bool)#(B->real^3))->bool`;
                             `J':num->bool`; `e':num->real^3->A`; `cp':num->real^3->B`;
                             `cm':num->real^3->B`; `ff':A->B`; `gg':B->A`]) THEN
  ASM_REWRITE_TAC[]);;

(* M11: the sphere system statement.                                         *)

let RFS_SPHERE_SYSTEM = prove
 (`!(u:A->bool) (v:B->bool). RFS_SPHERE_SYSTEM_STATEMENT u v`,
  REWRITE_TAC[RFS_SPHERE_SYSTEM_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->B`;
                 `cm:num->real^3->B`; `ff:A->B`; `gg:B->A`] MSY_SYSTEM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPEC `(:A)` SMT_SC_SPHERE_SEP) THEN
  REWRITE_TAC[APX_SC_SPHERE_SEP_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM rfs_components_sc]);;

