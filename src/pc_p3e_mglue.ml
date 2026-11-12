(* ========================================================================= *)
(* pc_p3e_mglue: the glued metric on the retained part Y of a cut-and-capped *)
(* manifold (step S4a of the proof of MT Lemma 15.11).  Setting: the         *)
(* cut-and-cap data of pc_p3e_cutcap (Z = p3e_ctop, atlas p3e_catlas), a     *)
(* clopen discarded set D of Z containing the plus cores and missing the    *)
(* minus cores, Y = Z minus D with the restricted atlas, an open set Om of  *)
(* X containing the old points of Y with a metric gl (metric fields in the  *)
(* X charts over Om), and cap fields Gc i on ball(0,2) compatible with gl   *)
(* on the collars (Gc i is the inversion pullback of the neck pullback of  *)
(* gl there).  The glued metric p3e_gmet is the formal representative of   *)
(* gl in the preferred Y chart at old points and Gc i in the cap chart at  *)
(* the core points.  Results: riemannian on Y, the same metric as gl on the *)
(* old points (rfs_same_metric_on), its representative in the cap charts,  *)
(* and its pullbacks by parametrizations.                                    *)
(* ========================================================================= *)

needs "src/pc_p3e_cutcap.ml";;
needs "src/pc_mfd_restrict.ml";;
needs "src/pc_rfs_geom.ml";;
needs "src/pc_p2b_gpb.ml";;
needs "src/pc_apx_local.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The retained part Y = Z minus D, its atlas, the hypothesis                *)
(* bundle p3e_mgdata and the glued metric p3e_gmet; basic facts on Y: a    *)
(* compact Hausdorff smooth manifold, the old points W = Y INTER X are open *)
(* in X and in Z, the minus cap charts lie in Y, the plus caps in D.         *)
(* ------------------------------------------------------------------------- *)

let p3e_ysp = new_definition
 `p3e_ysp (topX:B topology) (J:num->bool) (e:num->real^3->B)
          (nw:num->bool->real^3->B) (D:B->bool) =
    topspace (p3e_ctop topX J e nw) DIFF D`;;

let p3e_ytop = new_definition
 `p3e_ytop (topX:B topology) (J:num->bool) (e:num->real^3->B)
           (nw:num->bool->real^3->B) (D:B->bool) =
    subtopology (p3e_ctop topX J e nw) (p3e_ysp topX J e nw D)`;;

let p3e_yatlas = new_definition
 `p3e_yatlas (topX:B topology) (atlasX:((B->bool)#(B->real^3))->bool) (J:num->bool)
             (e:num->real^3->B) (nw:num->bool->real^3->B) (D:B->bool) =
    restrict_atlas (p3e_catlas topX atlasX J e nw) (p3e_ysp topX J e nw D)`;;

let p3e_mgdata = new_definition
 `p3e_mgdata (topX:B topology) (atlasX:((B->bool)#(B->real^3))->bool) (J:num->bool)
             (e:num->real^3->B) (nw:num->bool->real^3->B) (D:B->bool) (Om:B->bool)
             (gl:B->real^3^3) (Gc:num->real^3->real^3^3) <=>
    p3e_cutdata topX atlasX J e nw /\
    open_in (p3e_ctop topX J e nw) D /\ closed_in (p3e_ctop topX J e nw) D /\
    (!i. i IN J
         ==> IMAGE (p3e_ccp e nw i) (cball(vec 0,&1)) SUBSET D /\
             DISJOINT (IMAGE (p3e_ccm e nw i) (cball(vec 0,&1))) D) /\
    open_in topX Om /\
    p3e_ysp topX J e nw D INTER topspace topX SUBSET Om /\
    (!c. c IN atlasX
         ==> metric_field (IMAGE (SND c) (FST c INTER Om)) (metric_local atlasX c gl)) /\
    (!i. i IN J ==> metric_field (ball(vec 0,&2)) (Gc i)) /\
    (!i z. i IN J /\ &1 < norm z /\ norm z < &2
           ==> Gc i z = mpullback (\w:real^3. inv(norm w pow 2) % w)
                                  (rfs_pullback atlasX (e i) gl) z)`;;

let p3e_gmet = new_definition
 `p3e_gmet (topX:B topology) (atlasX:((B->bool)#(B->real^3))->bool) (J:num->bool)
           (e:num->real^3->B) (nw:num->bool->real^3->B) (D:B->bool)
           (gl:B->real^3^3) (Gc:num->real^3->real^3^3) =
    \p. if p IN topspace topX
        then metric_local atlasX (chart_at (p3e_yatlas topX atlasX J e nw D) p) gl
                          (SND(chart_at (p3e_yatlas topX atlasX J e nw D) p) p)
        else Gc (@i. i IN J /\ p IN IMAGE (p3e_ccm e nw i) (cball(vec 0,&1)))
                (SND(chart_at (p3e_yatlas topX atlasX J e nw D) p) p)`;;

let P3E_MG_Y = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc.
     p3e_mgdata topX atlasX J e nw D Om gl Gc
     ==> open_in (p3e_ctop topX J e nw) (p3e_ysp topX J e nw D) /\
         closed_in (p3e_ctop topX J e nw) (p3e_ysp topX J e nw D) /\
         topspace (p3e_ytop topX J e nw D) = p3e_ysp topX J e nw D /\
         hausdorff_space (p3e_ytop topX J e nw D) /\
         compact_space (p3e_ytop topX J e nw D) /\
         smooth_manifold_atlas (p3e_ytop topX J e nw D)
                               (p3e_yatlas topX atlasX J e nw D)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3e_mgdata] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_CUTCAP_FACTS) THEN
  SUBGOAL_THEN
   `open_in (p3e_ctop topX J e nw) (p3e_ysp topX J e nw D) /\
    closed_in (p3e_ctop topX J e nw) (p3e_ysp (topX:B topology) J e nw D)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p3e_ysp] THEN CONJ_TAC THENL
     [UNDISCH_TAC `closed_in (p3e_ctop topX J e nw) (D:B->bool)` THEN
      SIMP_TAC[closed_in];
      MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p3e_ytop; p3e_yatlas; TOPSPACE_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[p3e_ysp] THEN SET_TAC[];
    MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[]]);;

let P3E_MG_OLD = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc.
     p3e_mgdata topX atlasX J e nw D Om gl Gc
     ==> p3e_ysp topX J e nw D INTER topspace topX =
         p3e_ysp topX J e nw D INTER (topspace topX DIFF mfd_cut_spheres J e) /\
         open_in topX (p3e_ysp topX J e nw D INTER topspace topX) /\
         open_in (p3e_ctop topX J e nw) (p3e_ysp topX J e nw D INTER topspace topX) /\
         p3e_ysp topX J e nw D INTER topspace topX SUBSET Om`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_mgdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_CUTCAP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_CTOP_OLD) THEN
  SUBGOAL_THEN
   `p3e_ysp topX J e nw D INTER topspace topX =
    p3e_ysp topX J e nw D INTER (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `topspace (p3e_ctop topX J e nw) = p3e_czs (topX:B topology) J e nw` THEN
    UNDISCH_TAC
     `DISJOINT (topspace (topX:B topology))
               (mfd_cut_cores J (p3e_ccp e nw) (p3e_ccm e nw))` THEN
    REWRITE_TAC[p3e_ysp; p3e_czs] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (p3e_ctop topX J e nw)
            (p3e_ysp topX J e nw D INTER topspace (topX:B topology))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
  EXISTS_TAC `topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B)` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o CONJUNCT2 o MATCH_MP P3E_CTOP_OLD) THEN
    SUBGOAL_THEN
     `p3e_ysp topX J e nw D INTER (topspace topX DIFF mfd_cut_spheres J e) =
      (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B)) INTER
      (p3e_ysp topX J e nw D INTER (topspace topX DIFF mfd_cut_spheres J e))`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN
    UNDISCH_TAC
     `open_in (p3e_ctop topX J e nw)
              (p3e_ysp topX J e nw D INTER topspace (topX:B topology))` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP P3E_CUT_SPHERES_COMPACT th)) THEN
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Charts of Y.  The minus cap images lie in Y and the plus                  *)
(* cap images in D (connectedness, D clopen); restricted X charts and the   *)
(* minus cap charts are charts of Y; a point of Y outside X is a minus      *)
(* core point cm i z (|z| <= 1), the cm i chart is the only chart of Y at   *)
(* it, and i is the index selected in p3e_gmet.                             *)
(* ------------------------------------------------------------------------- *)

let P3E_MG_CAPS = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc i.
     p3e_mgdata topX atlasX J e nw D Om gl Gc /\ i IN J
     ==> IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)) SUBSET p3e_ysp topX J e nw D /\
         IMAGE (p3e_ccp e nw i) (ball(vec 0,&2)) SUBSET D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_mgdata]) THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                 `i:num`] P3E_CAP_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `connected_in (subtopology euclidean (ball(vec 0:real^3,&2))) (ball(vec 0,&2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL; CONNECTED_IN_EUCLIDEAN;
                CONNECTED_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p3e_ccp e nw i) (cball(vec 0,&1)) SUBSET D /\
    DISJOINT (IMAGE (p3e_ccm e nw i) (cball(vec 0,&1))) (D:B->bool)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^3) IN cball(vec 0,&1) /\ (vec 0:real^3) IN ball(vec 0,&2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0; IN_BALL_0; NORM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`p3e_ctop (topX:B topology) J e nw`;
                   `IMAGE (p3e_ccm (e:num->real^3->B) nw i) (ball(vec 0:real^3,&2))`; `D:B->bool`]
      CONNECTED_IN_CLOPEN_CASES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,&2))` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^3,&2))`;
                   `p3e_ctop (topX:B topology) J e nw`; `p3e_ccm (e:num->real^3->B) nw i`]
      CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; p3e_ysp] THEN
    SUBGOAL_THEN
     `p3e_ccm e nw i (vec 0) IN IMAGE (p3e_ccm e nw i) (ball(vec 0:real^3,&2)) /\
      ~(p3e_ccm e nw i (vec 0) IN (D:B->bool))`
    MP_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC
       `DISJOINT (IMAGE (p3e_ccm e nw i) (cball(vec 0:real^3,&1))) (D:B->bool)` THEN
      UNDISCH_TAC `(vec 0:real^3) IN cball(vec 0,&1)` THEN SET_TAC[];
      SET_TAC[]];
    MP_TAC(ISPECL [`p3e_ctop (topX:B topology) J e nw`;
                   `IMAGE (p3e_ccp (e:num->real^3->B) nw i) (ball(vec 0:real^3,&2))`; `D:B->bool`]
      CONNECTED_IN_CLOPEN_CASES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,&2))` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `p3e_ccp e nw i (vec 0) IN IMAGE (p3e_ccp e nw i) (ball(vec 0:real^3,&2)) /\
      p3e_ccp e nw i (vec 0) IN (D:B->bool)`
    MP_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC
       `IMAGE (p3e_ccp e nw i) (cball(vec 0:real^3,&1)) SUBSET (D:B->bool)` THEN
      UNDISCH_TAC `(vec 0:real^3) IN cball(vec 0,&1)` THEN SET_TAC[];
      SET_TAC[]]]);;

let P3E_MG_XCHART = prove
 (`!(topX:B topology) atlasX J e nw D V psi.
     (V,psi) IN atlasX
     ==> ((V INTER (topspace topX DIFF mfd_cut_spheres J e)) INTER
          p3e_ysp topX J e nw D,psi) IN p3e_yatlas topX atlasX J e nw D`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3e_yatlas; IN_RESTRICT_ATLAS] THEN
  EXISTS_TAC `V INTER (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B))` THEN
  REWRITE_TAC[IN_P3E_CATLAS] THEN DISJ1_TAC THEN
  EXISTS_TAC `V:B->bool` THEN ASM_REWRITE_TAC[]);;

let P3E_MG_CMCHART = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc i.
     p3e_mgdata topX atlasX J e nw D Om gl Gc /\ i IN J
     ==> (IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)),p3e_cinv (p3e_ccm e nw i))
         IN p3e_yatlas topX atlasX J e nw D`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL P3E_MG_CAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p3e_yatlas; IN_RESTRICT_ATLAS] THEN
  EXISTS_TAC `IMAGE (p3e_ccm (e:num->real^3->B) nw i) (ball(vec 0:real^3,&2))` THEN
  REWRITE_TAC[IN_P3E_CATLAS] THEN CONJ_TAC THENL
   [DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

let P3E_MG_NEWPT = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc p.
     p3e_mgdata topX atlasX J e nw D Om gl Gc /\
     p IN p3e_ysp topX J e nw D /\ ~(p IN topspace topX)
     ==> ?i z. i IN J /\ norm z <= &1 /\ p = p3e_ccm e nw i z /\
               (!c. c IN p3e_yatlas topX atlasX J e nw D /\ p IN FST c
                    ==> c = (IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)),
                             p3e_cinv (p3e_ccm e nw i))) /\
               (@i'. i' IN J /\ p IN IMAGE (p3e_ccm e nw i') (cball(vec 0,&1))) = i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_mgdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_CUTCAP_FACTS) THEN
  SUBGOAL_THEN
   `?i z. i IN J /\ norm z <= &1 /\ p = p3e_ccm (e:num->real^3->B) nw i z`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?i z. i IN J /\ norm z <= &1 /\
            (p = p3e_ccp e nw i z \/ p = p3e_ccm (e:num->real^3->B) nw i z)`
    MP_TAC THENL
     [REWRITE_TAC[GSYM IN_MFD_CUT_CORES; ETA_AX] THEN
      UNDISCH_TAC `p IN p3e_ysp (topX:B topology) J e nw D` THEN
      UNDISCH_TAC `~((p:B) IN topspace topX)` THEN
      ASM_REWRITE_TAC[p3e_ysp; p3e_czs] THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `w:real^3`] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `(p:B) IN D` MP_TAC THENL
       [SUBGOAL_THEN `IMAGE (p3e_ccp e nw j) (cball(vec 0:real^3,&1)) SUBSET (D:B->bool)`
        MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0] THEN
        DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `p IN p3e_ysp (topX:B topology) J e nw D` THEN
        REWRITE_TAC[p3e_ysp] THEN SET_TAC[]];
      MAP_EVERY EXISTS_TAC [`j:num`; `w:real^3`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `p:B`)) THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `z:real^3`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!j w. j IN J /\ w IN ball(vec 0:real^3,&2) /\ ~(norm w <= &1)
          ==> p3e_ccp e nw j w IN topspace topX /\
              p3e_ccm e nw j w IN topspace (topX:B topology)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `j:num`; `w:real^3`]
      P3E_CAP_VALUES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                     `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                     `j:num`; `w:real^3`] P3E_NECK_OFF_SPHERES);
      MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                     `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                     `j:num`; `inv(norm(w:real^3) pow 2) % w`] P3E_NECK_OFF_SPHERES)] THEN
    ASM_REWRITE_TAC[P3E_ANNULUS_HALF_TWO] THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SET_TAC[]]);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; p3e_yatlas; IN_RESTRICT_ATLAS; FST] THEN
    MAP_EVERY X_GEN_TAC [`U:B->bool`; `phi:B->real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `U0:B->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    UNDISCH_TAC `(U0:B->bool,phi:B->real^3) IN p3e_catlas topX atlasX J e nw` THEN
    REWRITE_TAC[IN_P3E_CATLAS] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(X_CHOOSE_THEN `V:B->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~(p3e_ccm e nw i z IN topspace (topX:B topology))` THEN
      UNDISCH_TAC `p3e_ccm e nw i z IN (U:B->bool)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `?w. w IN ball(vec 0:real^3,&2) /\
            p3e_ccm e nw i z = p3e_ccp (e:num->real^3->B) nw j w`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `p3e_ccm e nw i z IN (U:B->bool)` THEN
        ASM_REWRITE_TAC[IN_INTER; IN_IMAGE] THEN MESON_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `norm(w:real^3) <= &1` THENL
       [SUBGOAL_THEN `(nw:num->bool->real^3->B) i F z = nw j T w` MP_TAC THENL
         [UNDISCH_TAC `p3e_ccm e nw i z = p3e_ccp (e:num->real^3->B) nw j w` THEN
          ASM_REWRITE_TAC[p3e_ccm; p3e_ccp];
          FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_NW_EQ th])];
        UNDISCH_TAC `~(p3e_ccm e nw i z IN topspace (topX:B topology))` THEN
        ASM_SIMP_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `?w. w IN ball(vec 0:real^3,&2) /\
            p3e_ccm e nw i z = p3e_ccm (e:num->real^3->B) nw j w`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `p3e_ccm e nw i z IN (U:B->bool)` THEN
        ASM_REWRITE_TAC[IN_INTER; IN_IMAGE] THEN MESON_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `norm(w:real^3) <= &1` THENL
       [SUBGOAL_THEN `(nw:num->bool->real^3->B) i F z = nw j F w` MP_TAC THENL
         [UNDISCH_TAC `p3e_ccm e nw i z = p3e_ccm (e:num->real^3->B) nw j w` THEN
          ASM_REWRITE_TAC[p3e_ccm];
          FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_NW_EQ th])] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
        MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                       `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                       `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`;
                       `Gc:num->real^3->real^3^3`; `i:num`] P3E_MG_CAPS) THEN
        ASM_REWRITE_TAC[PAIR_EQ] THEN SET_TAC[];
        UNDISCH_TAC `~(p3e_ccm e nw i z IN topspace (topX:B topology))` THEN
        ASM_SIMP_TAC[]]];
    MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `j:num` THEN EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(nw:num->bool->real^3->B) i F z = nw j F w` MP_TAC THENL
       [UNDISCH_TAC `p3e_ccm e nw i z = p3e_ccm (e:num->real^3->B) nw j w` THEN
        ASM_REWRITE_TAC[p3e_ccm];
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_NW_EQ th]) THEN MESON_TAC[]];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Representatives of the glued metric.  At an old point p, in               *)
(* every chart c of Y, the representative is the formal representative of  *)
(* gl in c (P3E_GMET_FORMAL: the chain rule for chart Jacobians in the Y    *)
(* atlas, which contains the restricted X charts); hence the pullback of    *)
(* gl's representative by the transition to any X chart (P3E_GMET_OLD_REP). *)
(* In the cm i chart the representative is Gc i on all of ball(0,2)        *)
(* (P3E_GMET_CAP_REP: the cores by definition, the collar by the            *)
(* compatibility hypothesis).                                               *)
(* ------------------------------------------------------------------------- *)

let P3E_FORMAL_REP_AUX = prove
 (`!(TY:B topology) (AY:((B->bool)#(B->real^3))->bool) topX atlasX S
    (gl:B->real^3^3) U phi UY phiY UX phiX p.
     smooth_manifold_atlas TY AY /\ smooth_manifold_atlas topX atlasX /\
     (U,phi) IN AY /\ (UY,phiY) IN AY /\ (UX,phiX) IN atlasX /\
     (UX INTER S,phiX) IN AY /\
     p IN U /\ p IN UY /\ p IN UX /\ p IN S /\
     chart_at atlasX p = (UX,phiX)
     ==> transp(matrix(chart_jac (U,phi) (UY,phiY) p)) **
         metric_local atlasX (UY,phiY) gl (phiY p) **
         matrix(chart_jac (U,phi) (UY,phiY) p) =
         metric_local atlasX (U,phi) gl (phi p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (U:B->bool,phi) ((phi:B->real^3) p) = p /\
                chart_inv (UY:B->bool,phiY) ((phiY:B->real^3) p) = p`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[CHART_INV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[metric_local] THEN
  SUBGOAL_THEN
   `chart_jac (U,phi:B->real^3) (UX,phiX:B->real^3) (p:B) =
    chart_jac (UY,phiY:B->real^3) (UX,phiX) p o chart_jac (U,phi) (UY,phiY) p`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`TY:B topology`; `AY:((B->bool)#(B->real^3))->bool`;
                   `U:B->bool`; `phi:B->real^3`; `UY:B->bool`; `phiY:B->real^3`;
                   `UX INTER S:B->bool`; `phiX:B->real^3`; `p:B`] CHART_JAC_CHAIN) THEN
    ASM_REWRITE_TAC[IN_INTER; MFDR_CHART_JAC_RESTRICT_R] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(chart_jac (UY,phiY:B->real^3) (UX,phiX:B->real^3) (p:B)) /\
    linear(chart_jac (U,phi:B->real^3) (UY,phiY) (p:B))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`TY:B topology`; `AY:((B->bool)#(B->real^3))->bool`;
                     `UY:B->bool`; `phiY:B->real^3`;
                     `UX INTER S:B->bool`; `phiX:B->real^3`; `p:B`] CHART_JAC_LINEAR);
      MP_TAC(ISPECL [`TY:B topology`; `AY:((B->bool)#(B->real^3))->bool`;
                     `U:B->bool`; `phi:B->real^3`;
                     `UY:B->bool`; `phiY:B->real^3`; `p:B`] CHART_JAC_LINEAR)] THEN
    ASM_REWRITE_TAC[IN_INTER; MFDR_CHART_JAC_RESTRICT_R];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

let P3E_MG_XCHART_S = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc V psi.
     p3e_mgdata topX atlasX J e nw D Om gl Gc /\ (V,psi) IN atlasX
     ==> (V INTER (p3e_ysp topX J e nw D INTER topspace topX),psi)
         IN p3e_yatlas topX atlasX J e nw D`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_OLD) THEN
  SUBGOAL_THEN
   `V INTER (p3e_ysp topX J e nw D INTER topspace topX) =
    (V INTER (topspace topX DIFF mfd_cut_spheres J e)) INTER
    p3e_ysp (topX:B topology) J e nw D`
  SUBST1_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[P3E_MG_XCHART]]);;

let P3E_GMET_FORMAL = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc c p.
     p3e_mgdata topX atlasX J e nw D Om gl Gc /\
     c IN p3e_yatlas topX atlasX J e nw D /\ p IN FST c /\ p IN topspace topX
     ==> metric_local (p3e_yatlas topX atlasX J e nw D) c
                      (p3e_gmet topX atlasX J e nw D gl Gc) (SND c p) =
         metric_local atlasX c gl (SND c p)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `c:(B->bool)#(B->real^3)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `U:B->bool` (X_CHOOSE_THEN `phi:B->real^3` SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_OLD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_mgdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_CUTCAP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_cutdata]) THEN
  SUBGOAL_THEN `(p:B) IN topspace (p3e_ytop topX J e nw D)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                   `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                   `U:B->bool`; `phi:B->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    UNDISCH_TAC `(p:B) IN U` THEN
    UNDISCH_TAC `topspace (p3e_ytop topX J e nw D) = p3e_ysp (topX:B topology) J e nw D` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:B) IN p3e_ysp topX J e nw D INTER topspace topX` ASSUME_TAC THENL
   [UNDISCH_TAC `(p:B) IN topspace (p3e_ytop topX J e nw D)` THEN
    UNDISCH_TAC `(p:B) IN topspace topX` THEN
    UNDISCH_TAC `topspace (p3e_ytop topX J e nw D) = p3e_ysp (topX:B topology) J e nw D` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                 `p3e_yatlas (topX:B topology) atlasX J e nw D`; `p:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (p3e_yatlas (topX:B topology) atlasX J e nw D) p`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `UY:B->bool` (X_CHOOSE_THEN `phiY:B->real^3` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `p:B`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlasX:((B->bool)#(B->real^3))->bool) p` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `UX:B->bool` (X_CHOOSE_THEN `phiX:B->real^3` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                 `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                 `U:B->bool`; `phi:B->real^3`; `UY:B->bool`; `phiY:B->real^3`;
                 `p3e_gmet (topX:B topology) atlasX J e nw D gl Gc`; `p:B`]
    METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                 `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                 `p3e_gmet (topX:B topology) atlasX J e nw D gl Gc`; `p:B`]
    METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p3e_gmet] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3E_FORMAL_REP_AUX THEN
  MAP_EVERY EXISTS_TAC
   [`p3e_ytop (topX:B topology) J e nw D`;
    `p3e_yatlas (topX:B topology) atlasX J e nw D`; `topX:B topology`;
    `p3e_ysp (topX:B topology) J e nw D INTER topspace topX`;
    `UX:B->bool`; `phiX:B->real^3`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_MESON_TAC[P3E_MG_XCHART_S]);;

(* ------------------------------------------------------------------------- *)
(* Formal transformation laws (generic chain-rule lemmas for                 *)
(* charts of a Y-type atlas containing the restrictions of the X charts to  *)
(* an open set S), and their consequences for the glued metric: the        *)
(* representative at old points is the pullback of gl's representative by  *)
(* the transition to any X chart (P3E_GMET_OLD_REP), and the glued metric  *)
(* is gl on the old points (P3E_GMET_SAME, rfs_same_metric_on).            *)
(* ------------------------------------------------------------------------- *)

let P3E_FORMAL_TRANS_AUX = prove
 (`!(TY:B topology) (AY:((B->bool)#(B->real^3))->bool) topX atlasX S
    (gl:B->real^3^3) U phi V psi UX phiX p.
     smooth_manifold_atlas TY AY /\ smooth_manifold_atlas topX atlasX /\
     open_in topX S /\
     (U,phi) IN AY /\ (V,psi) IN atlasX /\ (V INTER S,psi) IN AY /\
     (UX,phiX) IN atlasX /\ (UX INTER S,phiX) IN AY /\
     p IN U /\ p IN V /\ p IN UX /\ p IN S /\
     chart_at atlasX p = (UX,phiX)
     ==> metric_local atlasX (U,phi) gl (phi p) =
         mpullback (chart_trans (U,phi) (V,psi)) (metric_local atlasX (V,psi) gl)
                   (phi p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (U:B->bool,phi) ((phi:B->real^3) p) = p /\
                chart_inv (V:B->bool,psi) ((psi:B->real^3) p) = p`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[CHART_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_trans (U:B->bool,phi:B->real^3) (V,psi) (phi p) = psi p`
  ASSUME_TAC THENL [ASM_MESON_TAC[CHART_TRANS_AT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[metric_local; mpullback] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[SND] (ISPECL
    [`(U:B->bool,phi:B->real^3)`; `(V:B->bool,psi:B->real^3)`; `p:B`] chart_jac))] THEN
  SUBGOAL_THEN
   `chart_jac (U,phi:B->real^3) (UX,phiX:B->real^3) (p:B) =
    chart_jac (V,psi:B->real^3) (UX,phiX) p o chart_jac (U,phi) (V,psi) p`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`TY:B topology`; `AY:((B->bool)#(B->real^3))->bool`;
                   `U:B->bool`; `phi:B->real^3`; `V INTER S:B->bool`; `psi:B->real^3`;
                   `UX INTER S:B->bool`; `phiX:B->real^3`; `p:B`] CHART_JAC_CHAIN) THEN
    ASM_REWRITE_TAC[IN_INTER; MFDR_CHART_JAC_RESTRICT_R] THEN
    MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                   `V:B->bool`; `psi:B->real^3`; `S:B->bool`; `(UX:B->bool,phiX:B->real^3)`;
                   `p:B`] MFDR_CHART_JAC_RESTRICT_L) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(chart_jac (V,psi:B->real^3) (UX,phiX:B->real^3) (p:B)) /\
    linear(chart_jac (U,phi:B->real^3) (V,psi) (p:B))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                     `V:B->bool`; `psi:B->real^3`;
                     `UX:B->bool`; `phiX:B->real^3`; `p:B`] CHART_JAC_LINEAR);
      MP_TAC(ISPECL [`TY:B topology`; `AY:((B->bool)#(B->real^3))->bool`;
                     `U:B->bool`; `phi:B->real^3`;
                     `V INTER S:B->bool`; `psi:B->real^3`; `p:B`] CHART_JAC_LINEAR)] THEN
    ASM_REWRITE_TAC[IN_INTER; MFDR_CHART_JAC_RESTRICT_R];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

let P3E_FORMAL_SAME_AUX = prove
 (`!(TY:B topology) (AY:((B->bool)#(B->real^3))->bool) topX atlasX S
    (gl:B->real^3^3) U phi V psi UX phiX q.
     smooth_manifold_atlas TY AY /\ smooth_manifold_atlas topX atlasX /\
     open_in topX S /\
     (U,phi) IN atlasX /\ (U INTER S,phi) IN AY /\ (V,psi) IN AY /\
     (UX,phiX) IN atlasX /\ (UX INTER S,phiX) IN AY /\
     q IN U /\ q IN V /\ q IN UX /\ q IN S /\
     chart_at atlasX q = (UX,phiX)
     ==> metric_local atlasX (U,phi) gl (phi q) =
         mpullback (chart_trans (U,phi) (V,psi)) (metric_local atlasX (V,psi) gl)
                   (phi q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (U:B->bool,phi) ((phi:B->real^3) q) = q /\
                chart_inv (V:B->bool,psi) ((psi:B->real^3) q) = q`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[CHART_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_trans (U:B->bool,phi:B->real^3) (V,psi) (phi q) = psi q`
  ASSUME_TAC THENL [ASM_MESON_TAC[CHART_TRANS_AT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[metric_local; mpullback] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[SND] (ISPECL
    [`(U:B->bool,phi:B->real^3)`; `(V:B->bool,psi:B->real^3)`; `q:B`] chart_jac))] THEN
  SUBGOAL_THEN
   `chart_jac (U,phi:B->real^3) (UX,phiX:B->real^3) (q:B) =
    chart_jac (V,psi:B->real^3) (UX,phiX) q o chart_jac (U,phi) (V,psi) q`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`TY:B topology`; `AY:((B->bool)#(B->real^3))->bool`;
                   `U INTER S:B->bool`; `phi:B->real^3`; `V:B->bool`; `psi:B->real^3`;
                   `UX INTER S:B->bool`; `phiX:B->real^3`; `q:B`] CHART_JAC_CHAIN) THEN
    ASM_REWRITE_TAC[IN_INTER; MFDR_CHART_JAC_RESTRICT_R] THEN
    MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                   `U:B->bool`; `phi:B->real^3`; `S:B->bool`; `(V:B->bool,psi:B->real^3)`;
                   `q:B`] MFDR_CHART_JAC_RESTRICT_L) THEN
    MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                   `U:B->bool`; `phi:B->real^3`; `S:B->bool`; `(UX:B->bool,phiX:B->real^3)`;
                   `q:B`] MFDR_CHART_JAC_RESTRICT_L) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(chart_jac (V,psi:B->real^3) (UX,phiX:B->real^3) (q:B)) /\
    linear(chart_jac (U,phi:B->real^3) (V,psi) (q:B))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`TY:B topology`; `AY:((B->bool)#(B->real^3))->bool`;
                     `V:B->bool`; `psi:B->real^3`;
                     `UX INTER S:B->bool`; `phiX:B->real^3`; `q:B`] CHART_JAC_LINEAR) THEN
      ASM_REWRITE_TAC[IN_INTER; MFDR_CHART_JAC_RESTRICT_R];
      MP_TAC(ISPECL [`TY:B topology`; `AY:((B->bool)#(B->real^3))->bool`;
                     `U INTER S:B->bool`; `phi:B->real^3`;
                     `V:B->bool`; `psi:B->real^3`; `q:B`] CHART_JAC_LINEAR) THEN
      MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                     `U:B->bool`; `phi:B->real^3`; `S:B->bool`;
                     `(V:B->bool,psi:B->real^3)`; `q:B`] MFDR_CHART_JAC_RESTRICT_L) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

let P3E_MG_XFACTS = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc p.
     p3e_mgdata topX atlasX J e nw D Om gl Gc /\ p IN topspace topX
     ==> smooth_manifold_atlas topX atlasX /\
         chart_at atlasX p IN atlasX /\ p IN FST(chart_at atlasX p) /\
         (FST(chart_at atlasX p) INTER (p3e_ysp topX J e nw D INTER topspace topX),
          SND(chart_at atlasX p)) IN p3e_yatlas topX atlasX J e nw D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_mgdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_cutdata]) THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `p:B`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3E_MG_XCHART_S THEN
  MAP_EVERY EXISTS_TAC [`Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`] THEN
  ASM_REWRITE_TAC[PAIR]);;

let P3E_GMET_OLD_REP = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc c V psi p.
     p3e_mgdata topX atlasX J e nw D Om gl Gc /\
     c IN p3e_yatlas topX atlasX J e nw D /\ (V,psi) IN atlasX /\
     p IN FST c /\ p IN V /\ p IN topspace topX
     ==> metric_local (p3e_yatlas topX atlasX J e nw D) c
                      (p3e_gmet topX atlasX J e nw D gl Gc) (SND c p) =
         mpullback (chart_trans c (V,psi)) (metric_local atlasX (V,psi) gl) (SND c p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                `c:(B->bool)#(B->real^3)`; `p:B`] P3E_GMET_FORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                `p:B`] P3E_MG_XFACTS) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlasX:((B->bool)#(B->real^3))->bool) p` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `UX:B->bool` (X_CHOOSE_THEN `phiX:B->real^3` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_OLD) THEN
  MP_TAC(ISPEC `c:(B->bool)#(B->real^3)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `U:B->bool` (X_CHOOSE_THEN `phi:B->real^3` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[SND] THEN
  SUBGOAL_THEN `(p:B) IN p3e_ysp topX J e nw D INTER topspace topX` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                   `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                   `U:B->bool`; `phi:B->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    UNDISCH_TAC `(p:B) IN U` THEN UNDISCH_TAC `(p:B) IN topspace topX` THEN
    UNDISCH_TAC `topspace (p3e_ytop topX J e nw D) = p3e_ysp (topX:B topology) J e nw D` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P3E_FORMAL_TRANS_AUX THEN
  MAP_EVERY EXISTS_TAC
   [`p3e_ytop (topX:B topology) J e nw D`;
    `p3e_yatlas (topX:B topology) atlasX J e nw D`; `topX:B topology`;
    `p3e_ysp (topX:B topology) J e nw D INTER topspace topX`;
    `UX:B->bool`; `phiX:B->real^3`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_MESON_TAC[P3E_MG_XCHART_S]);;

let P3E_GMET_SAME = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc.
     p3e_mgdata topX atlasX J e nw D Om gl Gc
     ==> rfs_same_metric_on atlasX gl (p3e_yatlas topX atlasX J e nw D)
                            (p3e_gmet topX atlasX J e nw D gl Gc)
                            (topspace (p3e_ytop topX J e nw D) INTER topspace topX)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_OLD) THEN
  REWRITE_TAC[rfs_same_metric_on; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:B->bool`; `phi:B->real^3`; `V:B->bool`; `psi:B->real^3`;
                       `y:real^3`] THEN
  REWRITE_TAC[FST; SND; IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `q:B` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SUBGOAL_THEN `(q:B) IN p3e_ysp topX J e nw D INTER topspace topX` ASSUME_TAC THENL
   [UNDISCH_TAC `(q:B) IN topspace (p3e_ytop topX J e nw D)` THEN
    UNDISCH_TAC `(q:B) IN topspace topX` THEN
    UNDISCH_TAC `topspace (p3e_ytop topX J e nw D) = p3e_ysp (topX:B topology) J e nw D` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                `q:B`] P3E_MG_XFACTS) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlasX:((B->bool)#(B->real^3))->bool) q` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `UX:B->bool` (X_CHOOSE_THEN `phiX:B->real^3` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(psi:B->real^3) o chart_inv (U,phi:B->real^3) = chart_trans (U,phi) (V,psi)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; chart_trans; SND]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mpullback (chart_trans (U,phi) (V,psi))
              (metric_local (p3e_yatlas topX atlasX J e nw D) (V,psi)
                            (p3e_gmet topX atlasX J e nw D gl Gc)) ((phi:B->real^3) q) =
    mpullback (chart_trans (U,phi) (V,psi:B->real^3))
              (metric_local atlasX (V,psi) gl) (phi q)`
  SUBST1_TAC THENL
   [REWRITE_TAC[mpullback] THEN
    SUBGOAL_THEN `chart_trans (U,phi) (V,psi) ((phi:B->real^3) q) = (psi:B->real^3) q`
    SUBST1_TAC THENL [ASM_MESON_TAC[CHART_TRANS_AT]; ALL_TAC] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                  `(V:B->bool,psi:B->real^3)`; `q:B`] P3E_GMET_FORMAL) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  MATCH_MP_TAC P3E_FORMAL_SAME_AUX THEN
  MAP_EVERY EXISTS_TAC
   [`p3e_ytop (topX:B topology) J e nw D`;
    `p3e_yatlas (topX:B topology) atlasX J e nw D`; `topX:B topology`;
    `p3e_ysp (topX:B topology) J e nw D INTER topspace topX`;
    `UX:B->bool`; `phiX:B->real^3`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_MESON_TAC[P3E_MG_XCHART_S]);;

(* ------------------------------------------------------------------------- *)
(* The cm i chart: its inverse is cm i on ball(0,2); the                     *)
(* representative of the glued metric in it is Gc i (P3E_GMET_CAP_REP);    *)
(* the glued metric is a Riemannian metric of Y (P3E_GMET_RIEMANNIAN).     *)
(* ------------------------------------------------------------------------- *)

let P3E_MG_CM_CHART = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc i w.
     p3e_mgdata topX atlasX J e nw D Om gl Gc /\ i IN J /\ w IN ball(vec 0,&2)
     ==> p3e_cinv (p3e_ccm e nw i) (p3e_ccm e nw i w) = w /\
         chart_inv (IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)),p3e_cinv (p3e_ccm e nw i)) w =
         p3e_ccm e nw i w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_mgdata]) THEN
  SUBGOAL_THEN `p3e_cinv (p3e_ccm e nw i) (p3e_ccm (e:num->real^3->B) nw i w) = w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_CINV THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                   `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                   `i:num`; `i:num`; `x:real^3`; `y:real^3`] P3E_CCM_EQ) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                 `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                 `IMAGE (p3e_ccm (e:num->real^3->B) nw i) (ball(vec 0,&2))`;
                 `p3e_cinv (p3e_ccm (e:num->real^3->B) nw i)`] CHART_INV) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_MG_Y th]);
      MATCH_MP_TAC P3E_MG_CMCHART THEN
      MAP_EVERY EXISTS_TAC [`Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM SET_TAC[]]);;

let P3E_MG_NEWPT_CM = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc i z.
     p3e_mgdata topX atlasX J e nw D Om gl Gc /\ i IN J /\ norm z <= &1
     ==> ~(p3e_ccm e nw i z IN topspace topX) /\
         p3e_ccm e nw i z IN p3e_ysp topX J e nw D /\
         chart_at (p3e_yatlas topX atlasX J e nw D) (p3e_ccm e nw i z) =
         (IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)),p3e_cinv (p3e_ccm e nw i)) /\
         (@i'. i' IN J /\
               p3e_ccm e nw i z IN IMAGE (p3e_ccm e nw i') (cball(vec 0,&1))) = i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_mgdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_cutdata]) THEN
  SUBGOAL_THEN
   `~(p3e_ccm e nw i z IN topspace (topX:B topology)) /\
    p3e_ccm e nw i z IN p3e_ysp topX J e nw D`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[p3e_ccm];
      MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                    `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                    `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`;
                    `Gc:num->real^3->real^3^3`; `i:num`] P3E_MG_CAPS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                `p3e_ccm (e:num->real^3->B) nw i z`] P3E_MG_NEWPT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i':num` (X_CHOOSE_THEN `z':real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "UNQ") (LABEL_TAC "IDX"))))))) THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                 `i':num`; `i:num`; `z:real^3`; `z':real^3`] P3E_CCM_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  CONJ_TAC THENL
   [USE_THEN "UNQ" MATCH_MP_TAC THEN MATCH_MP_TAC CHART_AT THEN
    EXISTS_TAC `p3e_ytop (topX:B topology) J e nw D` THEN ASM_REWRITE_TAC[];
    USE_THEN "IDX" ACCEPT_TAC]);;

let P3E_GMET_CAP_REP = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc i z.
     p3e_mgdata topX atlasX J e nw D Om gl Gc /\ i IN J /\ z IN ball(vec 0,&2)
     ==> metric_local (p3e_yatlas topX atlasX J e nw D)
                      (IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)),p3e_cinv (p3e_ccm e nw i))
                      (p3e_gmet topX atlasX J e nw D gl Gc) z = Gc i z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_mgdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_cutdata]) THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                `i:num`; `z:real^3`] P3E_MG_CM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `norm(z:real^3) <= &1` THENL
   [MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                  `i:num`; `z:real^3`] P3E_MG_NEWPT_CM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                   `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                   `p3e_gmet (topX:B topology) atlasX J e nw D gl Gc`;
                   `p3e_ccm (e:num->real^3->B) nw i z`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[SND] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[p3e_gmet; SND];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`; `z:real^3`]
    P3E_CAP_VALUES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN annulus (&1) (&2) /\ ~(z = vec 0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN UNDISCH_TAC `&1 < norm(z:real^3)` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `y = inv(norm(z:real^3) pow 2) % z` THEN
  SUBGOAL_THEN `(e:num->real^3->B) i y IN topspace topX DIFF mfd_cut_spheres J e`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_NECK_OFF_SPHERES THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`;
                          `nw:num->bool->real^3->B`] THEN
    ASM_REWRITE_TAC[P3E_ANNULUS_HALF_TWO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                 `(e:num->real^3->B) i y`] CHART_AT) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]]; ALL_TAC] THEN
  MP_TAC(ISPEC `chart_at (atlasX:((B->bool)#(B->real^3))->bool) ((e:num->real^3->B) i y)`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:B->bool` (X_CHOOSE_THEN `psi:B->real^3` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                `(IMAGE (p3e_ccm (e:num->real^3->B) nw i) (ball(vec 0,&2)),
                  p3e_cinv (p3e_ccm e nw i))`;
                `V:B->bool`; `psi:B->real^3`; `(e:num->real^3->B) i y`]
    P3E_GMET_OLD_REP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FST] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3E_MG_CMCHART THEN
      MAP_EVERY EXISTS_TAC [`Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (IMAGE (p3e_ccm (e:num->real^3->B) nw i) (ball(vec 0,&2)),
                     p3e_cinv (p3e_ccm e nw i)) (e i y) = z`
  SUBST1_TAC THENL
   [REWRITE_TAC[SND] THEN
    UNDISCH_TAC `p3e_cinv (p3e_ccm e nw i) (p3e_ccm (e:num->real^3->B) nw i z) = z` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `Gc i z = mpullback (\w:real^3. inv(norm w pow 2) % w)
                       (rfs_pullback atlasX ((e:num->real^3->B) i) gl) z`
  SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^3. w IN annulus (&1) (&2)
               ==> chart_trans (IMAGE (p3e_ccm (e:num->real^3->B) nw i) (ball(vec 0,&2)),
                                p3e_cinv (p3e_ccm e nw i)) (V,psi) w =
                   ((psi o e i) o (\w:real^3. inv(norm w pow 2) % w)) w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[chart_trans; o_THM; SND] THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                  `i:num`; `w:real^3`] P3E_MG_CM_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`; `w:real^3`]
      P3E_CAP_VALUES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
    STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback ((psi o (e:num->real^3->B) i) o (\w:real^3. inv(norm w pow 2) % w))
                        (metric_local atlasX (V,psi) gl) z` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mpullback] THEN
    SUBGOAL_THEN
     `frechet_derivative
        (chart_trans (IMAGE (p3e_ccm (e:num->real^3->B) nw i) (ball(vec 0,&2)),
                      p3e_cinv (p3e_ccm e nw i)) (V,psi)) (at z) =
      frechet_derivative ((psi o e i) o (\w:real^3. inv(norm w pow 2) % w)) (at z)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `annulus (&1) (&2):real^3->bool` THEN
      ASM_SIMP_TAC[OPEN_ANNULUS];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mpullback (\w:real^3. inv(norm w pow 2) % w)
              (rfs_pullback atlasX ((e:num->real^3->B) i) gl) z =
    mpullback (\w:real^3. inv(norm w pow 2) % w)
              (mpullback (psi o e i) (metric_local atlasX (V,psi) gl)) z`
  SUBST1_TAC THENL
   [REWRITE_TAC[mpullback] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[rfs_pullback; SND] THEN REWRITE_TAC[mpullback];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BX_MPULLBACK_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_INVERSION; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_param topX atlasX (annulus (&1 / &2) (&2)) ((e:num->real^3->B) i)`
  ASSUME_TAC THENL [ASM_MESON_TAC[mfd_neck_chart]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                 `annulus (&1 / &2) (&2):real^3->bool`; `(e:num->real^3->B) i`;
                 `V:B->bool`; `psi:B->real^3`] APX_PARAM_CHART_REP) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `{w:real^3 | w IN annulus (&1 / &2) (&2) /\ (e:num->real^3->B) i w IN V}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; P3E_ANNULUS_HALF_TWO] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The glued metric is a Riemannian metric of Y                              *)
(* (P3E_GMET_RIEMANNIAN: near an old point it is the pullback of gl's       *)
(* representative by a chart transition, near a core point it is Gc i in    *)
(* the cm i chart); its pullbacks by the cap maps cm i are the cap fields   *)
(* (P3E_GMET_PULLBACK_CM) and by parametrizations of X into the old points *)
(* those of gl (P3E_GMET_PULLBACK_OLD).                                     *)
(* ------------------------------------------------------------------------- *)

let P3E_GMET_RIEMANNIAN = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc.
     p3e_mgdata topX atlasX J e nw D Om gl Gc
     ==> riemannian_metric (p3e_yatlas topX atlasX J e nw D)
                           (p3e_gmet topX atlasX J e nw D gl Gc)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_mgdata]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3e_cutdata]) THEN
  REWRITE_TAC[riemannian_metric; FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`U:B->bool`; `phi:B->real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                 `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                 `U:B->bool`; `phi:B->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_LOCAL THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `p:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(p:B) IN p3e_ysp topX J e nw D` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
      check (fun th -> rand(concl th) = `U:B->bool`)) THEN
    UNDISCH_TAC `(p:B) IN U` THEN
    UNDISCH_TAC `topspace (p3e_ytop topX J e nw D) = p3e_ysp (topX:B topology) J e nw D` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(p:B) IN topspace topX` THENL
   [MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                  `p:B`] P3E_MG_XFACTS) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `chart_at (atlasX:((B->bool)#(B->real^3))->bool) p` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `V:B->bool` (X_CHOOSE_THEN `psi:B->real^3` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                   `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                   `U:B->bool`; `phi:B->real^3`;
                   `V INTER (p3e_ysp (topX:B topology) J e nw D INTER topspace topX)`;
                   `psi:B->real^3`] CHART_TRANS_DIFFEO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    EXISTS_TAC `IMAGE (phi:B->real^3)
                  (U INTER V INTER (p3e_ysp topX J e nw D INTER topspace topX))` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
      REWRITE_TAC[INTER_ASSOC];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `p:B` THEN ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
    EXISTS_TAC `mpullback (chart_trans (U,phi) (V,psi:B->real^3))
                          (metric_local atlasX (V,psi) gl)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      EXISTS_TAC `IMAGE (psi:B->real^3)
                    (U INTER V INTER (p3e_ysp topX J e nw D INTER topspace topX))` THEN
      EXISTS_TAC `chart_trans (V INTER (p3e_ysp topX J e nw D INTER topspace topX),psi)
                              (U:B->bool,phi:B->real^3)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
        EXISTS_TAC `IMAGE (psi:B->real^3) (V INTER Om)` THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `(V:B->bool,psi:B->real^3)` o
            check (fun th -> can (find_term ((=) `Om:B->bool`)) (concl th) &&
                             is_forall(concl th))) THEN
          ASM_REWRITE_TAC[FST; SND];
          CONJ_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
              GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
            REWRITE_TAC[INTER_ASSOC];
            MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]]];
        FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `diffeomorphism_on:(real^3->bool)->(real^3->bool)->(real^3->real^3)->(real^3->real^3)->bool`)) (concl th))) THEN
        REWRITE_TAC[INTER_ASSOC; chart_trans; SND]];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `q:B` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                    `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                    `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`;
                    `Gc:num->real^3->real^3^3`; `(U:B->bool,phi:B->real^3)`;
                    `V:B->bool`; `psi:B->real^3`; `q:B`] P3E_GMET_OLD_REP) THEN
      ASM_REWRITE_TAC[FST; SND]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                `p:B`] P3E_MG_NEWPT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `z:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o
    check (fun th -> is_eq(concl th) && lhs(concl th) = `p:B`)) THEN
  DISCH_THEN(MP_TAC o SPEC `(U:B->bool,phi:B->real^3)`) THEN
  ASM_REWRITE_TAC[FST; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
  SUBGOAL_THEN `(z:real^3) IN ball(vec 0,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                `i:num`; `z:real^3`] P3E_MG_CM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN EXISTS_TAC `(Gc:num->real^3->real^3^3) i` THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P3E_GMET_CAP_REP THEN EXISTS_TAC `Om:B->bool` THEN ASM_REWRITE_TAC[]);;

let P3E_MPULLBACK_ID_OPEN = prove
 (`!(h:real^3->real^3) G s z.
     open s /\ z IN s /\ (!w. w IN s ==> h w = w) ==> mpullback h G z = G z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (h:real^3->real^3) (at z) = frechet_derivative (\w. w) (at z)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (\w:real^3. w) (at z) = (\h. h)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let P3E_MG_CM_PARAM = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc i.
     p3e_mgdata topX atlasX J e nw D Om gl Gc /\ i IN J
     ==> mfd_param (p3e_ytop topX J e nw D) (p3e_yatlas topX atlasX J e nw D)
                   (ball(vec 0,&2)) (p3e_ccm e nw i)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_CUTCAP_FACTS o CONJUNCT1 o
    GEN_REWRITE_RULE I [p3e_mgdata]) THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                `i:num`] P3E_MG_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p3e_ytop; p3e_yatlas] THEN
  MP_TAC(ISPECL [`p3e_ctop (topX:B topology) J e nw`; `p3e_catlas (topX:B topology) atlasX J e nw`;
                 `p3e_ysp (topX:B topology) J e nw D`; `ball(vec 0:real^3,&2)`;
                 `p3e_ccm (e:num->real^3->B) nw i`] APX_PARAM_RESTRICT_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                 `i:num`] P3E_CAP_BALL_CHART) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[p3e_mgdata]; SIMP_TAC[mfd_ball_chart]]);;

let P3E_GMET_PULLBACK_CM = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc i z.
     p3e_mgdata topX atlasX J e nw D Om gl Gc /\ i IN J /\ z IN ball(vec 0,&2)
     ==> rfs_pullback (p3e_yatlas topX atlasX J e nw D) (p3e_ccm e nw i)
                      (p3e_gmet topX atlasX J e nw D gl Gc) z = Gc i z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                `p3e_gmet (topX:B topology) atlasX J e nw D gl Gc`;
                `ball(vec 0:real^3,&2)`; `p3e_ccm (e:num->real^3->B) nw i`;
                `IMAGE (p3e_ccm (e:num->real^3->B) nw i) (ball(vec 0,&2))`;
                `p3e_cinv (p3e_ccm (e:num->real^3->B) nw i)`; `z:real^3`]
    APX_RFS_PULLBACK_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3E_MG_CM_PARAM THEN
      MAP_EVERY EXISTS_TAC [`Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3E_MG_CMCHART THEN
      MAP_EVERY EXISTS_TAC [`Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`] THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                `i:num`; `z:real^3`] P3E_GMET_CAP_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC P3E_MPULLBACK_ID_OPEN THEN EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
  ASM_REWRITE_TAC[OPEN_BALL; o_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                `i:num`; `w:real^3`] P3E_MG_CM_CHART) THEN
  ASM_SIMP_TAC[]);;

let P3E_GMET_PULLBACK_OLD = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc s (f:real^3->B) x.
     p3e_mgdata topX atlasX J e nw D Om gl Gc /\
     mfd_param (p3e_ytop topX J e nw D) (p3e_yatlas topX atlasX J e nw D) s f /\
     mfd_param topX atlasX s f /\ x IN s /\ f x IN topspace topX
     ==> rfs_pullback (p3e_yatlas topX atlasX J e nw D) f
                      (p3e_gmet topX atlasX J e nw D gl Gc) x =
         rfs_pullback atlasX f gl x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(CONJUNCT1(CONJUNCT2(MATCH_MP P3E_MG_OLD th)))) THEN
  SUBGOAL_THEN `(f:real^3->B) x IN p3e_ysp topX J e nw D` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS o
      check (fun th -> can (find_term ((=) `p3e_ytop (topX:B topology) J e nw D`)) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `f':B->real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
      check (fun th -> can (find_term ((=) `IMAGE (f:real^3->B) s`)) (concl th) &&
                       can (find_term ((=) `open_in:(B)topology->(B->bool)->bool`)) (concl th))) THEN
    UNDISCH_TAC `(x:real^3) IN s` THEN
    UNDISCH_TAC `topspace (p3e_ytop topX J e nw D) = p3e_ysp (topX:B topology) J e nw D` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                `(f:real^3->B) x`] P3E_MG_XFACTS) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlasX:((B->bool)#(B->real^3))->bool) ((f:real^3->B) x)`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:B->bool` (X_CHOOSE_THEN `psi:B->real^3` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p3e_ytop (topX:B topology) J e nw D`;
                `p3e_yatlas (topX:B topology) atlasX J e nw D`;
                `p3e_gmet (topX:B topology) atlasX J e nw D gl Gc`;
                `s:real^3->bool`; `f:real^3->B`;
                `V INTER (p3e_ysp (topX:B topology) J e nw D INTER topspace topX)`;
                `psi:B->real^3`; `x:real^3`] APX_RFS_PULLBACK_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `gl:B->real^3^3`; `s:real^3->bool`; `f:real^3->B`;
                `V:B->bool`; `psi:B->real^3`; `x:real^3`] APX_RFS_PULLBACK_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[mpullback; o_THM] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`;
                `(V INTER (p3e_ysp (topX:B topology) J e nw D INTER topspace topX),
                  psi:B->real^3)`;
                `(f:real^3->B) x`] P3E_GMET_FORMAL) THEN
  ASM_REWRITE_TAC[FST; SND; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC MFDR_METRIC_LOCAL_RESTRICT_CHART THEN
  EXISTS_TAC `topX:B topology` THEN ASM_REWRITE_TAC[IN_INTER]);;

(* ------------------------------------------------------------------------- *)
(* The main results together (P3E_MGLUE_FACTS).                              *)
(* ------------------------------------------------------------------------- *)

let P3E_MGLUE_FACTS = prove
 (`!(topX:B topology) atlasX J e nw D Om gl Gc.
     p3e_mgdata topX atlasX J e nw D Om gl Gc
     ==> hausdorff_space (p3e_ytop topX J e nw D) /\
         compact_space (p3e_ytop topX J e nw D) /\
         smooth_manifold_atlas (p3e_ytop topX J e nw D)
                               (p3e_yatlas topX atlasX J e nw D) /\
         topspace (p3e_ytop topX J e nw D) = p3e_ysp topX J e nw D /\
         riemannian_metric (p3e_yatlas topX atlasX J e nw D)
                           (p3e_gmet topX atlasX J e nw D gl Gc) /\
         rfs_same_metric_on atlasX gl (p3e_yatlas topX atlasX J e nw D)
                            (p3e_gmet topX atlasX J e nw D gl Gc)
                            (topspace (p3e_ytop topX J e nw D) INTER topspace topX) /\
         (!i. i IN J
              ==> mfd_param (p3e_ytop topX J e nw D) (p3e_yatlas topX atlasX J e nw D)
                            (ball(vec 0,&2)) (p3e_ccm e nw i) /\
                  !z. z IN ball(vec 0,&2)
                      ==> rfs_pullback (p3e_yatlas topX atlasX J e nw D) (p3e_ccm e nw i)
                                       (p3e_gmet topX atlasX J e nw D gl Gc) z = Gc i z) /\
         (!s (f:real^3->B) x.
              mfd_param (p3e_ytop topX J e nw D) (p3e_yatlas topX atlasX J e nw D) s f /\
              mfd_param topX atlasX s f /\ x IN s /\ f x IN topspace topX
              ==> rfs_pullback (p3e_yatlas topX atlasX J e nw D) f
                               (p3e_gmet topX atlasX J e nw D gl Gc) x =
                  rfs_pullback atlasX f gl x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_MG_Y) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3E_GMET_RIEMANNIAN THEN EXISTS_TAC `Om:B->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `D:B->bool`; `Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`]
      P3E_GMET_SAME) THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3E_MG_CM_PARAM THEN
      MAP_EVERY EXISTS_TAC [`Om:B->bool`; `gl:B->real^3^3`; `Gc:num->real^3->real^3^3`] THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P3E_GMET_PULLBACK_CM THEN
      EXISTS_TAC `Om:B->bool` THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P3E_GMET_PULLBACK_OLD THEN
    MAP_EVERY EXISTS_TAC [`Om:B->bool`; `s:real^3->bool`] THEN ASM_REWRITE_TAC[]]);;

