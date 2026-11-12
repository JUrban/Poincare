(* ========================================================================= *)
(* Unit pc_p3e_retain: step S3 of MT Lemma 15.11 (Sec 15.4, p. 361), the     *)
(* retained part of the cut-and-capped manifold Z of unit pc_p3e_cutcap.     *)
(* For an open set Om of X (Omega) and P inside Om (Omega_rho), W is the     *)
(* union of the components of Om minus the cut spheres that meet P or        *)
(* contain a minus point e i (3/4 basis 1); R = W plus the minus cores is    *)
(* clopen in Z, so D = Z minus R is a discarded part as rfs_event_ok needs.  *)
(* The hypotheses of the generic theorem are derived from the outputs of MT  *)
(* Lemma 11.30 and Thm 11.31, with the separation clause of Thm 11.31 (the   *)
(* component of Om minus the central sphere at the plus side lies in the     *)
(* open horn), and apx_sphere_sep.                                           *)
(* ========================================================================= *)

needs "src/pc_p3e_cutcap.ml";;
needs "src/pc_apx_sep.ml";;
needs "src/pc_mfd_diff.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The generic theorem.  W = p3e_wret (union of the components               *)
(* of Om DIFF S, S the cut spheres, meeting P or containing a minus point), *)
(* the minus cores p3e_mcores, D = p3e_rdisc = Zs DIFF (W UNION minus      *)
(* cores).  P3E_RETAIN_GENERIC: D is clopen in Z, contains the plus cores,  *)
(* misses the minus cores, P and every connected subset of Om DIFF S       *)
(* through a minus point, and the old points off D are exactly W.           *)
(* ------------------------------------------------------------------------- *)

let p3e_wret = new_definition
 `p3e_wret (topX:B topology) (J:num->bool) (e:num->real^3->B) (Om:B->bool) (P:B->bool) =
    UNIONS {Q | Q IN connected_components_of
                       (subtopology topX (Om DIFF mfd_cut_spheres J e)) /\
                (~(Q INTER P = {}) \/ ?i. i IN J /\ e i (&3 / &4 % basis 1) IN Q)}`;;

let p3e_mcores = new_definition
 `p3e_mcores (J:num->bool) (e:num->real^3->B) (nw:num->bool->real^3->B) =
    UNIONS {IMAGE (p3e_ccm e nw i) (cball(vec 0,&1)) | i IN J}`;;

let p3e_rdisc = new_definition
 `p3e_rdisc (topX:B topology) (J:num->bool) (e:num->real^3->B)
            (nw:num->bool->real^3->B) (Om:B->bool) (P:B->bool) =
    p3e_czs topX J e nw DIFF (p3e_wret topX J e Om P UNION p3e_mcores J e nw)`;;

let P3E_NORM_BASIS1_MUL = prove
 (`!c. norm(c % basis 1:real^3) = abs c`,
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID]);;

let P3E_COMPONENT_OF_SELF = prove
 (`!top x:B. x IN topspace top ==> x IN connected_component_of top x`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [IN] THEN
  REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL]);;

let P3E_COMPONENT_OF_IN = prove
 (`!top x y:B. y IN connected_component_of top x
               ==> connected_component_of top y = connected_component_of top x`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
  MESON_TAC[CONNECTED_COMPONENT_OF_EQUIV]);;

let P3E_COMPONENT_OPEN_SUB = prove
 (`!(top:B topology) (atlas:((B->bool)#(B->real^3))->bool) W x.
     smooth_manifold_atlas top atlas /\ open_in top W
     ==> open_in top (connected_component_of (subtopology top W) x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
  EXISTS_TAC `W:B->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENT_OF_LOCALLY_CONNECTED_SPACE THEN
  MATCH_MP_TAC LOCALLY_CONNECTED_SPACE_OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE THEN
  MATCH_MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`]
                      GEO_MANIFOLD_LOCALLY_PATH_CONNECTED) THEN
  ASM_REWRITE_TAC[]);;

let IN_P3E_WRET = prove
 (`!(topX:B topology) J e Om P p.
     p IN p3e_wret topX J e Om P <=>
     p IN topspace topX /\ p IN Om /\ ~(p IN mfd_cut_spheres J e) /\
     (~(connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) p INTER P =
        {}) \/
      ?i. i IN J /\
          e i (&3 / &4 % basis 1) IN
          connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) p)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p3e_wret; IN_UNIONS; IN_ELIM_THM; connected_components_of] THEN
  ABBREV_TAC `top = subtopology (topX:B topology) (Om DIFF mfd_cut_spheres J e)` THEN
  SUBGOAL_THEN
   `!x:B. x IN topspace top <=>
          x IN topspace topX /\ x IN Om /\ ~(x IN mfd_cut_spheres J e)`
  ASSUME_TAC THENL
   [EXPAND_TAC "top" THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_DIFF];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `Q:B->bool` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) MP_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `connected_component_of top (p:B) = connected_component_of top x`
    SUBST1_TAC THENL [MATCH_MP_TAC P3E_COMPONENT_OF_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(p:B) IN topspace top` MP_TAC THENL
     [ASM_MESON_TAC[CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN EXISTS_TAC `connected_component_of top (p:B)` THEN
    (CONJ_TAC THENL
      [CONJ_TAC THENL [EXISTS_TAC `p:B` THEN ASM_REWRITE_TAC[]; ALL_TAC];
       MATCH_MP_TAC P3E_COMPONENT_OF_SELF THEN ASM_REWRITE_TAC[]]) THEN
    ASM_MESON_TAC[]]);;

let P3E_WRET_SUB = prove
 (`!(topX:B topology) J e Om P.
     p3e_wret topX J e Om P SUBSET topspace topX INTER (Om DIFF mfd_cut_spheres J e)`,
  REWRITE_TAC[SUBSET; IN_P3E_WRET; IN_INTER; IN_DIFF] THEN MESON_TAC[]);;

let P3E_OM_DIFF_OPEN = prove
 (`!(topX:B topology) atlasX J e nw Om.
     p3e_cutdata topX atlasX J e nw /\ open_in topX Om
     ==> open_in topX (Om DIFF mfd_cut_spheres J e)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[P3E_CUT_SPHERES_COMPACT]);;

let P3E_WRET_OPEN = prove
 (`!(topX:B topology) atlasX J e nw Om P.
     p3e_cutdata topX atlasX J e nw /\ open_in topX Om
     ==> open_in topX (p3e_wret topX J e Om P)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3e_wret] THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
  REWRITE_TAC[IN_ELIM_THM; connected_components_of] THEN
  X_GEN_TAC `Q:B->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) (K ALL_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3E_COMPONENT_OPEN_SUB THEN
  EXISTS_TAC `atlasX:((B->bool)#(B->real^3))->bool` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[p3e_cutdata]; ALL_TAC] THEN
  MATCH_MP_TAC P3E_OM_DIFF_OPEN THEN
  MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`; `nw:num->bool->real^3->B`] THEN
  ASM_REWRITE_TAC[]);;

(* The whole component of a point of W lies in W; a component through a    *)
(* point outside W misses W.                                                 *)

let P3E_WRET_COMPONENT = prove
 (`!(topX:B topology) J e Om P a.
     a IN p3e_wret topX J e Om P
     ==> connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) a SUBSET
         p3e_wret topX J e Om P`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET] THEN DISCH_TAC THEN
  X_GEN_TAC `p:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) (p:B) =
    connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) a`
  ASSUME_TAC THENL [MATCH_MP_TAC P3E_COMPONENT_OF_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(p:B) IN topspace (subtopology topX (Om DIFF mfd_cut_spheres J e))` MP_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_DIFF] THEN STRIP_TAC THEN
  UNDISCH_TAC `(a:B) IN p3e_wret topX J e Om P` THEN
  ASM_REWRITE_TAC[IN_P3E_WRET] THEN MESON_TAC[]);;

let P3E_WRET_COMPONENT_DISJ = prove
 (`!(topX:B topology) J e Om P x.
     ~(x IN p3e_wret topX J e Om P)
     ==> DISJOINT (connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) x)
                  (p3e_wret topX J e Om P)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `p:B` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) (p:B) =
    connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) x`
  ASSUME_TAC THENL [MATCH_MP_TAC P3E_COMPONENT_OF_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:B) IN topspace (subtopology topX (Om DIFF mfd_cut_spheres J e))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENT_OF_EQ_EMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:B topology`; `J:num->bool`; `e:num->real^3->B`; `Om:B->bool`;
                 `P:B->bool`; `p:B`] P3E_WRET_COMPONENT) THEN
  ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:B`) THEN
  ASM_SIMP_TAC[P3E_COMPONENT_OF_SELF]);;

(* Connected subsets of Om DIFF S through a point of W lie in W.            *)

let P3E_WRET_CONNECTED = prove
 (`!(topX:B topology) J e Om P A a.
     connected_in topX A /\ A SUBSET Om DIFF mfd_cut_spheres J e /\
     a IN A /\ a IN p3e_wret topX J e Om P
     ==> A SUBSET p3e_wret topX J e Om P`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) (a:B)` THEN
  ASM_SIMP_TAC[P3E_WRET_COMPONENT] THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY]);;

(* Seeds of W: points of P and minus points off the spheres.                *)

let P3E_WRET_SEED = prove
 (`!(topX:B topology) J e Om P a.
     a IN topspace topX /\ a IN Om /\ ~(a IN mfd_cut_spheres J e) /\
     (a IN P \/ ?i. i IN J /\ a = e i (&3 / &4 % basis 1))
     ==> a IN p3e_wret topX J e Om P`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c")))) THEN
  REWRITE_TAC[IN_P3E_WRET] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(a:B) IN connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) a`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_COMPONENT_OF_SELF THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_DIFF];
    ALL_TAC] THEN
  REMOVE_THEN "c" STRIP_ASSUME_TAC THENL
   [DISJ1_TAC THEN ASM SET_TAC[];
    DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_MESON_TAC[]]);;

(* The neck pieces: images of connected subsets of the annulus are          *)
(* connected; the minus and plus half annuli contain the minus and plus     *)
(* points.                                                                  *)

let P3E_NECK_PIECE_CONNECTED = prove
 (`!(topX:B topology) atlasX J e nw i s.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ connected s /\
     s SUBSET annulus (&1 / &2) (&2)
     ==> connected_in topX (IMAGE (e i) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
  EXISTS_TAC `subtopology euclidean (annulus (&1 / &2) (&2):real^3->bool)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[P3E_CUTDATA_NECK]; ALL_TAC] THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN]);;

let P3E_HALF_ANNULI = prove
 (`connected {y:real^3 | &1 / &2 < norm y /\ norm y < &1} /\
   connected {y:real^3 | &1 < norm y /\ norm y < &2} /\
   {y:real^3 | &1 / &2 < norm y /\ norm y < &1} SUBSET annulus (&1 / &2) (&2) /\
   {y:real^3 | &1 < norm y /\ norm y < &2} SUBSET annulus (&1 / &2) (&2) /\
   (&3 / &4 % basis 1:real^3) IN {y:real^3 | &1 / &2 < norm y /\ norm y < &1} /\
   (&4 / &3 % basis 1:real^3) IN {y:real^3 | &1 < norm y /\ norm y < &2}`,
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`vec 0:real^3`; `&1 / &2`; `&1`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; DIMINDEX_3; ARITH];
    MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `&2`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; DIMINDEX_3; ARITH];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; P3E_ANNULUS_HALF_TWO] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM; P3E_ANNULUS_HALF_TWO] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM; P3E_NORM_BASIS1_MUL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM; P3E_NORM_BASIS1_MUL] THEN REAL_ARITH_TAC]);;

let P3E_HALF_ANNULUS_OFF = prove
 (`!(topX:B topology) atlasX J e nw Om i.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\
     IMAGE (e i) (annulus (&1 / &2) (&2)) SUBSET Om
     ==> IMAGE (e i) {y:real^3 | &1 / &2 < norm y /\ norm y < &1} SUBSET
         Om DIFF mfd_cut_spheres J e /\
         IMAGE (e i) {y:real^3 | &1 < norm y /\ norm y < &2} SUBSET
         Om DIFF mfd_cut_spheres J e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_DIFF] THEN
  CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  (SUBGOAL_THEN `(y:real^3) IN annulus (&1 / &2) (&2) /\ ~(norm y = &1)` STRIP_ASSUME_TAC
   THENL [REWRITE_TAC[P3E_ANNULUS_HALF_TWO] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`; `y:real^3`] P3E_NECK_OFF_SPHERES) THEN
   ASM_REWRITE_TAC[IN_DIFF] THEN MESON_TAC[]));;

(* The ball images of the cap charts: core plus the half annulus.           *)

let P3E_CAP_BALL2_PARTS = prove
 (`!(e:num->real^3->B) nw i.
     IMAGE (p3e_ccp e nw i) (ball(vec 0,&2)) SUBSET
     IMAGE (p3e_ccp e nw i) (cball(vec 0,&1)) UNION
     IMAGE (e i) {y:real^3 | &1 < norm y /\ norm y < &2} /\
     IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)) SUBSET
     IMAGE (p3e_ccm e nw i) (cball(vec 0,&1)) UNION
     IMAGE (e i) {y:real^3 | &1 / &2 < norm y /\ norm y < &1}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`; `x:real^3`]
    P3E_CAP_VALUES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[IN_UNION; IN_IMAGE] THENL
   [DISJ1_TAC THEN EXISTS_TAC `x:real^3` THEN
    ASM_REWRITE_TAC[IN_CBALL_0];
    DISJ2_TAC THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    DISJ1_TAC THEN EXISTS_TAC `x:real^3` THEN
    ASM_REWRITE_TAC[IN_CBALL_0];
    DISJ2_TAC THEN EXISTS_TAC `inv(norm(x:real^3) pow 2) % x` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM]]);;

(* The minus cores: old-point free, disjoint from the plus cores, in Zs.    *)

let P3E_CBALL1_BALL2 = prove
 (`cball(vec 0:real^3,&1) SUBSET ball(vec 0,&2)`,
  REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC);;

let P3E_MCORES_FACTS = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw
     ==> DISJOINT (p3e_mcores J e nw) (topspace topX) /\
         p3e_mcores J e nw SUBSET p3e_czs topX J e nw /\
         (!i. i IN J ==> IMAGE (p3e_ccm e nw i) (cball(vec 0,&1)) SUBSET p3e_mcores J e nw) /\
         (!i. i IN J
              ==> DISJOINT (IMAGE (p3e_ccp e nw i) (cball(vec 0,&1))) (p3e_mcores J e nw) /\
                  DISJOINT (IMAGE (p3e_ccp e nw i) (cball(vec 0,&1))) (topspace topX) /\
                  IMAGE (p3e_ccp e nw i) (cball(vec 0,&1)) SUBSET p3e_czs topX J e nw)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i b x. ~((nw:num->bool->real^3->B) i b x IN topspace topX)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3e_cutdata]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN cball(vec 0,&1) ==> x IN ball(vec 0,&2)` ASSUME_TAC THENL
   [MP_TAC P3E_CBALL1_BALL2 THEN REWRITE_TAC[SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[p3e_mcores] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `p:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:B->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(p:B) IN topspace topX` THEN ASM_SIMP_TAC[P3E_CCM_CORE];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `p:B` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:B->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    ASM_MESON_TAC[P3E_CCP_IN_CZS];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `p:B` THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `t:B->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) MP_TAC))) THEN
      ASM_REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(p:B) = p3e_ccp e nw i y` THEN ASM_SIMP_TAC[P3E_CCP_CORE; P3E_CCM_CORE] THEN
      ASM_MESON_TAC[P3E_NW_EQ];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_CBALL_0] THEN
      X_GEN_TAC `p:B` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
      ASM_SIMP_TAC[P3E_CCP_CORE];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[P3E_CCP_IN_CZS]]]);;

let P3E_CZS_INTER_X = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw
     ==> p3e_czs topX J e nw INTER topspace topX = topspace topX DIFF mfd_cut_spheres J e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3E_CORES_FRESH) THEN
  REWRITE_TAC[p3e_czs] THEN SET_TAC[]);;

let P3E_CUTDATA_NECK_CHART = prove
 (`!(topX:B topology) atlasX J e nw i.
     p3e_cutdata topX atlasX J e nw /\ i IN J ==> mfd_neck_chart topX atlasX (e i)`,
  SIMP_TAC[p3e_cutdata]);;

(* ------------------------------------------------------------------------- *)
(* The generic theorem.  p3e_rhyp collects its hypotheses:                   *)
(* cut-cap data, Om open, P inside Om and off the cut spheres, the neck    *)
(* annuli inside Om, (h1) the component of Om DIFF S at a plus point misses *)
(* P and all minus points, (h2) W inside a compact subset of Om.  Then      *)
(* R = W UNION minus cores is open in Z (P3E_RETAIN_ROPEN), so is           *)
(* Zs DIFF R (P3E_RETAIN_COPEN), and D = Zs DIFF R has the properties that *)
(* rfs_event_ok and p3_omega_rho_ok need (P3E_RETAIN_GENERIC).              *)
(* ------------------------------------------------------------------------- *)

let p3e_rhyp = new_definition
 `p3e_rhyp (topX:B topology) (atlasX:((B->bool)#(B->real^3))->bool) (J:num->bool)
           (e:num->real^3->B) (nw:num->bool->real^3->B) (Om:B->bool) (P:B->bool) <=>
    p3e_cutdata topX atlasX J e nw /\ open_in topX Om /\ P SUBSET Om /\
    DISJOINT P (mfd_cut_spheres J e) /\
    (!i. i IN J ==> IMAGE (e i) (annulus (&1 / &2) (&2)) SUBSET Om) /\
    (!j. j IN J
         ==> DISJOINT (connected_component_of
                         (subtopology topX (Om DIFF mfd_cut_spheres J e))
                         (e j (&4 / &3 % basis 1))) P /\
             !i. i IN J
                 ==> ~(e i (&3 / &4 % basis 1) IN
                       connected_component_of
                         (subtopology topX (Om DIFF mfd_cut_spheres J e))
                         (e j (&4 / &3 % basis 1)))) /\
    (?K. compact_in topX K /\ K SUBSET Om /\ p3e_wret topX J e Om P SUBSET K)`;;

let P3E_RETAIN_MINUS = prove
 (`!(topX:B topology) atlasX J e nw Om P i.
     p3e_rhyp topX atlasX J e nw Om P /\ i IN J
     ==> IMAGE (e i) {y:real^3 | &1 / &2 < norm y /\ norm y < &1} SUBSET
         p3e_wret topX J e Om P`,
  REWRITE_TAC[p3e_rhyp] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Om SUBSET topspace (topX:B topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P3E_WRET_CONNECTED THEN
  EXISTS_TAC `(e:num->real^3->B) i (&3 / &4 % basis 1)` THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                 `e:num->real^3->B`; `nw:num->bool->real^3->B`; `Om:B->bool`; `i:num`]
                P3E_HALF_ANNULUS_OFF) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(e:num->real^3->B) i (&3 / &4 % basis 1) IN Om DIFF mfd_cut_spheres J e`
  ASSUME_TAC THENL
   [MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 P3E_HALF_ANNULI))))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3E_NECK_PIECE_CONNECTED THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                          `nw:num->bool->real^3->B`] THEN
    ASM_REWRITE_TAC[P3E_HALF_ANNULI];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[P3E_HALF_ANNULI];
    MATCH_MP_TAC P3E_WRET_SEED THEN
    UNDISCH_TAC `(e:num->real^3->B) i (&3 / &4 % basis 1) IN Om DIFF mfd_cut_spheres J e` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]]);;

let P3E_RETAIN_PLUS = prove
 (`!(topX:B topology) atlasX J e nw Om P i.
     p3e_rhyp topX atlasX J e nw Om P /\ i IN J
     ==> DISJOINT (IMAGE (e i) {y:real^3 | &1 < norm y /\ norm y < &2})
                  (p3e_wret topX J e Om P)`,
  REWRITE_TAC[p3e_rhyp] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!c:B->bool. (s:B->bool) SUBSET c /\ DISJOINT c (w:B->bool) ==> DISJOINT s w`) THEN
  EXISTS_TAC `connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e))
                ((e:num->real^3->B) i (&4 / &3 % basis 1))` THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                 `e:num->real^3->B`; `nw:num->bool->real^3->B`; `Om:B->bool`; `i:num`]
                P3E_HALF_ANNULUS_OFF) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3E_NECK_PIECE_CONNECTED THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                            `nw:num->bool->real^3->B`] THEN
      ASM_REWRITE_TAC[P3E_HALF_ANNULI];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[P3E_HALF_ANNULI]];
    MATCH_MP_TAC P3E_WRET_COMPONENT_DISJ THEN
    REWRITE_TAC[IN_P3E_WRET; DE_MORGAN_THM] THEN REPEAT DISJ2_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
    ASM_REWRITE_TAC[DISJOINT; NOT_EXISTS_THM] THEN MESON_TAC[INTER_COMM]]);;

let P3E_RETAIN_ROPEN = prove
 (`!(topX:B topology) atlasX J e nw Om P.
     p3e_rhyp topX atlasX J e nw Om P
     ==> open_in (p3e_ctop topX J e nw) (p3e_wret topX J e Om P UNION p3e_mcores J e nw)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p3e_rhyp]) THEN
  SUBGOAL_THEN
   `p3e_wret topX J e Om P UNION p3e_mcores J e nw =
    p3e_wret topX J e Om P UNION
    UNIONS {IMAGE (p3e_ccm (e:num->real^3->B) nw i) (ball(vec 0,&2)) | i IN J}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[p3e_mcores] THEN MP_TAC P3E_CBALL1_BALL2 THEN SET_TAC[];
      REWRITE_TAC[UNION_SUBSET; SUBSET_UNION; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`]
        P3E_CAP_BALL2_PARTS) THEN
      MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                     `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                     `Om:B->bool`; `P:B->bool`; `i:num`] P3E_RETAIN_MINUS) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `IMAGE (p3e_ccm (e:num->real^3->B) nw i) (cball(vec 0,&1)) SUBSET p3e_mcores J e nw`
      MP_TAC THENL [REWRITE_TAC[p3e_mcores] THEN ASM SET_TAC[]; ALL_TAC] THEN
      SET_TAC[]];
    MATCH_MP_TAC OPEN_IN_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3E_CTOP_OPEN_OLD THEN
      EXISTS_TAC `atlasX:((B->bool)#(B->real^3))->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P3E_WRET_OPEN THEN
        MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`;
                              `nw:num->bool->real^3->B`] THEN
        ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`topX:B topology`; `J:num->bool`; `e:num->real^3->B`; `Om:B->bool`;
                       `P:B->bool`] P3E_WRET_SUB) THEN SET_TAC[]];
      MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                     `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                     `i:num`; `ball(vec 0:real^3,&2)`] P3E_CAP_IMAGE_OPEN) THEN
      ASM_SIMP_TAC[OPEN_BALL; SUBSET_REFL]]]);;

let P3E_COPEN_SETS = prove
 (`!A PC Ep czs W MC X S Om:B->bool.
     A SUBSET PC UNION Ep /\ Ep SUBSET Om DIFF S /\ DISJOINT Ep W /\
     DISJOINT PC MC /\ DISJOINT PC X /\ PC SUBSET czs /\
     W SUBSET X INTER (Om DIFF S) /\ czs INTER X = X DIFF S /\ DISJOINT MC X /\
     Om SUBSET X
     ==> A SUBSET czs DIFF (W UNION MC)`,
  SET_TAC[]);;

let P3E_RETAIN_COPEN = prove
 (`!(topX:B topology) atlasX J e nw Om P.
     p3e_rhyp topX atlasX J e nw Om P
     ==> open_in (p3e_ctop topX J e nw)
                 (p3e_czs topX J e nw DIFF (p3e_wret topX J e Om P UNION p3e_mcores J e nw))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p3e_rhyp]) THEN
  SUBGOAL_THEN `Om SUBSET topspace (topX:B topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                 `e:num->real^3->B`; `nw:num->bool->real^3->B`] P3E_MCORES_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:B topology`; `J:num->bool`; `e:num->real^3->B`; `Om:B->bool`;
                 `P:B->bool`] P3E_WRET_SUB) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                 `e:num->real^3->B`; `nw:num->bool->real^3->B`] P3E_CZS_INTER_X) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open_in topX (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B))`
  ASSUME_TAC THENL [ASM_MESON_TAC[P3E_OLD_OPEN_IN_X]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `p:B` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(p:B) IN topspace topX` THENL
   [SUBGOAL_THEN
     `(p:B) IN topspace topX DIFF mfd_cut_spheres J e /\ ~(p IN p3e_wret topX J e Om P)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(p:B) IN topspace topX` THEN
      UNDISCH_TAC
       `(p:B) IN p3e_czs topX J e nw DIFF (p3e_wret topX J e Om P UNION p3e_mcores J e nw)` THEN
      UNDISCH_TAC `p3e_czs (topX:B topology) J e nw INTER topspace topX =
                   topspace topX DIFF mfd_cut_spheres J e` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(p:B) IN K` THENL
     [EXISTS_TAC
       `connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) (p:B)` THEN
      MP_TAC(ISPECL [`subtopology topX (Om DIFF mfd_cut_spheres J e:B->bool)`; `p:B`]
        CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`topX:B topology`; `J:num->bool`; `e:num->real^3->B`; `Om:B->bool`;
                     `P:B->bool`; `p:B`] P3E_WRET_COMPONENT_DISJ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC P3E_CTOP_OPEN_OLD THEN
        EXISTS_TAC `atlasX:((B->bool)#(B->real^3))->bool` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC P3E_COMPONENT_OPEN_SUB THEN
          EXISTS_TAC `atlasX:((B->bool)#(B->real^3))->bool` THEN
          CONJ_TAC THENL [ASM_MESON_TAC[p3e_cutdata]; ALL_TAC] THEN
          MATCH_MP_TAC P3E_OM_DIFF_OPEN THEN
          MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`;
                                `nw:num->bool->real^3->B`] THEN
          ASM_REWRITE_TAC[];
          UNDISCH_TAC
           `connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) (p:B)
            SUBSET topspace topX INTER (Om DIFF mfd_cut_spheres J e)` THEN
          SET_TAC[]];
        MATCH_MP_TAC P3E_COMPONENT_OF_SELF THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_DIFF] THEN
        UNDISCH_TAC `(p:B) IN K` THEN UNDISCH_TAC `K SUBSET (Om:B->bool)` THEN
        UNDISCH_TAC `(p:B) IN topspace topX DIFF mfd_cut_spheres J e` THEN SET_TAC[];
        UNDISCH_TAC
         `connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) (p:B)
          SUBSET topspace topX INTER (Om DIFF mfd_cut_spheres J e)` THEN
        UNDISCH_TAC
         `DISJOINT (connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e))
                                           (p:B)) (p3e_wret topX J e Om P)` THEN
        UNDISCH_TAC `p3e_czs (topX:B topology) J e nw INTER topspace topX =
                     topspace topX DIFF mfd_cut_spheres J e` THEN
        UNDISCH_TAC `DISJOINT (p3e_mcores J e nw) (topspace (topX:B topology))` THEN
        SET_TAC[]];
      EXISTS_TAC `(topspace topX DIFF mfd_cut_spheres J e) DIFF (K:B->bool)` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC P3E_CTOP_OPEN_OLD THEN
        EXISTS_TAC `atlasX:((B->bool)#(B->real^3))->bool` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_MESON_TAC[p3e_cutdata];
          SET_TAC[]];
        UNDISCH_TAC `(p:B) IN topspace topX DIFF mfd_cut_spheres J e` THEN
        UNDISCH_TAC `~((p:B) IN K)` THEN SET_TAC[];
        UNDISCH_TAC `p3e_wret (topX:B topology) J e Om P SUBSET K` THEN
        UNDISCH_TAC `p3e_czs (topX:B topology) J e nw INTER topspace topX =
                     topspace topX DIFF mfd_cut_spheres J e` THEN
        UNDISCH_TAC `DISJOINT (p3e_mcores J e nw) (topspace (topX:B topology))` THEN
        SET_TAC[]]];
    SUBGOAL_THEN
     `?i x. i IN J /\ norm(x:real^3) <= &1 /\ (p:B) = p3e_ccp e nw i x`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(p:B) IN mfd_cut_cores J (p3e_ccp e nw) (p3e_ccm e nw)` MP_TAC THENL
       [UNDISCH_TAC `~((p:B) IN topspace topX)` THEN
        UNDISCH_TAC
         `(p:B) IN p3e_czs topX J e nw DIFF (p3e_wret topX J e Om P UNION p3e_mcores J e nw)` THEN
        REWRITE_TAC[p3e_czs] THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[P3E_CUT_CORES] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `b:bool`
        (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC))) THEN
      MAP_EVERY EXISTS_TAC [`i:num`; `x:real^3`] THEN ASM_SIMP_TAC[P3E_CCP_CORE] THEN
      ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `(p:B) IN p3e_czs topX J e nw DIFF (p3e_wret topX J e Om P UNION p3e_mcores J e nw)` THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      REWRITE_TAC[p3e_mcores; IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `IMAGE (p3e_ccm (e:num->real^3->B) nw i) (cball(vec 0,&1))` THEN
      CONJ_TAC THENL [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN EXISTS_TAC `x:real^3` THEN
      ASM_SIMP_TAC[P3E_CCM_CORE];
      ALL_TAC] THEN
    EXISTS_TAC `IMAGE (p3e_ccp (e:num->real^3->B) nw i) (ball(vec 0,&2))` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                     `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                     `i:num`; `ball(vec 0:real^3,&2)`] P3E_CAP_IMAGE_OPEN) THEN
      ASM_SIMP_TAC[OPEN_BALL; SUBSET_REFL];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      MP_TAC P3E_CBALL1_BALL2 THEN REWRITE_TAC[SUBSET; IN_CBALL_0] THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                     `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                     `Om:B->bool`; `i:num`] P3E_HALF_ANNULUS_OFF) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
      MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                     `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                     `Om:B->bool`; `P:B->bool`; `i:num`] P3E_RETAIN_PLUS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`]
        P3E_CAP_BALL2_PARTS) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN REPEAT DISCH_TAC THEN
      UNDISCH_TAC `!i. i IN J
                       ==> DISJOINT (IMAGE (p3e_ccp (e:num->real^3->B) nw i) (cball(vec 0,&1)))
                                    (p3e_mcores J e nw) /\
                           DISJOINT (IMAGE (p3e_ccp e nw i) (cball(vec 0,&1)))
                                    (topspace topX) /\
                           IMAGE (p3e_ccp e nw i) (cball(vec 0,&1)) SUBSET p3e_czs topX J e nw` THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC P3E_COPEN_SETS THEN
      MAP_EVERY EXISTS_TAC
       [`IMAGE (p3e_ccp (e:num->real^3->B) nw i) (cball(vec 0,&1))`;
        `IMAGE ((e:num->real^3->B) i) {y:real^3 | &1 < norm y /\ norm y < &2}`;
        `topspace (topX:B topology)`; `mfd_cut_spheres J (e:num->real^3->B)`; `Om:B->bool`] THEN
      ASM_REWRITE_TAC[]]]);;

let P3E_RETAIN_GENERIC = prove
 (`!(topX:B topology) atlasX J e nw Om P.
     p3e_rhyp topX atlasX J e nw Om P
     ==> p3e_rdisc topX J e nw Om P SUBSET topspace (p3e_ctop topX J e nw) /\
         open_in (p3e_ctop topX J e nw) (p3e_rdisc topX J e nw Om P) /\
         closed_in (p3e_ctop topX J e nw) (p3e_rdisc topX J e nw Om P) /\
         (!i. i IN J
              ==> IMAGE (p3e_ccp e nw i) (cball(vec 0,&1)) SUBSET
                  p3e_rdisc topX J e nw Om P /\
                  DISJOINT (IMAGE (p3e_ccm e nw i) (cball(vec 0,&1)))
                           (p3e_rdisc topX J e nw Om P)) /\
         P SUBSET topspace (p3e_ctop topX J e nw) DIFF p3e_rdisc topX J e nw Om P /\
         (topspace (p3e_ctop topX J e nw) DIFF p3e_rdisc topX J e nw Om P) INTER
         topspace topX = p3e_wret topX J e Om P /\
         p3e_wret topX J e Om P SUBSET Om /\
         (!i A. i IN J /\ connected_in topX A /\ A SUBSET Om DIFF mfd_cut_spheres J e /\
                e i (&3 / &4 % basis 1) IN A
                ==> A SUBSET topspace (p3e_ctop topX J e nw) DIFF
                             p3e_rdisc topX J e nw Om P)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p3e_rhyp] th) THEN
    ASSUME_TAC(MATCH_MP P3E_RETAIN_ROPEN th) THEN
    ASSUME_TAC(MATCH_MP P3E_RETAIN_COPEN th)) THEN
  SUBGOAL_THEN `Om SUBSET topspace (topX:B topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                 `e:num->real^3->B`; `nw:num->bool->real^3->B`] P3E_MCORES_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:B topology`; `J:num->bool`; `e:num->real^3->B`; `Om:B->bool`;
                 `P:B->bool`] P3E_WRET_SUB) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                 `e:num->real^3->B`; `nw:num->bool->real^3->B`] P3E_CZS_INTER_X) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `P SUBSET p3e_wret (topX:B topology) J e Om P` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `a:B` THEN DISCH_TAC THEN
    MATCH_MP_TAC P3E_WRET_SEED THEN
    UNDISCH_TAC `(a:B) IN P` THEN UNDISCH_TAC `P SUBSET (Om:B->bool)` THEN
    UNDISCH_TAC `DISJOINT P (mfd_cut_spheres J (e:num->real^3->B))` THEN
    UNDISCH_TAC `Om SUBSET topspace (topX:B topology)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closed_in (p3e_ctop topX J e nw)
              (p3e_czs topX J e nw DIFF
               (p3e_wret topX J e Om P UNION p3e_mcores J e (nw:num->bool->real^3->B)))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
      [SYM(MATCH_MP P3E_CTOP_TOPSPACE th)]) THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A. connected_in topX A /\ A SUBSET Om DIFF mfd_cut_spheres J e /\
        (?i. i IN J /\ (e:num->real^3->B) i (&3 / &4 % basis 1) IN A)
        ==> A SUBSET p3e_wret topX J e Om P`
  (LABEL_TAC "conn") THENL
   [GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC P3E_WRET_CONNECTED THEN
    EXISTS_TAC `(e:num->real^3->B) i (&3 / &4 % basis 1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P3E_WRET_SEED THEN
    SUBGOAL_THEN `(e:num->real^3->B) i (&3 / &4 % basis 1) IN Om DIFF mfd_cut_spheres J e`
    MP_TAC THENL
     [UNDISCH_TAC `(e:num->real^3->B) i (&3 / &4 % basis 1) IN A` THEN
      UNDISCH_TAC `(A:B->bool) SUBSET Om DIFF mfd_cut_spheres J e` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t x:B. s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `Om:B->bool` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_CTOP_TOPSPACE th]) THEN
  REWRITE_TAC[p3e_rdisc] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `W = p3e_wret (topX:B topology) J e Om P` THEN
  ABBREV_TAC `MC = p3e_mcores J (e:num->real^3->B) nw` THEN
  ABBREV_TAC `Zs = p3e_czs (topX:B topology) J e nw` THEN
  ABBREV_TAC `SS = mfd_cut_spheres J (e:num->real^3->B)` THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `!i. i IN J
                     ==> DISJOINT (IMAGE (p3e_ccp (e:num->real^3->B) nw i) (cball(vec 0,&1))) MC /\
                         DISJOINT (IMAGE (p3e_ccp e nw i) (cball(vec 0,&1))) (topspace topX) /\
                         IMAGE (p3e_ccp e nw i) (cball(vec 0,&1)) SUBSET Zs` THEN
    UNDISCH_TAC `!i. i IN J
                     ==> IMAGE (p3e_ccm (e:num->real^3->B) nw i) (cball(vec 0,&1)) SUBSET MC` THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(W:B->bool) SUBSET topspace topX INTER (Om DIFF SS)` THEN
    UNDISCH_TAC `IMAGE (p3e_ccm (e:num->real^3->B) nw i) (cball(vec 0,&1)) SUBSET MC` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (p3e_ccp (e:num->real^3->B) nw i) (cball(vec 0,&1))) MC` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (p3e_ccp (e:num->real^3->B) nw i) (cball(vec 0,&1)))
                          (topspace (topX:B topology))` THEN
    UNDISCH_TAC `IMAGE (p3e_ccp (e:num->real^3->B) nw i) (cball(vec 0,&1)) SUBSET Zs` THEN
    SET_TAC[];
    UNDISCH_TAC `P SUBSET (W:B->bool)` THEN
    UNDISCH_TAC `(W:B->bool) SUBSET topspace topX INTER (Om DIFF SS)` THEN
    UNDISCH_TAC `(Zs:B->bool) INTER topspace topX = topspace topX DIFF SS` THEN SET_TAC[];
    UNDISCH_TAC `(W:B->bool) SUBSET topspace topX INTER (Om DIFF SS)` THEN
    UNDISCH_TAC `(Zs:B->bool) INTER topspace topX = topspace topX DIFF SS` THEN
    UNDISCH_TAC `DISJOINT (MC:B->bool) (topspace topX)` THEN SET_TAC[];
    UNDISCH_TAC `(W:B->bool) SUBSET topspace topX INTER (Om DIFF SS)` THEN SET_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `A:B->bool`] THEN STRIP_TAC THEN
    USE_THEN "conn" (MP_TAC o SPEC `A:B->bool`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(W:B->bool) SUBSET topspace topX INTER (Om DIFF SS)` THEN
    UNDISCH_TAC `(Zs:B->bool) INTER topspace topX = topspace topX DIFF SS` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The hypotheses p3e_rhyp from the data of MT Lemma 11.30 and Thm 11.31 in  *)
(* abstract form (p3e_hdata): K compact and the horn sets H j (|z| >= 1)     *)
(* inside Om, disjoint from P and pairwise, the union of the components of   *)
(* Om meeting P equal to K plus the horn sets, compact horn pieces           *)
(* H j (1 <= |z| <= R), the surgery neck e j continuous and injective on     *)
(* 1/2 < |y| <= 2 with image in its horn set, the far end of the horn inside *)
(* the end component cut off by the central sphere S j (11.31), and (the     *)
(* separation clause) the component of Om DIFF S j at the plus point e j     *)
(* (2 basis 1) inside the open horn H j (|z| > 1); plus apx_sphere_sep of X. *)
(* Ej = that component: it contains the plus piece of the neck, misses P and *)
(* every minus point, so (h1) holds; W lies in the union of the components   *)
(* of Om meeting P and misses each Ej, which holds the far end, so W lies in *)
(* K' = K plus the pieces H j (1 <= |z| <= R1 j).                            *)
(* ------------------------------------------------------------------------- *)

let p3e_hdata = new_definition
 `p3e_hdata (topX:B topology) (atlasX:((B->bool)#(B->real^3))->bool) (J:num->bool)
            (e:num->real^3->B) (nw:num->bool->real^3->B) (Om:B->bool) (P:B->bool)
            (K:B->bool) (H:num->real^3->B) (R1:num->real) <=>
    p3e_cutdata topX atlasX J e nw /\ apx_sphere_sep topX atlasX /\
    open_in topX Om /\ P SUBSET Om /\ compact_in topX K /\
    UNIONS {U | U IN connected_components_of (subtopology topX Om) /\ ~(U INTER P = {})} =
    K UNION UNIONS {IMAGE (H j) {z:real^3 | &1 <= norm z} | j IN J} /\
    (!j. j IN J
         ==> IMAGE (H j) {z:real^3 | &1 <= norm z} SUBSET Om /\
             (!R. compact_in topX (IMAGE (H j) {z:real^3 | &1 <= norm z /\ norm z <= R})) /\
             DISJOINT (IMAGE (H j) {z:real^3 | &1 <= norm z}) P /\
             IMAGE (e j) {y:real^3 | &1 / &2 < norm y /\ norm y <= &2} SUBSET
             IMAGE (H j) {z:real^3 | &1 <= norm z} /\
             continuous_map
               (subtopology euclidean {y:real^3 | &1 / &2 < norm y /\ norm y <= &2},topX)
               (e j) /\
             (!x y. &1 / &2 < norm x /\ norm x <= &2 /\ &1 / &2 < norm y /\ norm y <= &2 /\
                    e j x = e j y ==> x = y) /\
             (!z. R1 j <= norm z
                  ==> H j z IN connected_component_of
                                 (subtopology topX
                                   (IMAGE (H j) {z:real^3 | &1 <= norm z} DIFF
                                    IMAGE (e j) (sphere(vec 0,&1))))
                                 (e j (&2 % basis 1))) /\
             connected_component_of
               (subtopology topX (Om DIFF IMAGE (e j) (sphere(vec 0,&1))))
               (e j (&2 % basis 1)) SUBSET
             IMAGE (H j) {z:real^3 | &1 < norm z}) /\
    (!i j. i IN J /\ j IN J /\ ~(i = j)
           ==> DISJOINT (IMAGE (H i) {z:real^3 | &1 <= norm z})
                        (IMAGE (H j) {z:real^3 | &1 <= norm z}))`;;

let P3E_HD_SETS = prove
 (`connected {y:real^3 | &1 < norm y /\ norm y <= &2} /\
   {y:real^3 | &1 < norm y /\ norm y <= &2} SUBSET
   {y:real^3 | &1 / &2 < norm y /\ norm y <= &2} /\
   sphere(vec 0:real^3,&1) SUBSET {y:real^3 | &1 / &2 < norm y /\ norm y <= &2} /\
   annulus (&1 / &2) (&2) SUBSET {y:real^3 | &1 / &2 < norm y /\ norm y <= &2} /\
   (&2 % basis 1:real^3) IN {y:real^3 | &1 < norm y /\ norm y <= &2} /\
   (&4 / &3 % basis 1:real^3) IN {y:real^3 | &1 < norm y /\ norm y <= &2} /\
   (&3 / &4 % basis 1:real^3) IN {y:real^3 | &1 / &2 < norm y /\ norm y <= &2}`,
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `&2`]
      (CONJUNCT1(CONJUNCT2 CONNECTED_ANNULUS))) THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; DIMINDEX_3; ARITH];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM; P3E_ANNULUS_HALF_TWO] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM; P3E_NORM_BASIS1_MUL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM; P3E_NORM_BASIS1_MUL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM; P3E_NORM_BASIS1_MUL] THEN REAL_ARITH_TAC]);;

(* Points of the neck off its central sphere and off all cut spheres.       *)

let P3E_HD_OFF_SPHERE = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1 j y.
     p3e_hdata topX atlasX J e nw Om P K H R1 /\ j IN J /\
     &1 / &2 < norm y /\ norm y <= &2 /\ ~(norm y = &1)
     ==> ~(e j y IN IMAGE (e j) (sphere(vec 0,&1)))`,
  REWRITE_TAC[p3e_hdata] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(e:num->real^3->B) j y IN IMAGE (e j) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous_map")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `s:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]);;

(* The end component Ej of Om DIFF S j at the plus point: it contains the   *)
(* plus piece of the neck, lies in the horn set, misses P and every minus   *)
(* point (other horns by disjointness, its own neck by apx_sphere_sep).     *)

let P3E_HD_EJ = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1 j.
     p3e_hdata topX atlasX J e nw Om P K H R1 /\ j IN J
     ==> IMAGE (e j) {y:real^3 | &1 < norm y /\ norm y <= &2} SUBSET
         connected_component_of (subtopology topX (Om DIFF IMAGE (e j) (sphere(vec 0,&1))))
                                (e j (&2 % basis 1)) /\
         connected_component_of (subtopology topX (Om DIFF IMAGE (e j) (sphere(vec 0,&1))))
                                (e j (&2 % basis 1)) SUBSET
         IMAGE (H j) {z:real^3 | &1 <= norm z} /\
         DISJOINT (connected_component_of
                     (subtopology topX (Om DIFF IMAGE (e j) (sphere(vec 0,&1))))
                     (e j (&2 % basis 1))) P /\
         (!i. i IN J
              ==> ~(e i (&3 / &4 % basis 1) IN
                    connected_component_of
                      (subtopology topX (Om DIFF IMAGE (e j) (sphere(vec 0,&1))))
                      (e j (&2 % basis 1))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p3e_hdata] th)) THEN
  SUBGOAL_THEN `Om SUBSET topspace (topX:B topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous_map")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
  ABBREV_TAC `Ej = connected_component_of
                     (subtopology topX (Om DIFF IMAGE ((e:num->real^3->B) j) (sphere(vec 0,&1))))
                     (e j (&2 % basis 1))` THEN
  SUBGOAL_THEN `IMAGE ((e:num->real^3->B) j) {y:real^3 | &1 < norm y /\ norm y <= &2} SUBSET Ej`
  ASSUME_TAC THENL
   [EXPAND_TAC "Ej" THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclidean {y:real^3 | &1 / &2 < norm y /\ norm y <= &2}` THEN
      ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN; P3E_HD_SETS];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(y:real^3) IN {y:real^3 | &1 / &2 < norm y /\ norm y <= &2}` MP_TAC THENL
         [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `IMAGE ((e:num->real^3->B) j) {y:real^3 | &1 / &2 < norm y /\ norm y <= &2} SUBSET IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z}` THEN
        UNDISCH_TAC `IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z} SUBSET Om` THEN SET_TAC[];
        MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                       `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                       `Om:B->bool`; `P:B->bool`; `K:B->bool`; `H:num->real^3->B`;
                       `R1:num->real`; `j:num`; `y:real^3`] P3E_HD_OFF_SPHERE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[P3E_HD_SETS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Ej SUBSET IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 < norm z}` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `Ej SUBSET IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z}` THEN
    UNDISCH_TAC `DISJOINT (IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z}) P` THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i:num = j` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `apx_sphere_sep (topX:B topology) atlasX` THEN
    REWRITE_TAC[apx_sphere_sep] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:num->real^3->B) j`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC P3E_CUTDATA_NECK_CHART THEN
      MAP_EVERY EXISTS_TAC [`J:num->bool`; `nw:num->bool->real^3->B`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[apx_separates] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(e:num->real^3->B) j (&4 / &3 % basis 1) IN
      connected_component_of
        (subtopology topX (topspace topX DIFF IMAGE (e j) (sphere(vec 0,&1))))
        (e j (&3 / &4 % basis 1))`
    MP_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s:B->bool. (x:B) IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `Ej:B->bool` THEN CONJ_TAC THENL
       [MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 P3E_HD_SETS)))))) THEN
        UNDISCH_TAC `IMAGE ((e:num->real^3->B) j) {y:real^3 | &1 < norm y /\ norm y <= &2}
                     SUBSET Ej` THEN SET_TAC[];
        MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
        ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
        EXPAND_TAC "Ej" THEN CONJ_TAC THENL
         [MESON_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF; CONNECTED_IN_SUBTOPOLOGY];
          MP_TAC(ISPECL [`subtopology topX
                            (Om DIFF IMAGE ((e:num->real^3->B) j) (sphere(vec 0,&1)))`;
                         `(e:num->real^3->B) j (&2 % basis 1)`]
            CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
          REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]]];
      REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[]];
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(e:num->real^3->B) i (&3 / &4 % basis 1) IN IMAGE (H i) {z:real^3 | &1 <= norm z}`
    MP_TAC THENL
     [(FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous_map"))
            (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
      MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 P3E_HD_SETS)))))) THEN
      UNDISCH_TAC `IMAGE ((e:num->real^3->B) i) {y:real^3 | &1 / &2 < norm y /\ norm y <= &2}
                   SUBSET IMAGE ((H:num->real^3->B) i) {z:real^3 | &1 <= norm z}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous_map"))
               (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `Ej SUBSET IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z}` THEN
    UNDISCH_TAC `(e:num->real^3->B) i (&3 / &4 % basis 1) IN Ej` THEN SET_TAC[]]);;

(* The plus component of Om DIFF S lies in Ej.                              *)

let P3E_HD_PJ = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1 j.
     p3e_hdata topX atlasX J e nw Om P K H R1 /\ j IN J
     ==> connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e))
                                (e j (&4 / &3 % basis 1)) SUBSET
         connected_component_of (subtopology topX (Om DIFF IMAGE (e j) (sphere(vec 0,&1))))
                                (e j (&2 % basis 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                 `Om:B->bool`; `P:B->bool`; `K:B->bool`; `H:num->real^3->B`;
                 `R1:num->real`; `j:num`] P3E_HD_EJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Ej = connected_component_of
                     (subtopology topX (Om DIFF IMAGE ((e:num->real^3->B) j) (sphere(vec 0,&1))))
                     (e j (&2 % basis 1))` THEN
  SUBGOAL_THEN `(e:num->real^3->B) j (&4 / &3 % basis 1) IN Ej` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 P3E_HD_SETS)))))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected_component_of
      (subtopology topX (Om DIFF IMAGE ((e:num->real^3->B) j) (sphere(vec 0,&1))))
      (e j (&4 / &3 % basis 1)) = Ej`
  (SUBST1_TAC o SYM) THENL
   [EXPAND_TAC "Ej" THEN MATCH_MP_TAC P3E_COMPONENT_OF_IN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `(e:num->real^3->B) j (&4 / &3 % basis 1) IN
    topspace (subtopology topX (Om DIFF mfd_cut_spheres J e))`
  THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    ASM_SIMP_TAC[P3E_COMPONENT_OF_SELF; CONNECTED_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MESON_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF; CONNECTED_IN_SUBTOPOLOGY];
      MP_TAC(ISPECL [`subtopology topX (Om DIFF mfd_cut_spheres J (e:num->real^3->B))`;
                     `(e:num->real^3->B) j (&4 / &3 % basis 1)`]
        CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; mfd_cut_spheres] THEN ASM SET_TAC[]];
    ASM_MESON_TAC[CONNECTED_COMPONENT_OF_EQ_EMPTY; EMPTY_SUBSET]]);;

(* W lies in the union CU of the components of Om meeting P.               *)

let P3E_HD_W_CU = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1.
     p3e_hdata topX atlasX J e nw Om P K H R1
     ==> p3e_wret topX J e Om P SUBSET
         UNIONS {U | U IN connected_components_of (subtopology topX Om) /\ ~(U INTER P = {})}`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p3e_hdata] th)) THEN
  REWRITE_TAC[SUBSET; IN_P3E_WRET] THEN X_GEN_TAC `p:B` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cond")))) THEN
  ABBREV_TAC `Q = connected_component_of
                    (subtopology topX (Om DIFF mfd_cut_spheres J (e:num->real^3->B))) (p:B)` THEN
  ABBREV_TAC `C = connected_component_of (subtopology (topX:B topology) Om) (p:B)` THEN
  SUBGOAL_THEN `(p:B) IN C /\ C IN connected_components_of (subtopology topX Om)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3E_COMPONENT_OF_SELF THEN
      ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER];
      REWRITE_TAC[connected_components_of; IN_ELIM_THM] THEN EXISTS_TAC `p:B` THEN
      ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q:B->bool) SUBSET C` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Q"; "C"] THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MESON_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF; CONNECTED_IN_SUBTOPOLOGY];
        MP_TAC(ISPECL [`subtopology topX (Om DIFF mfd_cut_spheres J (e:num->real^3->B))`;
                       `p:B`] CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]];
      MATCH_MP_TAC P3E_COMPONENT_OF_SELF THEN
      ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_DIFF]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `C:B->bool` THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "cond" DISJ_CASES_TAC THENL
   [UNDISCH_TAC `(Q:B->bool) SUBSET C` THEN UNDISCH_TAC `~((Q:B->bool) INTER P = {})` THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(e:num->real^3->B) i (&3 / &4 % basis 1) IN
    UNIONS {U | U IN connected_components_of (subtopology topX Om) /\ ~(U INTER P = {})}`
  MP_TAC THENL
   [(FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous_map"))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    SUBGOAL_THEN
     `(e:num->real^3->B) i (&3 / &4 % basis 1) IN
      IMAGE ((H:num->real^3->B) i) {z:real^3 | &1 <= norm z}`
    ASSUME_TAC THENL
     [MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 P3E_HD_SETS)))))) THEN
      UNDISCH_TAC `IMAGE ((e:num->real^3->B) i) {y:real^3 | &1 / &2 < norm y /\ norm y <= &2}
                   SUBSET IMAGE ((H:num->real^3->B) i) {z:real^3 | &1 <= norm z}` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `UNIONS {U | U IN connected_components_of (subtopology topX Om) /\
                             ~(U INTER P = {})} =
                 K UNION UNIONS {IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z} |
                                 j IN J}` THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN DISJ2_TAC THEN
    EXISTS_TAC `IMAGE ((H:num->real^3->B) i) {z:real^3 | &1 <= norm z}` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; connected_components_of] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:B->bool` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:B` STRIP_ASSUME_TAC) ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `U:B->bool = C` (fun th -> SUBST1_TAC(SYM th) THEN ASM_REWRITE_TAC[]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`subtopology (topX:B topology) Om`; `u:B`;
                 `(e:num->real^3->B) i (&3 / &4 % basis 1)`] P3E_COMPONENT_OF_IN) THEN
  MP_TAC(ISPECL [`subtopology (topX:B topology) Om`; `p:B`;
                 `(e:num->real^3->B) i (&3 / &4 % basis 1)`] P3E_COMPONENT_OF_IN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `(e:num->real^3->B) i (&3 / &4 % basis 1) IN Q` THEN
    UNDISCH_TAC `(Q:B->bool) SUBSET C` THEN SET_TAC[];
    ALL_TAC] THEN
  MESON_TAC[]);;

(* W lies in the compact set K' = K plus the horn pieces up to R1 j.        *)

let P3E_HD_W_K = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1.
     p3e_hdata topX atlasX J e nw Om P K H R1
     ==> p3e_wret topX J e Om P SUBSET
         K UNION UNIONS {IMAGE (H j) {z:real^3 | &1 <= norm z /\ norm z <= R1 j} | j IN J}`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p3e_hdata] th) THEN
    ASSUME_TAC(MATCH_MP P3E_HD_W_CU th)) THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(p:B) IN K UNION UNIONS {IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z} | j IN J}`
  MP_TAC THENL
   [UNDISCH_TAC `UNIONS {U | U IN connected_components_of (subtopology topX Om) /\
                             ~(U INTER P = {})} =
                 K UNION UNIONS {IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z} |
                                 j IN J}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE `!s:B->bool. (x:B) IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `p3e_wret (topX:B topology) J e Om P` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNION] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th]) MP_TAC) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:B->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `norm(z:real^3) <= R1(j:num)` THENL
   [DISJ2_TAC THEN EXISTS_TAC `IMAGE ((H:num->real^3->B) j)
                                 {z:real^3 | &1 <= norm z /\ norm z <= R1 j}` THEN
    CONJ_TAC THENL [EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* far point: p is in Ej, so is its component, which then cannot be a W-component *)
  (FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous_map")) (concl th))) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
  ABBREV_TAC `E0 = connected_component_of
                     (subtopology topX
                       (IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z} DIFF
                        IMAGE ((e:num->real^3->B) j) (sphere(vec 0,&1))))
                     (e j (&2 % basis 1))` THEN
  SUBGOAL_THEN `(p:B) IN E0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `E0:B->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `(p:B) = (H:num->real^3->B) j z`)) THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                 `Om:B->bool`; `P:B->bool`; `K:B->bool`; `H:num->real^3->B`;
                 `R1:num->real`; `j:num`] P3E_HD_EJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Ej = connected_component_of
                     (subtopology topX (Om DIFF IMAGE ((e:num->real^3->B) j) (sphere(vec 0,&1))))
                     (e j (&2 % basis 1))` THEN
  SUBGOAL_THEN `(p:B) IN Ej` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s:B->bool. (x:B) IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `E0:B->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Ej" THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    SUBGOAL_THEN `(E0:B->bool) SUBSET
                  IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z} DIFF
                  IMAGE ((e:num->real^3->B) j) (sphere(vec 0,&1))`
    ASSUME_TAC THENL
     [EXPAND_TAC "E0" THEN
      MP_TAC(ISPECL [`subtopology topX
                        (IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z} DIFF
                         IMAGE ((e:num->real^3->B) j) (sphere(vec 0,&1)))`;
                     `(e:num->real^3->B) j (&2 % basis 1)`]
        CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "E0" THEN
      MESON_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF; CONNECTED_IN_SUBTOPOLOGY];
      UNDISCH_TAC `(E0:B->bool) SUBSET
                   IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z} DIFF
                   IMAGE ((e:num->real^3->B) j) (sphere(vec 0,&1))` THEN
      UNDISCH_TAC `IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z} SUBSET Om` THEN
      SET_TAC[];
      UNDISCH_TAC `(p:B) IN E0` THEN EXPAND_TAC "E0" THEN
      MESON_TAC[CONNECTED_COMPONENT_OF_EQ_EMPTY; MEMBER_NOT_EMPTY; P3E_COMPONENT_OF_SELF]];
    ALL_TAC] THEN
  (* the W-component of p lies in Ej *)
  UNDISCH_TAC `(p:B) IN p3e_wret topX J e Om P` THEN REWRITE_TAC[IN_P3E_WRET] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  SUBGOAL_THEN
   `connected_component_of (subtopology topX (Om DIFF mfd_cut_spheres J e)) (p:B) SUBSET Ej`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `connected_component_of
        (subtopology topX (Om DIFF IMAGE ((e:num->real^3->B) j) (sphere(vec 0,&1)))) (p:B) =
      Ej`
    (SUBST1_TAC o SYM) THENL
     [EXPAND_TAC "Ej" THEN MATCH_MP_TAC P3E_COMPONENT_OF_IN THEN
      UNDISCH_TAC `(p:B) IN Ej` THEN EXPAND_TAC "Ej" THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MESON_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF; CONNECTED_IN_SUBTOPOLOGY];
        MP_TAC(ISPECL [`subtopology topX (Om DIFF mfd_cut_spheres J (e:num->real^3->B))`;
                       `p:B`] CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; mfd_cut_spheres] THEN
        UNDISCH_TAC `(j:num) IN J` THEN SET_TAC[]];
      MATCH_MP_TAC P3E_COMPONENT_OF_SELF THEN
      ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_DIFF]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Ej:B->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN ASM SET_TAC[]]);;

(* The hypotheses of the generic theorem.                                   *)

let P3E_RETAIN_HYPS = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1.
     p3e_hdata topX atlasX J e nw Om P K H R1
     ==> p3e_rhyp topX atlasX J e nw Om P`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p3e_hdata] th) THEN
    ASSUME_TAC(MATCH_MP P3E_HD_W_K th)) THEN
  SUBGOAL_THEN `Om SUBSET topspace (topX:B topology)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN J
        ==> IMAGE ((e:num->real^3->B) i) {y:real^3 | &1 / &2 < norm y /\ norm y <= &2} SUBSET
            IMAGE (H i) {z:real^3 | &1 <= norm z} /\
            IMAGE ((H:num->real^3->B) i) {z:real^3 | &1 <= norm z} SUBSET Om /\
            DISJOINT (IMAGE (H i) {z:real^3 | &1 <= norm z}) P`
  (LABEL_TAC "nk") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous_map"))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p3e_rhyp] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_cut_spheres; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS;
                IN_ELIM_THM] THEN
    X_GEN_TAC `q:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:B->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    USE_THEN "nk" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) IN J`))) THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 P3E_HD_SETS))) THEN
    UNDISCH_TAC `(q:B) IN t` THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(q:B) IN P` THEN
    SET_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "nk" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) IN J`))) THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 P3E_HD_SETS)))) THEN SET_TAC[];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                   `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                   `Om:B->bool`; `P:B->bool`; `K:B->bool`; `H:num->real^3->B`;
                   `R1:num->real`; `j:num`] P3E_HD_PJ) THEN
    MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                   `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                   `Om:B->bool`; `P:B->bool`; `K:B->bool`; `H:num->real^3->B`;
                   `R1:num->real`; `j:num`] P3E_HD_EJ) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
    CONJ_TAC THENL [REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "basis")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl))) THEN ASM SET_TAC[];
    EXISTS_TAC `K UNION UNIONS {IMAGE ((H:num->real^3->B) j)
                                      {z:real^3 | &1 <= norm z /\ norm z <= R1 j} | j IN J}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IN_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPACT_IN_UNIONS THEN
      SUBGOAL_THEN `FINITE (J:num->bool)` ASSUME_TAC THENL
       [UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN SIMP_TAC[p3e_cutdata];
        ALL_TAC] THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      (FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous_map"))
            (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
       [UNDISCH_TAC
         `UNIONS {U | U IN connected_components_of (subtopology topX Om) /\
                      ~(U INTER P = {})} =
          K UNION UNIONS {IMAGE ((H:num->real^3->B) j) {z:real^3 | &1 <= norm z} | j IN J}` THEN
        MP_TAC(ISPEC `subtopology (topX:B topology) Om` CONNECTED_COMPONENTS_OF_SUBSET) THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        USE_THEN "nk" (fun th -> MP_TAC(MP (SPEC `j:num` th) (ASSUME `(j:num) IN J`))) THEN
        MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t
                               ==> (a /\ IMAGE (f:real^3->B) t SUBSET u /\ b)
                                   ==> IMAGE f s SUBSET u`) THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC]]]);;

(* Main theorem: from the 11.30 / 11.31 data, the discarded part D of Z.     *)

let P3E_RETAIN = prove
 (`!(topX:B topology) atlasX J e nw Om P K H R1.
     p3e_hdata topX atlasX J e nw Om P K H R1
     ==> p3e_rdisc topX J e nw Om P SUBSET topspace (p3e_ctop topX J e nw) /\
         open_in (p3e_ctop topX J e nw) (p3e_rdisc topX J e nw Om P) /\
         closed_in (p3e_ctop topX J e nw) (p3e_rdisc topX J e nw Om P) /\
         (!i. i IN J
              ==> IMAGE (p3e_ccp e nw i) (cball(vec 0,&1)) SUBSET
                  p3e_rdisc topX J e nw Om P /\
                  DISJOINT (IMAGE (p3e_ccm e nw i) (cball(vec 0,&1)))
                           (p3e_rdisc topX J e nw Om P)) /\
         P SUBSET topspace (p3e_ctop topX J e nw) DIFF p3e_rdisc topX J e nw Om P /\
         (topspace (p3e_ctop topX J e nw) DIFF p3e_rdisc topX J e nw Om P) INTER
         topspace topX = p3e_wret topX J e Om P /\
         p3e_wret topX J e Om P SUBSET Om /\
         (!i A. i IN J /\ connected_in topX A /\ A SUBSET Om DIFF mfd_cut_spheres J e /\
                e i (&3 / &4 % basis 1) IN A
                ==> A SUBSET topspace (p3e_ctop topX J e nw) DIFF
                             p3e_rdisc topX J e nw Om P)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P3E_RETAIN_HYPS) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP P3E_RETAIN_GENERIC));;

