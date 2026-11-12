(* ========================================================================= *)
(* Unit pc_rfs_ccsc: cutting along neck spheres and capping keeps the        *)
(* components simply connected,                                              *)
(*   RFS_CUTCAP_SC: |- !u v. RFS_CUTCAP_SC_STATEMENT u v                     *)
(* (the statement is in pc_rfs_top).                                         *)
(*                                                                           *)
(* Route: for a component W of the capped space Z, every loop of W is      *)
(* homotopic in W to a loop off the closed 3/2-balls of its caps (general  *)
(* position, pc_rfs_ccscpush); the inverse gluing map gg takes it into one *)
(* simply connected component of X; a pinch map P from X to W (the identity *)
(* through ff off the collars, the radial collapse of each collar into its *)
(* cap, the cap centre beyond the cut sphere) brings the null-homotopy back *)
(* (CCS_SC_FROM_PINCH).  The far sides are disjoint because every neck      *)
(* sphere separates (SMT_SC_SPHERE_SEP).  The core argument is stated for   *)
(* topological cut-and-cap data, ccs_cutcap (Hausdorff, locally path        *)
(* connected spaces, separating spheres): CCS_CUTCAP_SC_TOP.  Compactness   *)
(* of X is not used.                                                        *)
(* ========================================================================= *)

needs "src/pc_rfs_ccscpush.ml";;
needs "src/pc_rfs_top.ml";;
needs "src/pc_smt_sep.ml";;

prioritize_real();;
type_invention_error := true;;

(* The topological content of mfd_cut_cap: neck charts e i of X, ball       *)
(* charts cp i, cm i of Z (homeomorphisms onto open sets), the disjointness *)
(* conditions, the homeomorphism ff of X minus the spheres onto Z minus    *)
(* the cores with inverse gg, and the collar identities.                    *)

let ccs_cutcap = new_definition
 `ccs_cutcap (topX:A topology) (topZ:B topology) (J:num->bool)
             (e:num->real^3->A) (cp:num->real^3->B) (cm:num->real^3->B)
             (ff:A->B) (gg:B->A) <=>
    FINITE J /\
    (!i. i IN J
         ==> open_in topX (IMAGE (e i) (annulus (&1 / &2) (&2))) /\
             homeomorphic_map
               (subtopology euclidean (annulus (&1 / &2) (&2)),
                subtopology topX (IMAGE (e i) (annulus (&1 / &2) (&2)))) (e i) /\
             open_in topZ (IMAGE (cp i) (ball(vec 0,&2))) /\
             homeomorphic_map
               (subtopology euclidean (ball(vec 0,&2)),
                subtopology topZ (IMAGE (cp i) (ball(vec 0,&2)))) (cp i) /\
             open_in topZ (IMAGE (cm i) (ball(vec 0,&2))) /\
             homeomorphic_map
               (subtopology euclidean (ball(vec 0,&2)),
                subtopology topZ (IMAGE (cm i) (ball(vec 0,&2)))) (cm i)) /\
    (!i j. i IN J /\ j IN J /\ ~(i = j)
           ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                        (IMAGE (e j) (annulus (&1 / &2) (&2)))) /\
    (!i j. i IN J /\ j IN J
           ==> DISJOINT (IMAGE (cp i) (ball(vec 0,&2)))
                        (IMAGE (cm j) (ball(vec 0,&2))) /\
               (~(i = j)
                ==> DISJOINT (IMAGE (cp i) (ball(vec 0,&2)))
                             (IMAGE (cp j) (ball(vec 0,&2))) /\
                    DISJOINT (IMAGE (cm i) (ball(vec 0,&2)))
                             (IMAGE (cm j) (ball(vec 0,&2))))) /\
    open_in topX (topspace topX DIFF mfd_cut_spheres J e) /\
    open_in topZ (topspace topZ DIFF mfd_cut_cores J cp cm) /\
    homeomorphic_maps
      (subtopology topX (topspace topX DIFF mfd_cut_spheres J e),
       subtopology topZ (topspace topZ DIFF mfd_cut_cores J cp cm)) (ff,gg) /\
    (!i x. i IN J /\ x IN annulus (&1) (&2) ==> ff(e i x) = cp i x) /\
    (!i x. i IN J /\ x IN annulus (&1 / &2) (&1)
           ==> ff(e i x) = cm i (inv(norm x pow 2) % x))`;;

(* A smooth parametrization is a homeomorphism onto an open set.            *)

let CCS_PARAM_HOMEO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (e:real^N->A).
        mfd_param top atlas s e
        ==> open_in top (IMAGE e s) /\
            homeomorphic_map (subtopology euclidean s,
                              subtopology top (IMAGE e s)) e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o
             MATCH_MP MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHIC_MAPS_IMP_MAP THEN
  EXISTS_TAC `e':A->real^N` THEN
  ASM_REWRITE_TAC[homeomorphic_maps; CONTINUOUS_MAP_IN_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; IN_INTER] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`; `top:A topology`;
                   `e:real^N->A`] CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN SET_TAC[];
    ASM SET_TAC[]]);;

let CCS_CUTCAP_TOP = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topZ (atlasZ:((B->bool)#(B->real^3))->bool) J e cp cm ff gg.
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm ff gg
        ==> ccs_cutcap topX topZ J e cp cm ff gg`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mfd_cut_cap; ccs_cutcap; mfd_diffeo; mfd_neck_chart;
              mfd_ball_chart] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[CCS_PARAM_HOMEO]);;

(* ------------------------------------------------------------------------- *)
(* Elementary consequences of the cut-and-cap data.                          *)
(* ------------------------------------------------------------------------- *)

let CCS_INVERSION = prove
 (`!y:real^N. ~(y = vec 0)
              ==> norm(inv(norm y pow 2) % y) = inv(norm y) /\
                  inv(norm(inv(norm y pow 2) % y) pow 2) % (inv(norm y pow 2) % y) = y`,
  GEN_TAC THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(inv(norm(y:real^N) pow 2) % y) = inv(norm y)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    UNDISCH_TAC `&0 < norm(y:real^N)` THEN CONV_TAC REAL_FIELD;
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    MATCH_MP_TAC(MESON[VECTOR_MUL_LID] `!c v:real^N. c = &1 ==> c % v = v`) THEN
    UNDISCH_TAC `&0 < norm(y:real^N)` THEN CONV_TAC REAL_FIELD]);;

(* The inversion exchanges the two collar annuli.                          *)

let CCS_INVERSION_ANNULUS = prove
 (`!y:real^3. y IN annulus (&1) (&2)
              ==> inv(norm y pow 2) % y IN annulus (&1 / &2) (&1) /\
                  inv(norm(inv(norm y pow 2) % y) pow 2) % (inv(norm y pow 2) % y) = y`,
  GEN_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CCS_INVERSION] THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]]);;

(* Membership of chart points in the cut spheres and in the cap cores.    *)

let CCS_SPHERES_CHART = prove
 (`!J (e:num->real^3->A) i y.
        (!i y y'. i IN J /\ y IN annulus (&1 / &2) (&2) /\
                  y' IN annulus (&1 / &2) (&2) /\ e i y = e i y' ==> y = y') /\
        (!i j. i IN J /\ j IN J /\ ~(i = j)
               ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                            (IMAGE (e j) (annulus (&1 / &2) (&2)))) /\
        i IN J /\ y IN annulus (&1 / &2) (&2)
        ==> (e i y IN mfd_cut_spheres J e <=> norm y = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IN_MFD_CUT_SPHERES] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `x:real^3`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `j:num = i` THENL
     [UNDISCH_TAC `j:num = i` THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`i:num`; `y:real^3`] THEN
    ASM_REWRITE_TAC[]]);;

let CCS_CORES_CHART = prove
 (`!J (cp:num->real^3->B) cm i y.
        (!i y y'. i IN J /\ y IN ball(vec 0,&2) /\ y' IN ball(vec 0,&2) /\
                  cp i y = cp i y' ==> y = y') /\
        (!i y y'. i IN J /\ y IN ball(vec 0,&2) /\ y' IN ball(vec 0,&2) /\
                  cm i y = cm i y' ==> y = y') /\
        (!i j. i IN J /\ j IN J
               ==> DISJOINT (IMAGE (cp i) (ball(vec 0,&2)))
                            (IMAGE (cm j) (ball(vec 0,&2))) /\
                   (~(i = j)
                    ==> DISJOINT (IMAGE (cp i) (ball(vec 0,&2)))
                                 (IMAGE (cp j) (ball(vec 0,&2))) /\
                        DISJOINT (IMAGE (cm i) (ball(vec 0,&2)))
                                 (IMAGE (cm j) (ball(vec 0,&2))))) /\
        i IN J /\ y IN ball(vec 0,&2)
        ==> (cp i y IN mfd_cut_cores J cp cm <=> norm y <= &1) /\
            (cm i y IN mfd_cut_cores J cp cm <=> norm y <= &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IN_MFD_CUT_CORES] THEN
  SUBGOAL_THEN
   `!j x. j IN J /\ x IN ball(vec 0,&2)
          ==> ~((cp:num->real^3->B) i y = cm j x) /\ ~(cm i y = cp j x) /\
              (~(j = i) ==> ~(cp i y = cp j x) /\ ~(cm i y = cm j x))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`i:num`; `j:num`] th) THEN
                            MP_TAC(SPECL [`j:num`; `i:num`] th)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SET_RULE `DISJOINT (IMAGE (f:real^3->B) s) (IMAGE (g:real^3->B) t) <=>
                          !x y. x IN s /\ y IN t ==> ~(f x = g y)`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. norm x <= &1 ==> x IN ball(vec 0,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN EQ_TAC THEN
  (DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `x:real^3`
     STRIP_ASSUME_TAC)) ORELSE
   (DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`i:num`; `y:real^3`] THEN
    ASM_REWRITE_TAC[] THEN NO_TAC)) THEN
  ASM_CASES_TAC `j:num = i` THEN ASM_MESON_TAC[]);;

let CCS_CUTCAP_FACTS = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg.
        ccs_cutcap topX topZ J e cp cm ff gg
        ==> (!i y. i IN J /\ y IN annulus (&1 / &2) (&2)
                   ==> e i y IN topspace topX) /\
            (!i y. i IN J /\ y IN ball(vec 0,&2)
                   ==> cp i y IN topspace topZ /\ cm i y IN topspace topZ) /\
            (!i y. i IN J /\ y IN annulus (&1 / &2) (&2)
                   ==> (e i y IN mfd_cut_spheres J e <=> norm y = &1)) /\
            (!i y. i IN J /\ y IN ball(vec 0,&2)
                   ==> (cp i y IN mfd_cut_cores J cp cm <=> norm y <= &1) /\
                       (cm i y IN mfd_cut_cores J cp cm <=> norm y <= &1)) /\
            (!x. x IN topspace topX DIFF mfd_cut_spheres J e
                 ==> ff x IN topspace topZ DIFF mfd_cut_cores J cp cm /\
                     gg(ff x) = x) /\
            (!z. z IN topspace topZ DIFF mfd_cut_cores J cp cm
                 ==> gg z IN topspace topX DIFF mfd_cut_spheres J e /\
                     ff(gg z) = z) /\
            (!i y. i IN J /\ y IN annulus (&1) (&2) ==> gg(cp i y) = e i y) /\
            (!i y. i IN J /\ y IN annulus (&1) (&2)
                   ==> gg(cm i y) = e i (inv(norm y pow 2) % y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ccs_cutcap] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!i y. i IN J /\ y IN annulus (&1 / &2) (&2)
           ==> (e:num->real^3->A) i y IN topspace topX) /\
    (!i y y'. i IN J /\ y IN annulus (&1 / &2) (&2) /\
              y' IN annulus (&1 / &2) (&2) /\ e i y = e i y' ==> y = y') /\
    (!i y. i IN J /\ y IN ball(vec 0,&2)
           ==> (cp:num->real^3->B) i y IN topspace topZ /\
               (cm:num->real^3->B) i y IN topspace topZ) /\
    (!i y y'. i IN J /\ y IN ball(vec 0,&2) /\ y' IN ball(vec 0,&2) /\
              cp i y = cp i y' ==> y = y') /\
    (!i y y'. i IN J /\ y IN ball(vec 0,&2) /\ y' IN ball(vec 0,&2) /\
              cm i y = cm i y' ==> y = y')`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (annulus (&1 / &2) (&2):real^3->bool)`;
                     `subtopology topX (IMAGE ((e:num->real^3->A) i)
                                              (annulus (&1 / &2) (&2)))`;
                     `(e:num->real^3->A) i`]
                    HOMEOMORPHIC_IMP_SURJECTIVE_MAP);
      MP_TAC(ISPECL [`subtopology euclidean (annulus (&1 / &2) (&2):real^3->bool)`;
                     `subtopology topX (IMAGE ((e:num->real^3->A) i)
                                              (annulus (&1 / &2) (&2)))`;
                     `(e:num->real^3->A) i`]
                    HOMEOMORPHIC_IMP_INJECTIVE_MAP);
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^3,&2))`;
                       `subtopology topZ (IMAGE ((cp:num->real^3->B) i)
                                                (ball(vec 0,&2)))`;
                       `(cp:num->real^3->B) i`]
                      HOMEOMORPHIC_IMP_SURJECTIVE_MAP);
        MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^3,&2))`;
                       `subtopology topZ (IMAGE ((cm:num->real^3->B) i)
                                                (ball(vec 0,&2)))`;
                       `(cm:num->real^3->B) i`]
                      HOMEOMORPHIC_IMP_SURJECTIVE_MAP)];
      MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^3,&2))`;
                     `subtopology topZ (IMAGE ((cp:num->real^3->B) i)
                                              (ball(vec 0,&2)))`;
                     `(cp:num->real^3->B) i`]
                    HOMEOMORPHIC_IMP_INJECTIVE_MAP);
      MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^3,&2))`;
                     `subtopology topZ (IMAGE ((cm:num->real^3->B) i)
                                              (ball(vec 0,&2)))`;
                     `(cm:num->real^3->B) i`]
                    HOMEOMORPHIC_IMP_INJECTIVE_MAP)] THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i y. i IN J /\ y IN annulus (&1 / &2) (&2)
          ==> ((e:num->real^3->A) i y IN mfd_cut_spheres J e <=> norm y = &1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CCS_SPHERES_CHART THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i y. i IN J /\ y IN ball(vec 0,&2)
          ==> ((cp:num->real^3->B) i y IN mfd_cut_cores J cp cm <=> norm y <= &1) /\
              ((cm:num->real^3->B) i y IN mfd_cut_cores J cp cm <=> norm y <= &1)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CCS_CORES_CHART THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic_maps] o
    check (fun th -> fst(dest_const(fst(strip_comb(concl th)))) =
                     "homeomorphic_maps")) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(!x. x IN topspace topX DIFF mfd_cut_spheres J e
         ==> (ff:A->B) x IN topspace topZ DIFF mfd_cut_cores J cp cm /\
             (gg:B->A)(ff x) = x) /\
    (!z. z IN topspace topZ DIFF mfd_cut_cores J cp cm
         ==> gg z IN topspace topX DIFF mfd_cut_spheres J e /\ ff(gg z) = z)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_DIFF] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `(e:num->real^3->A) i y IN topspace topX DIFF mfd_cut_spheres J e`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN annulus (&1) (&2)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[IN_DIFF] THEN
      UNDISCH_TAC `(y:real^3) IN annulus (&1) (&2)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    MP_TAC(SPEC `y:real^3` CCS_INVERSION_ANNULUS) THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `x = inv(norm(y:real^3) pow 2) % y` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e:num->real^3->A) i x IN topspace topX DIFF mfd_cut_spheres J e`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(x:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN annulus (&1 / &2) (&1)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[IN_DIFF] THEN
      UNDISCH_TAC `(x:real^3) IN annulus (&1 / &2) (&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[]]]);;

(* Per-index chart facts and the disjointness of the caps.                  *)

(* Injectivity of the charts (kept apart: as rewrite rules these facts make  *)
(* ASM_SIMP_TAC hang).                                                      *)

let CCS_CUTCAP_INJ = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg.
        ccs_cutcap topX topZ J e cp cm ff gg
        ==> (!i y y'. i IN J /\ y IN annulus (&1 / &2) (&2) /\
                      y' IN annulus (&1 / &2) (&2) /\ e i y = e i y'
                      ==> y = y') /\
            (!i y y'. i IN J /\ y IN ball(vec 0,&2) /\ y' IN ball(vec 0,&2) /\
                      cp i y = cp i y' ==> y = y') /\
            (!i y y'. i IN J /\ y IN ball(vec 0,&2) /\ y' IN ball(vec 0,&2) /\
                      cm i y = cm i y' ==> y = y')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ccs_cutcap] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (annulus (&1 / &2) (&2):real^3->bool)`;
                   `subtopology topX (IMAGE ((e:num->real^3->A) i)
                                            (annulus (&1 / &2) (&2)))`;
                   `(e:num->real^3->A) i`]
                  HOMEOMORPHIC_IMP_INJECTIVE_MAP);
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^3,&2))`;
                   `subtopology topZ (IMAGE ((cp:num->real^3->B) i)
                                            (ball(vec 0,&2)))`;
                   `(cp:num->real^3->B) i`]
                  HOMEOMORPHIC_IMP_INJECTIVE_MAP);
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^3,&2))`;
                   `subtopology topZ (IMAGE ((cm:num->real^3->B) i)
                                            (ball(vec 0,&2)))`;
                   `(cm:num->real^3->B) i`]
                  HOMEOMORPHIC_IMP_INJECTIVE_MAP)] THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM_MESON_TAC[]);;

let CCS_CUTCAP_CHARTS = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg i.
        ccs_cutcap topX topZ J e cp cm ff gg /\ i IN J
        ==> open_in topX (IMAGE (e i) (annulus (&1 / &2) (&2))) /\
            homeomorphic_map
              (subtopology euclidean (annulus (&1 / &2) (&2)),
               subtopology topX (IMAGE (e i) (annulus (&1 / &2) (&2)))) (e i) /\
            open_in topZ (IMAGE (cp i) (ball(vec 0,&2))) /\
            homeomorphic_map
              (subtopology euclidean (ball(vec 0,&2)),
               subtopology topZ (IMAGE (cp i) (ball(vec 0,&2)))) (cp i) /\
            open_in topZ (IMAGE (cm i) (ball(vec 0,&2))) /\
            homeomorphic_map
              (subtopology euclidean (ball(vec 0,&2)),
               subtopology topZ (IMAGE (cm i) (ball(vec 0,&2)))) (cm i)`,
  SIMP_TAC[ccs_cutcap]);;

let CCS_CUTCAP_CAPS_DISJOINT = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg i j.
        ccs_cutcap topX topZ J e cp cm ff gg /\ i IN J /\ j IN J
        ==> DISJOINT (IMAGE (cp i) (ball(vec 0,&2))) (IMAGE (cm j) (ball(vec 0,&2))) /\
            (~(i = j)
             ==> DISJOINT (IMAGE (cp i) (ball(vec 0,&2)))
                          (IMAGE (cp j) (ball(vec 0,&2))) /\
                 DISJOINT (IMAGE (cm i) (ball(vec 0,&2)))
                          (IMAGE (cm j) (ball(vec 0,&2))) /\
                 DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                          (IMAGE (e j) (annulus (&1 / &2) (&2))))`,
  SIMP_TAC[ccs_cutcap]);;

(* ------------------------------------------------------------------------- *)
(* Components of the capped space Z.  Removing from a                        *)
(* connected set a set C covered by disjoint open sets, each of which stays *)
(* connected and nonempty after the removal, keeps it connected; hence a    *)
(* component of Z minus the cap cores is connected.                          *)
(* ------------------------------------------------------------------------- *)

let CCS_CHART_IMAGE_CONNECTED = prove
 (`!top (b:real^N->A) s t.
        homeomorphic_map (subtopology euclidean s,subtopology top (IMAGE b s)) b /\
        connected t /\ t SUBSET s
        ==> connected_in top (IMAGE b t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
  EXISTS_TAC `subtopology euclidean (s:real^N->bool)` THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
  EXISTS_TAC `IMAGE (b:real^N->A) s` THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP]);;

let CCS_CONNECTED_DIFF_CAPS = prove
 (`!top (W:A->bool) C os.
        connected_in top W /\ open_in top (W DIFF C) /\
        (!u. u IN os ==> open_in top u /\ u SUBSET W /\
                         connected_in top (u DIFF C) /\ ~(u DIFF C = {})) /\
        (!u u'. u IN os /\ u' IN os /\ ~(u = u') ==> DISJOINT u u') /\
        W INTER C SUBSET UNIONS os
        ==> connected_in top (W DIFF C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[CONNECTED_IN] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_IN_SUBSET_TOPSPACE) THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`e1:A->bool`; `e2:A->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. u IN os ==> ((u:A->bool) DIFF C SUBSET e1 /\ DISJOINT (u DIFF C) e2) \/
                    (u DIFF C SUBSET e2 /\ DISJOINT (u DIFF C) e1)`
  (LABEL_TAC "dich") THENL
   [X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:A->bool` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> is_const t &&
                                       fst(dest_const t) = "connected_in")) (concl th))) THEN
    ASM_REWRITE_TAC[CONNECTED_IN] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
                                            is_exists(dest_neg(concl th)))) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`e1:A->bool`; `e2:A->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(u:A->bool) DIFF C SUBSET W DIFF C` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(W:A->bool) DIFF C SUBSET e1 UNION e2`;
      `(e1:A->bool) INTER e2 INTER (W DIFF C) = {}`;
      `~((u:A->bool) DIFF C = {})`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u u'. u IN os /\ u' IN os /\ (u:A->bool) DIFF C SUBSET e1 /\
           u' DIFF C SUBSET e2 ==> DISJOINT u u'`
  (LABEL_TAC "uu") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `u:A->bool = u'` THENL
     [UNDISCH_TAC `u:A->bool = u'` THEN DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u':A->bool` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> is_const t &&
                                         fst(dest_const t) = "connected_in")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`(e1:A->bool) INTER e2 INTER (W DIFF C) = {}`;
        `(u':A->bool) DIFF C SUBSET e1`; `(u':A->bool) DIFF C SUBSET e2`;
        `(u':A->bool) SUBSET W`; `~((u':A->bool) DIFF C = {})`] THEN
      SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT"))
            (concl th) && is_forall(concl th) &&
        not (can (find_term (fun t -> t = `e1:A->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`(e1 INTER (W DIFF C)) UNION UNIONS {u | u IN os /\ (u:A->bool) DIFF C SUBSET e1}`;
    `(e2 INTER (W DIFF C)) UNION UNIONS {u | u IN os /\ (u:A->bool) DIFF C SUBSET e2}`]
   (REWRITE_RULE[NOT_EXISTS_THM] (CONJUNCT2 (GEN_REWRITE_RULE I [CONNECTED_IN]
      (ASSUME `connected_in top (W:A->bool)`))))) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_UNION THEN ASM_SIMP_TAC[OPEN_IN_INTER] THEN
    MATCH_MP_TAC OPEN_IN_UNIONS THEN SIMP_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC OPEN_IN_UNION THEN ASM_SIMP_TAC[OPEN_IN_INTER] THEN
    MATCH_MP_TAC OPEN_IN_UNIONS THEN SIMP_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNION; IN_INTER; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(x:A) IN C` THENL
     [SUBGOAL_THEN `?u:A->bool. u IN os /\ x IN u` STRIP_ASSUME_TAC THENL
       [MP_TAC(SPEC `x:A` (GEN_REWRITE_RULE I [SUBSET]
          (ASSUME `(W:A->bool) INTER C SUBSET UNIONS os`))) THEN
        ASM_REWRITE_TAC[IN_INTER; IN_UNIONS];
        ALL_TAC] THEN
      USE_THEN "dich" (MP_TAC o SPEC `u:A->bool`) THEN
      REWRITE_TAC[ASSUME `(u:A->bool) IN os`] THEN STRIP_TAC THENL
       [DISJ1_TAC THEN DISJ2_TAC THEN EXISTS_TAC `u:A->bool` THEN
        ASM_REWRITE_TAC[];
        DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `u:A->bool` THEN
        ASM_REWRITE_TAC[]];
      MP_TAC(SPEC `x:A` (GEN_REWRITE_RULE I [SUBSET]
        (ASSUME `(W:A->bool) DIFF C SUBSET e1 UNION e2`))) THEN
      ASM_REWRITE_TAC[IN_UNION; IN_DIFF] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_UNION; IN_UNIONS;
                IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN
    REWRITE_TAC[TAUT `~(p /\ q /\ r) <=> p /\ q ==> ~r`] THEN
    STRIP_TAC THENL
     [MP_TAC(ASSUME `(e1:A->bool) INTER e2 INTER (W DIFF C) = {}`) THEN
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[];
      MP_TAC(ASSUME `(e1:A->bool) INTER e2 INTER (W DIFF C) = {}`) THEN
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(t:A->bool) DIFF C SUBSET e2` THEN
      UNDISCH_TAC `(x:A) IN t` THEN UNDISCH_TAC `(x:A) IN W DIFF C` THEN
      SET_TAC[];
      MP_TAC(ASSUME `(e1:A->bool) INTER e2 INTER (W DIFF C) = {}`) THEN
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(t:A->bool) DIFF C SUBSET e1` THEN
      UNDISCH_TAC `(x:A) IN t` THEN UNDISCH_TAC `(x:A) IN W DIFF C` THEN
      SET_TAC[];
      REMOVE_THEN "uu" (MP_TAC o SPECL [`t:A->bool`; `t':A->bool`]) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let CCS_ANNULUS_CONNECTED = prove
 (`!r1 r2. connected (annulus r1 r2:real^3->bool)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `r1:real`; `r2:real`]
    (CONJUNCT1 CONNECTED_ANNULUS)) THEN
  REWRITE_TAC[DIMINDEX_3; VECTOR_SUB_RZERO; annulus] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* A chart image of a connected set lies inside a component or misses it.  *)

let CCS_COMPONENT_CHART = prove
 (`!top W (b:real^N->A) s y.
        W IN connected_components_of top /\
        homeomorphic_map (subtopology euclidean s,subtopology top (IMAGE b s)) b /\
        connected s /\ y IN s
        ==> (b y IN W <=> IMAGE b s SUBSET W) /\
            (~(b y IN W) ==> DISJOINT (IMAGE b s) W)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected_in top (IMAGE (b:real^N->A) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC CCS_CHART_IMAGE_CONNECTED THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    DISCH_TAC THEN REWRITE_TAC[DISJOINT] THEN
    MATCH_MP_TAC(SET_RULE `~((s:A->bool) SUBSET w) /\ (~(s INTER w = {}) ==> s SUBSET w)
                           ==> s INTER w = {}`) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* A component of Z minus the cap cores is connected.                      *)

let CCS_DIFF_CORES_CONNECTED = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W.
        ccs_cutcap topX topZ J e cp cm ff gg /\
        locally_connected_space topZ /\
        W IN connected_components_of topZ
        ==> connected_in topZ (W DIFF mfd_cut_cores J cp cm)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i y. i IN J /\ y IN ball(vec 0,&2)
          ==> ((cp:num->real^3->B) i y IN mfd_cut_cores J cp cm <=> norm y <= &1) /\
              ((cm:num->real^3->B) i y IN mfd_cut_cores J cp cm <=> norm y <= &1)`
  (LABEL_TAC "core") THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CCS_CUTCAP_FACTS) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN J
        ==> open_in topZ (IMAGE ((cp:num->real^3->B) i) (ball(vec 0,&2))) /\
            homeomorphic_map
              (subtopology euclidean (ball(vec 0,&2)),
               subtopology topZ (IMAGE (cp i) (ball(vec 0,&2)))) (cp i) /\
            open_in topZ (IMAGE ((cm:num->real^3->B) i) (ball(vec 0,&2))) /\
            homeomorphic_map
              (subtopology euclidean (ball(vec 0,&2)),
               subtopology topZ (IMAGE (cm i) (ball(vec 0,&2)))) (cm i)`
  (LABEL_TAC "chart") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `i:num`] CCS_CUTCAP_CHARTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN J
        ==> IMAGE ((cp:num->real^3->B) i) (ball(vec 0,&2)) DIFF
              mfd_cut_cores J cp cm = IMAGE (cp i) (annulus (&1) (&2)) /\
            IMAGE ((cm:num->real^3->B) i) (ball(vec 0,&2)) DIFF
              mfd_cut_cores J cp cm = IMAGE (cm i) (annulus (&1) (&2))`
  (LABEL_TAC "diff") THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
    (REWRITE_TAC[EXTENSION; IN_DIFF; IN_IMAGE] THEN X_GEN_TAC `z:B` THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((z:B) IN mfd_cut_cores J cp cm)` THEN ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN ball(vec 0,&2)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; IN_BALL_0] THEN REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^3) IN ball(vec 0,&2)` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN annulus (&1) (&2)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM; IN_BALL_0] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[] THEN UNDISCH_TAC `(y:real^3) IN annulus (&1) (&2)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &2) % basis 1 IN annulus (&1) (&2):real^3->bool`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `annulus (&1) (&2) SUBSET ball(vec 0:real^3,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `vec 0 IN ball(vec 0:real^3,&2) /\ connected(ball(vec 0:real^3,&2))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONNECTED_BALL; CENTRE_IN_BALL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN J
        ==> (!y. y IN ball(vec 0,&2)
                 ==> ((cp:num->real^3->B) i y IN W <=>
                      IMAGE (cp i) (ball(vec 0,&2)) SUBSET W)) /\
            (!y. y IN ball(vec 0,&2)
                 ==> ((cm:num->real^3->B) i y IN W <=>
                      IMAGE (cm i) (ball(vec 0,&2)) SUBSET W))`
  (LABEL_TAC "inW") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "chart" (MP_TAC o C MATCH_MP (ASSUME `(i:num) IN J`)) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THENL
     [MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`; `(cp:num->real^3->B) i`;
                     `ball(vec 0:real^3,&2)`; `y:real^3`] CCS_COMPONENT_CHART);
      MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`; `(cm:num->real^3->B) i`;
                     `ball(vec 0:real^3,&2)`; `y:real^3`] CCS_COMPONENT_CHART)] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CCS_CONNECTED_DIFF_CAPS THEN
  EXISTS_TAC
   `{IMAGE ((cp:num->real^3->B) i) (ball(vec 0,&2)) | i | i IN J /\ cp i (vec 0) IN W}
    UNION
    {IMAGE ((cm:num->real^3->B) i) (ball(vec 0,&2)) | i | i IN J /\ cm i (vec 0) IN W}`
  THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[CONNECTED_IN_CONNECTED_COMPONENTS_OF];
    SUBGOAL_THEN
     `W DIFF mfd_cut_cores J cp cm =
      W INTER (topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`]
                    CONNECTED_COMPONENTS_OF_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `ccs_cutcap topX topZ J (e:num->real^3->A) (cp:num->real^3->B)
                                cm ff gg` THEN
        SIMP_TAC[ccs_cutcap]]];
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN GEN_TAC THEN
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "chart" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(i:num) IN J`)) THEN
    USE_THEN "diff" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(i:num) IN J`)) THEN
    USE_THEN "inW" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(i:num) IN J`)) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST
     [MATCH_MP_TAC CCS_CHART_IMAGE_CONNECTED THEN
      EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
      ASM_REWRITE_TAC[CCS_ANNULUS_CONNECTED] THEN NO_TAC;
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `(&3 / &2) % basis 1:real^3` THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      ASM_MESON_TAC[]];
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (DISJ_CASES_THEN (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2
        (DISJ_CASES_THEN (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `i:num`; `j:num`] CCS_CUTCAP_CAPS_DISJOINT) THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `j:num`; `i:num`] CCS_CUTCAP_CAPS_DISJOINT) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((u:B->bool) = u')` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[DISJOINT_SYM];
    REWRITE_TAC[SUBSET; IN_INTER; IN_MFD_CUT_CORES; IN_UNIONS; IN_UNION;
                IN_ELIM_THM] THEN
    X_GEN_TAC `z:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `i:num`
      (X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
    SUBGOAL_THEN `(x:real^3) IN ball(vec 0,&2)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN UNDISCH_TAC `norm(x:real^3) <= &1` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "inW" (MP_TAC o C MATCH_MP (ASSUME `(i:num) IN J`)) THEN
    DISCH_THEN(CONJUNCTS_THEN (fun th -> MP_TAC(SPEC `x:real^3` th) THEN
                                          MP_TAC(SPEC `vec 0:real^3` th))) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THENL
     [EXISTS_TAC `IMAGE ((cp:num->real^3->B) i) (ball(vec 0,&2))` THEN
      CONJ_TAC THENL
       [DISJ1_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
        ASM_REWRITE_TAC[]];
      EXISTS_TAC `IMAGE ((cm:num->real^3->B) i) (ball(vec 0,&2))` THEN
      CONJ_TAC THENL
       [DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
        ASM_REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* The piece Q of X belonging to a component W of Z, the far                 *)
(* sides of its cut spheres, and their separation properties.              *)
(* ------------------------------------------------------------------------- *)

(* Q: the points of X off the cut spheres that ff sends into W.            *)

let ccs_piece = new_definition
 `ccs_piece (topX:A topology) (J:num->bool) (e:num->real^3->A) (ff:A->B)
            (W:B->bool) =
    {x | x IN topspace topX DIFF mfd_cut_spheres J e /\ ff x IN W}`;;

(* The far point of neck i (on the side away from W) and its side.          *)

let ccs_far = new_definition
 `ccs_far (e:num->real^3->A) (cp:num->real^3->B) (W:B->bool) i =
    if cp i (vec 0) IN W then e i (&3 / &4 % basis 1) else e i (&4 / &3 % basis 1)`;;

let ccs_branch = new_definition
 `ccs_branch (topX:A topology) (e:num->real^3->A) (cp:num->real^3->B)
             (W:B->bool) i =
    connected_component_of
      (subtopology topX (topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))))
      (ccs_far e cp W i)`;;

(* Chart points of a cap lie in W exactly when its centre does.             *)

let CCS_CAP_IN_COMPONENT = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W i y.
        ccs_cutcap topX topZ J e cp cm ff gg /\
        W IN connected_components_of topZ /\ i IN J /\ y IN ball(vec 0,&2)
        ==> (cp i y IN W <=> cp i (vec 0) IN W) /\
            (cm i y IN W <=> cm i (vec 0) IN W)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `i:num`] CCS_CUTCAP_CHARTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `vec 0 IN ball(vec 0:real^3,&2) /\ connected(ball(vec 0:real^3,&2))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONNECTED_BALL; CENTRE_IN_BALL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`; `(cp:num->real^3->B) i`;
                   `ball(vec 0:real^3,&2)`; `y:real^3`] CCS_COMPONENT_CHART) THEN
    MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`; `(cp:num->real^3->B) i`;
                   `ball(vec 0:real^3,&2)`; `vec 0:real^3`] CCS_COMPONENT_CHART);
    MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`; `(cm:num->real^3->B) i`;
                   `ball(vec 0:real^3,&2)`; `y:real^3`] CCS_COMPONENT_CHART) THEN
    MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`; `(cm:num->real^3->B) i`;
                   `ball(vec 0:real^3,&2)`; `vec 0:real^3`] CCS_COMPONENT_CHART)] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let CCS_PIECE_FACTS = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W.
        ccs_cutcap topX topZ J e cp cm ff gg /\
        locally_connected_space topZ /\
        W IN connected_components_of topZ
        ==> open_in topX (ccs_piece topX J e ff W) /\
            connected_in topX (ccs_piece topX J e ff W) /\
            ccs_piece topX J e ff W SUBSET
            topspace topX DIFF mfd_cut_spheres J e /\
            (!i y. i IN J /\ y IN annulus (&1) (&2)
                   ==> (e i y IN ccs_piece topX J e ff W <=> cp i (vec 0) IN W)) /\
            (!i y. i IN J /\ y IN annulus (&1 / &2) (&1)
                   ==> (e i y IN ccs_piece topX J e ff W <=> cm i (vec 0) IN W))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CCS_CUTCAP_FACTS) THEN
  SUBGOAL_THEN
   `open_in topX (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)) /\
    open_in topZ (topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm) /\
    homeomorphic_maps
      (subtopology topX (topspace topX DIFF mfd_cut_spheres J e),
       subtopology topZ (topspace topZ DIFF mfd_cut_cores J cp cm)) (ff:A->B,gg) /\
    (!i x. i IN J /\ x IN annulus (&1) (&2) ==> ff(e i x) = cp i x) /\
    (!i x. i IN J /\ x IN annulus (&1 / &2) (&1)
           ==> ff(e i x) = cm i (inv(norm x pow 2) % x))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ccs_cutcap topX topZ J (e:num->real^3->A) (cp:num->real^3->B)
                            cm ff gg` THEN SIMP_TAC[ccs_cutcap];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps] o
    check (fun th -> fst(dest_const(fst(strip_comb(concl th)))) =
                     "homeomorphic_maps")) THEN
  REWRITE_TAC[ccs_piece] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
    EXISTS_TAC `topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ff:A->B`;
                   `subtopology topX (topspace topX DIFF mfd_cut_spheres J
                                        (e:num->real^3->A))`;
                   `topZ:B topology`; `W:B->bool`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
        EXISTS_TAC `topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER;
                  IN_DIFF] THEN
      MESON_TAC[]];
    SUBGOAL_THEN
     `{x | x IN topspace topX DIFF mfd_cut_spheres J e /\ (ff:A->B) x IN W} =
      IMAGE (gg:B->A) (W DIFF mfd_cut_cores J (cp:num->real^3->B) cm)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_DIFF] THEN
      X_GEN_TAC `x:A` THEN EQ_TAC THENL
       [STRIP_TAC THEN EXISTS_TAC `(ff:A->B) x` THEN
        ASM_MESON_TAC[IN_DIFF];
        DISCH_THEN(X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(z:B) IN topspace topZ DIFF mfd_cut_cores J cp cm`
        ASSUME_TAC THENL
         [ASM_REWRITE_TAC[IN_DIFF] THEN
          MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`]
                        CONNECTED_COMPONENTS_OF_SUBSET) THEN
          ASM SET_TAC[];
          ASM_MESON_TAC[IN_DIFF]]];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology topZ (topspace topZ DIFF mfd_cut_cores J
                                    (cp:num->real^3->B) cm)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
      EXISTS_TAC `topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CCS_DIFF_CORES_CONNECTED THEN ASM_MESON_TAC[];
        MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`]
                      CONNECTED_COMPONENTS_OF_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]]];
    SET_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
    SUBGOAL_THEN `(y:real^3) IN annulus (&1 / &2) (&2) /\ y IN ball(vec 0,&2) /\
                  ~(norm y = &1)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN annulus (&1) (&2)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; IN_BALL_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`; `y:real^3`]
                  CCS_CAP_IN_COMPONENT) THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
    SUBGOAL_THEN `(y:real^3) IN annulus (&1 / &2) (&2) /\ ~(norm y = &1) /\
                  ~(y = vec 0)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN annulus (&1 / &2) (&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; GSYM NORM_POS_LT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm(y:real^3) pow 2) % y IN ball(vec 0,&2)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[IN_BALL_0; CCS_INVERSION] THEN
      MP_TAC(SPECL [`&1 / &2`; `norm(y:real^3)`] REAL_LT_INV2) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN annulus (&1 / &2) (&1)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`;
                   `inv(norm(y:real^3) pow 2) % y`] CCS_CAP_IN_COMPONENT) THEN
    ASM_SIMP_TAC[]]);;

(* The closure of Q adds only cut spheres of necks adjacent to W.           *)

let CCS_PIECE_CLOSURE = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W.
        ccs_cutcap topX topZ J e cp cm ff gg /\
        locally_connected_space topZ /\
        W IN connected_components_of topZ
        ==> topX closure_of (ccs_piece topX J e ff W) SUBSET
            ccs_piece topX J e ff W UNION
            UNIONS {IMAGE (e i) (sphere(vec 0,&1)) | i |
                    i IN J /\ (cp i (vec 0) IN W \/ cm i (vec 0) IN W)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`] CCS_PIECE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CCS_CUTCAP_FACTS) THEN
  DISCH_THEN(fun th -> LABEL_TAC "sph" (CONJUNCT1(CONJUNCT2(CONJUNCT2 th))) THEN
                       LABEL_TAC "ffx" (CONJUNCT1(funpow 4 CONJUNCT2 th))) THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_CLOSURE_OF]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nb")) THEN
  ASM_CASES_TAC `(x:A) IN mfd_cut_spheres J e` THENL
   [DISJ2_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_MFD_CUT_SPHERES]) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN EXISTS_TAC `u:real^3` THEN
      ASM_REWRITE_TAC[]] THEN
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "nb" (MP_TAC o SPEC
      `IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2))`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `u:real^3` THEN
        ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                       `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                       `ff:A->B`; `gg:B->A`; `j:num`] CCS_CUTCAP_CHARTS) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `~(norm(y:real^3) = &1)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(z:A) IN mfd_cut_spheres J e` MP_TAC THENL
       [USE_THEN "sph" (MP_TAC o SPECL [`j:num`; `y:real^3`]) THEN
        REWRITE_TAC[ASSUME `(j:num) IN J`;
                    ASSUME `(y:real^3) IN annulus (&1 / &2) (&2)`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(z:A) IN ccs_piece topX J (e:num->real^3->A) (ff:A->B) W` THEN
      UNDISCH_TAC `ccs_piece topX J e (ff:A->B) W SUBSET
                   topspace topX DIFF mfd_cut_spheres J e` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `&1 < norm(y:real^3)` THENL
     [DISJ1_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `y:real^3`] o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> t = `cp:num->real^3->B`)) (concl th) &&
                         can (find_term (fun t -> is_const t &&
                              fst(dest_const t) = "ccs_piece")) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN annulus (&1 / &2) (&2)` THEN
        UNDISCH_TAC `&1 < norm(y:real^3)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `(z:A) IN ccs_piece topX J (e:num->real^3->A) (ff:A->B) W` THEN
        ASM_REWRITE_TAC[]];
      DISJ2_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `y:real^3`] o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> t = `cm:num->real^3->B`)) (concl th) &&
                         can (find_term (fun t -> is_const t &&
                              fst(dest_const t) = "ccs_piece")) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN annulus (&1 / &2) (&2)` THEN
        UNDISCH_TAC `~(norm(y:real^3) = &1)` THEN
        UNDISCH_TAC `~(&1 < norm(y:real^3))` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `(z:A) IN ccs_piece topX J (e:num->real^3->A) (ff:A->B) W` THEN
        ASM_REWRITE_TAC[]]];
    DISJ1_TAC THEN REWRITE_TAC[ccs_piece; IN_ELIM_THM; IN_DIFF] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    REMOVE_THEN "nb" (MP_TAC o SPEC
      `{x' | x' IN topspace topX DIFF mfd_cut_spheres J e /\
             (ff:A->B) x' IN topspace topZ DIFF W}`) THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "ffx" (MP_TAC o SPEC `x:A`) THEN
        REWRITE_TAC[IN_DIFF; ASSUME `(x:A) IN topspace topX`;
                    ASSUME `~((x:A) IN mfd_cut_spheres J e)`] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `open_in topX (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)) /\
        homeomorphic_maps
          (subtopology topX (topspace topX DIFF mfd_cut_spheres J e),
           subtopology topZ (topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm))
          (ff:A->B,gg)`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `ccs_cutcap topX topZ J (e:num->real^3->A) (cp:num->real^3->B)
                                cm ff gg` THEN SIMP_TAC[ccs_cutcap];
        ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
      EXISTS_TAC `topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`ff:A->B`;
                     `subtopology topX (topspace topX DIFF mfd_cut_spheres J
                                          (e:num->real^3->A))`;
                     `topZ:B topology`; `topspace topZ DIFF W:B->bool`]
                    OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
          EXISTS_TAC `topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm` THEN
          FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
          SIMP_TAC[];
          MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
          MATCH_MP_TAC CLOSED_IN_CONNECTED_COMPONENTS_OF THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER;
                    IN_DIFF] THEN
        MESON_TAC[]];
      REWRITE_TAC[NOT_EXISTS_THM; ccs_piece; IN_ELIM_THM; IN_DIFF] THEN
      MESON_TAC[]]]);;

(* Components of the complement of a closed set in a locally connected     *)
(* space: open, connected, with closure inside the component plus the set, *)
(* and maximal among connected sets off the closed set.                    *)

let CCS_SIDE_FACTS = prove
 (`!top S (p:A).
        locally_connected_space top /\ closed_in top S /\
        p IN topspace top DIFF S
        ==> open_in top
              (connected_component_of (subtopology top (topspace top DIFF S)) p) /\
            connected_in top
              (connected_component_of (subtopology top (topspace top DIFF S)) p) /\
            p IN connected_component_of (subtopology top (topspace top DIFF S)) p /\
            connected_component_of (subtopology top (topspace top DIFF S)) p SUBSET
            topspace top DIFF S /\
            top closure_of
              (connected_component_of (subtopology top (topspace top DIFF S)) p)
            SUBSET
            connected_component_of (subtopology top (topspace top DIFF S)) p UNION S /\
            (!C x. connected_in top C /\ C SUBSET topspace top DIFF S /\
                   x IN C /\
                   x IN connected_component_of (subtopology top (topspace top DIFF S)) p
                   ==> C SUBSET
                       connected_component_of (subtopology top (topspace top DIFF S)) p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `O = topspace top DIFF (S:A->bool)` THEN
  SUBGOAL_THEN `open_in top (O:A->bool) /\ O SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology top O) = O:A->bool` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `connected_component_of (subtopology top O) (p:A) SUBSET O`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (O:A->bool)`; `p:A`]
                  CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [LOCALLY_CONNECTED_SPACE_OPEN_CONNECTED_COMPONENTS]) THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `O:A->bool` THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF];
    MP_TAC(ISPECL [`subtopology top (O:A->bool)`; `p:A`]
                  CONNECTED_IN_CONNECTED_COMPONENT_OF) THEN
    SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY];
    REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL];
    MP_TAC(ISPECL [`subtopology top (O:A->bool)`; `p:A`]
                  CLOSED_IN_CONNECTED_COMPONENT_OF) THEN
    REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`;
                   `connected_component_of (subtopology top O) (p:A)`;
                   `t:A->bool`] CLOSURE_OF_MINIMAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`;
                   `connected_component_of (subtopology top O) (p:A)`]
                  CLOSURE_OF_SUBSET_TOPSPACE) THEN
    UNDISCH_TAC `topspace top DIFF S = (O:A->bool)` THEN
    UNDISCH_TAC `connected_component_of (subtopology top O) (p:A) = t INTER O` THEN
    SET_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `connected_component_of (subtopology top O) (p:A) =
      connected_component_of (subtopology top O) x`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`subtopology top (O:A->bool)`; `p:A`; `x:A`]
                    CONNECTED_COMPONENT_OF_EQUIV) THEN
      UNDISCH_TAC `(x:A) IN connected_component_of (subtopology top O) p` THEN
      REWRITE_TAC[IN] THEN MESON_TAC[];
      MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
      ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY]]]);;

(* Facts about one neck chart.                                              *)

let CCS_NECK_FACTS = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg i.
        ccs_cutcap topX topZ J e cp cm ff gg /\ hausdorff_space topX /\ i IN J
        ==> closed_in topX (IMAGE (e i) (sphere(vec 0,&1))) /\
            open_in topX (IMAGE (e i) (annulus (&1 / &2) (&2))) /\
            connected_in topX (IMAGE (e i) (annulus (&1 / &2) (&2))) /\
            connected_in topX (IMAGE (e i) (annulus (&1) (&2))) /\
            connected_in topX (IMAGE (e i) (annulus (&1 / &2) (&1))) /\
            IMAGE (e i) (annulus (&1) (&2)) SUBSET
            topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1)) /\
            IMAGE (e i) (annulus (&1 / &2) (&1)) SUBSET
            topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1)) /\
            IMAGE (e i) (sphere(vec 0,&1)) SUBSET
            IMAGE (e i) (annulus (&1 / &2) (&2)) /\
            IMAGE (e i) (annulus (&1) (&2)) SUBSET
            IMAGE (e i) (annulus (&1 / &2) (&2)) /\
            IMAGE (e i) (annulus (&1 / &2) (&1)) SUBSET
            IMAGE (e i) (annulus (&1 / &2) (&2)) /\
            &3 / &4 % basis 1 IN (annulus (&1 / &2) (&1):real^3->bool) /\
            &4 / &3 % basis 1 IN (annulus (&1) (&2):real^3->bool)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `i:num`] CCS_CUTCAP_CHARTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP CCS_CUTCAP_INJ) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[ASSUME `(i:num) IN J`] THEN
  DISCH_THEN(LABEL_TAC "inj") THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP CCS_CUTCAP_FACTS) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[ASSUME `(i:num) IN J`] THEN
  DISCH_THEN(LABEL_TAC "top") THEN
  SUBGOAL_THEN
   `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2) /\
    (annulus (&1) (&2):real^3->bool) SUBSET annulus (&1 / &2) (&2) /\
    (annulus (&1 / &2) (&1):real^3->bool) SUBSET annulus (&1 / &2) (&2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (annulus (&1 / &2) (&2):real^3->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2))` THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CCS_CHART_IMAGE_CONNECTED THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_REWRITE_TAC[CCS_ANNULUS_CONNECTED; SUBSET_REFL];
    MATCH_MP_TAC CCS_CHART_IMAGE_CONNECTED THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_REWRITE_TAC[CCS_ANNULUS_CONNECTED];
    MATCH_MP_TAC CCS_CHART_IMAGE_CONNECTED THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_REWRITE_TAC[CCS_ANNULUS_CONNECTED];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_IMAGE; NOT_EXISTS_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "top" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `u:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN STRIP_TAC THEN
    SUBGOAL_THEN `y:real^3 = u` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(u:real^3) IN annulus (&1) (&2)` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_IMAGE; NOT_EXISTS_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "top" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `u:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN STRIP_TAC THEN
    SUBGOAL_THEN `y:real^3 = u` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(u:real^3) IN annulus (&1 / &2) (&1)` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC]);;

let CCS_NECK_OTHER = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg i j.
        ccs_cutcap topX topZ J e cp cm ff gg /\ i IN J /\ j IN J /\ ~(i = j)
        ==> IMAGE (e i) (annulus (&1 / &2) (&2)) SUBSET
            topspace topX DIFF IMAGE (e j) (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `i:num`; `j:num`] CCS_CUTCAP_CAPS_DISJOINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP CCS_CUTCAP_FACTS) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN REWRITE_TAC[ASSUME `(i:num) IN J`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)) SUBSET
                IMAGE (e j) (annulus (&1 / &2) (&2))` MP_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)))
                        (IMAGE (e j) (annulus (&1 / &2) (&2)))` THEN
  UNDISCH_TAC `!y. y IN annulus (&1 / &2) (&2)
                   ==> (e:num->real^3->A) i y IN topspace topX` THEN
  REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; FORALL_IN_IMAGE; IN_INTER; IN_DIFF;
              NOT_IN_EMPTY; IN_IMAGE] THEN
  MESON_TAC[]);;

let CCS_SPHERE_SUBSET_SPHERES = prove
 (`!J (e:num->real^3->A) i.
        i IN J ==> IMAGE (e i) (sphere(vec 0,&1)) SUBSET mfd_cut_spheres J e`,
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_MFD_CUT_SPHERES; IN_SPHERE_0] THEN
  MESON_TAC[]);;

(* Every neck sphere separates: W cannot contain both caps of a neck.       *)

let CCS_NOT_BOTH_CAPS = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W i.
        ccs_cutcap topX topZ J e cp cm ff gg /\ hausdorff_space topX /\
        locally_connected_space topZ /\ W IN connected_components_of topZ /\
        (!i. i IN J
             ==> ~connected_component_of
                   (subtopology topX
                      (topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))))
                   (e i (&3 / &4 % basis 1)) (e i (&4 / &3 % basis 1))) /\
        i IN J
        ==> ~(cp i (vec 0) IN W /\ cm i (vec 0) IN W)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`] CCS_PIECE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `i:num`] CCS_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(e:num->real^3->A) i (&3 / &4 % basis 1) IN ccs_piece topX J e (ff:A->B) W /\
    e i (&4 / &3 % basis 1) IN ccs_piece topX J e ff W`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `&3 / &4 % basis 1:real^3`] o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> t = `cm:num->real^3->B`)) (concl th) &&
                         can (find_term (fun t -> is_const t &&
                              fst(dest_const t) = "ccs_piece")) (concl th)));
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `&4 / &3 % basis 1:real^3`] o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> t = `cp:num->real^3->B`)) (concl th) &&
                         can (find_term (fun t -> is_const t &&
                              fst(dest_const t) = "ccs_piece")) (concl th)))] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> is_const t &&
                          fst(dest_const t) = "connected_component_of")) (concl th))) THEN
  REWRITE_TAC[ASSUME `(i:num) IN J`] THEN
  GEN_REWRITE_TAC I [GSYM IN] THEN
  MATCH_MP_TAC(SPEC `ccs_piece topX J (e:num->real^3->A) (ff:A->B) W`
    (SET_RULE `!s (x:A) t. x IN s /\ s SUBSET t ==> x IN t`)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
  MP_TAC(ISPECL [`J:num->bool`; `e:num->real^3->A`; `i:num`]
                CCS_SPHERE_SUBSET_SPHERES) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ccs_piece topX J (e:num->real^3->A) (ff:A->B) W SUBSET
               topspace topX DIFF mfd_cut_spheres J e` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The far sides (branches) of the necks adjacent to W.                      *)
(* ------------------------------------------------------------------------- *)

let CCS_BRANCH_FACTS = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W i.
        ccs_cutcap topX topZ J e cp cm ff gg /\ hausdorff_space topX /\
        locally_connected_space topX /\ locally_connected_space topZ /\
        W IN connected_components_of topZ /\
        (!i. i IN J
             ==> ~connected_component_of
                   (subtopology topX
                      (topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))))
                   (e i (&3 / &4 % basis 1)) (e i (&4 / &3 % basis 1))) /\
        i IN J /\ (cp i (vec 0) IN W \/ cm i (vec 0) IN W)
        ==> open_in topX (ccs_branch topX e cp W i) /\
            connected_in topX (ccs_branch topX e cp W i) /\
            ccs_far e cp W i IN ccs_branch topX e cp W i /\
            ccs_branch topX e cp W i SUBSET
            topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1)) /\
            topX closure_of (ccs_branch topX e cp W i) SUBSET
            ccs_branch topX e cp W i UNION IMAGE (e i) (sphere(vec 0,&1)) /\
            (!C x. connected_in topX C /\
                   C SUBSET topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1)) /\
                   x IN C /\ x IN ccs_branch topX e cp W i
                   ==> C SUBSET ccs_branch topX e cp W i) /\
            DISJOINT (ccs_piece topX J e ff W) (ccs_branch topX e cp W i) /\
            (!y. y IN annulus (&1 / &2) (&2) /\ ~(norm y = &1)
                 ==> (e i y IN ccs_branch topX e cp W i <=>
                      ~(e i y IN ccs_piece topX J e ff W)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`] CCS_PIECE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `i:num`] CCS_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`] CCS_NOT_BOTH_CAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ccs_piece topX J (e:num->real^3->A) (ff:A->B) W SUBSET
    topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`J:num->bool`; `e:num->real^3->A`; `i:num`]
                  CCS_SPHERE_SUBSET_SPHERES) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ccs_piece topX J (e:num->real^3->A) (ff:A->B) W SUBSET
                 topspace topX DIFF mfd_cut_spheres J e` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN annulus (&1) (&2)
        ==> ((e:num->real^3->A) i y IN ccs_piece topX J e (ff:A->B) W <=>
             (cp:num->real^3->B) i (vec 0) IN W)`
  (LABEL_TAC "plus") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `y:real^3`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `cp:num->real^3->B`)) (concl th) &&
                       can (find_term (fun t -> is_const t &&
                            fst(dest_const t) = "ccs_piece")) (concl th))) THEN
    REWRITE_TAC[ASSUME `(i:num) IN J`; ASSUME `(y:real^3) IN annulus (&1) (&2)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN annulus (&1 / &2) (&1)
        ==> ((e:num->real^3->A) i y IN ccs_piece topX J e (ff:A->B) W <=>
             (cm:num->real^3->B) i (vec 0) IN W)`
  (LABEL_TAC "minus") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `y:real^3`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `cm:num->real^3->B`)) (concl th) &&
                       can (find_term (fun t -> is_const t &&
                            fst(dest_const t) = "ccs_piece")) (concl th))) THEN
    REWRITE_TAC[ASSUME `(i:num) IN J`; ASSUME `(y:real^3) IN annulus (&1 / &2) (&1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ccs_far (e:num->real^3->A) (cp:num->real^3->B) W i IN
    topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[ccs_far] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC(SPEC `IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&1))`
        (SET_RULE `!s (x:A) t. x IN s /\ s SUBSET t ==> x IN t`));
      MATCH_MP_TAC(SPEC `IMAGE ((e:num->real^3->A) i) (annulus (&1) (&2))`
        (SET_RULE `!s (x:A) t. x IN s /\ s SUBSET t ==> x IN t`))] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))`;
                 `ccs_far (e:num->real^3->A) (cp:num->real^3->B) W i`]
                CCS_SIDE_FACTS) THEN
  ASM_REWRITE_TAC[GSYM ccs_branch] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!C x. connected_in topX C /\
          C SUBSET topspace topX DIFF IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) /\
          x IN C /\ x IN ccs_branch topX e (cp:num->real^3->B) W i
          ==> C SUBSET ccs_branch topX e cp W i`
  (LABEL_TAC "max") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (ccs_piece topX J (e:num->real^3->A) (ff:A->B) W)
             (ccs_branch topX e (cp:num->real^3->B) W i)`
  ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `ccs_piece topX J (e:num->real^3->A) (ff:A->B) W SUBSET
      ccs_branch topX e (cp:num->real^3->B) W i`
    ASSUME_TAC THENL
     [USE_THEN "max" MATCH_MP_TAC THEN EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> is_const t &&
                            fst(dest_const t) = "connected_component_of")) (concl th))) THEN
    REWRITE_TAC[ASSUME `(i:num) IN J`] THEN
    ASM_CASES_TAC `(cp:num->real^3->B) i (vec 0) IN W` THENL
     [SUBGOAL_THEN
       `(e:num->real^3->A) i (&4 / &3 % basis 1) IN
        ccs_branch topX e (cp:num->real^3->B) W i`
      MP_TAC THENL
       [MATCH_MP_TAC(SPEC `ccs_piece topX J (e:num->real^3->A) (ff:A->B) W`
          (SET_RULE `!s (x:A) t. x IN s /\ s SUBSET t ==> x IN t`)) THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "plus" (MP_TAC o SPEC `&4 / &3 % basis 1:real^3`) THEN
        REWRITE_TAC[ASSUME `&4 / &3 % basis 1 IN (annulus (&1) (&2):real^3->bool)`] THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[ccs_branch; ccs_far] THEN REWRITE_TAC[IN]];
      SUBGOAL_THEN `(cm:num->real^3->B) i (vec 0) IN W` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `(e:num->real^3->A) i (&3 / &4 % basis 1) IN
        ccs_branch topX e (cp:num->real^3->B) W i`
      MP_TAC THENL
       [MATCH_MP_TAC(SPEC `ccs_piece topX J (e:num->real^3->A) (ff:A->B) W`
          (SET_RULE `!s (x:A) t. x IN s /\ s SUBSET t ==> x IN t`)) THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "minus" (MP_TAC o SPEC `&3 / &4 % basis 1:real^3`) THEN
        REWRITE_TAC[ASSUME `&3 / &4 % basis 1 IN (annulus (&1 / &2) (&1):real^3->bool)`] THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[ccs_branch; ccs_far] THEN REWRITE_TAC[IN] THEN
        MESON_TAC[CONNECTED_COMPONENT_OF_SYM]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "max" MATCH_MP_TAC THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `&1 < norm(y:real^3)` THENL
   [SUBGOAL_THEN `(y:real^3) IN annulus (&1) (&2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN annulus (&1 / &2) (&2)` THEN
      UNDISCH_TAC `&1 < norm(y:real^3)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "plus" (MP_TAC o SPEC `y:real^3`) THEN
    REWRITE_TAC[ASSUME `(y:real^3) IN annulus (&1) (&2)`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `(cp:num->real^3->B) i (vec 0) IN W` THENL
     [UNDISCH_TAC `DISJOINT (ccs_piece topX J (e:num->real^3->A) (ff:A->B) W)
                            (ccs_branch topX e (cp:num->real^3->B) W i)` THEN
      ASM SET_TAC[];
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SPEC `IMAGE ((e:num->real^3->A) i) (annulus (&1) (&2))`
        (SET_RULE `!s (x:A) t. x IN s /\ s SUBSET t ==> x IN t`)) THEN
      CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "max" MATCH_MP_TAC THEN
      EXISTS_TAC `(e:num->real^3->A) i (&4 / &3 % basis 1)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC(REWRITE_RULE[ccs_far;
          ASSUME `~((cp:num->real^3->B) i (vec 0) IN W)`]
          (ASSUME `ccs_far (e:num->real^3->A) (cp:num->real^3->B) W i IN
                   ccs_branch topX e cp W i`))]];
    SUBGOAL_THEN `(y:real^3) IN annulus (&1 / &2) (&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN annulus (&1 / &2) (&2)` THEN
      UNDISCH_TAC `~(&1 < norm(y:real^3))` THEN
      UNDISCH_TAC `~(norm(y:real^3) = &1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "minus" (MP_TAC o SPEC `y:real^3`) THEN
    REWRITE_TAC[ASSUME `(y:real^3) IN annulus (&1 / &2) (&1)`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `(cp:num->real^3->B) i (vec 0) IN W` THENL
     [SUBGOAL_THEN `~((cm:num->real^3->B) i (vec 0) IN W)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SPEC `IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&1))`
        (SET_RULE `!s (x:A) t. x IN s /\ s SUBSET t ==> x IN t`)) THEN
      CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "max" MATCH_MP_TAC THEN
      EXISTS_TAC `(e:num->real^3->A) i (&3 / &4 % basis 1)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC(REWRITE_RULE[ccs_far;
          ASSUME `(cp:num->real^3->B) i (vec 0) IN W`]
          (ASSUME `ccs_far (e:num->real^3->A) (cp:num->real^3->B) W i IN
                   ccs_branch topX e cp W i`))];
      SUBGOAL_THEN `(cm:num->real^3->B) i (vec 0) IN W` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `DISJOINT (ccs_piece topX J (e:num->real^3->A) (ff:A->B) W)
                            (ccs_branch topX e (cp:num->real^3->B) W i)` THEN
      ASM SET_TAC[]]]);;

(* Different necks adjacent to W: the collar of one misses the branch of   *)
(* the other, and the branches are disjoint.                                *)

let CCS_BRANCHES_DISJOINT = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W i j.
        ccs_cutcap topX topZ J e cp cm ff gg /\ hausdorff_space topX /\
        locally_connected_space topX /\ locally_connected_space topZ /\
        W IN connected_components_of topZ /\
        (!i. i IN J
             ==> ~connected_component_of
                   (subtopology topX
                      (topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))))
                   (e i (&3 / &4 % basis 1)) (e i (&4 / &3 % basis 1))) /\
        i IN J /\ (cp i (vec 0) IN W \/ cm i (vec 0) IN W) /\
        j IN J /\ (cp j (vec 0) IN W \/ cm j (vec 0) IN W) /\ ~(i = j)
        ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                     (ccs_branch topX e cp W j) /\
            DISJOINT (ccs_branch topX e cp W i) (ccs_branch topX e cp W j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `!i j. i IN J /\ ((cp:num->real^3->B) i (vec 0) IN W \/
                     (cm:num->real^3->B) i (vec 0) IN W) /\
          j IN J /\ (cp j (vec 0) IN W \/ cm j (vec 0) IN W) /\ ~(i = j)
          ==> DISJOINT (IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)))
                       (ccs_branch topX e (cp:num->real^3->B) W j)`
  (LABEL_TAC "col") THENL
   [MAP_EVERY X_GEN_TAC [`i':num`; `j':num`] THEN
    REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`; `j':num`] CCS_BRANCH_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `i':num`] CCS_NECK_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `i':num`; `j':num`] CCS_NECK_OTHER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`] CCS_PIECE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?q. q IN IMAGE ((e:num->real^3->A) i') (annulus (&1 / &2) (&2)) /\
          q IN ccs_piece topX J e (ff:A->B) W`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl) o
        check (fun th -> can (find_term (fun t -> t = `i':num`)) (concl th))) THENL
       [EXISTS_TAC `(e:num->real^3->A) i' (&4 / &3 % basis 1)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC(SPEC `IMAGE ((e:num->real^3->A) i') (annulus (&1) (&2))`
            (SET_RULE `!s (x:A) t. x IN s /\ s SUBSET t ==> x IN t`)) THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
          FIRST_X_ASSUM(MP_TAC o SPECL [`i':num`; `&4 / &3 % basis 1:real^3`] o
            check (fun th -> is_forall(concl th) &&
                             can (find_term (fun t -> t = `cp:num->real^3->B`)) (concl th) &&
                             can (find_term (fun t -> is_const t &&
                                  fst(dest_const t) = "ccs_piece")) (concl th))) THEN
          ASM_REWRITE_TAC[]];
        EXISTS_TAC `(e:num->real^3->A) i' (&3 / &4 % basis 1)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC(SPEC `IMAGE ((e:num->real^3->A) i') (annulus (&1 / &2) (&1))`
            (SET_RULE `!s (x:A) t. x IN s /\ s SUBSET t ==> x IN t`)) THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
          FIRST_X_ASSUM(MP_TAC o SPECL [`i':num`; `&3 / &4 % basis 1:real^3`] o
            check (fun th -> is_forall(concl th) &&
                             can (find_term (fun t -> t = `cm:num->real^3->B`)) (concl th) &&
                             can (find_term (fun t -> is_const t &&
                                  fst(dest_const t) = "ccs_piece")) (concl th))) THEN
          ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `IMAGE ((e:num->real^3->A) i') (annulus (&1 / &2) (&2)) SUBSET
      ccs_branch topX e (cp:num->real^3->B) W j'`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> t = `C:A->bool`)) (concl th))) THEN
      EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (ccs_piece topX J (e:num->real^3->A) (ff:A->B) W)
                          (ccs_branch topX e (cp:num->real^3->B) W j')` THEN
    UNDISCH_TAC `(q:A) IN ccs_piece topX J (e:num->real^3->A) (ff:A->B) W` THEN
    UNDISCH_TAC `(q:A) IN IMAGE ((e:num->real^3->A) i') (annulus (&1 / &2) (&2))` THEN
    UNDISCH_TAC
     `IMAGE ((e:num->real^3->A) i') (annulus (&1 / &2) (&2)) SUBSET
      ccs_branch topX e (cp:num->real^3->B) W j'` THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "col" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`] CCS_BRANCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[IMP_CONJ]) THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`; `j:num`] CCS_BRANCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "maxj") (K ALL_TAC))))))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `i:num`] CCS_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `j:num`] CCS_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(j:num = i)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(i:num = j)` THEN MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "col" (MP_TAC o SPECL [`j:num`; `i:num`]) THEN
  USE_THEN "col" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  REWRITE_TAC[ASSUME `(i:num) IN J`; ASSUME `(j:num) IN J`; ASSUME `~(i:num = j)`;
              ASSUME `~(j:num = i)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `ccs_far (e:num->real^3->A) (cp:num->real^3->B) W i IN
    IMAGE (e i) (annulus (&1 / &2) (&2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[ccs_far] THEN COND_CASES_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `basis 1:real^3`)) (concl th)))) THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ccs_branch topX (e:num->real^3->A) (cp:num->real^3->B) W i SUBSET
    ccs_branch topX e cp W j`
  ASSUME_TAC THENL
   [USE_THEN "maxj" MATCH_MP_TAC THEN EXISTS_TAC `z:A` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2)))
                          (ccs_branch topX e (cp:num->real^3->B) W i)` THEN
    UNDISCH_TAC `IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)) SUBSET
                 IMAGE (e j) (annulus (&1 / &2) (&2))` THEN
    UNDISCH_TAC `ccs_branch topX (e:num->real^3->A) (cp:num->real^3->B) W i SUBSET
                 topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)))
                        (ccs_branch topX e (cp:num->real^3->B) W j)` THEN
  UNDISCH_TAC `ccs_branch topX (e:num->real^3->A) (cp:num->real^3->B) W i SUBSET
               ccs_branch topX e cp W j` THEN
  UNDISCH_TAC `ccs_far (e:num->real^3->A) (cp:num->real^3->B) W i IN
               ccs_branch topX e cp W i` THEN
  UNDISCH_TAC `ccs_far (e:num->real^3->A) (cp:num->real^3->B) W i IN
               IMAGE (e i) (annulus (&1 / &2) (&2))` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The radial collapse of a collar into its cap.                             *)
(* ccs_collapse y = h(|y|) y / |y| with h = 0 on [0,1], h(t) = 3(t - 1) on  *)
(* [1,3/2] and h(t) = t from 3/2 on; inversion y -> y / |y|^2.             *)
(* ------------------------------------------------------------------------- *)

let ccs_collapse = new_definition
 `ccs_collapse (y:real^3) =
    (max (&0) (min (&3 * (norm y - &1)) (norm y)) / norm y) % y`;;

let CCS_COLLAPSE_FACTS = prove
 (`(!y. &3 / &2 <= norm y ==> ccs_collapse y = y) /\
   (!y. ~(y = vec 0) /\ norm y <= &1 ==> ccs_collapse y = vec 0) /\
   (!y. ~(y = vec 0) /\ norm y < &2 ==> ccs_collapse y IN ball(vec 0,&2))`,
  REWRITE_TAC[ccs_collapse] THEN REPEAT CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `max (&0) (min (&3 * (norm(y:real^3) - &1)) (norm y)) = norm y`
    SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm(y:real^3) / norm y = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_MUL_LID]];
    SUBGOAL_THEN `max (&0) (min (&3 * (norm(y:real^3) - &1)) (norm y)) = &0`
    SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO];
    REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
    ASM_REAL_ARITH_TAC]);;

let CCS_CONTINUOUS_NORM_SUB = prove
 (`!s. continuous_map (subtopology euclidean s,euclideanreal) (norm:real^N->real)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`; `\x:real^N. x`]
                CCS_CONTINUOUS_MAP_NORM) THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  REWRITE_TAC[CONTINUOUS_MAP_ID]);;

let CCS_COLLAPSE_CONTINUOUS = prove
 (`!s. ~(vec 0 IN s)
       ==> continuous_map (subtopology euclidean s,euclidean) ccs_collapse`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ccs_collapse = \y:real^3. (max (&0) (min (&3 * (norm y - &1)) (norm y)) /
                               norm y) % y`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; ccs_collapse]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_MUL THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    REWRITE_TAC[CONTINUOUS_MAP_ID]] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_DIV THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN
    REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_MIN THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST; ETA_AX; CCS_CONTINUOUS_NORM_SUB];
      REWRITE_TAC[ETA_AX; CCS_CONTINUOUS_NORM_SUB]];
    REWRITE_TAC[ETA_AX; CCS_CONTINUOUS_NORM_SUB];
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; NORM_EQ_0] THEN ASM_MESON_TAC[]]);;

let CCS_INVERSION_CONTINUOUS = prove
 (`!s. ~(vec 0 IN s)
       ==> continuous_map (subtopology euclidean s,euclidean)
                          (\y:real^3. inv(norm y pow 2) % y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_MUL THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    REWRITE_TAC[CONTINUOUS_MAP_ID]] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_INV THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_POW THEN
    REWRITE_TAC[ETA_AX; CCS_CONTINUOUS_NORM_SUB];
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; REAL_POW_EQ_0; NORM_EQ_0] THEN
    ASM_MESON_TAC[]]);;

(* The collar part of the local pinch map is continuous on the collar.     *)

let CCS_COLLAR_MAP_CONTINUOUS = prove
 (`!topX topZ (e:real^3->A) (b:real^3->B) einv W inv_side.
        homeomorphic_maps
          (subtopology euclidean (annulus (&1 / &2) (&2)),
           subtopology topX (IMAGE e (annulus (&1 / &2) (&2)))) (e,einv) /\
        homeomorphic_map
          (subtopology euclidean (ball(vec 0,&2)),
           subtopology topZ (IMAGE b (ball(vec 0,&2)))) b /\
        IMAGE b (ball(vec 0,&2)) SUBSET W
        ==> continuous_map
              (subtopology topX (IMAGE e (annulus (&1 / &2) (&2))),
               subtopology topZ W)
              (\x. b(ccs_collapse (if inv_side
                                   then inv(norm(einv x) pow 2) % einv x
                                   else einv x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  SUBGOAL_THEN `~(vec 0 IN annulus (&1 / &2) (&2):real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM; NORM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology topX (IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))),
                    subtopology euclidean (annulus (&1 / &2) (&2)))
                   (\x. if inv_side then inv(norm((einv:A->real^3) x) pow 2) % einv x
                        else einv x)`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `inv_side:bool` THEN ASM_REWRITE_TAC[ETA_AX] THEN
    SUBGOAL_THEN
     `(\x. inv(norm((einv:A->real^3) x) pow 2) % einv x) =
      (\y:real^3. inv(norm y pow 2) % y) o einv`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (annulus (&1 / &2) (&2):real^3->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[CCS_INVERSION_CONTINUOUS] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_SIMP_TAC[CCS_INVERSION] THEN
    UNDISCH_TAC `(y:real^3) IN annulus (&1 / &2) (&2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`norm(y:real^3)`; `&2`] REAL_LT_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
      REAL_ARITH_TAC;
      MP_TAC(SPECL [`&1 / &2`; `norm(y:real^3)`] REAL_LT_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,&2))` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
      EXISTS_TAC `IMAGE (b:real^3->B) (ball(vec 0,&2))` THEN
      ASM_SIMP_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP];
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[]]] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (annulus (&1 / &2) (&2):real^3->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[CCS_COLLAPSE_CONTINUOUS] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC(CONJUNCT2(CONJUNCT2 CCS_COLLAPSE_FACTS)) THEN
  UNDISCH_TAC `(y:real^3) IN annulus (&1 / &2) (&2)` THEN
  REWRITE_TAC[annulus; IN_ELIM_THM; GSYM NORM_POS_LT] THEN REAL_ARITH_TAC);;

(* The pinch map near neck i: the radial collapse on the collar, the cap   *)
(* centre on the branch beyond the cut sphere.                              *)

let ccs_local = new_definition
 `ccs_local (e:num->real^3->A) (cp:num->real^3->B) cm (W:B->bool) i
            (einv:A->real^3) (x:A) =
    if x IN IMAGE (e i) (annulus (&1 / &2) (&2))
    then (if cp i (vec 0) IN W then cp i (ccs_collapse (einv x))
          else cm i (ccs_collapse (inv(norm(einv x) pow 2) % einv x)))
    else (if cp i (vec 0) IN W then cp i (vec 0) else cm i (vec 0))`;;

let CCS_LOCAL_VALUES = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W i einv.
        ccs_cutcap topX topZ J e cp cm ff gg /\ hausdorff_space topX /\
        locally_connected_space topX /\ locally_connected_space topZ /\
        W IN connected_components_of topZ /\
        (!i. i IN J
             ==> ~connected_component_of
                   (subtopology topX
                      (topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))))
                   (e i (&3 / &4 % basis 1)) (e i (&4 / &3 % basis 1))) /\
        i IN J /\ (cp i (vec 0) IN W \/ cm i (vec 0) IN W) /\
        homeomorphic_maps
          (subtopology euclidean (annulus (&1 / &2) (&2)),
           subtopology topX (IMAGE (e i) (annulus (&1 / &2) (&2)))) (e i,einv)
        ==> (!x. x IN IMAGE (e i) (annulus (&1 / &2) (&2)) /\
                 x IN ccs_branch topX e cp W i
                 ==> ccs_local e cp cm W i einv x =
                     (if cp i (vec 0) IN W then cp i (vec 0) else cm i (vec 0))) /\
            (!x. x IN IMAGE (e i) (annulus (&1 / &2) (&2)) /\
                 x IN ccs_piece topX J e ff W /\
                 ~(ff x IN IMAGE (cp i) (cball(vec 0,&3 / &2))) /\
                 ~(ff x IN IMAGE (cm i) (cball(vec 0,&3 / &2)))
                 ==> ccs_local e cp cm W i einv x = ff x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                              TOPSPACE_SUBTOPOLOGY; IN_INTER]) THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`] CCS_PIECE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "Qsub") (CONJUNCTS_THEN2 (LABEL_TAC "Qplus")
      (LABEL_TAC "Qminus"))))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`] CCS_BRANCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "Nsub")
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "Niff")))))))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`] CCS_NOT_BOTH_CAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(!x. x IN annulus (&1) (&2) ==> (ff:A->B)((e:num->real^3->A) i x) = cp i x) /\
    (!x. x IN annulus (&1 / &2) (&1)
         ==> ff(e i x) = (cm:num->real^3->B) i (inv(norm x pow 2) % x))`
  (CONJUNCTS_THEN2 (LABEL_TAC "colp") (LABEL_TAC "colm")) THENL
   [UNDISCH_TAC `ccs_cutcap topX topZ J (e:num->real^3->A) (cp:num->real^3->B)
                            cm ff gg` THEN
    REWRITE_TAC[ccs_cutcap] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2))
        ==> einv x IN annulus (&1 / &2) (&2) /\ e i (einv x) = x`
  (LABEL_TAC "inv") THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN annulus (&1 / &2) (&2)
        ==> ccs_local (e:num->real^3->A) (cp:num->real^3->B) cm W i einv (e i y) =
            (if cp i (vec 0) IN W then cp i (ccs_collapse y)
             else cm i (ccs_collapse (inv(norm y pow 2) % y)))`
  (LABEL_TAC "val") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[ccs_local] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN annulus (&1 / &2) (&2) /\ norm y = &1
        ==> (e:num->real^3->A) i y IN mfd_cut_spheres J e /\
            e i y IN IMAGE (e i) (sphere(vec 0,&1))`
  (LABEL_TAC "sph") THENL
   [REPEAT STRIP_TAC THENL
     [REWRITE_TAC[IN_MFD_CUT_SPHERES] THEN
      MAP_EVERY EXISTS_TAC [`i:num`; `y:real^3`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(vec 0 IN annulus (&1 / &2) (&2):real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM; NORM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `x:A` THEN REPEAT DISCH_TAC THEN
  USE_THEN "inv" (MP_TAC o C MATCH_MP
    (ASSUME `(x:A) IN IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2))`)) THEN
  SPEC_TAC(`(einv:A->real^3) x`,`y:real^3`) THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
  USE_THEN "val" (fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `(y:real^3) IN annulus (&1 / &2) (&2)`)]) THEN
  (SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `~(norm(y:real^3) = &1)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "sph" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `(y:real^3) IN annulus (&1 / &2) (&2)`)
            (ASSUME `norm(y:real^3) = &1`))) THEN
    STRIP_TAC THEN
    FIRST
     [UNDISCH_TAC `(e:num->real^3->A) i y IN ccs_branch topX e (cp:num->real^3->B) W i` THEN
      USE_THEN "Nsub" MP_TAC THEN
      UNDISCH_TAC `(e:num->real^3->A) i y IN IMAGE (e i) (sphere(vec 0,&1))` THEN
      SET_TAC[];
      UNDISCH_TAC `(e:num->real^3->A) i y IN ccs_piece topX J e (ff:A->B) W` THEN
      USE_THEN "Qsub" MP_TAC THEN
      UNDISCH_TAC `(e:num->real^3->A) i y IN mfd_cut_spheres J e` THEN
      SET_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `(&1 < norm(y:real^3) ==> y IN annulus (&1) (&2)) /\
    (norm y < &1 ==> y IN annulus (&1 / &2) (&1))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN annulus (&1 / &2) (&2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `(&1 < norm(y:real^3)
     ==> ((e:num->real^3->A) i y IN ccs_piece topX J e (ff:A->B) W <=>
          (cp:num->real^3->B) i (vec 0) IN W)) /\
    (norm y < &1
     ==> (e i y IN ccs_piece topX J e ff W <=> (cm:num->real^3->B) i (vec 0) IN W))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "Qplus" MATCH_MP_TAC; USE_THEN "Qminus" MATCH_MP_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `norm(inv(norm(y:real^3) pow 2) % y) = inv(norm y) /\
                ~(inv(norm y pow 2) % y = vec 0)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CCS_INVERSION] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_POW_EQ_0; NORM_EQ_0] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC]) THEN
  FIRST
   [UNDISCH_TAC `(e:num->real^3->A) i y IN ccs_branch topX e (cp:num->real^3->B) W i` THEN
    USE_THEN "Niff" (fun th -> REWRITE_TAC[MATCH_MP th
      (CONJ (ASSUME `(y:real^3) IN annulus (&1 / &2) (&2)`)
            (ASSUME `~(norm(y:real^3) = &1)`))]) THEN
    DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 CCS_COLLAPSE_FACTS)) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((e:num->real^3->A) i y IN ccs_piece topX J e (ff:A->B) W)` THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `(cm:num->real^3->B) i (vec 0) IN W` ASSUME_TAC THENL
       [UNDISCH_TAC `(cp:num->real^3->B) i (vec 0) IN W \/
                     (cm:num->real^3->B) i (vec 0) IN W` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 CCS_COLLAPSE_FACTS)) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(norm(y:real^3) < &1)` ASSUME_TAC THENL
       [DISCH_TAC THEN
        UNDISCH_TAC `~((e:num->real^3->A) i y IN ccs_piece topX J e (ff:A->B) W)` THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN
      UNDISCH_TAC `~(norm(y:real^3) < &1)` THEN REAL_ARITH_TAC] THEN NO_TAC;
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `~((cm:num->real^3->B) i (vec 0) IN W)` ASSUME_TAC THENL
       [UNDISCH_TAC `~((cp:num->real^3->B) i (vec 0) IN W /\
                       (cm:num->real^3->B) i (vec 0) IN W)` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 < norm(y:real^3)` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
        SUBGOAL_THEN `norm(y:real^3) < &1` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`norm(y:real^3) <= &1`; `~(norm(y:real^3) = &1)`] THEN
          REAL_ARITH_TAC;
          UNDISCH_TAC `(e:num->real^3->A) i y IN ccs_piece topX J e (ff:A->B) W` THEN
          ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      USE_THEN "colp" (fun th -> REWRITE_TAC[MATCH_MP th
        (MP (ASSUME `&1 < norm(y:real^3) ==> y IN annulus (&1) (&2)`)
            (ASSUME `&1 < norm(y:real^3)`))]) THEN
      AP_TERM_TAC THEN MATCH_MP_TAC(CONJUNCT1 CCS_COLLAPSE_FACTS) THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((ff:A->B)((e:num->real^3->A) i y) IN
                     IMAGE ((cp:num->real^3->B) i) (cball(vec 0,&3 / &2)))` THEN
      USE_THEN "colp" (fun th -> REWRITE_TAC[MATCH_MP th
        (MP (ASSUME `&1 < norm(y:real^3) ==> y IN annulus (&1) (&2)`)
            (ASSUME `&1 < norm(y:real^3)`))]) THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_CBALL_0] THEN
      UNDISCH_TAC `norm(y:real^3) < &3 / &2` THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `(cm:num->real^3->B) i (vec 0) IN W` ASSUME_TAC THENL
       [UNDISCH_TAC `(cp:num->real^3->B) i (vec 0) IN W \/
                     (cm:num->real^3->B) i (vec 0) IN W` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `norm(y:real^3) < &1` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
        SUBGOAL_THEN `&1 < norm(y:real^3)` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`&1 <= norm(y:real^3)`; `~(norm(y:real^3) = &1)`] THEN
          REAL_ARITH_TAC;
          UNDISCH_TAC `(e:num->real^3->A) i y IN ccs_piece topX J e (ff:A->B) W` THEN
          ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      USE_THEN "colm" (fun th -> REWRITE_TAC[MATCH_MP th
        (MP (ASSUME `norm(y:real^3) < &1 ==> y IN annulus (&1 / &2) (&1)`)
            (ASSUME `norm(y:real^3) < &1`))]) THEN
      AP_TERM_TAC THEN MATCH_MP_TAC(CONJUNCT1 CCS_COLLAPSE_FACTS) THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((ff:A->B)((e:num->real^3->A) i y) IN
                     IMAGE ((cm:num->real^3->B) i) (cball(vec 0,&3 / &2)))` THEN
      USE_THEN "colm" (fun th -> REWRITE_TAC[MATCH_MP th
        (MP (ASSUME `norm(y:real^3) < &1 ==> y IN annulus (&1 / &2) (&1)`)
            (ASSUME `norm(y:real^3) < &1`))]) THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_CBALL_0] THEN
      UNDISCH_TAC `norm(inv(norm(y:real^3) pow 2) % y) < &3 / &2` THEN
      REAL_ARITH_TAC]]);;

let CCS_LOCAL_CONTINUOUS = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W i einv.
        ccs_cutcap topX topZ J e cp cm ff gg /\ hausdorff_space topX /\
        locally_connected_space topX /\ locally_connected_space topZ /\
        W IN connected_components_of topZ /\
        (!i. i IN J
             ==> ~connected_component_of
                   (subtopology topX
                      (topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))))
                   (e i (&3 / &4 % basis 1)) (e i (&4 / &3 % basis 1))) /\
        i IN J /\ (cp i (vec 0) IN W \/ cm i (vec 0) IN W) /\
        homeomorphic_maps
          (subtopology euclidean (annulus (&1 / &2) (&2)),
           subtopology topX (IMAGE (e i) (annulus (&1 / &2) (&2)))) (e i,einv)
        ==> continuous_map
              (subtopology topX (IMAGE (e i) (annulus (&1 / &2) (&2)) UNION
                                 ccs_branch topX e cp W i),
               subtopology topZ W)
              (ccs_local e cp cm W i einv)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CCS_LOCAL_VALUES) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "branchval") (K ALL_TAC)) THEN
  FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o
                check (fun th -> is_conj(concl th))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `i:num`] CCS_CUTCAP_CHARTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`] CCS_BRANCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `U = IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2))` THEN
  ABBREV_TAC `N = ccs_branch topX (e:num->real^3->A) (cp:num->real^3->B) W i` THEN
  SUBGOAL_THEN
   `(cp:num->real^3->B) i (vec 0) IN W
    ==> IMAGE (cp i) (ball(vec 0,&2)) SUBSET W`
  ASSUME_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`; `y:real^3`]
                  CCS_CAP_IN_COMPONENT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(cm:num->real^3->B) i (vec 0) IN W
    ==> IMAGE (cm i) (ball(vec 0,&2)) SUBSET W`
  ASSUME_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`; `y:real^3`]
                  CCS_CAP_IN_COMPONENT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CCS_CONTINUOUS_MAP_OPEN_CASES THEN
  MAP_EVERY EXISTS_TAC
   [`U:A->bool`; `N:A->bool`;
    `\x. if (cp:num->real^3->B) i (vec 0) IN W
         then cp i (ccs_collapse ((einv:A->real^3) x))
         else (cm:num->real^3->B) i (ccs_collapse (inv(norm(einv x) pow 2) % einv x))`;
    `\x:A. if (cp:num->real^3->B) i (vec 0) IN W then cp i (vec 0)
           else (cm:num->real^3->B) i (vec 0)`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `N:A->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(U UNION N) INTER U = U:A->bool` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(cp:num->real^3->B) i (vec 0) IN W` THEN
    ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`;
                     `(e:num->real^3->A) i`; `(cp:num->real^3->B) i`;
                     `einv:A->real^3`; `W:B->bool`; `F`]
                    CCS_COLLAR_MAP_CONTINUOUS);
      SUBGOAL_THEN `(cm:num->real^3->B) i (vec 0) IN W` ASSUME_TAC THENL
       [UNDISCH_TAC `(cp:num->real^3->B) i (vec 0) IN W \/
                     (cm:num->real^3->B) i (vec 0) IN W` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`;
                     `(e:num->real^3->A) i`; `(cm:num->real^3->B) i`;
                     `einv:A->real^3`; `W:B->bool`; `T`]
                    CCS_COLLAR_MAP_CONTINUOUS)] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[ETA_AX];
    REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    DISJ2_TAC THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`]
                    CONNECTED_COMPONENTS_OF_SUBSET) THEN
      ASM SET_TAC[];
      SUBGOAL_THEN `(cm:num->real^3->B) i (vec 0) IN W` ASSUME_TAC THENL
       [UNDISCH_TAC `(cp:num->real^3->B) i (vec 0) IN W \/
                     (cm:num->real^3->B) i (vec 0) IN W` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`]
                    CONNECTED_COMPONENTS_OF_SUBSET) THEN
      ASM SET_TAC[]];
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[ccs_local];
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `(x:A) IN U` THENL
     [USE_THEN "branchval" (fun th -> REWRITE_TAC[MATCH_MP th
        (CONJ (ASSUME `(x:A) IN U`) (ASSUME `(x:A) IN N`))]);
      ASM_REWRITE_TAC[ccs_local]]]);;

(* ------------------------------------------------------------------------- *)
(* The pinch map P : X -> W, glued from ff on the deep part of               *)
(* Q, the local maps on the necks adjacent to W and a constant elsewhere.  *)
(* ------------------------------------------------------------------------- *)

(* The closed balls of radius r < 2 of the caps of W form a closed set.     *)

let CCS_CAP_BALLS_CLOSED = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W r.
        ccs_cutcap topX topZ J e cp cm ff gg /\ hausdorff_space topZ /\
        &0 <= r /\ r < &2
        ==> closed_in topZ
              (UNIONS {IMAGE (cp i) (cball(vec 0,r)) | i | i IN J /\ cp i (vec 0) IN W}
               UNION
               UNIONS {IMAGE (cm i) (cball(vec 0,r)) | i | i IN J /\ cm i (vec 0) IN W})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(J:num->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `ccs_cutcap topX topZ J (e:num->real^3->A) (cp:num->real^3->B)
                            cm ff gg` THEN SIMP_TAC[ccs_cutcap];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^3,r) SUBSET ball(vec 0,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b:real^3->B.
        homeomorphic_map (subtopology euclidean (ball(vec 0,&2)),
                          subtopology topZ (IMAGE b (ball(vec 0,&2)))) b
        ==> closed_in topZ (IMAGE b (cball(vec 0,r)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,&2))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `IMAGE (b:real^3->B) (ball(vec 0,&2))` THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN J ==> closed_in topZ (IMAGE ((cp:num->real^3->B) i) (cball(vec 0,r))) /\
                   closed_in topZ (IMAGE ((cm:num->real^3->B) i) (cball(vec 0,r)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `i:num`] CCS_CUTCAP_CHARTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_UNION THEN CONJ_TAC THEN
  MATCH_MP_TAC CLOSED_IN_UNIONS THEN
  ASM_SIMP_TAC[FORALL_IN_GSPEC] THEN
  MATCH_MP_TAC FINITE_SUBSET THENL
   [EXISTS_TAC `IMAGE (\i. IMAGE ((cp:num->real^3->B) i) (cball(vec 0,r))) J`;
    EXISTS_TAC `IMAGE (\i. IMAGE ((cm:num->real^3->B) i) (cball(vec 0,r))) J`] THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN SET_TAC[]);;

let CCS_UNIONS_LEMMA = prove
 (`!s n c (q:A->bool) f.
        c SUBSET n UNION s /\ (s UNION n) IN f
        ==> s UNION c SUBSET q UNION UNIONS f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS] THEN
  STRIP_TAC THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN DISJ2_TAC THEN
  EXISTS_TAC `(s:A->bool) UNION n` THEN ASM_REWRITE_TAC[IN_UNION] THEN
  ASM_MESON_TAC[]);;

(* Q together with the cut spheres and branches of the necks adjacent to W *)
(* is closed in X.                                                          *)

let CCS_TAIL_CLOSED = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W.
        ccs_cutcap topX topZ J e cp cm ff gg /\ hausdorff_space topX /\
        locally_connected_space topX /\ locally_connected_space topZ /\
        W IN connected_components_of topZ /\
        (!i. i IN J
             ==> ~connected_component_of
                   (subtopology topX
                      (topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))))
                   (e i (&3 / &4 % basis 1)) (e i (&4 / &3 % basis 1)))
        ==> closed_in topX
              (ccs_piece topX J e ff W UNION
               UNIONS {IMAGE (e i) (sphere(vec 0,&1)) UNION ccs_branch topX e cp W i |
                       i | i IN J /\ (cp i (vec 0) IN W \/ cm i (vec 0) IN W)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(J:num->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `ccs_cutcap topX topZ J (e:num->real^3->A) (cp:num->real^3->B)
                            cm ff gg` THEN SIMP_TAC[ccs_cutcap];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`] CCS_PIECE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`] CCS_PIECE_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. i IN J /\ ((cp:num->real^3->B) i (vec 0) IN W \/
                   (cm:num->real^3->B) i (vec 0) IN W)
        ==> closed_in topX (IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))) /\
            ccs_branch topX e cp W i SUBSET topspace topX /\
            topX closure_of (ccs_branch topX e cp W i) SUBSET
            ccs_branch topX e cp W i UNION IMAGE (e i) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `i:num`] CCS_NECK_FACTS) THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`] CCS_BRANCH_FACTS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "closure_of"))
            (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[UNION_SUBSET] THEN
      ASM_MESON_TAC[CLOSED_IN_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
            ccs_branch topX e (cp:num->real^3->B) W i |
            i | i IN J /\ (cp i (vec 0) IN W \/ (cm:num->real^3->B) i (vec 0) IN W)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\i. IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
                           ccs_branch topX e (cp:num->real^3->B) W i) J` THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CLOSURE_OF_UNION; CLOSURE_OF_UNIONS] THEN
  REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC
     `ccs_piece topX J (e:num->real^3->A) (ff:A->B) W UNION
      UNIONS {IMAGE (e i) (sphere(vec 0,&1)) | i |
              i IN J /\ ((cp:num->real^3->B) i (vec 0) IN W \/
                         (cm:num->real^3->B) i (vec 0) IN W)}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "closure_of"))
        (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "ccs_branch"))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CLOSURE_OF_UNION; CLOSURE_OF_CLOSED_IN] THEN
  SUBGOAL_THEN
   `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
    ccs_branch topX e (cp:num->real^3->B) W i IN
    {IMAGE (e i) (sphere(vec 0,&1)) UNION ccs_branch topX e cp W i |
     i | i IN J /\ (cp i (vec 0) IN W \/ (cm:num->real^3->B) i (vec 0) IN W)}`
  MP_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC CCS_UNIONS_LEMMA THEN
  EXISTS_TAC `ccs_branch topX (e:num->real^3->A) (cp:num->real^3->B) W i` THEN
  ASM_REWRITE_TAC[]);;

let CCS_IN_CAP_BALLS = prove
 (`!J (cp:num->real^3->B) (cm:num->real^3->B) W r z.
        z IN UNIONS {IMAGE (cp i) (cball(vec 0,r)) | i | i IN J /\ cp i (vec 0) IN W}
             UNION
             UNIONS {IMAGE (cm i) (cball(vec 0,r)) | i | i IN J /\ cm i (vec 0) IN W} <=>
        ?i. i IN J /\
            (cp i (vec 0) IN W /\ z IN IMAGE (cp i) (cball(vec 0,r)) \/
             cm i (vec 0) IN W /\ z IN IMAGE (cm i) (cball(vec 0,r)))`,
  REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

(* Points of X off the spheres sent into a 3/2-ball of a cap lie on that    *)
(* neck's collar.                                                           *)

let CCS_DEEP_COLLAR = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg i x.
        ccs_cutcap topX topZ J e cp cm ff gg /\ i IN J /\
        x IN topspace topX /\ ~(x IN mfd_cut_spheres J e) /\
        (ff x IN IMAGE (cp i) (cball(vec 0,&3 / &2)) \/
         ff x IN IMAGE (cm i) (cball(vec 0,&3 / &2)))
        ==> x IN IMAGE (e i) (annulus (&1 / &2) (&2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CCS_CUTCAP_FACTS) THEN
  DISCH_THEN(fun th ->
    LABEL_TAC "core" (CONJUNCT1(funpow 3 CONJUNCT2 th)) THEN
    LABEL_TAC "ffx" (CONJUNCT1(funpow 4 CONJUNCT2 th)) THEN
    LABEL_TAC "ggp" (CONJUNCT1(funpow 6 CONJUNCT2 th)) THEN
    LABEL_TAC "ggm" (funpow 7 CONJUNCT2 th)) THEN
  USE_THEN "ffx" (MP_TAC o SPEC `x:A`) THEN
  REWRITE_TAC[IN_DIFF; ASSUME `(x:A) IN topspace topX`;
              ASSUME `~((x:A) IN mfd_cut_spheres J e)`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (MP_TAC o REWRITE_RULE[IN_IMAGE; IN_CBALL_0]) o
                check (is_disj o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  (SUBGOAL_THEN `(y:real^3) IN ball(vec 0,&2)` ASSUME_TAC THENL
    [REWRITE_TAC[IN_BALL_0] THEN UNDISCH_TAC `norm(y:real^3) <= &3 / &2` THEN
     REAL_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `(y:real^3) IN annulus (&1) (&2)` ASSUME_TAC THENL
    [UNDISCH_TAC `~((ff:A->B) x IN mfd_cut_cores J (cp:num->real^3->B) cm)` THEN
     ASM_REWRITE_TAC[] THEN
     USE_THEN "core" (fun th -> REWRITE_TAC[MATCH_MP th
       (CONJ (ASSUME `(i:num) IN J`) (ASSUME `(y:real^3) IN ball(vec 0,&2)`))]) THEN
     UNDISCH_TAC `norm(y:real^3) <= &3 / &2` THEN
     REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  UNDISCH_TAC `(gg:B->A)((ff:A->B) x) = x` THEN ASM_REWRITE_TAC[] THEN
  FIRST [USE_THEN "ggp" (fun th -> REWRITE_TAC[MATCH_MP th
           (CONJ (ASSUME `(i:num) IN J`) (ASSUME `(y:real^3) IN annulus (&1) (&2)`))]) THEN
         DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
         UNDISCH_TAC `(y:real^3) IN annulus (&1) (&2)` THEN
         REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC THEN NO_TAC;
         USE_THEN "ggm" (fun th -> REWRITE_TAC[MATCH_MP th
           (CONJ (ASSUME `(i:num) IN J`) (ASSUME `(y:real^3) IN annulus (&1) (&2)`))]) THEN
         DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
         MP_TAC(SPEC `y:real^3` CCS_INVERSION_ANNULUS) THEN
         ASM_REWRITE_TAC[] THEN
         REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

(* The deep part, the rest and the neck regions cover X.                    *)

let CCS_PINCH_COVER = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W x.
        ccs_cutcap topX topZ J e cp cm ff gg /\ hausdorff_space topX /\
        locally_connected_space topX /\ locally_connected_space topZ /\
        W IN connected_components_of topZ /\
        (!i. i IN J
             ==> ~connected_component_of
                   (subtopology topX
                      (topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))))
                   (e i (&3 / &4 % basis 1)) (e i (&4 / &3 % basis 1))) /\
        x IN topspace topX
        ==> (x IN topspace topX DIFF mfd_cut_spheres J e /\
             ff x IN W DIFF
             (UNIONS {IMAGE (cp i) (cball(vec 0,&3 / &2)) | i | i IN J /\ cp i (vec 0) IN W}
              UNION
              UNIONS {IMAGE (cm i) (cball(vec 0,&3 / &2)) | i | i IN J /\ cm i (vec 0) IN W})) \/
            ~(x IN ccs_piece topX J e ff W UNION
                   UNIONS {IMAGE (e i) (sphere(vec 0,&1)) UNION ccs_branch topX e cp W i |
                           i | i IN J /\ (cp i (vec 0) IN W \/ cm i (vec 0) IN W)}) \/
            (?i. i IN J /\ (cp i (vec 0) IN W \/ cm i (vec 0) IN W) /\
                 x IN IMAGE (e i) (annulus (&1 / &2) (&2)) UNION ccs_branch topX e cp W i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `(x:A) IN ccs_piece topX J e (ff:A->B) W UNION
             UNIONS {IMAGE (e i) (sphere(vec 0,&1)) UNION
                     ccs_branch topX e (cp:num->real^3->B) W i |
                     i | i IN J /\ (cp i (vec 0) IN W \/ (cm:num->real^3->B) i (vec 0) IN W)}` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IN_UNION; IN_UNIONS; IN_ELIM_THM] o
    check (fun th -> is_comb(concl th) && is_const(fst(strip_comb(concl th))) &&
                     fst(dest_const(fst(strip_comb(concl th)))) = "IN" &&
                     can (find_term (fun t -> is_const t &&
                          fst(dest_const t) = "ccs_branch")) (concl th))) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:A->bool`
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2
       (CONJUNCTS_THEN ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC))) THENL
   [ALL_TAC;
    DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `i:num`] CCS_NECK_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(x:A) IN t` THEN
    UNDISCH_TAC `t = IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
                     ccs_branch topX e (cp:num->real^3->B) W i` THEN
    UNDISCH_TAC `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) SUBSET
                 IMAGE (e i) (annulus (&1 / &2) (&2))` THEN
    SET_TAC[]] THEN
  REWRITE_TAC[IN_DIFF; CCS_IN_CAP_BALLS] THEN
  SUBGOAL_THEN `(x:A) IN topspace topX DIFF mfd_cut_spheres J e /\ (ff:A->B) x IN W`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN ccs_piece topX J (e:num->real^3->A) (ff:A->B) W` THEN
    REWRITE_TAC[ccs_piece; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_DIFF]) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC
   `?i. i IN J /\
        ((cp:num->real^3->B) i (vec 0) IN W /\
         (ff:A->B) x IN IMAGE (cp i) (cball(vec 0,&3 / &2)) \/
         (cm:num->real^3->B) i (vec 0) IN W /\
         ff x IN IMAGE (cm i) (cball(vec 0,&3 / &2)))` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
  MATCH_MP_TAC CCS_DEEP_COLLAR THEN
  MAP_EVERY EXISTS_TAC [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                        `cp:num->real^3->B`; `cm:num->real^3->B`;
                        `ff:A->B`; `gg:B->A`] THEN
  ASM_REWRITE_TAC[IN_DIFF]);;

(* A point of W off the 3/2-balls of the caps of W is off the 3/2-balls of *)
(* every cap.                                                               *)

let CCS_OFF_CAP_BALLS = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W i z.
        ccs_cutcap topX topZ J e cp cm ff gg /\
        W IN connected_components_of topZ /\ i IN J /\ z IN W /\
        ~(z IN UNIONS {IMAGE (cp i) (cball(vec 0,&3 / &2)) | i |
                       i IN J /\ cp i (vec 0) IN W} UNION
               UNIONS {IMAGE (cm i) (cball(vec 0,&3 / &2)) | i |
                       i IN J /\ cm i (vec 0) IN W})
        ==> ~(z IN IMAGE (cp i) (cball(vec 0,&3 / &2))) /\
            ~(z IN IMAGE (cm i) (cball(vec 0,&3 / &2)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CCS_IN_CAP_BALLS; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  REWRITE_TAC[ASSUME `(i:num) IN J`] THEN
  SUBGOAL_THEN
   `(z IN IMAGE ((cp:num->real^3->B) i) (cball(vec 0,&3 / &2)) ==> cp i (vec 0) IN W) /\
    (z IN IMAGE ((cm:num->real^3->B) i) (cball(vec 0,&3 / &2)) ==> cm i (vec 0) IN W)`
  MP_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`; `y:real^3`]
                  CCS_CAP_IN_COMPONENT) THEN
    (ANTS_TAC THENL
      [ASM_REWRITE_TAC[IN_BALL_0] THEN
       UNDISCH_TAC `norm(y:real^3) <= &3 / &2` THEN REAL_ARITH_TAC;
       ALL_TAC]) THEN
    UNDISCH_TAC `(z:B) IN W` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MESON_TAC[]]);;

(* The facts behind the agreement of the pieces of the pinch map.           *)

let CCS_PINCH_PIECES = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W einv.
        ccs_cutcap topX topZ J e cp cm ff gg /\ hausdorff_space topX /\
        locally_connected_space topX /\ locally_connected_space topZ /\
        W IN connected_components_of topZ /\
        (!i. i IN J
             ==> ~connected_component_of
                   (subtopology topX
                      (topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))))
                   (e i (&3 / &4 % basis 1)) (e i (&4 / &3 % basis 1))) /\
        (!i. i IN J
             ==> homeomorphic_maps
                   (subtopology euclidean (annulus (&1 / &2) (&2)),
                    subtopology topX (IMAGE (e i) (annulus (&1 / &2) (&2))))
                   (e i,einv i))
        ==> (!i x. i IN J /\ (cp i (vec 0) IN W \/ cm i (vec 0) IN W) /\
                   x IN topspace topX DIFF mfd_cut_spheres J e /\
                   ff x IN W DIFF
                   (UNIONS {IMAGE (cp i) (cball(vec 0,&3 / &2)) | i |
                            i IN J /\ cp i (vec 0) IN W} UNION
                    UNIONS {IMAGE (cm i) (cball(vec 0,&3 / &2)) | i |
                            i IN J /\ cm i (vec 0) IN W}) /\
                   x IN IMAGE (e i) (annulus (&1 / &2) (&2)) UNION
                        ccs_branch topX e cp W i
                   ==> ccs_local e cp cm W i (einv i) x = ff x) /\
            (!i. i IN J /\ (cp i (vec 0) IN W \/ cm i (vec 0) IN W)
                 ==> IMAGE (e i) (annulus (&1 / &2) (&2)) UNION
                     ccs_branch topX e cp W i SUBSET
                     ccs_piece topX J e ff W UNION
                     UNIONS {IMAGE (e i) (sphere(vec 0,&1)) UNION
                             ccs_branch topX e cp W i |
                             i | i IN J /\ (cp i (vec 0) IN W \/ cm i (vec 0) IN W)}) /\
            (!i j. i IN J /\ (cp i (vec 0) IN W \/ cm i (vec 0) IN W) /\
                   j IN J /\ (cp j (vec 0) IN W \/ cm j (vec 0) IN W) /\ ~(i = j)
                   ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)) UNION
                                 ccs_branch topX e cp W i)
                                (IMAGE (e j) (annulus (&1 / &2) (&2)) UNION
                                 ccs_branch topX e cp W j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `x:A`] THEN
    REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`;
                   `(einv:num->A->real^3) i`] CCS_LOCAL_VALUES) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `(x:A) IN ccs_piece topX J e (ff:A->B) W` ASSUME_TAC THENL
     [REWRITE_TAC[ccs_piece; IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`] CCS_BRANCH_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `(x:A) IN IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)) UNION
                            ccs_branch topX e (cp:num->real^3->B) W i` THEN
      UNDISCH_TAC `(x:A) IN ccs_piece topX J (e:num->real^3->A) (ff:A->B) W` THEN
      UNDISCH_TAC `DISJOINT (ccs_piece topX J (e:num->real^3->A) (ff:A->B) W)
                            (ccs_branch topX e (cp:num->real^3->B) W i)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CCS_OFF_CAP_BALLS THEN
    MAP_EVERY EXISTS_TAC [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                          `e:num->real^3->A`; `ff:A->B`; `gg:B->A`; `W:B->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `(ff:A->B) x IN W DIFF
      (UNIONS {IMAGE ((cp:num->real^3->B) i) (cball(vec 0,&3 / &2)) | i |
               i IN J /\ cp i (vec 0) IN W} UNION
       UNIONS {IMAGE ((cm:num->real^3->B) i) (cball(vec 0,&3 / &2)) | i |
               i IN J /\ cm i (vec 0) IN W})` THEN
    REWRITE_TAC[IN_DIFF] THEN SIMP_TAC[];
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`] CCS_BRANCH_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
      ccs_branch topX e (cp:num->real^3->B) W i IN
      {IMAGE (e i) (sphere(vec 0,&1)) UNION ccs_branch topX e cp W i |
       i | i IN J /\ (cp i (vec 0) IN W \/ (cm:num->real^3->B) i (vec 0) IN W)}`
    MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SPEC_TAC(`{IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
               ccs_branch topX e (cp:num->real^3->B) W i |
               i | i IN J /\ (cp i (vec 0) IN W \/ (cm:num->real^3->B) i (vec 0) IN W)}`,
             `fam:(A->bool)->bool`) THEN
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!z. z IN IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
               ccs_branch topX e (cp:num->real^3->B) W i
          ==> z IN ccs_piece topX J e (ff:A->B) W UNION UNIONS fam`
    (LABEL_TAC "zr") THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_UNION; IN_UNIONS] THEN DISJ2_TAC THEN
      EXISTS_TAC `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) UNION
                  ccs_branch topX e (cp:num->real^3->B) W i` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      ASM_CASES_TAC `norm(y:real^3) = &1` THENL
       [USE_THEN "zr" MATCH_MP_TAC THEN REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
        ALL_TAC] THEN
      ASM_CASES_TAC `(e:num->real^3->A) i y IN ccs_piece topX J e (ff:A->B) W` THENL
       [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
      USE_THEN "zr" MATCH_MP_TAC THEN REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> t = `&1 / &2`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "ccs_branch"))
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
      USE_THEN "zr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION]];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `~(j:num = i)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(i:num = j)` THEN MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!u1 n1 u2 n2:A->bool.
        DISJOINT u1 u2 /\ DISJOINT u1 n2 /\ DISJOINT n1 u2 /\ DISJOINT n1 n2
        ==> DISJOINT (u1 UNION n1) (u2 UNION n2)`) THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                     `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                     `ff:A->B`; `gg:B->A`; `i:num`; `j:num`]
                    CCS_CUTCAP_CAPS_DISJOINT) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                     `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                     `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`; `j:num`]
                    CCS_BRANCHES_DISJOINT) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                     `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                     `ff:A->B`; `gg:B->A`; `W:B->bool`; `j:num`; `i:num`]
                    CCS_BRANCHES_DISJOINT) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[DISJOINT_SYM];
      MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                     `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                     `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`; `j:num`]
                    CCS_BRANCHES_DISJOINT) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]]]);;

(* The pinch map.                                                           *)

let CCS_PINCH_MAP = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W.
        ccs_cutcap topX topZ J e cp cm ff gg /\ hausdorff_space topX /\
        hausdorff_space topZ /\
        locally_connected_space topX /\ locally_connected_space topZ /\
        W IN connected_components_of topZ /\
        (!i. i IN J
             ==> ~connected_component_of
                   (subtopology topX
                      (topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))))
                   (e i (&3 / &4 % basis 1)) (e i (&4 / &3 % basis 1)))
        ==> ?P. continuous_map (topX,subtopology topZ W) P /\
                (!z. z IN W /\
                     ~(z IN UNIONS {IMAGE (cp i) (cball(vec 0,&3 / &2)) | i |
                                    i IN J /\ cp i (vec 0) IN W} UNION
                            UNIONS {IMAGE (cm i) (cball(vec 0,&3 / &2)) | i |
                                    i IN J /\ cm i (vec 0) IN W})
                     ==> P(gg z) = z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?einv:num->A->real^3.
      !i. i IN J
          ==> homeomorphic_maps
                (subtopology euclidean (annulus (&1 / &2) (&2)),
                 subtopology topX (IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2))))
                (e i,einv i)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM HOMEOMORPHIC_MAP_MAPS] THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `i:num`] CCS_CUTCAP_CHARTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w0:B. w0 IN W` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`]
                  NONEMPTY_CONNECTED_COMPONENTS_OF) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`; `einv:num->A->real^3`]
                CCS_PINCH_PIECES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "agA")
    (CONJUNCTS_THEN2 (LABEL_TAC "inT") (LABEL_TAC "disj"))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`; `&3 / &2`]
                CCS_CAP_BALLS_CLOSED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`] CCS_TAIL_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC
   `D = UNIONS {IMAGE ((cp:num->real^3->B) i) (cball(vec 0,&3 / &2)) | i |
                i IN J /\ cp i (vec 0) IN W} UNION
        UNIONS {IMAGE ((cm:num->real^3->B) i) (cball(vec 0,&3 / &2)) | i |
                i IN J /\ cm i (vec 0) IN W}` THEN
  ABBREV_TAC
   `TT = ccs_piece topX J (e:num->real^3->A) (ff:A->B) W UNION
         UNIONS {IMAGE (e i) (sphere(vec 0,&1)) UNION
                 ccs_branch topX e (cp:num->real^3->B) W i |
                 i | i IN J /\ (cp i (vec 0) IN W \/ (cm:num->real^3->B) i (vec 0) IN W)}` THEN
  ABBREV_TAC
   `OA = {x | x IN topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A) /\
              (ff:A->B) x IN W DIFF D}` THEN
  SUBGOAL_THEN `!x:A. x IN OA ==> x IN TT` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["OA"; "TT"] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION; IN_DIFF; ccs_piece] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in topX (OA:A->bool) /\
    continuous_map (subtopology topX OA,subtopology topZ W) (ff:A->B)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `open_in topX (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)) /\
      homeomorphic_maps
        (subtopology topX (topspace topX DIFF mfd_cut_spheres J e),
         subtopology topZ (topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm))
        (ff:A->B,gg)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ccs_cutcap topX topZ J (e:num->real^3->A) (cp:num->real^3->B)
                              cm ff gg` THEN SIMP_TAC[ccs_cutcap];
      ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
    SUBGOAL_THEN
     `continuous_map (subtopology topX (topspace topX DIFF mfd_cut_spheres J
                        (e:num->real^3->A)), topZ) (ff:A->B)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
      EXISTS_TAC `topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "OA" THEN MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
      EXISTS_TAC `topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`ff:A->B`;
                     `subtopology topX (topspace topX DIFF mfd_cut_spheres J
                                          (e:num->real^3->A))`;
                     `topZ:B topology`; `W DIFF D:B->bool`]
                    OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN EXPAND_TAC "OA" THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER;
                    IN_DIFF] THEN
        MESON_TAC[]];
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
        EXISTS_TAC `topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "OA" THEN SET_TAC[];
        EXPAND_TAC "OA" THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER;
                    IN_ELIM_THM; IN_DIFF] THEN
        SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`topX:A topology`; `subtopology topZ (W:B->bool)`;
    `\p:num#num. if FST p = 0 then (ff:A->B)
                 else if FST p = 1 then (\x:A. (w0:B))
                 else ccs_local (e:num->real^3->A) (cp:num->real^3->B) cm W (SND p)
                                ((einv:num->A->real^3) (SND p))`;
    `\p:num#num. if FST p = 0 then OA
                 else if FST p = 1 then topspace topX DIFF TT
                 else IMAGE ((e:num->real^3->A) (SND p)) (annulus (&1 / &2) (&2)) UNION
                      ccs_branch topX e (cp:num->real^3->B) W (SND p)`;
    `(0,0) INSERT (1,0) INSERT
     IMAGE (\i:num. (2,i)) {i | i IN J /\ ((cp:num->real^3->B) i (vec 0) IN W \/
                                           (cm:num->real^3->B) i (vec 0) IN W)}`]
   PASTING_LEMMA_EXISTS) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_ELIM_THM; FST; SND; ARITH_EQ] THEN
  SUBGOAL_THEN `!x:A. x IN OA ==> x IN topspace topX DIFF mfd_cut_spheres J e /\
                                  (ff:A->B) x IN W DIFF D`
  ASSUME_TAC THENL
   [EXPAND_TAC "OA" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`; `x:A`] CCS_PINCH_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `i:num` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THENL
     [EXISTS_TAC `OA:A->bool` THEN CONJ_TAC THENL
       [EXISTS_TAC `(0,0)` THEN REWRITE_TAC[IN_INSERT; FST; SND; ARITH_EQ];
        EXPAND_TAC "OA" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
      EXISTS_TAC `topspace topX DIFF TT:A->bool` THEN CONJ_TAC THENL
       [EXISTS_TAC `(1,0)` THEN REWRITE_TAC[IN_INSERT; FST; SND; ARITH_EQ];
        ASM_REWRITE_TAC[IN_DIFF]];
      EXISTS_TAC `IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)) UNION
                  ccs_branch topX e (cp:num->real^3->B) W i` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `(2,i:num)` THEN
      REWRITE_TAC[IN_INSERT; IN_IMAGE; FST; SND; ARITH_EQ; PAIR_EQ; IN_ELIM_THM] THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]; ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`] CONNECTED_COMPONENTS_OF_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_UNION THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                       `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                       `ff:A->B`; `gg:B->A`; `i:num`] CCS_CUTCAP_CHARTS) THEN
        ASM_SIMP_TAC[];
        MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                       `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                       `ff:A->B`; `gg:B->A`; `W:B->bool`; `i:num`] CCS_BRANCH_FACTS) THEN
        ASM_SIMP_TAC[]];
      MATCH_MP_TAC CCS_LOCAL_CONTINUOUS THEN
      MAP_EVERY EXISTS_TAC [`J:num->bool`; `ff:A->B`; `gg:B->A`] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN J /\ ((cp:num->real^3->B) i (vec 0) IN W \/
                   (cm:num->real^3->B) i (vec 0) IN W)
        ==> !x. x IN IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)) UNION
                     ccs_branch topX e cp W i ==> x IN TT`
  (LABEL_TAC "inT'") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "inT" (MP_TAC o SPEC `i:num`) THEN
    EXPAND_TAC "TT" THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_DIFF] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    USE_THEN "agA" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_DIFF] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_INTER; IN_DIFF] THEN STRIP_TAC THEN
    USE_THEN "inT'" (MP_TAC o SPEC `x:A` o C MATCH_MP
      (ASSUME `(i:num) IN J /\ ((cp:num->real^3->B) i (vec 0) IN W \/
                                (cm:num->real^3->B) i (vec 0) IN W)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      USE_THEN "agA" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_INTER; IN_DIFF] THEN STRIP_TAC THEN
      USE_THEN "inT'" (MP_TAC o SPEC `x:A` o C MATCH_MP
        (ASSUME `(i:num) IN J /\ ((cp:num->real^3->B) i (vec 0) IN W \/
                                  (cm:num->real^3->B) i (vec 0) IN W)`)) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      ASM_CASES_TAC `j:num = i` THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "disj" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      REWRITE_TAC[ASSUME `(i:num) IN J /\ ((cp:num->real^3->B) i (vec 0) IN W \/
                                         (cm:num->real^3->B) i (vec 0) IN W)`;
                  ASSUME `(j:num) IN J /\ ((cp:num->real^3->B) j (vec 0) IN W \/
                                         (cm:num->real^3->B) j (vec 0) IN W)`] THEN
      ANTS_TAC THENL [UNDISCH_TAC `~(j:num = i)` THEN MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:A) IN IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)) UNION
                            ccs_branch topX e (cp:num->real^3->B) W i` THEN
      UNDISCH_TAC `(x:A) IN IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2)) UNION
                            ccs_branch topX e (cp:num->real^3->B) W j` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:A->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `P:A->B` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:B` THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CCS_CUTCAP_FACTS) THEN
  DISCH_THEN(LABEL_TAC "ggz" o CONJUNCT1 o funpow 5 CONJUNCT2) THEN
  SUBGOAL_THEN `(z:B) IN topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`]
                    CONNECTED_COMPONENTS_OF_SUBSET) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_MFD_CUT_CORES] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `y:real^3`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
    UNDISCH_TAC `~((z:B) IN D)` THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[CCS_IN_CAP_BALLS] THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`; `j:num`; `y:real^3`]
                  CCS_CAP_IN_COMPONENT) THEN
    (ANTS_TAC THENL
      [ASM_REWRITE_TAC[IN_BALL_0] THEN UNDISCH_TAC `norm(y:real^3) <= &1` THEN
       REAL_ARITH_TAC;
       ALL_TAC]) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN cball(vec 0,&3 / &2)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_CBALL_0] THEN UNDISCH_TAC `norm(y:real^3) <= &1` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  USE_THEN "ggz" (MP_TAC o C MATCH_MP
    (ASSUME `(z:B) IN topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm`)) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o SPEC `(gg:B->A) z` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> t = `P:A->B`)) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "OA" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[IN_DIFF];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The components of the capped space are simply connected:                  *)
(* the topological theorem CCS_CUTCAP_SC_TOP and the headline RFS_CUTCAP_SC. *)
(* ------------------------------------------------------------------------- *)

let CCS_COMPONENT_PATH_CONNECTED = prove
 (`!top (W:A->bool).
        locally_path_connected_space top /\ W IN connected_components_of top
        ==> path_connected_space (subtopology top W)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `top:A topology` PATH_COMPONENTS_EQ_CONNECTED_COMPONENTS_OF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PATH_CONNECTED_IN_PATH_COMPONENTS_OF) THEN
  SIMP_TAC[path_connected_in]);;

(* A point of W off the 3/2-balls of its caps is off the cap cores.        *)

let CCS_OFF_BALLS_OFF_CORES = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W z.
        ccs_cutcap topX topZ J e cp cm ff gg /\
        W IN connected_components_of topZ /\ z IN W /\
        ~(z IN UNIONS {IMAGE (cp i) (cball(vec 0,&3 / &2)) | i |
                       i IN J /\ cp i (vec 0) IN W} UNION
               UNIONS {IMAGE (cm i) (cball(vec 0,&3 / &2)) | i |
                       i IN J /\ cm i (vec 0) IN W})
        ==> z IN topspace topZ DIFF mfd_cut_cores J cp cm`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`topZ:B topology`; `W:B->bool`]
                  CONNECTED_COMPONENTS_OF_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_MFD_CUT_CORES] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `y:real^3`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  UNDISCH_TAC
   `~((z:B) IN UNIONS {IMAGE ((cp:num->real^3->B) i) (cball(vec 0,&3 / &2)) | i |
                       i IN J /\ cp i (vec 0) IN W} UNION
               UNIONS {IMAGE ((cm:num->real^3->B) i) (cball(vec 0,&3 / &2)) | i |
                       i IN J /\ cm i (vec 0) IN W})` THEN
  REWRITE_TAC[CCS_IN_CAP_BALLS] THEN EXISTS_TAC `j:num` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`; `j:num`; `y:real^3`]
                CCS_CAP_IN_COMPONENT) THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[IN_BALL_0] THEN UNDISCH_TAC `norm(y:real^3) <= &1` THEN
     REAL_ARITH_TAC;
     ALL_TAC]) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN cball(vec 0,&3 / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0] THEN UNDISCH_TAC `norm(y:real^3) <= &1` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FUN_IN_IMAGE]);;

(* Loops of W are homotopic in W to loops off the 3/2-balls of its caps.   *)

let CCS_LOOPS_INTO_DEEP = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg W h.
        ccs_cutcap topX topZ J e cp cm ff gg /\ hausdorff_space topZ /\
        W IN connected_components_of topZ /\
        path_in (subtopology topZ W) h /\ h(&1) = h(&0)
        ==> ?h'. path_in (subtopology topZ
                   (W DIFF
                    (UNIONS {IMAGE (cp i) (cball(vec 0,&3 / &2)) | i |
                             i IN J /\ cp i (vec 0) IN W} UNION
                     UNIONS {IMAGE (cm i) (cball(vec 0,&3 / &2)) | i |
                             i IN J /\ cm i (vec 0) IN W}))) h' /\
                 h'(&1) = h'(&0) /\
                 homotopic_with (\r. r(&1) = r(&0))
                   (subtopology euclideanreal (real_interval[&0,&1]),
                    subtopology topZ W) h h'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(J:num->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `ccs_cutcap topX topZ J (e:num->real^3->A) (cp:num->real^3->B)
                            cm ff gg` THEN SIMP_TAC[ccs_cutcap];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b:real^3->B.
        IMAGE b (ball(vec 0,&2)) SUBSET W /\ open_in topZ (IMAGE b (ball(vec 0,&2))) /\
        homeomorphic_map (subtopology euclidean (ball(vec 0,&2)),
                          subtopology topZ (IMAGE b (ball(vec 0,&2)))) b
        ==> open_in (subtopology topZ W) (IMAGE b (ball(vec 0,&2))) /\
            homeomorphic_map
              (subtopology euclidean (ball(vec 0,&2)),
               subtopology (subtopology topZ W) (IMAGE b (ball(vec 0,&2)))) b`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THENL
     [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
      EXISTS_TAC `IMAGE (b:real^3->B) (ball(vec 0,&2))` THEN ASM SET_TAC[];
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
      SUBGOAL_THEN `W INTER IMAGE (b:real^3->B) (ball(vec 0,&2)) =
                    IMAGE b (ball(vec 0,&2))` SUBST1_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology topZ (W:B->bool)`; `h:real->B`;
                 `IMAGE (cp:num->real^3->B) {i | i IN J /\ cp i (vec 0) IN W} UNION
                  IMAGE (cm:num->real^3->B) {i | i IN J /\ cm i (vec 0) IN W}`;
                 `&2`; `&3 / &2`] CCS_LOOP_PUSH_OFF_BALLS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; DIMINDEX_3; ARITH;
                 FINITE_UNION; FINITE_IMAGE; FINITE_RESTRICT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "sub" MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                     `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                     `ff:A->B`; `gg:B->A`; `x:num`] CCS_CUTCAP_CHARTS) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                     `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                     `ff:A->B`; `gg:B->A`; `W:B->bool`; `x:num`; `y:real^3`]
                    CCS_CAP_IN_COMPONENT) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `x:num`; `x':num`] CCS_CUTCAP_CAPS_DISJOINT) THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `x':num`; `x:num`] CCS_CUTCAP_CAPS_DISJOINT) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `x:num = x'` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[DISJOINT_SYM] THEN
    UNDISCH_TAC `x:num = x'` THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h':real->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h':real->B` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PATH_IN_SUBTOPOLOGY] o
    check (fun th -> is_comb(concl th) && is_const(fst(strip_comb(concl th))) &&
                     fst(dest_const(fst(strip_comb(concl th)))) = "path_in" &&
                     can (find_term (fun t -> t = `h':real->B`)) (concl th))) THEN
  REWRITE_TAC[PATH_IN_SUBTOPOLOGY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_DIFF; CCS_IN_CAP_BALLS; NOT_EXISTS_THM] THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  ASM_CASES_TAC `(i:num) IN J` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN ASM_CASES_TAC `(cp:num->real^3->B) i (vec 0) IN W` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(cm:num->real^3->B) i (vec 0) IN W` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> t = `&3 / &2`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let CCS_CUTCAP_SC_TOP = prove
 (`!topX topZ J (e:num->real^3->A) (cp:num->real^3->B) cm ff gg.
        ccs_cutcap topX topZ J e cp cm ff gg /\
        hausdorff_space topX /\ hausdorff_space topZ /\
        locally_path_connected_space topX /\ locally_path_connected_space topZ /\
        (!i. i IN J
             ==> ~connected_component_of
                   (subtopology topX
                      (topspace topX DIFF IMAGE (e i) (sphere(vec 0,&1))))
                   (e i (&3 / &4 % basis 1)) (e i (&4 / &3 % basis 1))) /\
        (!U. U IN connected_components_of topX
             ==> simply_connected_space (subtopology topX U))
        ==> !W. W IN connected_components_of topZ
                ==> simply_connected_space (subtopology topZ W)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `W:B->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `locally_connected_space (topX:A topology) /\
                locally_connected_space (topZ:B topology)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`] CCS_PINCH_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:A->B` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `D = UNIONS {IMAGE ((cp:num->real^3->B) i) (cball(vec 0,&3 / &2)) | i |
                i IN J /\ cp i (vec 0) IN W} UNION
        UNIONS {IMAGE ((cm:num->real^3->B) i) (cball(vec 0,&3 / &2)) | i |
                i IN J /\ cm i (vec 0) IN W}` THEN
  SUBGOAL_THEN `path_connected_space (subtopology topZ (W:B->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CCS_COMPONENT_PATH_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!h. path_in (subtopology topZ W) h /\ h(&1) = h(&0)
        ==> ?h'. path_in (subtopology topZ (W DIFF D)) h' /\ h'(&1) = h'(&0) /\
                 homotopic_with (\r. r(&1) = r(&0))
                   (subtopology euclideanreal (real_interval[&0,&1]),
                    subtopology topZ W) h (h':real->B)`
  (LABEL_TAC "push") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                   `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                   `ff:A->B`; `gg:B->A`; `W:B->bool`; `h:real->B`]
                  CCS_LOOPS_INTO_DEEP) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(W:B->bool) DIFF D = {}` THENL
   [REWRITE_TAC[SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_LOOP_SOME] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real->B` THEN STRIP_TAC THEN
    USE_THEN "push" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `path_in (subtopology topZ W) (h:real->B)`)
            (ASSUME `(h:real->B)(&1) = h(&0)`))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h':real->B` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`subtopology topZ ({}:B->bool)`; `h':real->B`; `&0`]
                  TOPC_PATH_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; INTER_EMPTY; NOT_IN_EMPTY;
                    IN_REAL_INTERVAL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `z0:B` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN
   `!z. z IN W DIFF D
        ==> z IN topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm /\
            (gg:B->A) z IN ccs_piece topX J (e:num->real^3->A) (ff:A->B) W`
  (LABEL_TAC "zQ") THENL
   [X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:B) IN topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CCS_OFF_BALLS_OFF_CORES THEN
      MAP_EVERY EXISTS_TAC [`topX:A topology`; `e:num->real^3->A`; `ff:A->B`;
                            `gg:B->A`; `W:B->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:B) IN W DIFF D` THEN EXPAND_TAC "D" THEN
      REWRITE_TAC[IN_DIFF] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o funpow 5 CONJUNCT2 o MATCH_MP CCS_CUTCAP_FACTS) THEN
    DISCH_THEN(MP_TAC o SPEC `z:B`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[ccs_piece; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:B) IN W DIFF D` THEN SIMP_TAC[IN_DIFF];
    ALL_TAC] THEN
  MATCH_MP_TAC CCS_SC_FROM_PINCH THEN
  MAP_EVERY EXISTS_TAC
   [`W DIFF D:B->bool`; `topX:A topology`;
    `connected_component_of topX ((gg:B->A) z0)`; `gg:B->A`; `P:A->B`] THEN
  USE_THEN "zQ" (MP_TAC o C MATCH_MP (ASSUME `(z0:B) IN W DIFF D`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `topZ:B topology`; `J:num->bool`;
                 `e:num->real^3->A`; `cp:num->real^3->B`; `cm:num->real^3->B`;
                 `ff:A->B`; `gg:B->A`; `W:B->bool`] CCS_PIECE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `ccs_piece topX J (e:num->real^3->A) (ff:A->B) W SUBSET
    connected_component_of topX ((gg:B->A) z0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gg:B->A) z0 IN topspace topX` ASSUME_TAC THENL
   [UNDISCH_TAC `ccs_piece topX J (e:num->real^3->A) (ff:A->B) W SUBSET
                 topspace topX DIFF mfd_cut_spheres J e` THEN
    UNDISCH_TAC `(gg:B->A) z0 IN ccs_piece topX J (e:num->real^3->A) (ff:A->B) W` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF];
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->B) cm` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `ccs_cutcap topX topZ J (e:num->real^3->A) (cp:num->real^3->B)
                                cm ff gg` THEN
        REWRITE_TAC[ccs_cutcap; homeomorphic_maps] THEN STRIP_TAC THEN
        MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
        EXISTS_TAC `topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
        USE_THEN "zQ" (MP_TAC o C MATCH_MP (ASSUME `(z:B) IN W DIFF D`)) THEN
        SIMP_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      X_GEN_TAC `z:B` THEN STRIP_TAC THEN
      USE_THEN "zQ" (MP_TAC o C MATCH_MP (ASSUME `(z:B) IN W DIFF D`)) THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      UNDISCH_TAC `ccs_piece topX J (e:num->real^3->A) (ff:A->B) W SUBSET
                   connected_component_of topX ((gg:B->A) z0)` THEN
      SET_TAC[]];
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "push" ACCEPT_TAC]);;

(* The headline: cutting a closed smooth 3-manifold whose components are    *)
(* simply connected along neck spheres and capping keeps the components    *)
(* simply connected.  Compactness of X is not needed.                      *)

let RFS_CUTCAP_SC = prove
 (`!u:A->bool v:B->bool. RFS_CUTCAP_SC_STATEMENT u v`,
  REWRITE_TAC[RFS_CUTCAP_SC_STATEMENT; rfs_components_sc] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CCS_CUTCAP_SC_TOP THEN
  MAP_EVERY EXISTS_TAC [`topX:A topology`; `J:num->bool`; `e:num->real^3->A`;
                        `cp:num->real^3->B`; `cm:num->real^3->B`;
                        `ff:A->B`; `gg:B->A`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CCS_CUTCAP_TOP THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`;
                          `atlasZ:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`]
                  GEO_MANIFOLD_LOCALLY_PATH_CONNECTED) THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`]
                  GEO_MANIFOLD_LOCALLY_PATH_CONNECTED) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `(:A)` SMT_SC_SPHERE_SEP) THEN
    REWRITE_TAC[APX_SC_SPHERE_SEP_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`topX:A topology`;
                               `atlasX:((A->bool)#(A->real^3))->bool`]) THEN
    ASM_REWRITE_TAC[apx_sphere_sep; apx_separates] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:num->real^3->A) i`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `mfd_cut_cap topX (atlasX:((A->bool)#(A->real^3))->bool) topZ
                               (atlasZ:((B->bool)#(B->real^3))->bool) J e cp cm ff gg` THEN
      REWRITE_TAC[mfd_cut_cap] THEN ASM_MESON_TAC[];
      SIMP_TAC[]]]);;

