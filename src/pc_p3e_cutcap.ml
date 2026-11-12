(* ========================================================================= *)
(* Unit pc_p3e_cutcap: step S2 of the proof of MT Lemma 15.11: the           *)
(* cut-and-capped manifold Z of a compact smooth 3-manifold X along finitely *)
(* many neck spheres, on the carrier of X, with fresh points nw i b x for    *)
(* the cap cores (b = T plus side, F minus side): the plus cap of neck i is  *)
(* the neck on 1 < |x| < 2 and nw i T on the closed unit ball, the minus cap *)
(* the neck composed with the inversion x / |x|^2 and nw i F.  Z has the     *)
(* final topology of the inclusion of X minus the cut spheres and the cap    *)
(* maps; it is a compact Hausdorff smooth manifold and mfd_cut_cap holds     *)
(* with the identity maps.                                                   *)
(* ========================================================================= *)

needs "src/pc_mfd_cut.ml";;
needs "src/pc_smt_radial.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The cap maps, the point set of Z and its topology.                        *)
(* ------------------------------------------------------------------------- *)

let p3e_ccp = new_definition
 `p3e_ccp (e:num->real^3->B) (nw:num->bool->real^3->B) (i:num) (x:real^3) =
    if norm x <= &1 then nw i T x else e i x`;;

let p3e_ccm = new_definition
 `p3e_ccm (e:num->real^3->B) (nw:num->bool->real^3->B) (i:num) (x:real^3) =
    if norm x <= &1 then nw i F x else e i (inv(norm x pow 2) % x)`;;

let p3e_czs = new_definition
 `p3e_czs (topX:B topology) (J:num->bool) (e:num->real^3->B)
          (nw:num->bool->real^3->B) =
    (topspace topX DIFF mfd_cut_spheres J e) UNION
    mfd_cut_cores J (p3e_ccp e nw) (p3e_ccm e nw)`;;

let p3e_copen = new_definition
 `p3e_copen (topX:B topology) (J:num->bool) (e:num->real^3->B)
            (nw:num->bool->real^3->B) (U:B->bool) <=>
    U SUBSET p3e_czs topX J e nw /\
    open_in topX (U INTER (topspace topX DIFF mfd_cut_spheres J e)) /\
    !i. i IN J
        ==> open {x | x IN ball(vec 0,&2) /\ p3e_ccp e nw i x IN U} /\
            open {x | x IN ball(vec 0,&2) /\ p3e_ccm e nw i x IN U}`;;

let p3e_ctop = new_definition
 `p3e_ctop (topX:B topology) (J:num->bool) (e:num->real^3->B)
           (nw:num->bool->real^3->B) =
    topology (p3e_copen topX J e nw)`;;

let P3E_COPEN_ISTOPOLOGY = prove
 (`!(topX:B topology) J e nw. istopology (p3e_copen topX J e nw)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[istopology; IN] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p3e_copen; EMPTY_SUBSET; INTER_EMPTY; OPEN_IN_EMPTY; NOT_IN_EMPTY;
                EMPTY_GSPEC; OPEN_EMPTY];
    MAP_EVERY X_GEN_TAC [`s:B->bool`; `t:B->bool`] THEN
    REWRITE_TAC[p3e_copen] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      SUBGOAL_THEN
       `(s INTER t) INTER (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B)) =
        (s INTER (topspace topX DIFF mfd_cut_spheres J e)) INTER
        (t INTER (topspace topX DIFF mfd_cut_spheres J e))`
      SUBST1_TAC THENL [SET_TAC[]; ASM_SIMP_TAC[OPEN_IN_INTER]];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      REWRITE_TAC[SET_RULE
       `{x:real^3 | x IN b /\ (f:real^3->B) x IN s INTER t} =
        {x | x IN b /\ f x IN s} INTER {x | x IN b /\ f x IN t}`] THEN
      ASM_SIMP_TAC[OPEN_INTER]];
    X_GEN_TAC `k:(B->bool)->bool` THEN REWRITE_TAC[SUBSET; IN] THEN DISCH_TAC THEN
    SUBGOAL_THEN `!s:B->bool. s IN k ==> p3e_copen topX J e nw s` (LABEL_TAC "K") THENL
     [ASM_REWRITE_TAC[IN]; ALL_TAC] THEN
    REWRITE_TAC[p3e_copen] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET] THEN X_GEN_TAC `s:B->bool` THEN DISCH_TAC THEN
      USE_THEN "K" (MP_TAC o SPEC `s:B->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[p3e_copen]];
      SUBGOAL_THEN
       `UNIONS k INTER (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B)) =
        UNIONS {s INTER (topspace topX DIFF mfd_cut_spheres J e) | s IN k}`
      SUBST1_TAC THENL
       [REWRITE_TAC[INTER_UNIONS] THEN SET_TAC[];
        MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
        X_GEN_TAC `s:B->bool` THEN DISCH_TAC THEN
        USE_THEN "K" (MP_TAC o SPEC `s:B->bool`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[p3e_copen]]];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `{x | x IN ball(vec 0,&2) /\ p3e_ccp e nw i x IN UNIONS k} =
          UNIONS {{x | x IN ball(vec 0,&2) /\ p3e_ccp (e:num->real^3->B) nw i x IN s} |
                  s IN k}`
        SUBST1_TAC THENL [REWRITE_TAC[UNIONS_GSPEC; IN_UNIONS] THEN SET_TAC[]; ALL_TAC];
        SUBGOAL_THEN
         `{x | x IN ball(vec 0,&2) /\ p3e_ccm e nw i x IN UNIONS k} =
          UNIONS {{x | x IN ball(vec 0,&2) /\ p3e_ccm (e:num->real^3->B) nw i x IN s} |
                  s IN k}`
        SUBST1_TAC THENL [REWRITE_TAC[UNIONS_GSPEC; IN_UNIONS] THEN SET_TAC[]; ALL_TAC]] THEN
      (MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
       X_GEN_TAC `s:B->bool` THEN DISCH_TAC THEN
       USE_THEN "K" (MP_TAC o SPEC `s:B->bool`) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[p3e_copen] THEN ASM_SIMP_TAC[]])]]);;

let P3E_CTOP_OPEN = prove
 (`!(topX:B topology) J e nw U.
     open_in (p3e_ctop topX J e nw) U <=> p3e_copen topX J e nw U`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3e_ctop] THEN
  MP_TAC(SPECL [`topX:B topology`; `J:num->bool`; `e:num->real^3->B`;
                `nw:num->bool->real^3->B`] P3E_COPEN_ISTOPOLOGY) THEN
  REWRITE_TAC[CONJUNCT2 topology_tybij] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The input data and the point-set facts.  p3e_cutdata: X is                *)
(* a compact Hausdorff smooth 3-manifold, J finite, e i neck charts with    *)
(* disjoint annulus(1/2,2) images, nw an injective fresh-point map.          *)
(* ------------------------------------------------------------------------- *)

let p3e_cutdata = new_definition
 `p3e_cutdata (topX:B topology) (atlasX:((B->bool)#(B->real^3))->bool) (J:num->bool)
              (e:num->real^3->B) (nw:num->bool->real^3->B) <=>
    hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\ compact_space topX /\
    FINITE J /\
    (!i. i IN J ==> mfd_neck_chart topX atlasX (e i)) /\
    (!i j. i IN J /\ j IN J /\ ~(i = j)
           ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                        (IMAGE (e j) (annulus (&1 / &2) (&2)))) /\
    (!i b x. ~(nw i b x IN topspace topX)) /\
    (!i b x j c y. nw i b x = nw j c y ==> i = j /\ (b <=> c) /\ x = y)`;;

let P3E_ANNULUS_HALF_TWO = prove
 (`!x:real^3. x IN annulus (&1 / &2) (&2) <=> &1 / &2 < norm x /\ norm x < &2`,
  REWRITE_TAC[annulus; IN_ELIM_THM]);;

let P3E_INVERSION_NORM = prove
 (`!x:real^3. ~(x = vec 0) ==> norm(inv(norm x pow 2) % x) = inv(norm x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; CONV_TAC REAL_FIELD]);;

let P3E_INVERSION_INVOL = prove
 (`!x:real^3. ~(x = vec 0)
              ==> inv(norm(inv(norm x pow 2) % x) pow 2) % (inv(norm x pow 2) % x) = x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[P3E_INVERSION_NORM] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(inv(norm(x:real^3)) pow 2) * inv(norm x pow 2) = &1`
    (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
  UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD);;

let P3E_CUTDATA_NECK = prove
 (`!(topX:B topology) atlasX J e nw i.
     p3e_cutdata topX atlasX J e nw /\ i IN J
     ==> (!x. x IN annulus (&1 / &2) (&2) ==> e i x IN topspace topX) /\
         (!x y. x IN annulus (&1 / &2) (&2) /\ y IN annulus (&1 / &2) (&2) /\
                e i x = e i y ==> x = y) /\
         (!t. open t /\ t SUBSET annulus (&1 / &2) (&2)
              ==> open_in topX (IMAGE (e i) t)) /\
         (!k. compact k /\ k SUBSET annulus (&1 / &2) (&2)
              ==> compact_in topX (IMAGE (e i) k)) /\
         continuous_map (subtopology euclidean (annulus (&1 / &2) (&2)),topX) (e i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3e_cutdata] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param topX atlasX (annulus (&1 / &2) (&2)) ((e:num->real^3->B) i)`
  ASSUME_TAC THENL [ASM_MESON_TAC[mfd_neck_chart]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':B->real^3` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    ASM_MESON_TAC[MFD_PARAM_INJ];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`;
                          `annulus (&1 / &2) (&2):real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`;
                          `annulus (&1 / &2) (&2):real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The cut spheres (compact, closed), the cores (fresh points)               *)
(* and the collar values of the cap maps.                                    *)
(* ------------------------------------------------------------------------- *)

let P3E_CUT_SPHERES_COMPACT = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw
     ==> compact_in topX (mfd_cut_spheres J e) /\
         closed_in topX (mfd_cut_spheres J e) /\
         mfd_cut_spheres J e SUBSET topspace topX`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `compact_in topX (mfd_cut_spheres J (e:num->real^3->B))` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_cut_spheres] THEN MATCH_MP_TAC COMPACT_IN_UNIONS THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_MESON_TAC[p3e_cutdata];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`] P3E_CUTDATA_NECK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o el 3 o CONJUNCTS) THEN
    REWRITE_TAC[COMPACT_SPHERE; SUBSET; IN_SPHERE_0; P3E_ANNULUS_HALF_TWO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_MESON_TAC[p3e_cutdata];
    ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]]);;

let P3E_CCP_COLLAR = prove
 (`!(e:num->real^3->B) nw i x.
     &1 < norm x ==> p3e_ccp e nw i x = e i x`,
  SIMP_TAC[p3e_ccp; GSYM REAL_NOT_LT]);;

let P3E_CCM_COLLAR = prove
 (`!(e:num->real^3->B) nw i x.
     &1 < norm x ==> p3e_ccm e nw i x = e i (inv(norm x pow 2) % x)`,
  SIMP_TAC[p3e_ccm; GSYM REAL_NOT_LT]);;

let P3E_CCP_CORE = prove
 (`!(e:num->real^3->B) nw i x.
     norm x <= &1 ==> p3e_ccp e nw i x = nw i T x`,
  SIMP_TAC[p3e_ccp]);;

let P3E_CCM_CORE = prove
 (`!(e:num->real^3->B) nw i x.
     norm x <= &1 ==> p3e_ccm e nw i x = nw i F x`,
  SIMP_TAC[p3e_ccm]);;

let P3E_CUT_CORES = prove
 (`!(e:num->real^3->B) nw J p.
     p IN mfd_cut_cores J (p3e_ccp e nw) (p3e_ccm e nw) <=>
     ?i b x. i IN J /\ norm x <= &1 /\ p = nw i b x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MFD_CUT_CORES] THEN EQ_TAC THEN STRIP_TAC THENL
   [ASM_MESON_TAC[P3E_CCP_CORE];
    ASM_MESON_TAC[P3E_CCM_CORE];
    MAP_EVERY EXISTS_TAC [`i:num`; `x:real^3`] THEN
    ASM_SIMP_TAC[P3E_CCP_CORE; P3E_CCM_CORE] THEN
    ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[]]);;

let P3E_CORES_FRESH = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw
     ==> DISJOINT (topspace topX) (mfd_cut_cores J (p3e_ccp e nw) (p3e_ccm e nw))`,
  REWRITE_TAC[p3e_cutdata; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; P3E_CUT_CORES] THEN
  MESON_TAC[]);;

let P3E_NECK_OFF_SPHERES = prove
 (`!(topX:B topology) atlasX J e nw i x.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\
     x IN annulus (&1 / &2) (&2) /\ ~(norm x = &1)
     ==> e i x IN topspace topX DIFF mfd_cut_spheres J e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P3E_ANNULUS_HALF_TWO] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `i:num`] P3E_CUTDATA_NECK) THEN
  ASM_REWRITE_TAC[P3E_ANNULUS_HALF_TWO] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_DIFF; IN_MFD_CUT_SPHERES] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`j:num`; `y:real^3`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `j:num = i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `x:real^3 = y` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    REWRITE_TAC[p3e_cutdata] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`] o el 5 o CONJUNCTS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:num->real^3->B) i x` o
      REWRITE_RULE[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE]) THEN
    MATCH_MP_TAC(TAUT `p /\ q ==> ~(p /\ q) ==> F`) THEN CONJ_TAC THENL
     [EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[P3E_ANNULUS_HALF_TWO];
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[P3E_ANNULUS_HALF_TWO] THEN
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Equalities between values of the neck maps, the fresh                     *)
(* points and the cap maps (all the identifications of Z).                  *)
(* ------------------------------------------------------------------------- *)

let P3E_NECK_EQ = prove
 (`!(topX:B topology) atlasX J e nw i j x y.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ j IN J /\
     x IN annulus (&1 / &2) (&2) /\ y IN annulus (&1 / &2) (&2)
     ==> (e i x = e j y <=> i = j /\ x = y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN DISCH_TAC THEN
  ASM_CASES_TAC `i:num = j` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `j:num`] P3E_CUTDATA_NECK) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    REWRITE_TAC[p3e_cutdata] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`] o el 5 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:num->real^3->B) i x`) THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]]);;

let P3E_NW_NOT_NECK = prove
 (`!(topX:B topology) atlasX J e nw i j b x y.
     p3e_cutdata topX atlasX J e nw /\ j IN J /\ y IN annulus (&1 / &2) (&2)
     ==> ~(nw i b x = e j y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `j:num`] P3E_CUTDATA_NECK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
  REWRITE_TAC[p3e_cutdata] THEN ASM_MESON_TAC[]);;

let P3E_NW_EQ = prove
 (`!(topX:B topology) atlasX J e nw i b x j c y.
     p3e_cutdata topX atlasX J e nw
     ==> (nw i b x = nw j c y <=> i = j /\ (b <=> c) /\ x = y)`,
  REWRITE_TAC[p3e_cutdata] THEN MESON_TAC[]);;

(* The values of the cap maps on ball(0,2): a fresh point on the closed unit *)
(* ball, a neck point with parameter in annulus(1,2) (plus side) or in       *)
(* annulus(1/2,1) (minus side) on the collar.                                *)

let P3E_CAP_VALUES = prove
 (`!(e:num->real^3->B) nw i x.
     x IN ball(vec 0,&2)
     ==> (norm x <= &1 /\ p3e_ccp e nw i x = nw i T x /\
          p3e_ccm e nw i x = nw i F x) \/
         (&1 < norm x /\ norm x < &2 /\ p3e_ccp e nw i x = e i x /\
          p3e_ccm e nw i x = e i (inv(norm x pow 2) % x) /\
          &1 / &2 < norm(inv(norm x pow 2) % x) /\ norm(inv(norm x pow 2) % x) < &1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
  ASM_CASES_TAC `norm(x:real^3) <= &1` THENL
   [DISJ1_TAC THEN ASM_SIMP_TAC[P3E_CCP_CORE; P3E_CCM_CORE];
    DISJ2_TAC THEN
    SUBGOAL_THEN `&1 < norm(x:real^3)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[P3E_CCP_COLLAR; P3E_CCM_COLLAR] THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `&1 < norm(x:real^3)` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[P3E_INVERSION_NORM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `inv(&2) < y ==> &1 / &2 < y`) THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The cap maps take ball(0,2) into the point set of Z; the                  *)
(* preimages under the cap maps of sets of old points; the open sets of X   *)
(* inside X minus the cut spheres are open in Z.                            *)
(* ------------------------------------------------------------------------- *)

let P3E_CCP_IN_CZS = prove
 (`!(topX:B topology) atlasX J e nw i x.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ x IN ball(vec 0,&2)
     ==> p3e_ccp e nw i x IN p3e_czs topX J e nw /\
         p3e_ccm e nw i x IN p3e_czs topX J e nw`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`; `x:real^3`]
    P3E_CAP_VALUES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[p3e_czs; IN_UNION] THENL
   [CONJ_TAC THEN DISJ2_TAC THEN REWRITE_TAC[P3E_CUT_CORES] THEN ASM_MESON_TAC[];
    CONJ_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC P3E_NECK_OFF_SPHERES THEN
    MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`;
                          `nw:num->bool->real^3->B`] THEN
    ASM_REWRITE_TAC[P3E_ANNULUS_HALF_TWO] THEN ASM_REAL_ARITH_TAC]);;

let P3E_CZS_OLD = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw
     ==> p3e_czs topX J e nw INTER (topspace topX DIFF mfd_cut_spheres J e) =
         topspace topX DIFF mfd_cut_spheres J e /\
         p3e_czs topX J e nw DIFF mfd_cut_cores J (p3e_ccp e nw) (p3e_ccm e nw) =
         topspace topX DIFF mfd_cut_spheres J e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3E_CORES_FRESH) THEN
  REWRITE_TAC[p3e_czs] THEN SET_TAC[]);;

(* Preimages of sets of old points: only the collar annulus(1,2) maps there. *)

let P3E_CAP_PREIMAGE_OLD = prove
 (`!(topX:B topology) atlasX J e nw i V.
     p3e_cutdata topX atlasX J e nw /\ V SUBSET topspace topX
     ==> {x | x IN ball(vec 0,&2) /\ p3e_ccp e nw i x IN V} =
         {x | x IN annulus (&1) (&2) /\ e i x IN V} /\
         {x | x IN ball(vec 0,&2) /\ p3e_ccm e nw i x IN V} =
         {x | x IN annulus (&1) (&2) /\ e i (inv(norm x pow 2) % x) IN V}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!b x. ~((nw:num->bool->real^3->B) i b x IN V)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    REWRITE_TAC[p3e_cutdata] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN
  (ASM_CASES_TAC `x IN ball(vec 0:real^3,&2)` THENL
    [MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`;
                    `x:real^3`] P3E_CAP_VALUES) THEN
     ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_SIMP_TAC[REAL_ARITH `n <= &1 ==> ~(&1 < n)`];
     SUBGOAL_THEN `~(norm(x:real^3) < &2)` ASSUME_TAC THENL
      [ASM_MESON_TAC[IN_BALL_0]; ALL_TAC] THEN
     ASM_REWRITE_TAC[annulus; IN_ELIM_THM]]));;

let P3E_COPEN_OLD = prove
 (`!(topX:B topology) atlasX J e nw V.
     p3e_cutdata topX atlasX J e nw /\ open_in topX V /\
     V SUBSET topspace topX DIFF mfd_cut_spheres J e
     ==> p3e_copen topX J e nw V`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3e_copen] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p3e_czs] THEN ASM SET_TAC[];
    SUBGOAL_THEN `V INTER (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B)) = V`
      (fun th -> ASM_REWRITE_TAC[th]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `i:num`; `V:B->bool`] P3E_CAP_PREIMAGE_OLD) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `i:num`] P3E_CUTDATA_NECK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open {y | y IN annulus (&1 / &2) (&2) /\ (e:num->real^3->B) i y IN V}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    REWRITE_TAC[OPEN_ANNULUS] THEN
    MP_TAC(ISPECL [`(e:num->real^3->B) i`;
                   `subtopology euclidean (annulus (&1 / &2) (&2):real^3->bool)`;
                   `topX:B topology`; `V:B->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN annulus (&1) (&2)
               ==> ~(x = vec 0) /\ inv(norm x pow 2) % x IN annulus (&1 / &2) (&2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `&1 < norm(x:real^3)` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[P3E_INVERSION_NORM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `inv(&2) < y ==> &1 / &2 < y`) THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `y < &1 ==> y < &2`) THEN
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `{x | x IN annulus (&1) (&2) /\ (e:num->real^3->B) i x IN V} =
      annulus (&1) (&2) INTER
      {y | y IN annulus (&1 / &2) (&2) /\ (e:num->real^3->B) i y IN V}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_CASES_TAC `(e:num->real^3->B) i x IN V` THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[OPEN_ANNULUS]];
    SUBGOAL_THEN
     `{x | x IN annulus (&1) (&2) /\
           (e:num->real^3->B) i (inv(norm x pow 2) % x) IN V} =
      {x | x IN annulus (&1) (&2) /\
           (\x:real^3. inv(norm x pow 2) % x) x IN
           {y | y IN annulus (&1 / &2) (&2) /\ (e:num->real^3->B) i y IN V}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS; SMOOTH_MAP_ON_INVERSION] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The topology of Z on old points.  The point set p3e_czs is                *)
(* open (so it is the topspace), X minus the cut spheres is open in Z, open  *)
(* sets of X there are open in Z, and both subspace topologies agree.       *)
(* ------------------------------------------------------------------------- *)

let P3E_OLD_OPEN_IN_X = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw
     ==> open_in topX (topspace topX DIFF mfd_cut_spheres J e)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
  REWRITE_TAC[OPEN_IN_TOPSPACE] THEN ASM_MESON_TAC[P3E_CUT_SPHERES_COMPACT]);;

let P3E_COPEN_CZS = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw ==> p3e_copen topX J e nw (p3e_czs topX J e nw)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3e_copen; SUBSET_REFL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP P3E_CZS_OLD th)]) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[P3E_OLD_OPEN_IN_X]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{x | x IN ball(vec 0,&2) /\
         p3e_ccp (e:num->real^3->B) nw i x IN p3e_czs (topX:B topology) J e nw} =
    ball(vec 0,&2) /\
    {x | x IN ball(vec 0,&2) /\ p3e_ccm e nw i x IN p3e_czs topX J e nw} =
    ball(vec 0:real^3,&2)`
    (fun th -> REWRITE_TAC[th; OPEN_BALL]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[P3E_CCP_IN_CZS]);;

let P3E_CTOP_TOPSPACE = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw
     ==> topspace (p3e_ctop topX J e nw) = p3e_czs topX J e nw`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[topspace; P3E_CTOP_OPEN] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN SIMP_TAC[p3e_copen];
    MATCH_MP_TAC(SET_RULE `(s:B->bool) IN f ==> s SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[P3E_COPEN_CZS]]);;

let P3E_CTOP_OPEN_OLD = prove
 (`!(topX:B topology) atlasX J e nw V.
     p3e_cutdata topX atlasX J e nw /\ open_in topX V /\
     V SUBSET topspace topX DIFF mfd_cut_spheres J e
     ==> open_in (p3e_ctop topX J e nw) V`,
  REWRITE_TAC[P3E_CTOP_OPEN] THEN MESON_TAC[P3E_COPEN_OLD]);;

let P3E_CTOP_OLD = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw
     ==> open_in (p3e_ctop topX J e nw) (topspace topX DIFF mfd_cut_spheres J e) /\
         subtopology (p3e_ctop topX J e nw) (topspace topX DIFF mfd_cut_spheres J e) =
         subtopology topX (topspace topX DIFF mfd_cut_spheres J e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3E_OLD_OPEN_IN_X) THEN CONJ_TAC THENL
   [MATCH_MP_TAC P3E_CTOP_OPEN_OLD THEN
    EXISTS_TAC `atlasX:((B->bool)#(B->real^3))->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[TOPOLOGY_EQ; OPEN_IN_SUBTOPOLOGY; P3E_CTOP_OPEN] THEN
  X_GEN_TAC `u:B->bool` THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t:B->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t INTER (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B))` THEN
  (CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]]) THENL
   [ASM_MESON_TAC[p3e_copen];
    MATCH_MP_TAC P3E_COPEN_OLD THEN
    EXISTS_TAC `atlasX:((B->bool)#(B->real^3))->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* The cap maps on ball(0,2) are injective and the caps are                  *)
(* pairwise disjoint (plus caps of distinct necks, minus caps of distinct    *)
(* necks, and every plus cap with every minus cap).                          *)
(* ------------------------------------------------------------------------- *)

let P3E_IN_ANNULUS_HALF_TWO = prove
 (`!x:real^3. &1 < norm x /\ norm x < &2 ==> x IN annulus (&1 / &2) (&2)`,
  REWRITE_TAC[P3E_ANNULUS_HALF_TWO] THEN REAL_ARITH_TAC);;

let P3E_INV_IN_ANNULUS_HALF_TWO = prove
 (`!x:real^3. &1 / &2 < norm(inv(norm x pow 2) % x) /\ norm(inv(norm x pow 2) % x) < &1
              ==> inv(norm x pow 2) % x IN annulus (&1 / &2) (&2)`,
  REWRITE_TAC[P3E_ANNULUS_HALF_TWO] THEN REAL_ARITH_TAC);;

let P3E_CCP_EQ = prove
 (`!(topX:B topology) atlasX J e nw i j x y.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ j IN J /\
     x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2)
     ==> (p3e_ccp e nw j x = p3e_ccp e nw i y <=> j = i /\ x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `j:num`; `x:real^3`]
    P3E_CAP_VALUES) THEN
  MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`; `y:real^3`]
    P3E_CAP_VALUES) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[P3E_NW_EQ];
    DISCH_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`; `j:num`; `T`; `y:real^3`; `x:real^3`] P3E_NW_NOT_NECK) THEN
    ASM_SIMP_TAC[P3E_IN_ANNULUS_HALF_TWO];
    DISCH_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `j:num`; `i:num`; `T`; `x:real^3`; `y:real^3`] P3E_NW_NOT_NECK) THEN
    ASM_SIMP_TAC[P3E_IN_ANNULUS_HALF_TWO];
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `j:num`; `i:num`; `x:real^3`; `y:real^3`] P3E_NECK_EQ) THEN
    ASM_SIMP_TAC[P3E_IN_ANNULUS_HALF_TWO]]);;

let P3E_CCM_EQ = prove
 (`!(topX:B topology) atlasX J e nw i j x y.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ j IN J /\
     x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2)
     ==> (p3e_ccm e nw j x = p3e_ccm e nw i y <=> j = i /\ x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `j:num`; `x:real^3`]
    P3E_CAP_VALUES) THEN
  MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`; `y:real^3`]
    P3E_CAP_VALUES) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[P3E_NW_EQ];
    DISCH_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`; `j:num`; `F`; `y:real^3`;
                  `inv(norm(x:real^3) pow 2) % x`] P3E_NW_NOT_NECK) THEN
    ASM_SIMP_TAC[P3E_INV_IN_ANNULUS_HALF_TWO];
    DISCH_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `j:num`; `i:num`; `F`; `x:real^3`;
                  `inv(norm(y:real^3) pow 2) % y`] P3E_NW_NOT_NECK) THEN
    ASM_SIMP_TAC[P3E_INV_IN_ANNULUS_HALF_TWO];
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `j:num`; `i:num`; `inv(norm(x:real^3) pow 2) % x`;
                  `inv(norm(y:real^3) pow 2) % y`] P3E_NECK_EQ) THEN
    ASM_SIMP_TAC[P3E_INV_IN_ANNULUS_HALF_TWO] THEN
    DISCH_THEN(K ALL_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0) /\ ~(y:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_TAC THENL
       [UNDISCH_TAC `&1 < norm(x:real^3)`; UNDISCH_TAC `&1 < norm(y:real^3)`] THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\z:real^3. inv(norm z pow 2) % z`) THEN
    ASM_SIMP_TAC[P3E_INVERSION_INVOL]]);;

let P3E_CCP_NEQ_CCM = prove
 (`!(topX:B topology) atlasX J e nw i j x y.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ j IN J /\
     x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2)
     ==> ~(p3e_ccp e nw j x = p3e_ccm e nw i y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `j:num`; `x:real^3`]
    P3E_CAP_VALUES) THEN
  MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`; `y:real^3`]
    P3E_CAP_VALUES) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[P3E_NW_EQ];
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`; `j:num`; `F`; `y:real^3`; `x:real^3`] P3E_NW_NOT_NECK) THEN
    ASM_SIMP_TAC[P3E_IN_ANNULUS_HALF_TWO] THEN MESON_TAC[];
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `j:num`; `i:num`; `T`; `x:real^3`;
                  `inv(norm(y:real^3) pow 2) % y`] P3E_NW_NOT_NECK) THEN
    ASM_SIMP_TAC[P3E_INV_IN_ANNULUS_HALF_TWO];
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `j:num`; `i:num`; `x:real^3`;
                  `inv(norm(y:real^3) pow 2) % y`] P3E_NECK_EQ) THEN
    ASM_SIMP_TAC[P3E_IN_ANNULUS_HALF_TWO; P3E_INV_IN_ANNULUS_HALF_TWO] THEN
    DISCH_THEN(K ALL_TAC) THEN STRIP_TAC THEN
    UNDISCH_TAC `&1 < norm(x:real^3)` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Images of open subsets of ball(0,2) under the cap maps are                *)
(* open in Z (their old part is a neck image of an open set, their preimages *)
(* under the cap maps are the set itself or empty).                          *)
(* ------------------------------------------------------------------------- *)

let P3E_INVERSION_IMAGE_OPEN = prove
 (`!W:real^3->bool.
     open W /\ W SUBSET annulus (&1) (&2)
     ==> open (IMAGE (\x. inv(norm x pow 2) % x) W) /\
         IMAGE (\x. inv(norm x pow 2) % x) W SUBSET annulus (&1 / &2) (&2)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN W ==> ~(x = vec 0) /\ &1 < norm x /\ norm x < &2`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 < norm(x:real^3) /\ norm x < &2` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `W SUBSET annulus (&1) (&2):real^3->bool` THEN
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `&1 < norm(x:real^3)` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; annulus; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[P3E_INVERSION_NORM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `inv(&2) < y ==> &1 / &2 < y`) THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `y < &1 ==> y < &2`) THEN
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]]] THEN
  (* the image of W is its preimage under the inversion on R^3 - 0 *)
  SUBGOAL_THEN
   `IMAGE (\x:real^3. inv(norm x pow 2) % x) W =
    {y | y IN (:real^3) DELETE vec 0 /\ (\x. inv(norm x pow 2) % x) y IN W}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[P3E_INVERSION_INVOL] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_POW_EQ_0; NORM_EQ_0];
      STRIP_TAC THEN EXISTS_TAC `inv(norm(y:real^3) pow 2) % y` THEN
      ASM_SIMP_TAC[P3E_INVERSION_INVOL]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
  SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS; SMOOTH_MAP_ON_INVERSION] THEN
  SET_TAC[]);;

(* The preimages of cap images under the cap maps. *)

let P3E_CAP_PREIMAGES = prove
 (`!(topX:B topology) atlasX J e nw i j W.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ j IN J /\ W SUBSET ball(vec 0,&2)
     ==> {x | x IN ball(vec 0,&2) /\ p3e_ccp e nw j x IN IMAGE (p3e_ccp e nw i) W} =
         (if j = i then W else {}) /\
         {x | x IN ball(vec 0,&2) /\ p3e_ccm e nw j x IN IMAGE (p3e_ccp e nw i) W} = {} /\
         {x | x IN ball(vec 0,&2) /\ p3e_ccp e nw j x IN IMAGE (p3e_ccm e nw i) W} = {} /\
         {x | x IN ball(vec 0,&2) /\ p3e_ccm e nw j x IN IMAGE (p3e_ccm e nw i) W} =
         (if j = i then W else {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN W ==> x IN ball(vec 0,&2)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN
  ASM_CASES_TAC `j:num = i` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THENL
   [ASM_MESON_TAC[P3E_CCP_EQ];
    ASM_MESON_TAC[P3E_CCP_EQ];
    ASM_MESON_TAC[P3E_CCP_NEQ_CCM];
    ASM_MESON_TAC[P3E_CCP_NEQ_CCM];
    ASM_MESON_TAC[P3E_CCP_NEQ_CCM];
    ASM_MESON_TAC[P3E_CCP_NEQ_CCM];
    ASM_MESON_TAC[P3E_CCM_EQ];
    ASM_MESON_TAC[P3E_CCM_EQ]]);;

(* The old points of a cap image: a neck image of an open subset of the    *)
(* neck domain (through the inversion for minus caps).                     *)

let P3E_CAP_IMAGE_OLD = prove
 (`!(topX:B topology) atlasX J e nw i W.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ W SUBSET ball(vec 0,&2)
     ==> IMAGE (p3e_ccp e nw i) W INTER (topspace topX DIFF mfd_cut_spheres J e) =
         IMAGE (e i) (W INTER annulus (&1) (&2)) /\
         IMAGE (p3e_ccm e nw i) W INTER (topspace topX DIFF mfd_cut_spheres J e) =
         IMAGE (e i) (IMAGE (\x. inv(norm x pow 2) % x) (W INTER annulus (&1) (&2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!b x. ~((nw:num->bool->real^3->B) i b x IN topspace topX)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    REWRITE_TAC[p3e_cutdata] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_DIFF] THEN CONJ_TAC THEN
  X_GEN_TAC `p:B` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
                               STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`; `x:real^3`]
      P3E_CAP_VALUES) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THENL
     [ASM_MESON_TAC[];
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real^3) IN annulus (&1) (&2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[P3E_CCP_COLLAR] THEN CONJ_TAC THENL
     [EXISTS_TAC `x:real^3` THEN ASM_SIMP_TAC[P3E_CCP_COLLAR];
      REWRITE_TAC[GSYM IN_DIFF] THEN MATCH_MP_TAC P3E_NECK_OFF_SPHERES THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`;
                            `nw:num->bool->real^3->B`] THEN
      ASM_REWRITE_TAC[P3E_ANNULUS_HALF_TWO] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
                               STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`; `x:real^3`]
      P3E_CAP_VALUES) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THENL
     [ASM_MESON_TAC[];
      EXISTS_TAC `inv(norm(x:real^3) pow 2) % x` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; EXISTS_TAC `x:real^3` THEN
        ASM_REWRITE_TAC[annulus; IN_ELIM_THM]]];
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)))) THEN
    UNDISCH_TAC `(x:real^3) IN annulus (&1) (&2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `&1 < norm(x:real^3)` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 / &2 < norm(inv(norm(x:real^3) pow 2) % x) /\
                  norm(inv(norm(x:real^3) pow 2) % x) < &1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[P3E_INVERSION_NORM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `inv(&2) < y ==> &1 / &2 < y`) THEN
        MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `x:real^3` THEN ASM_SIMP_TAC[P3E_CCM_COLLAR];
      REWRITE_TAC[GSYM IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P3E_NECK_OFF_SPHERES THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`;
                            `nw:num->bool->real^3->B`] THEN
      ASM_REWRITE_TAC[P3E_ANNULUS_HALF_TWO] THEN ASM_REAL_ARITH_TAC]]);;

let P3E_CAP_IMAGE_OPEN = prove
 (`!(topX:B topology) atlasX J e nw i W.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ open W /\ W SUBSET ball(vec 0,&2)
     ==> open_in (p3e_ctop topX J e nw) (IMAGE (p3e_ccp e nw i) W) /\
         open_in (p3e_ctop topX J e nw) (IMAGE (p3e_ccm e nw i) W)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[P3E_CTOP_OPEN; p3e_copen] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `i:num`; `W:real^3->bool`] P3E_CAP_IMAGE_OLD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `i:num`] P3E_CUTDATA_NECK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (W INTER annulus (&1) (&2):real^3->bool) /\
                W INTER annulus (&1) (&2) SUBSET annulus (&1) (&2)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; OPEN_ANNULUS; INTER_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPEC `W INTER annulus (&1) (&2):real^3->bool` P3E_INVERSION_IMAGE_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[P3E_CCP_IN_CZS; SUBSET];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTER; annulus; IN_ELIM_THM; P3E_ANNULUS_HALF_TWO] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`; `j:num`; `W:real^3->bool`] P3E_CAP_PREIMAGES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[OPEN_EMPTY] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[OPEN_EMPTY];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[P3E_CCP_IN_CZS; SUBSET];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`; `j:num`; `W:real^3->bool`] P3E_CAP_PREIMAGES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[OPEN_EMPTY] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[OPEN_EMPTY]]);;

let P3E_CAP_CONTINUOUS = prove
 (`!(topX:B topology) atlasX J e nw i.
     p3e_cutdata topX atlasX J e nw /\ i IN J
     ==> continuous_map (subtopology euclidean (ball(vec 0,&2)),p3e_ctop topX J e nw)
                        (p3e_ccp e nw i) /\
         continuous_map (subtopology euclidean (ball(vec 0,&2)),p3e_ctop topX J e nw)
                        (p3e_ccm e nw i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_CTOP_TOPSPACE th]) THEN
  REWRITE_TAC[P3E_CTOP_OPEN] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[P3E_CCP_IN_CZS];
    X_GEN_TAC `u:B->bool` THEN REWRITE_TAC[p3e_copen] THEN STRIP_TAC THEN
    MATCH_MP_TAC OPEN_SUBSET THEN CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[]];
    ASM_MESON_TAC[P3E_CCP_IN_CZS];
    X_GEN_TAC `u:B->bool` THEN REWRITE_TAC[p3e_copen] THEN STRIP_TAC THEN
    MATCH_MP_TAC OPEN_SUBSET THEN CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The complement of a closed 3/2-cap is open in Z, and Z is                 *)
(* Hausdorff.                                                                *)
(* ------------------------------------------------------------------------- *)

let P3E_COLLAR_IMAGE_CLOSED = prove
 (`!(topX:B topology) atlasX J e nw i a b.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ &1 / &2 < a /\ b < &2
     ==> closed_in topX (IMAGE (e i) {x:real^3 | a <= norm x /\ norm x <= b})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN
  CONJ_TAC THENL [ASM_MESON_TAC[p3e_cutdata]; ALL_TAC] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `i:num`] P3E_CUTDATA_NECK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o el 3 o CONJUNCTS) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `{x:real^3 | a <= norm x /\ norm x <= b} =
                  cball(vec 0,b) DIFF ball(vec 0,a)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; P3E_ANNULUS_HALF_TWO] THEN ASM_REAL_ARITH_TAC]);;

let P3E_CCP_OLD_PART = prove
 (`!(topX:B topology) atlasX J e nw i p.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\
     p IN topspace topX DIFF mfd_cut_spheres J e
     ==> (p IN IMAGE (p3e_ccp e nw i) (cball(vec 0,&3 / &2)) <=>
          p IN IMAGE (e i) {x:real^3 | &1 <= norm x /\ norm x <= &3 / &2})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_CBALL_0] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN EXISTS_TAC `x:real^3` THENL
   [ASM_CASES_TAC `norm(x:real^3) <= &1` THENL
     [UNDISCH_TAC `(p:B) IN topspace topX` THEN ASM_SIMP_TAC[P3E_CCP_CORE] THEN
      UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
      REWRITE_TAC[p3e_cutdata] THEN MESON_TAC[];
      ASM_SIMP_TAC[P3E_CCP_COLLAR; REAL_ARITH `~(n <= &1) ==> &1 < n`] THEN
      ASM_REAL_ARITH_TAC];
    ASM_CASES_TAC `norm(x:real^3) = &1` THENL
     [UNDISCH_TAC `~((p:B) IN mfd_cut_spheres J e)` THEN
      REWRITE_TAC[IN_MFD_CUT_SPHERES] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[P3E_CCP_COLLAR; REAL_ARITH `&1 <= n /\ ~(n = &1) ==> &1 < n`]]]);;

let P3E_CCM_OLD_PART = prove
 (`!(topX:B topology) atlasX J e nw i p.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\
     p IN topspace topX DIFF mfd_cut_spheres J e
     ==> (p IN IMAGE (p3e_ccm e nw i) (cball(vec 0,&3 / &2)) <=>
          p IN IMAGE (e i) {x:real^3 | &2 / &3 <= norm x /\ norm x <= &1})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_CBALL_0] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THENL
   [ASM_CASES_TAC `norm(x:real^3) <= &1` THENL
     [UNDISCH_TAC `(p:B) IN topspace topX` THEN ASM_SIMP_TAC[P3E_CCM_CORE] THEN
      UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
      REWRITE_TAC[p3e_cutdata] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 < norm(x:real^3)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `&1 < norm(x:real^3)` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `inv(norm(x:real^3) pow 2) % x` THEN
    ASM_SIMP_TAC[P3E_CCM_COLLAR; P3E_INVERSION_NORM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `inv(&3 / &2) <= y ==> &2 / &3 <= y`) THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_INV_LT_1 THEN
      ASM_REWRITE_TAC[]];
    ASM_CASES_TAC `norm(x:real^3) = &1` THENL
     [UNDISCH_TAC `~((p:B) IN mfd_cut_spheres J e)` THEN
      REWRITE_TAC[IN_MFD_CUT_SPHERES] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(x:real^3) /\ norm x < &1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM NORM_POS_LT]; ALL_TAC] THEN
    EXISTS_TAC `inv(norm(x:real^3) pow 2) % x` THEN
    ASM_SIMP_TAC[P3E_INVERSION_NORM] THEN
    SUBGOAL_THEN `&1 < inv(norm(x:real^3))` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_INV_1] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm(x:real^3)) <= &3 / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `y <= inv(&2 / &3) ==> y <= &3 / &2`) THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 < norm(inv(norm(x:real^3) pow 2) % x)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[P3E_INVERSION_NORM]; ALL_TAC] THEN
    ASM_SIMP_TAC[P3E_CCM_COLLAR; P3E_INVERSION_INVOL]]);;

let P3E_CCP_COMPLEMENT_OPEN = prove
 (`!(topX:B topology) atlasX J e nw i.
     p3e_cutdata topX atlasX J e nw /\ i IN J
     ==> open_in (p3e_ctop topX J e nw)
                 (p3e_czs topX J e nw DIFF IMAGE (p3e_ccp e nw i) (cball(vec 0,&3 / &2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[P3E_CTOP_OPEN; p3e_copen] THEN
  SUBGOAL_THEN `!x:real^3. x IN cball(vec 0,&3 / &2) ==> x IN ball(vec 0,&2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3E_OLD_OPEN_IN_X) THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[];
    SUBGOAL_THEN
     `(p3e_czs topX J e nw DIFF IMAGE (p3e_ccp e nw i) (cball(vec 0,&3 / &2))) INTER
      (topspace topX DIFF mfd_cut_spheres J e) =
      (topspace topX DIFF mfd_cut_spheres J e) DIFF
      IMAGE ((e:num->real^3->B) i) {x:real^3 | &1 <= norm x /\ norm x <= &3 / &2}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF] THEN X_GEN_TAC `p:B` THEN
      ASM_CASES_TAC `(p:B) IN topspace topX /\ ~(p IN mfd_cut_spheres J e)` THENL
       [MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                      `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                      `i:num`; `p:B`] P3E_CCP_OLD_PART) THEN
        ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `(p:B) IN p3e_czs topX J e nw` (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[p3e_czs; IN_UNION; IN_DIFF] THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]];
      MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P3E_COLLAR_IMAGE_CLOSED THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                            `nw:num->bool->real^3->B`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_CASES_TAC `j:num = i` THENL
       [SUBGOAL_THEN
         `{x | x IN ball(vec 0,&2) /\
               p3e_ccp (e:num->real^3->B) nw j x IN
               p3e_czs topX J e nw DIFF IMAGE (p3e_ccp e nw i) (cball(vec 0,&3 / &2))} =
          ball(vec 0,&2) DIFF cball(vec 0:real^3,&3 / &2)`
        SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_IMAGE] THEN
          X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `x IN ball(vec 0:real^3,&2)` THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[P3E_CCP_IN_CZS; P3E_CCP_EQ];
          SIMP_TAC[OPEN_DIFF; OPEN_BALL; CLOSED_CBALL]];
        SUBGOAL_THEN
         `{x | x IN ball(vec 0,&2) /\
               p3e_ccp (e:num->real^3->B) nw j x IN
               p3e_czs topX J e nw DIFF IMAGE (p3e_ccp e nw i) (cball(vec 0,&3 / &2))} =
          ball(vec 0:real^3,&2)`
        SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_IMAGE] THEN
          ASM_MESON_TAC[P3E_CCP_IN_CZS; P3E_CCP_EQ];
          REWRITE_TAC[OPEN_BALL]]];
      SUBGOAL_THEN
       `{x | x IN ball(vec 0,&2) /\
             p3e_ccm (e:num->real^3->B) nw j x IN
             p3e_czs topX J e nw DIFF IMAGE (p3e_ccp e nw i) (cball(vec 0,&3 / &2))} =
        ball(vec 0:real^3,&2)`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_IMAGE] THEN
        ASM_MESON_TAC[P3E_CCP_IN_CZS; P3E_CCP_NEQ_CCM];
        REWRITE_TAC[OPEN_BALL]]]]);;

let P3E_CCM_COMPLEMENT_OPEN = prove
 (`!(topX:B topology) atlasX J e nw i.
     p3e_cutdata topX atlasX J e nw /\ i IN J
     ==> open_in (p3e_ctop topX J e nw)
                 (p3e_czs topX J e nw DIFF IMAGE (p3e_ccm e nw i) (cball(vec 0,&3 / &2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[P3E_CTOP_OPEN; p3e_copen] THEN
  SUBGOAL_THEN `!x:real^3. x IN cball(vec 0,&3 / &2) ==> x IN ball(vec 0,&2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3E_OLD_OPEN_IN_X) THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[];
    SUBGOAL_THEN
     `(p3e_czs topX J e nw DIFF IMAGE (p3e_ccm e nw i) (cball(vec 0,&3 / &2))) INTER
      (topspace topX DIFF mfd_cut_spheres J e) =
      (topspace topX DIFF mfd_cut_spheres J e) DIFF
      IMAGE ((e:num->real^3->B) i) {x:real^3 | &2 / &3 <= norm x /\ norm x <= &1}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF] THEN X_GEN_TAC `p:B` THEN
      ASM_CASES_TAC `(p:B) IN topspace topX /\ ~(p IN mfd_cut_spheres J e)` THENL
       [MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                      `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                      `i:num`; `p:B`] P3E_CCM_OLD_PART) THEN
        ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `(p:B) IN p3e_czs topX J e nw` (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[p3e_czs; IN_UNION; IN_DIFF] THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]];
      MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P3E_COLLAR_IMAGE_CLOSED THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`; `J:num->bool`;
                            `nw:num->bool->real^3->B`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `{x | x IN ball(vec 0,&2) /\
             p3e_ccp (e:num->real^3->B) nw j x IN
             p3e_czs topX J e nw DIFF IMAGE (p3e_ccm e nw i) (cball(vec 0,&3 / &2))} =
        ball(vec 0:real^3,&2)`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_IMAGE] THEN
        ASM_MESON_TAC[P3E_CCP_IN_CZS; P3E_CCP_NEQ_CCM];
        REWRITE_TAC[OPEN_BALL]];
      ASM_CASES_TAC `j:num = i` THENL
       [SUBGOAL_THEN
         `{x | x IN ball(vec 0,&2) /\
               p3e_ccm (e:num->real^3->B) nw j x IN
               p3e_czs topX J e nw DIFF IMAGE (p3e_ccm e nw i) (cball(vec 0,&3 / &2))} =
          ball(vec 0,&2) DIFF cball(vec 0:real^3,&3 / &2)`
        SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_IMAGE] THEN
          X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `x IN ball(vec 0:real^3,&2)` THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[P3E_CCP_IN_CZS; P3E_CCM_EQ];
          SIMP_TAC[OPEN_DIFF; OPEN_BALL; CLOSED_CBALL]];
        SUBGOAL_THEN
         `{x | x IN ball(vec 0,&2) /\
               p3e_ccm (e:num->real^3->B) nw j x IN
               p3e_czs topX J e nw DIFF IMAGE (p3e_ccm e nw i) (cball(vec 0,&3 / &2))} =
          ball(vec 0:real^3,&2)`
        SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_IMAGE] THEN
          ASM_MESON_TAC[P3E_CCP_IN_CZS; P3E_CCM_EQ];
          REWRITE_TAC[OPEN_BALL]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Z is Hausdorff.  A core point of a cap is separated from                  *)
(* any other point by the cap chart (inside the cap) or by the cap image of  *)
(* ball(0,3/2) and the complement of the closed 3/2-cap (P3E_SEPARATE_CAP); *)
(* two old points are separated in X minus the cut spheres.                 *)
(* ------------------------------------------------------------------------- *)

let P3E_SEPARATE_CAP = prove
 (`!(top:B topology) (c:real^3->B) x0 q.
     (!w. open w /\ w SUBSET ball(vec 0,&2) ==> open_in top (IMAGE c w)) /\
     (!x y. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\ c x = c y ==> x = y) /\
     open_in top (topspace top DIFF IMAGE c (cball(vec 0,&3 / &2))) /\
     norm x0 <= &1 /\ q IN topspace top /\ ~(q = c x0)
     ==> ?u v. open_in top u /\ open_in top v /\ c x0 IN u /\ q IN v /\ DISJOINT u v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x0:real^3) IN ball(vec 0,&3 / &2) /\ x0 IN ball(vec 0,&2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `?y0. y0 IN ball(vec 0,&2) /\ q = (c:real^3->B) y0` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(x0:real^3 = y0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `r = norm(x0 - y0:real^3) / &2` THEN
    SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (c:real^3->B) (ball(x0,r) INTER ball(vec 0,&2))`;
      `IMAGE (c:real^3->B) (ball(y0,r) INTER ball(vec 0,&2))`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET];
      FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
      X_GEN_TAC `z:B` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC)
                                 (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `a:real^3 = b` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `(c:real^3->B) x = c y`)) (concl th))) THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(b:real^3) IN ball(x0,r)` THEN UNDISCH_TAC `(b:real^3) IN ball(y0,r)` THEN
      EXPAND_TAC "r" THEN REWRITE_TAC[IN_BALL] THEN CONV_TAC NORM_ARITH];
    MAP_EVERY EXISTS_TAC
     [`IMAGE (c:real^3->B) (ball(vec 0,&3 / &2))`;
      `topspace top DIFF IMAGE (c:real^3->B) (cball(vec 0,&3 / &2))`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[OPEN_BALL; SUBSET; IN_BALL_0] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_DIFF; IN_IMAGE; IN_CBALL_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
        is_exists(dest_neg(concl th)))) THEN
      REWRITE_TAC[] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[IN_BALL_0] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(SET_RULE `(s:B->bool) SUBSET t ==> DISJOINT s (u DIFF t)`) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL]]]);;

let P3E_CTOP_HAUSDORFF = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw ==> hausdorff_space (p3e_ctop topX J e nw)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i x0 q. i IN J /\ norm(x0:real^3) <= &1 /\
             (q:B) IN p3e_czs (topX:B topology) J (e:num->real^3->B) nw
             ==> (~(q = p3e_ccp e nw i x0)
                  ==> ?u v. open_in (p3e_ctop topX J e nw) u /\
                            open_in (p3e_ctop topX J e nw) v /\
                            p3e_ccp e nw i x0 IN u /\ q IN v /\ DISJOINT u v) /\
                 (~(q = p3e_ccm e nw i x0)
                  ==> ?u v. open_in (p3e_ctop topX J e nw) u /\
                            open_in (p3e_ctop topX J e nw) v /\
                            p3e_ccm e nw i x0 IN u /\ q IN v /\ DISJOINT u v)`
  (LABEL_TAC "SEP") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC P3E_SEPARATE_CAP THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_CTOP_TOPSPACE th]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(REPEAT STRIP_TAC THEN
        MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                      `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                      `i:num`; `w:real^3->bool`] P3E_CAP_IMAGE_OPEN) THEN
        ASM_SIMP_TAC[] THEN NO_TAC) THEN
    TRY(REPEAT STRIP_TAC THEN
        MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                      `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                      `i:num`; `i:num`; `x:real^3`; `y:real^3`] P3E_CCP_EQ) THEN
        ASM_SIMP_TAC[] THEN NO_TAC) THEN
    TRY(REPEAT STRIP_TAC THEN
        MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                      `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                      `i:num`; `i:num`; `x:real^3`; `y:real^3`] P3E_CCM_EQ) THEN
        ASM_SIMP_TAC[] THEN NO_TAC) THEN
    ASM_MESON_TAC[P3E_CCP_COMPLEMENT_OPEN; P3E_CCM_COMPLEMENT_OPEN];
    ALL_TAC] THEN
  REWRITE_TAC[hausdorff_space] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_CTOP_TOPSPACE th]) THEN
  MAP_EVERY X_GEN_TAC [`p:B`; `q:B`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `?i x. i IN J /\ norm(x:real^3) <= &1 /\
                       ((p:B) = p3e_ccp (e:num->real^3->B) nw i x \/
                        p = p3e_ccm e nw i x)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `x:real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)))) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "SEP" (MP_TAC o SPECL [`i:num`; `x:real^3`; `q:B`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?i x. i IN J /\ norm(x:real^3) <= &1 /\
                       ((q:B) = p3e_ccp (e:num->real^3->B) nw i x \/
                        q = p3e_ccm e nw i x)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `x:real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)))) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "SEP" (MP_TAC o SPECL [`i:num`; `x:real^3`; `p:B`]) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (SUBGOAL_THEN `~((p:B) = p3e_ccp e nw i x) /\ ~(p = p3e_ccm e nw i x)`
       (fun th -> REWRITE_TAC[th]) THENL
      [FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `x:real^3`] o
         REWRITE_RULE[NOT_EXISTS_THM] o
         check (fun th -> is_neg(concl th) && is_exists(rand(concl th)))) THEN
       ASM_REWRITE_TAC[DE_MORGAN_THM];
       ALL_TAC]) THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:B->bool` (X_CHOOSE_THEN `v:B->bool` STRIP_ASSUME_TAC))
      (X_CHOOSE_THEN `u':B->bool` (X_CHOOSE_THEN `v':B->bool` STRIP_ASSUME_TAC))) THEN
    ASM_MESON_TAC[DISJOINT_SYM];
    ALL_TAC] THEN
  (* both old *)
  SUBGOAL_THEN `(p:B) IN topspace topX DIFF mfd_cut_spheres J e /\
                (q:B) IN topspace topX DIFF mfd_cut_spheres J e`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:B) IN p3e_czs topX J e nw` THEN
    UNDISCH_TAC `(q:B) IN p3e_czs topX J e nw` THEN
    REWRITE_TAC[p3e_czs; IN_UNION; IN_MFD_CUT_CORES] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3E_OLD_OPEN_IN_X) THEN
  SUBGOAL_THEN `hausdorff_space (topX:B topology)` MP_TAC THENL
   [ASM_MESON_TAC[p3e_cutdata]; ALL_TAC] THEN
  REWRITE_TAC[hausdorff_space] THEN
  DISCH_THEN(MP_TAC o SPECL [`p:B`; `q:B`]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:B->bool`; `v:B->bool`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`u INTER (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B))`;
    `v INTER (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B))`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3E_CTOP_OPEN_OLD THEN
    EXISTS_TAC `atlasX:((B->bool)#(B->real^3))->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    MATCH_MP_TAC P3E_CTOP_OPEN_OLD THEN
    EXISTS_TAC `atlasX:((B->bool)#(B->real^3))->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Z is compact: it is the union of the closed set of X                      *)
(* outside the open collars e i(annulus(2/3,3/2)) (compact, inside X minus    *)
(* the cut spheres, with the same subspace topology in Z) and of the images   *)
(* of the closed 3/2-ball under the cap maps.                                *)
(* ------------------------------------------------------------------------- *)

let P3E_CZS_COVER = prove
 (`!(topX:B topology) atlasX J e nw p.
     p3e_cutdata topX atlasX J e nw /\ p IN p3e_czs topX J e nw
     ==> p IN topspace topX DIFF
              UNIONS {IMAGE (e i) (annulus (&2 / &3) (&3 / &2)) | i IN J} \/
         ?i x. i IN J /\ x IN cball(vec 0,&3 / &2) /\
               (p = p3e_ccp e nw i x \/ p = p3e_ccm e nw i x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(p:B) IN p3e_czs topX J e nw` THEN
  REWRITE_TAC[p3e_czs; IN_UNION; P3E_CUT_CORES; IN_DIFF] THEN STRIP_TAC THENL
   [ALL_TAC;
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`i:num`; `x:real^3`] THEN
    ASM_REWRITE_TAC[IN_CBALL_0] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `b:bool` THEN ASM_SIMP_TAC[P3E_CCP_CORE; P3E_CCM_CORE]] THEN
  ASM_CASES_TAC `(p:B) IN UNIONS {IMAGE ((e:num->real^3->B) i) (annulus (&2 / &3) (&3 / &2)) | i IN J}` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(p:B) IN UNIONS {IMAGE ((e:num->real^3->B) i) (annulus (&2 / &3) (&3 / &2)) | i IN J}` THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_IMAGE; annulus] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `norm(x:real^3) = &1` THENL
   [UNDISCH_TAC `~((p:B) IN mfd_cut_spheres J e)` THEN
    REWRITE_TAC[IN_MFD_CUT_SPHERES] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 < norm(x:real^3)` THENL
   [EXISTS_TAC `x:real^3` THEN ASM_SIMP_TAC[P3E_CCP_COLLAR; IN_CBALL_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3) /\ norm x < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_POS_LT]; ALL_TAC] THEN
  EXISTS_TAC `inv(norm(x:real^3) pow 2) % x` THEN
  SUBGOAL_THEN `&1 < inv(norm(x:real^3)) /\ inv(norm x) <= &3 / &2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_INV_1] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `y <= inv(&2 / &3) ==> y <= &3 / &2`) THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[IN_CBALL_0; P3E_INVERSION_NORM] THEN DISJ2_TAC THEN
  SUBGOAL_THEN `&1 < norm(inv(norm(x:real^3) pow 2) % x)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P3E_INVERSION_NORM]; ALL_TAC] THEN
  ASM_SIMP_TAC[P3E_CCM_COLLAR; P3E_INVERSION_INVOL]);;

let P3E_CTOP_COMPACT = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw ==> compact_space (p3e_ctop topX J e nw)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[compact_space] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_CTOP_TOPSPACE th]) THEN
  ABBREV_TAC `K0 = topspace topX DIFF
                   UNIONS {IMAGE ((e:num->real^3->B) i) (annulus (&2 / &3) (&3 / &2)) |
                           i IN J}` THEN
  SUBGOAL_THEN `FINITE (J:num->bool) /\ compact_space (topX:B topology)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    SIMP_TAC[p3e_cutdata];
    ALL_TAC] THEN
  (* the old compact piece *)
  SUBGOAL_THEN `compact_in (p3e_ctop topX J e nw) (K0:B->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `compact_in topX (K0:B->bool) /\
                  K0 SUBSET topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "K0" THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
        REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
        REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                      `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                      `i:num`] P3E_CUTDATA_NECK) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
        REWRITE_TAC[OPEN_ANNULUS; SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        EXPAND_TAC "K0" THEN
        MATCH_MP_TAC(SET_RULE `(s:B->bool) SUBSET u ==> t DIFF u SUBSET t DIFF s`) THEN
        REWRITE_TAC[SUBSET; IN_MFD_CUT_SPHERES; UNIONS_GSPEC; IN_ELIM_THM] THEN
        X_GEN_TAC `p:B` THEN
        DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)) THEN
        EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `compact_in (subtopology (p3e_ctop topX J e nw)
                    (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B))) (K0:B->bool)`
    MP_TAC THENL
     [MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                    `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`]
        P3E_CTOP_OLD) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY];
      SIMP_TAC[COMPACT_IN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  (* the closed caps *)
  SUBGOAL_THEN
   `!i. i IN J ==> compact_in (p3e_ctop topX J e nw)
                     (IMAGE (p3e_ccp (e:num->real^3->B) nw i) (cball(vec 0,&3 / &2))) /\
                   compact_in (p3e_ctop topX J e nw)
                     (IMAGE (p3e_ccm (e:num->real^3->B) nw i) (cball(vec 0,&3 / &2)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`] P3E_CAP_CONTINUOUS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `compact_in (subtopology euclidean (ball(vec 0:real^3,&2)))
                             (cball(vec 0,&3 / &2))` ASSUME_TAC THENL
     [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
      REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,&2))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the union *)
  ABBREV_TAC
   `UU = (K0:B->bool) UNION
         UNIONS {IMAGE (p3e_ccp (e:num->real^3->B) nw i) (cball(vec 0,&3 / &2)) | i IN J}
         UNION
         UNIONS {IMAGE (p3e_ccm (e:num->real^3->B) nw i) (cball(vec 0,&3 / &2)) | i IN J}` THEN
  SUBGOAL_THEN `compact_in (p3e_ctop topX J e nw) (UU:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "UU" THEN MATCH_MP_TAC COMPACT_IN_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_IN_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC COMPACT_IN_UNIONS THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3e_czs topX J e nw = (UU:B->bool)` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:B` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `p:B`] P3E_CZS_COVER) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "UU" THEN
    REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_IMAGE] THEN
    MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_CTOP_TOPSPACE th])]);;

(* ------------------------------------------------------------------------- *)
(* The inverse of a cap map on its image, and the cap maps as                *)
(* homeomorphisms of ball(0,2) onto open sets of Z (the cap charts).         *)
(* ------------------------------------------------------------------------- *)

let p3e_cinv = new_definition
 `p3e_cinv (c:real^3->B) = \p. @x. x IN ball(vec 0,&2) /\ c x = p`;;

let P3E_CINV = prove
 (`!(c:real^3->B) x.
     (!x y. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\ c x = c y ==> x = y) /\
     x IN ball(vec 0,&2)
     ==> p3e_cinv c (c x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3e_cinv] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[]);;

let P3E_CAP_CHART_HOMEO = prove
 (`!(top:B topology) (c:real^3->B).
     continuous_map (subtopology euclidean (ball(vec 0,&2)),top) c /\
     (!w. open w /\ w SUBSET ball(vec 0,&2) ==> open_in top (IMAGE c w)) /\
     (!x y. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\ c x = c y ==> x = y)
     ==> open_in top (IMAGE c (ball(vec 0,&2))) /\
         open (IMAGE (p3e_cinv c) (IMAGE c (ball(vec 0,&2)))) /\
         homeomorphic_map (subtopology top (IMAGE c (ball(vec 0,&2))),
                           subtopology euclidean
                             (IMAGE (p3e_cinv c) (IMAGE c (ball(vec 0,&2)))))
                          (p3e_cinv c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (p3e_cinv (c:real^3->B)) (IMAGE c (ball(vec 0,&2))) =
                ball(vec 0,&2)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (\x:real^3. x) (ball(vec 0,&2))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC P3E_CINV THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_ID]];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_BALL] THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[OPEN_BALL; SUBSET_REFL];
                  ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphic_map (subtopology euclidean (ball(vec 0,&2)),
                      subtopology top (IMAGE (c:real^3->B) (ball(vec 0,&2)))) c`
  MP_TAC THENL
   [MATCH_MP_TAC BIJECTIVE_OPEN_IMP_HOMEOMORPHIC_MAP THEN
    SUBGOAL_THEN `IMAGE (c:real^3->B) (ball(vec 0,&2)) SUBSET topspace top`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
      ALL_TAC] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[CONTINUOUS_MAP_INTO_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                   SUBSET_REFL];
      REWRITE_TAC[open_map; OPEN_IN_SUBTOPOLOGY] THEN
      X_GEN_TAC `u:real^3->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE (c:real^3->B) u` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[INTER_SUBSET] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[GSYM OPEN_IN]) THEN
        ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL];
        ASM SET_TAC[]];
      ASM SET_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:B->real^3` ASSUME_TAC o
    REWRITE_RULE[HOMEOMORPHIC_MAP_MAPS]) THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAP_EQ THEN EXISTS_TAC `g:B->real^3` THEN CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `p:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `p3e_cinv (c:real^3->B) (c x) = x` (fun th -> ASM_REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC P3E_CINV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM_MESON_TAC[];
    REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN EXISTS_TAC `c:real^3->B` THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_MAPS_SYM] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The atlas of Z (the charts of X restricted to X minus the                 *)
(* cut spheres, and the inverse cap maps on the cap images of ball(0,2)):   *)
(* every chart is an open embedding into real^3, and the charts cover Z.    *)
(* ------------------------------------------------------------------------- *)

let p3e_catlas = new_definition
 `p3e_catlas (topX:B topology) (atlasX:((B->bool)#(B->real^3))->bool) (J:num->bool)
             (e:num->real^3->B) (nw:num->bool->real^3->B) =
    restrict_atlas atlasX (topspace topX DIFF mfd_cut_spheres J e) UNION
    {(IMAGE (p3e_ccp e nw i) (ball(vec 0,&2)),p3e_cinv (p3e_ccp e nw i)) | i IN J} UNION
    {(IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)),p3e_cinv (p3e_ccm e nw i)) | i IN J}`;;

let IN_P3E_CATLAS = prove
 (`!(topX:B topology) atlasX J e nw U phi.
     (U,phi) IN p3e_catlas topX atlasX J e nw <=>
     (?V. (V,phi) IN atlasX /\ U = V INTER (topspace topX DIFF mfd_cut_spheres J e)) \/
     (?i. i IN J /\ U = IMAGE (p3e_ccp e nw i) (ball(vec 0,&2)) /\
          phi = p3e_cinv (p3e_ccp e nw i)) \/
     (?i. i IN J /\ U = IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)) /\
          phi = p3e_cinv (p3e_ccm e nw i))`,
  REWRITE_TAC[p3e_catlas; IN_UNION; IN_RESTRICT_ATLAS; IN_ELIM_THM; PAIR_EQ] THEN
  MESON_TAC[]);;

let P3E_CAP_CHART_FACTS = prove
 (`!(topX:B topology) atlasX J e nw i.
     p3e_cutdata topX atlasX J e nw /\ i IN J
     ==> open_in (p3e_ctop topX J e nw) (IMAGE (p3e_ccp e nw i) (ball(vec 0,&2))) /\
         open (IMAGE (p3e_cinv (p3e_ccp e nw i))
                     (IMAGE (p3e_ccp e nw i) (ball(vec 0,&2)))) /\
         homeomorphic_map
           (subtopology (p3e_ctop topX J e nw) (IMAGE (p3e_ccp e nw i) (ball(vec 0,&2))),
            subtopology euclidean
              (IMAGE (p3e_cinv (p3e_ccp e nw i)) (IMAGE (p3e_ccp e nw i) (ball(vec 0,&2)))))
           (p3e_cinv (p3e_ccp e nw i)) /\
         open_in (p3e_ctop topX J e nw) (IMAGE (p3e_ccm e nw i) (ball(vec 0,&2))) /\
         open (IMAGE (p3e_cinv (p3e_ccm e nw i))
                     (IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)))) /\
         homeomorphic_map
           (subtopology (p3e_ctop topX J e nw) (IMAGE (p3e_ccm e nw i) (ball(vec 0,&2))),
            subtopology euclidean
              (IMAGE (p3e_cinv (p3e_ccm e nw i)) (IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)))))
           (p3e_cinv (p3e_ccm e nw i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `i:num`] P3E_CAP_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(a /\ b /\ c) /\ (d /\ e /\ f) ==> a /\ b /\ c /\ d /\ e /\ f`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P3E_CAP_CHART_HOMEO THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                    `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                    `i:num`; `w:real^3->bool`] P3E_CAP_IMAGE_OPEN) THEN
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                    `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                    `i:num`; `i:num`; `x:real^3`; `y:real^3`] P3E_CCP_EQ) THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC P3E_CAP_CHART_HOMEO THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                    `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                    `i:num`; `w:real^3->bool`] P3E_CAP_IMAGE_OPEN) THEN
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                    `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                    `i:num`; `i:num`; `x:real^3`; `y:real^3`] P3E_CCM_EQ) THEN
      ASM_SIMP_TAC[]]]);;

let P3E_OLD_CHART_FACTS = prove
 (`!(topX:B topology) atlasX J e nw V phi.
     p3e_cutdata topX atlasX J e nw /\ (V,phi) IN atlasX
     ==> open_in (p3e_ctop topX J e nw)
                 (V INTER (topspace topX DIFF mfd_cut_spheres J e)) /\
         open (IMAGE phi (V INTER (topspace topX DIFF mfd_cut_spheres J e))) /\
         homeomorphic_map
           (subtopology (p3e_ctop topX J e nw)
                        (V INTER (topspace topX DIFF mfd_cut_spheres J e)),
            subtopology euclidean
              (IMAGE phi (V INTER (topspace topX DIFF mfd_cut_spheres J e)))) phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `W = topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B)` THEN
  SUBGOAL_THEN `smooth_manifold_atlas (topX:B topology)
                  (atlasX:((B->bool)#(B->real^3))->bool) /\ open_in topX W`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[p3e_cutdata]; EXPAND_TAC "W" THEN
                    ASM_MESON_TAC[P3E_OLD_OPEN_IN_X]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                 `W:B->bool`; `V:B->bool`; `phi:B->real^3`] MFDM_RESTRICT_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`]
    P3E_CTOP_OLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `subtopology (p3e_ctop topX J e nw) (V INTER W) =
                subtopology (subtopology (topX:B topology) W) (V INTER W)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    AP_TERM_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3E_CTOP_OPEN_OLD THEN
  EXISTS_TAC `atlasX:((B->bool)#(B->real^3))->bool` THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness of the neck charts read in charts of X (both                   *)
(* directions), from mfd_neck_chart, and the identity chart of real^3.       *)
(* ------------------------------------------------------------------------- *)

let P3E_CHART_INV_EUCLIDEAN = prove
 (`!y:real^3. chart_inv ((:real^3),(\x:real^3. x)) y = y`,
  REWRITE_TAC[chart_inv; IN_UNIV] THEN MESON_TAC[]);;

let P3E_NECK_CHART_SMOOTH = prove
 (`!(topX:B topology) atlasX J e nw i U phi.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ (U,phi) IN atlasX
     ==> open {y | y IN annulus (&1 / &2) (&2) /\ e i y IN U} /\
         smooth_map_on {y | y IN annulus (&1 / &2) (&2) /\ e i y IN U} (phi o e i) /\
         ?e'. (!y. y IN annulus (&1 / &2) (&2) ==> e'(e i y) = y) /\
              (!x. x IN IMAGE (e i) (annulus (&1 / &2) (&2))
                   ==> e' x IN annulus (&1 / &2) (&2) /\ e i (e' x) = x) /\
              open (IMAGE phi (U INTER IMAGE (e i) (annulus (&1 / &2) (&2)))) /\
              smooth_map_on (IMAGE phi (U INTER IMAGE (e i) (annulus (&1 / &2) (&2))))
                            (e' o chart_inv (U,phi))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (topX:B topology)
                  (atlasX:((B->bool)#(B->real^3))->bool) /\
                mfd_param topX atlasX (annulus (&1 / &2) (&2)) ((e:num->real^3->B) i)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    REWRITE_TAC[p3e_cutdata; mfd_neck_chart] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':B->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `mfd_smooth_map (open_set_atlas (:real^3)) (atlasX:((B->bool)#(B->real^3))->bool)
                   (annulus (&1 / &2) (&2)) ((e:num->real^3->B) i) /\
                mfd_smooth_map atlasX (open_set_atlas (:real^3))
                   (IMAGE (e i) (annulus (&1 / &2) (&2))) (e':B->real^3)`
  MP_TAC THENL [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (MP_TAC o SPECL [`((:real^3),(\x:real^3. x))`; `(U:B->bool,phi:B->real^3)`])
    (MP_TAC o SPECL [`(U:B->bool,phi:B->real^3)`; `((:real^3),(\x:real^3. x))`])) THEN
  ASM_REWRITE_TAC[FST; SND; IN_UNIV; INTER_UNIV; IMAGE_ID] THEN
  REWRITE_TAC[SET_RULE `{x:B | x IN s} = s`] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `open_in topX (U:B->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN REWRITE_TAC[OPEN_ANNULUS] THEN
    MP_TAC(ISPECL [`(e:num->real^3->B) i`;
                   `subtopology euclidean (annulus (&1 / &2) (&2):real^3->bool)`;
                   `topX:B topology`; `U:B->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(phi:B->real^3) o (e:num->real^3->B) i o chart_inv ((:real^3),(\x:real^3. x))` THEN
    ASM_REWRITE_TAC[o_THM; P3E_CHART_INV_EUCLIDEAN];
    ALL_TAC] THEN
  EXISTS_TAC `e':B->real^3` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [X_GEN_TAC `x:B` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
  MATCH_MP_TAC CHART_IMAGE_OPEN THEN
  MAP_EVERY EXISTS_TAC [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                        `U:B->bool`] THEN
  ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(\x:real^3. x) o (e':B->real^3) o chart_inv (U:B->bool,phi:B->real^3)` THEN
  ASM_REWRITE_TAC[o_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Transition maps between the charts of X (restricted) and                  *)
(* the cap charts: through the inverse e' of the neck chart (plus caps) and  *)
(* the inversion (minus caps); cap charts meet only when equal.              *)
(* ------------------------------------------------------------------------- *)

let P3E_CAP_OLD_POINT = prove
 (`!(topX:B topology) atlasX J e nw i x y.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ y IN ball(vec 0,&2) /\
     x IN topspace topX
     ==> (x = p3e_ccp e nw i y ==> &1 < norm y /\ norm y < &2 /\ x = e i y) /\
         (x = p3e_ccm e nw i y
          ==> &1 < norm y /\ norm y < &2 /\ x = e i (inv(norm y pow 2) % y) /\
              inv(norm y pow 2) % y IN annulus (&1 / &2) (&2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!b z. ~((nw:num->bool->real^3->B) i b z = x)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    REWRITE_TAC[p3e_cutdata] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:num->real^3->B`; `nw:num->bool->real^3->B`; `i:num`; `y:real^3`]
    P3E_CAP_VALUES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[P3E_INV_IN_ANNULUS_HALF_TWO] THEN ASM_MESON_TAC[]);;

let P3E_TRANS_OLD_CCP = prove
 (`!(topX:B topology) atlasX J e nw i U phi.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ (U,phi) IN atlasX
     ==> ?g. smooth_map_on
               (IMAGE phi ((U INTER (topspace topX DIFF mfd_cut_spheres J e)) INTER
                           IMAGE (p3e_ccp e nw i) (ball(vec 0,&2)))) g /\
             !x. x IN (U INTER (topspace topX DIFF mfd_cut_spheres J e)) INTER
                      IMAGE (p3e_ccp e nw i) (ball(vec 0,&2))
                 ==> g(phi x) = p3e_cinv (p3e_ccp e nw i) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `i:num`; `U:B->bool`; `phi:B->real^3`] P3E_NECK_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':B->real^3`
    (CONJUNCTS_THEN2 (LABEL_TAC "EINV") STRIP_ASSUME_TAC) o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (topX:B topology)
                  (atlasX:((B->bool)#(B->real^3))->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    SIMP_TAC[p3e_cutdata];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN (U INTER (topspace topX DIFF mfd_cut_spheres J e)) INTER
             IMAGE (p3e_ccp e nw i) (ball(vec 0,&2))
        ==> x IN U /\ ?y. y IN ball(vec 0,&2) /\ &1 < norm y /\ norm y < &2 /\
                          x = (e:num->real^3->B) i y /\ x = p3e_ccp e nw i y`
  (LABEL_TAC "OLD") THENL
   [X_GEN_TAC `x:B` THEN REWRITE_TAC[IN_INTER; IN_DIFF; IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `y:real^3` THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`; `x:B`; `y:real^3`] P3E_CAP_OLD_POINT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(e':B->real^3) o chart_inv (U:B->bool,phi:B->real^3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (phi:B->real^3)
                  (U INTER IMAGE ((e:num->real^3->B) i) (annulus (&1 / &2) (&2)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    USE_THEN "OLD" (MP_TAC o SPEC `x:B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_INTER; IN_IMAGE] THEN
    EXISTS_TAC `y:real^3` THEN ASM_SIMP_TAC[P3E_IN_ANNULUS_HALF_TWO];
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    USE_THEN "OLD" (MP_TAC o SPEC `x:B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                   `U:B->bool`; `phi:B->real^3`] CHART_INV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> SIMP_TAC[CONJUNCT1 th; ASSUME `(x:B) IN U`]) THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `y:real^3` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(x:B) = (e:num->real^3->B) i y` THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "EINV" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[P3E_IN_ANNULUS_HALF_TWO];
      UNDISCH_TAC `(x:B) = p3e_ccp e nw i y` THEN DISCH_THEN SUBST1_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P3E_CINV THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                    `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                    `i:num`; `i:num`; `x':real^3`; `y':real^3`] P3E_CCP_EQ) THEN
      ASM_SIMP_TAC[]]]);;

let P3E_CCP_OLD_PARAM = prove
 (`!(topX:B topology) atlasX J e nw i x.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ x IN topspace topX /\
     x IN IMAGE (p3e_ccp e nw i) (ball(vec 0,&2))
     ==> ?y. y IN ball(vec 0,&2) /\ &1 < norm y /\ norm y < &2 /\
             x = e i y /\ p3e_cinv (p3e_ccp e nw i) x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN
  EXISTS_TAC `x':real^3` THEN
  SUBGOAL_THEN `p3e_cinv (p3e_ccp (e:num->real^3->B) nw i) x = x'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3E_CINV THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`; `i:num`; `x'':real^3`; `y:real^3`] P3E_CCP_EQ) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `i:num`; `x:B`; `x':real^3`] P3E_CAP_OLD_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let P3E_CCM_OLD_PARAM = prove
 (`!(topX:B topology) atlasX J e nw i x.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ x IN topspace topX /\
     x IN IMAGE (p3e_ccm e nw i) (ball(vec 0,&2))
     ==> ?y. y IN ball(vec 0,&2) /\ &1 < norm y /\ norm y < &2 /\ ~(y = vec 0) /\
             inv(norm y pow 2) % y IN annulus (&1 / &2) (&2) /\
             x = e i (inv(norm y pow 2) % y) /\ p3e_cinv (p3e_ccm e nw i) x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN
  EXISTS_TAC `x':real^3` THEN
  SUBGOAL_THEN `p3e_cinv (p3e_ccm (e:num->real^3->B) nw i) x = x'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3E_CINV THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`; `i:num`; `x'':real^3`; `y:real^3`] P3E_CCM_EQ) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `i:num`; `x:B`; `x':real^3`] P3E_CAP_OLD_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN UNDISCH_TAC `&1 < norm(x':real^3)` THEN
  ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC);;

let P3E_TRANS_CCP_OLD = prove
 (`!(topX:B topology) atlasX J e nw i U phi.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ (U,phi) IN atlasX
     ==> ?g. smooth_map_on
               (IMAGE (p3e_cinv (p3e_ccp e nw i))
                      (IMAGE (p3e_ccp e nw i) (ball(vec 0,&2)) INTER
                       (U INTER (topspace topX DIFF mfd_cut_spheres J e)))) g /\
             !x. x IN IMAGE (p3e_ccp e nw i) (ball(vec 0,&2)) INTER
                      (U INTER (topspace topX DIFF mfd_cut_spheres J e))
                 ==> g(p3e_cinv (p3e_ccp e nw i) x) = phi x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `i:num`; `U:B->bool`; `phi:B->real^3`] P3E_NECK_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `(phi:B->real^3) o (e:num->real^3->B) i` THEN
  SUBGOAL_THEN
   `!x. x IN IMAGE (p3e_ccp e nw i) (ball(vec 0,&2)) INTER
             (U INTER (topspace topX DIFF mfd_cut_spheres J e))
        ==> ?y. y IN annulus (&1 / &2) (&2) /\ x = (e:num->real^3->B) i y /\
                p3e_cinv (p3e_ccp e nw i) x = y /\ x IN U`
  (LABEL_TAC "OLD") THENL
   [X_GEN_TAC `x:B` THEN REWRITE_TAC[IN_INTER; IN_DIFF] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`; `x:B`] P3E_CCP_OLD_PARAM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN ASM_SIMP_TAC[P3E_IN_ANNULUS_HALF_TWO];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{y | y IN annulus (&1 / &2) (&2) /\ (e:num->real^3->B) i y IN U}` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    USE_THEN "OLD" (MP_TAC o SPEC `x:B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    USE_THEN "OLD" (MP_TAC o SPEC `x:B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]]);;

let P3E_TRANS_CCM_OLD = prove
 (`!(topX:B topology) atlasX J e nw i U phi.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ (U,phi) IN atlasX
     ==> ?g. smooth_map_on
               (IMAGE (p3e_cinv (p3e_ccm e nw i))
                      (IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)) INTER
                       (U INTER (topspace topX DIFF mfd_cut_spheres J e)))) g /\
             !x. x IN IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)) INTER
                      (U INTER (topspace topX DIFF mfd_cut_spheres J e))
                 ==> g(p3e_cinv (p3e_ccm e nw i) x) = phi x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `i:num`; `U:B->bool`; `phi:B->real^3`] P3E_NECK_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Tn = {y | y IN annulus (&1 / &2) (&2) /\ (e:num->real^3->B) i y IN U}` THEN
  EXISTS_TAC `((phi:B->real^3) o (e:num->real^3->B) i) o
              (\z:real^3. inv(norm z pow 2) % z)` THEN
  SUBGOAL_THEN
   `!x. x IN IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)) INTER
             (U INTER (topspace topX DIFF mfd_cut_spheres J e))
        ==> ?y. y IN annulus (&1) (&2) /\
                inv(norm y pow 2) % y IN annulus (&1 / &2) (&2) /\
                x = (e:num->real^3->B) i (inv(norm y pow 2) % y) /\
                p3e_cinv (p3e_ccm e nw i) x = y /\ x IN U`
  (LABEL_TAC "OLD") THENL
   [X_GEN_TAC `x:B` THEN REWRITE_TAC[IN_INTER; IN_DIFF] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`; `x:B`] P3E_CCM_OLD_PARAM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{y:real^3 | y IN annulus (&1) (&2) /\
                            (\z:real^3. inv(norm z pow 2) % z) y IN Tn}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:B` THEN DISCH_TAC THEN
      USE_THEN "OLD" (MP_TAC o SPEC `x:B`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Tn" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `Tn:real^3->bool` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
      TRY(CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "Tn" THEN ASM_REWRITE_TAC[]]) THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
      SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS; SMOOTH_MAP_ON_INVERSION] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN X_GEN_TAC `x:real^3` THEN
      STRIP_TAC THEN DISCH_TAC THEN UNDISCH_TAC `&1 < norm(x:real^3)` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      EXPAND_TAC "Tn" THEN ASM_REWRITE_TAC[];
      SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_INVERSION; SUBSET; IN_ELIM_THM; annulus] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `&1 < norm(x:real^3)` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      EXPAND_TAC "Tn" THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    USE_THEN "OLD" (MP_TAC o SPEC `x:B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]]);;

let P3E_TRANS_OLD_CCM = prove
 (`!(topX:B topology) atlasX J e nw i U phi.
     p3e_cutdata topX atlasX J e nw /\ i IN J /\ (U,phi) IN atlasX
     ==> ?g. smooth_map_on
               (IMAGE phi ((U INTER (topspace topX DIFF mfd_cut_spheres J e)) INTER
                           IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)))) g /\
             !x. x IN (U INTER (topspace topX DIFF mfd_cut_spheres J e)) INTER
                      IMAGE (p3e_ccm e nw i) (ball(vec 0,&2))
                 ==> g(phi x) = p3e_cinv (p3e_ccm e nw i) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                `i:num`; `U:B->bool`; `phi:B->real^3`] P3E_NECK_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':B->real^3`
    (CONJUNCTS_THEN2 (LABEL_TAC "EINV") (CONJUNCTS_THEN2 (LABEL_TAC "EIN")
       STRIP_ASSUME_TAC)) o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (topX:B topology)
                  (atlasX:((B->bool)#(B->real^3))->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    SIMP_TAC[p3e_cutdata];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN (U INTER (topspace topX DIFF mfd_cut_spheres J e)) INTER
             IMAGE (p3e_ccm e nw i) (ball(vec 0,&2))
        ==> x IN U /\
            ?y. y IN ball(vec 0,&2) /\ &1 < norm y /\ norm y < &2 /\ ~(y = vec 0) /\
                inv(norm y pow 2) % y IN annulus (&1 / &2) (&2) /\
                x = (e:num->real^3->B) i (inv(norm y pow 2) % y) /\
                p3e_cinv (p3e_ccm e nw i) x = y`
  (LABEL_TAC "OLD") THENL
   [X_GEN_TAC `x:B` THEN REWRITE_TAC[IN_INTER; IN_DIFF] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3E_CCM_OLD_PARAM THEN
    MAP_EVERY EXISTS_TAC [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                          `J:num->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(\z:real^3. inv(norm z pow 2) % z) o
              (e':B->real^3) o chart_inv (U:B->bool,phi:B->real^3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (phi:B->real^3)
                  (U INTER IMAGE ((e:num->real^3->B) i) (annulus (&1 / &2) (&2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET] THEN
      X_GEN_TAC `x:B` THEN DISCH_TAC THEN
      USE_THEN "OLD" (MP_TAC o SPEC `x:B`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[IN_INTER; IN_IMAGE] THEN
      EXISTS_TAC `inv(norm(y:real^3) pow 2) % y` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_INVERSION] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{z:real^3 | ~(z = vec 0)} = (:real^3) DELETE vec 0` SUBST1_TAC THENL
       [SET_TAC[]; SIMP_TAC[OPEN_DELETE; OPEN_UNIV]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
      X_GEN_TAC `x:B` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                     `U:B->bool`; `phi:B->real^3`] CHART_INV) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> SIMP_TAC[CONJUNCT1 th; ASSUME `(x:B) IN U`]) THEN
      USE_THEN "EIN" (MP_TAC o SPEC `x:B`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      STRIP_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `&1 / &2 < norm((e':B->real^3) x)` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC];
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    USE_THEN "OLD" (MP_TAC o SPEC `x:B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                   `U:B->bool`; `phi:B->real^3`] CHART_INV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> SIMP_TAC[CONJUNCT1 th; ASSUME `(x:B) IN U`]) THEN
    SUBGOAL_THEN `(e':B->real^3) x = inv(norm(y:real^3) pow 2) % y` SUBST1_TAC THENL
     [UNDISCH_TAC `(x:B) = (e:num->real^3->B) i (inv(norm(y:real^3) pow 2) % y)` THEN
      DISCH_THEN SUBST1_TAC THEN USE_THEN "EINV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[P3E_INVERSION_INVOL]]);;

(* ------------------------------------------------------------------------- *)
(* The atlas of Z is a smooth atlas of the topology of Z.                    *)
(* ------------------------------------------------------------------------- *)

let P3E_CAP_CHARTS_EQ = prove
 (`!(topX:B topology) atlasX J e nw U phi V psi.
     p3e_cutdata topX atlasX J e nw /\
     ((?i. i IN J /\ U = IMAGE (p3e_ccp e nw i) (ball(vec 0,&2)) /\
           phi = p3e_cinv (p3e_ccp e nw i)) \/
      (?i. i IN J /\ U = IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)) /\
           phi = p3e_cinv (p3e_ccm e nw i))) /\
     ((?j. j IN J /\ V = IMAGE (p3e_ccp e nw j) (ball(vec 0,&2)) /\
           psi = p3e_cinv (p3e_ccp e nw j)) \/
      (?j. j IN J /\ V = IMAGE (p3e_ccm e nw j) (ball(vec 0,&2)) /\
           psi = p3e_cinv (p3e_ccm e nw j)))
     ==> U INTER V = {} \/ (U = V /\ phi = psi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC;
    DISJ1_TAC;
    DISJ1_TAC;
    ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN X_GEN_TAC `p:B` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
  ASM_MESON_TAC[P3E_CCP_EQ; P3E_CCM_EQ; P3E_CCP_NEQ_CCM]);;

let P3E_CAP_CAP_TRANS = prove
 (`!(topX:B topology) atlasX J e nw U phi V psi.
     p3e_cutdata topX atlasX J e nw /\
     ((?i. i IN J /\ U = IMAGE (p3e_ccp e nw i) (ball(vec 0,&2)) /\
           phi = p3e_cinv (p3e_ccp e nw i)) \/
      (?i. i IN J /\ U = IMAGE (p3e_ccm e nw i) (ball(vec 0,&2)) /\
           phi = p3e_cinv (p3e_ccm e nw i))) /\
     ((?j. j IN J /\ V = IMAGE (p3e_ccp e nw j) (ball(vec 0,&2)) /\
           psi = p3e_cinv (p3e_ccp e nw j)) \/
      (?j. j IN J /\ V = IMAGE (p3e_ccm e nw j) (ball(vec 0,&2)) /\
           psi = p3e_cinv (p3e_ccm e nw j)))
     ==> ?g. smooth_map_on (IMAGE phi (U INTER V)) g /\
             !x. x IN U INTER V ==> g(phi x) = psi x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP P3E_CAP_CHARTS_EQ) THEN
  EXISTS_TAC `\x:real^3. x` THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; NOT_IN_EMPTY]);;

let P3E_CATLAS_SMOOTH = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw
     ==> smooth_manifold_atlas (p3e_ctop topX J e nw) (p3e_catlas topX atlasX J e nw)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (topX:B topology)
                  (atlasX:((B->bool)#(B->real^3))->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    SIMP_TAC[p3e_cutdata];
    ALL_TAC] THEN
  REWRITE_TAC[smooth_manifold_atlas] THEN REPEAT CONJ_TAC THENL
   [(* the charts *)
    REWRITE_TAC[IN_P3E_CATLAS] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC P3E_OLD_CHART_FACTS THEN
      EXISTS_TAC `atlasX:((B->bool)#(B->real^3))->bool` THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                    `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                    `i:num`] P3E_CAP_CHART_FACTS) THEN
      ASM_SIMP_TAC[];
      MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                    `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                    `i:num`] P3E_CAP_CHART_FACTS) THEN
      ASM_SIMP_TAC[]];
    (* the charts cover Z *)
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_CTOP_TOPSPACE th]) THEN
    X_GEN_TAC `p:B` THEN REWRITE_TAC[p3e_czs; IN_UNION; IN_DIFF; IN_MFD_CUT_CORES] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `smooth_manifold_atlas (topX:B topology)
                     (atlasX:((B->bool)#(B->real^3))->bool)` THEN
      REWRITE_TAC[smooth_manifold_atlas] THEN
      DISCH_THEN(MP_TAC o SPEC `p:B` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `V:B->bool` (X_CHOOSE_THEN `psi:B->real^3`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC
       [`V INTER (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B))`;
        `psi:B->real^3`] THEN
      REWRITE_TAC[IN_P3E_CATLAS] THEN ASM_REWRITE_TAC[IN_INTER; IN_DIFF] THEN
      DISJ1_TAC THEN EXISTS_TAC `V:B->bool` THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`IMAGE (p3e_ccp (e:num->real^3->B) nw i) (ball(vec 0,&2))`;
                            `p3e_cinv (p3e_ccp (e:num->real^3->B) nw i)`] THEN
      REWRITE_TAC[IN_P3E_CATLAS] THEN CONJ_TAC THENL
       [DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
        ASM_REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC];
      MAP_EVERY EXISTS_TAC [`IMAGE (p3e_ccm (e:num->real^3->B) nw i) (ball(vec 0,&2))`;
                            `p3e_cinv (p3e_ccm (e:num->real^3->B) nw i)`] THEN
      REWRITE_TAC[IN_P3E_CATLAS] THEN CONJ_TAC THENL
       [DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
        ASM_REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC]];
    (* the transitions *)
    MAP_EVERY X_GEN_TAC [`U:B->bool`; `phi:B->real^3`; `V:B->bool`; `psi:B->real^3`] THEN
    REWRITE_TAC[IN_P3E_CATLAS] THEN
    ASM_CASES_TAC
     `?U1. (U1:B->bool,phi:B->real^3) IN (atlasX:((B->bool)#(B->real^3))->bool) /\
           U = U1 INTER (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B))` THEN
    ASM_CASES_TAC
     `?V1. (V1:B->bool,psi:B->real^3) IN (atlasX:((B->bool)#(B->real^3))->bool) /\
           V = V1 INTER (topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B))` THEN
    ASM_REWRITE_TAC[] THENL
     [(* old, old *)
      FIRST_X_ASSUM(X_CHOOSE_THEN `V1:B->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `U1:B->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `smooth_manifold_atlas (topX:B topology)
                     (atlasX:((B->bool)#(B->real^3))->bool)` THEN
      REWRITE_TAC[smooth_manifold_atlas] THEN
      DISCH_THEN(MP_TAC o SPECL [`U1:B->bool`; `phi:B->real^3`; `V1:B->bool`;
                                 `psi:B->real^3`] o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^3->real^3` THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (phi:B->real^3) (U1 INTER V1)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
      (* old, cap *)
      FIRST_X_ASSUM(X_CHOOSE_THEN `U1:B->bool` STRIP_ASSUME_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC P3E_TRANS_OLD_CCP; MATCH_MP_TAC P3E_TRANS_OLD_CCM] THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      (* cap, old *)
      FIRST_X_ASSUM(X_CHOOSE_THEN `V1:B->bool` STRIP_ASSUME_TAC) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC P3E_TRANS_CCP_OLD; MATCH_MP_TAC P3E_TRANS_CCM_OLD] THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      (* cap, cap *)
      DISCH_TAC THEN MATCH_MP_TAC P3E_CAP_CAP_TRANS THEN
      MAP_EVERY EXISTS_TAC [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                            `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`] THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The cap maps are ball charts of Z, the identity is a diffeomorphism of    *)
(* X minus the cut spheres onto Z minus the cores, and mfd_cut_cap holds     *)
(* with the identity maps.                                                   *)
(* ------------------------------------------------------------------------- *)

let P3E_BALL_CHART_FROM_CHART = prove
 (`!(top:B topology) atlas (c:real^3->B).
     smooth_manifold_atlas top atlas /\
     (IMAGE c (ball(vec 0,&2)),p3e_cinv c) IN atlas /\
     (!x y. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\ c x = c y ==> x = y)
     ==> mfd_ball_chart top atlas c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_ball_chart] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `IMAGE (c:real^3->B) (ball(vec 0,&2))`; `p3e_cinv (c:real^3->B)`]
    MFD_PARAM_CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (p3e_cinv (c:real^3->B)) (IMAGE c (ball(vec 0,&2))) =
                ball(vec 0,&2)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (\x:real^3. x) (ball(vec 0,&2))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC P3E_CINV THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_ID]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC MFD_PARAM_EQ THEN
  EXISTS_TAC `chart_inv (IMAGE (c:real^3->B) (ball(vec 0,&2)),p3e_cinv c)` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[chart_inv] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `p:B` THEN REWRITE_TAC[FST; SND; IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
    SUBGOAL_THEN `p3e_cinv (c:real^3->B) p = z` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3E_CINV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3E_CINV THEN ASM_REWRITE_TAC[]]]);;

let P3E_CAP_BALL_CHART = prove
 (`!(topX:B topology) atlasX J e nw i.
     p3e_cutdata topX atlasX J e nw /\ i IN J
     ==> mfd_ball_chart (p3e_ctop topX J e nw) (p3e_catlas topX atlasX J e nw)
                        (p3e_ccp e nw i) /\
         mfd_ball_chart (p3e_ctop topX J e nw) (p3e_catlas topX atlasX J e nw)
                        (p3e_ccm e nw i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3E_CATLAS_SMOOTH) THEN
  CONJ_TAC THEN MATCH_MP_TAC P3E_BALL_CHART_FROM_CHART THEN
  ASM_REWRITE_TAC[IN_P3E_CATLAS] THEN CONJ_TAC THENL
   [DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`; `i:num`; `x:real^3`; `y:real^3`] P3E_CCP_EQ) THEN
    ASM_SIMP_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`; `i:num`; `x:real^3`; `y:real^3`] P3E_CCM_EQ) THEN
    ASM_SIMP_TAC[]]);;

let P3E_ID_DIFFEO = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw
     ==> mfd_diffeo topX atlasX (topspace topX DIFF mfd_cut_spheres J e)
                    (p3e_ctop topX J e nw) (p3e_catlas topX atlasX J e nw)
                    (topspace (p3e_ctop topX J e nw) DIFF
                     mfd_cut_cores J (p3e_ccp e nw) (p3e_ccm e nw))
                    (\x. x) (\x. x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_CTOP_TOPSPACE th]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT2(MATCH_MP P3E_CZS_OLD th)]) THEN
  ABBREV_TAC `W = topspace topX DIFF mfd_cut_spheres J (e:num->real^3->B)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3E_CATLAS_SMOOTH) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (topX:B topology)
                  (atlasX:((B->bool)#(B->real^3))->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    SIMP_TAC[p3e_cutdata];
    ALL_TAC] THEN
  MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`]
    P3E_CTOP_OLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_diffeo] THEN ASM_REWRITE_TAC[HOMEOMORPHIC_MAPS_ID] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "W" THEN ASM_MESON_TAC[P3E_OLD_OPEN_IN_X];
    REWRITE_TAC[mfd_smooth_map; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`U:B->bool`; `phi:B->real^3`; `V:B->bool`; `psi:B->real^3`] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `smooth_manifold_atlas (p3e_ctop topX J e nw)
                   (p3e_catlas (topX:B topology) atlasX J e nw)` THEN
    REWRITE_TAC[smooth_manifold_atlas] THEN
    DISCH_THEN(MP_TAC o SPECL [`U INTER (W:B->bool)`; `phi:B->real^3`; `V:B->bool`;
                               `psi:B->real^3`] o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_P3E_CATLAS] THEN DISJ1_TAC THEN EXISTS_TAC `U:B->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `g:real^3->real^3` THEN
    SUBGOAL_THEN `{x:B | x IN U INTER W /\ x IN V} = (U INTER W) INTER V`
    SUBST1_TAC THENL [SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                   `U:B->bool`; `phi:B->real^3`] CHART_INV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:B` o CONJUNCT1) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[mfd_smooth_map; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`U:B->bool`; `phi:B->real^3`; `V:B->bool`; `psi:B->real^3`] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `smooth_manifold_atlas (p3e_ctop topX J e nw)
                   (p3e_catlas (topX:B topology) atlasX J e nw)` THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    REWRITE_TAC[smooth_manifold_atlas] THEN
    DISCH_THEN(MP_TAC o SPECL [`U:B->bool`; `phi:B->real^3`; `V INTER (W:B->bool)`;
                               `psi:B->real^3`] o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_P3E_CATLAS] THEN DISJ1_TAC THEN EXISTS_TAC `V:B->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `g:real^3->real^3` THEN
    SUBGOAL_THEN `{x:B | x IN U INTER W /\ x IN V} = U INTER (V INTER W)`
    SUBST1_TAC THENL [SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p3e_ctop (topX:B topology) J e nw`;
                   `p3e_catlas (topX:B topology) atlasX J e nw`;
                   `U:B->bool`; `phi:B->real^3`] CHART_INV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:B` o CONJUNCT1) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P3E_CUT_CAP = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw
     ==> mfd_cut_cap topX atlasX (p3e_ctop topX J e nw) (p3e_catlas topX atlasX J e nw)
                     J e (p3e_ccp e nw) (p3e_ccm e nw) (\x. x) (\x. x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_cut_cap] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_ID_DIFFEO th]) THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    SIMP_TAC[p3e_cutdata];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                  `J:num->bool`; `e:num->real^3->B`; `nw:num->bool->real^3->B`;
                  `i:num`] P3E_CAP_BALL_CHART) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    REWRITE_TAC[p3e_cutdata] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `p3e_cutdata (topX:B topology) atlasX J e nw` THEN
    SIMP_TAC[p3e_cutdata];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[P3E_CCP_EQ; P3E_CCM_EQ; P3E_CCP_NEQ_CCM];
    MAP_EVERY X_GEN_TAC [`i:num`; `x:real^3`] THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[P3E_CCP_COLLAR];
    MAP_EVERY X_GEN_TAC [`i:num`; `x:real^3`] THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `&1 / &2 < norm(x:real^3)` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 < norm(inv(norm(x:real^3) pow 2) % x)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[P3E_INVERSION_NORM] THEN
      ONCE_REWRITE_TAC[GSYM REAL_INV_1] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[P3E_CCM_COLLAR; P3E_INVERSION_INVOL]]);;

(* ------------------------------------------------------------------------- *)
(* Summary.  From cut data on X, Z = (p3e_ctop, p3e_catlas) is               *)
(* a compact Hausdorff smooth 3-manifold with mfd_cut_cap (identity maps)    *)
(* and fresh cores: the Z-part of rfs_event_ok.                              *)
(* ------------------------------------------------------------------------- *)

let P3E_CUTCAP_FACTS = prove
 (`!(topX:B topology) atlasX J e nw.
     p3e_cutdata topX atlasX J e nw
     ==> hausdorff_space (p3e_ctop topX J e nw) /\
         smooth_manifold_atlas (p3e_ctop topX J e nw) (p3e_catlas topX atlasX J e nw) /\
         compact_space (p3e_ctop topX J e nw) /\
         mfd_cut_cap topX atlasX (p3e_ctop topX J e nw) (p3e_catlas topX atlasX J e nw)
                     J e (p3e_ccp e nw) (p3e_ccm e nw) (\x. x) (\x. x) /\
         DISJOINT (topspace topX) (mfd_cut_cores J (p3e_ccp e nw) (p3e_ccm e nw)) /\
         topspace (p3e_ctop topX J e nw) = p3e_czs topX J e nw`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3E_CTOP_HAUSDORFF; MATCH_MP_TAC P3E_CATLAS_SMOOTH;
    MATCH_MP_TAC P3E_CTOP_COMPACT; MATCH_MP_TAC P3E_CUT_CAP;
    MATCH_MP_TAC P3E_CORES_FRESH; MATCH_MP_TAC P3E_CTOP_TOPSPACE] THEN
  TRY(EXISTS_TAC `atlasX:((B->bool)#(B->real^3))->bool`) THEN ASM_REWRITE_TAC[]);;

