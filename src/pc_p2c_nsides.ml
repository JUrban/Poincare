(* ========================================================================= *)
(* Unit pc_p2c_nsides (Part 2C): sides of neck spheres, in a unit of their   *)
(* own so that units needing only these facts (pc_p2b_allneck) avoid the     *)
(* closure of pc_p2c_horns2.  Two sides of a neck sphere, ends of tubes,     *)
(* sides of neck spheres in manifolds all of whose points are neck centres   *)
(* (general form: only the closure of the side) are not relatively compact;  *)
(* two ends in the form of P2C_REQ_TWO_ENDS_NO_CAP.                          *)
(* ========================================================================= *)

needs "src/pc_apx_chain.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Point-set topology of neck spheres.                                       *)
(* In a connected manifold every component of the complement of the        *)
(* central sphere of a neck chart contains one of the two collar halves     *)
(* (P2HN_SIDE_COLLAR); ends of tubes are not relatively compact in the      *)
(* tube; if every point is the centre of an eps-neck and neck spheres       *)
(* separate, no side of a neck sphere has compact closure (APX_A19 and the  *)
(* end separation in apx_tube), which gives the two ends of               *)
(* P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT.                                        *)
(* ========================================================================= *)

let P2HN_ANNULUS_CONNECTED = prove
 (`!r1 r2. connected(annulus r1 r2:real^3->bool)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `r1:real`; `r2:real`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
  REWRITE_TAC[DIMINDEX_3; VECTOR_SUB_RZERO; annulus] THEN ARITH_TAC);;

let P2HN_SPHERE_IN_ANNULUS = prove
 (`sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2) /\
   (annulus (&1 / &2) (&1):real^3->bool) SUBSET annulus (&1 / &2) (&2) /\
   (annulus (&1) (&2):real^3->bool) SUBSET annulus (&1 / &2) (&2) /\
   DISJOINT (annulus (&1 / &2) (&1)) (sphere(vec 0:real^3,&1)) /\
   DISJOINT (annulus (&1) (&2)) (sphere(vec 0:real^3,&1))`,
  REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SPHERE_0;
              annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* Images of subsets of the parameter domain avoid the image of a disjoint  *)
(* subset (injectivity of a parametrization).                               *)

let P2HN_PARAM_IMAGE_DISJOINT = prove
 (`!top atlas s (e:real^N->A) t1 t2.
     mfd_param top atlas s e /\ t1 SUBSET s /\ t2 SUBSET s /\ DISJOINT t1 t2
     ==> DISJOINT (IMAGE e t1) (IMAGE e t2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `p:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:real^N` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `y2:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `y1:real^N = y2` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM SET_TAC[]);;

let P2HN_PARAM_IMAGE_CONNECTED = prove
 (`!top atlas s (e:real^N->A) t.
     mfd_param top atlas s e /\ t SUBSET s /\ connected t
     ==> connected_in top (IMAGE e t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
  EXISTS_TAC `subtopology euclidean (s:real^N->bool)` THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN]);;

let P2HN_PARAM_IMAGE_COMPACT = prove
 (`!top atlas s (e:real^N->A) t.
     mfd_param top atlas s e /\ t SUBSET s /\ compact t
     ==> compact_in top (IMAGE e t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean (s:real^N->bool)` THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN]);;

(* Every component of the complement of the central sphere contains one of  *)
(* the collar halves.                                                        *)

let P2HN_SIDE_COLLAR_GEN = prove
 (`!top atlas (e:real^3->A) c.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     ~(top closure_of c INTER IMAGE e (sphere(vec 0,&1)) = {}) /\
     mfd_neck_chart top atlas e /\
     c IN connected_components_of
            (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
     ==> IMAGE e (annulus (&1 / &2) (&1)) SUBSET c \/
         IMAGE e (annulus (&1) (&2)) SUBSET c`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `S = IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `X = topspace top DIFF (S:A->bool)` THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_neck_chart top atlas (e:real^3->A)` THEN
  REWRITE_TAC[mfd_neck_chart] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  STRIP_ASSUME_TAC P2HN_SPHERE_IN_ANNULUS THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace top`
  ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (S:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC P2HN_PARAM_IMAGE_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus (&1 / &2) (&2):real^3->bool`] THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (X:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_SIMP_TAC[OPEN_IN_TOPSPACE; COMPACT_IN_IMP_CLOSED_IN];
    ALL_TAC] THEN
  SUBGOAL_THEN `locally_connected_space (top:A topology)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEO_MANIFOLD_LOCALLY_PATH_CONNECTED;
                  LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (c:A->bool) /\ closed_in (subtopology top X) c /\
                ~(c = {}) /\ c SUBSET X`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `X:A->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE THEN
      ASM_SIMP_TAC[LOCALLY_CONNECTED_SPACE_OPEN_SUBSET];
      ASM_MESON_TAC[CLOSED_IN_CONNECTED_COMPONENTS_OF];
      ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF];
      FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `~(top closure_of (c:A->bool) INTER S = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC) THEN
  (* a point of c in the collar *)
  SUBGOAL_THEN `?q:A. q IN c /\ q IN IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))` MP_TAC THENL
   [UNDISCH_TAC `(p:A) IN top closure_of c` THEN REWRITE_TAC[IN_CLOSURE_OF] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2))` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(norm(v:real^3) = &1)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(q:A) IN S` MP_TAC THENL
     [UNDISCH_TAC `(q:A) = e(v:real^3)` THEN DISCH_THEN SUBST1_TAC THEN
      EXPAND_TAC "S" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[IN_SPHERE_0];
      ALL_TAC] THEN
    UNDISCH_TAC `(q:A) IN c` THEN UNDISCH_TAC `(c:A->bool) SUBSET X` THEN
    EXPAND_TAC "X" THEN SET_TAC[];
    ALL_TAC] THEN
  (* the collar half through q is a connected subset of X meeting c *)
  SUBGOAL_THEN
   `!t. t SUBSET annulus (&1 / &2) (&2) /\ connected t /\ DISJOINT t (sphere(vec 0,&1)) /\
        (v:real^3) IN t
        ==> IMAGE (e:real^3->A) t SUBSET c`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `subtopology top (X:A->bool)` THEN
    UNDISCH_TAC `topspace top DIFF S = (X:A->bool)` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2HN_PARAM_IMAGE_CONNECTED THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                            `annulus (&1 / &2) (&2):real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `annulus (&1 / &2) (&2):real^3->bool`; `e:real^3->A`;
                     `t:real^3->bool`; `sphere(vec 0:real^3,&1)`]
        P2HN_PARAM_IMAGE_DISJOINT) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace top` THEN
      UNDISCH_TAC `(t:real^3->bool) SUBSET annulus (&1 / &2) (&2)` THEN
      UNDISCH_TAC `IMAGE (e:real^3->A) (sphere(vec 0,&1)) = S` THEN SET_TAC[];
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `q:A` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `norm(v:real^3) < &1` THENL
   [DISJ1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[P2HN_ANNULUS_CONNECTED] THEN
    UNDISCH_TAC `(v:real^3) IN annulus (&1 / &2) (&2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[P2HN_ANNULUS_CONNECTED] THEN
    UNDISCH_TAC `(v:real^3) IN annulus (&1 / &2) (&2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]);;

(* The closure of a component c of the complement of a closed set S meets S *)
(* when some connected set cn meets both c and S (locally connected spaces). *)

let P2HN_COMPONENT_CLOSURE_MEETS_CONN = prove
 (`!top (S:A->bool) c cn.
     locally_connected_space top /\ closed_in top S /\
     c IN connected_components_of (subtopology top (topspace top DIFF S)) /\
     connected_in top cn /\ ~(cn INTER c = {}) /\ ~(cn INTER S = {})
     ==> ~(top closure_of c INTER S = {})`,
  REPEAT GEN_TAC THEN ABBREV_TAC `X = topspace top DIFF (S:A->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (X:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (c:A->bool) /\ closed_in (subtopology top X) c /\
                ~(c = {}) /\ c SUBSET X`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `X:A->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE THEN
      ASM_SIMP_TAC[LOCALLY_CONNECTED_SPACE_OPEN_SUBSET];
      ASM_MESON_TAC[CLOSED_IN_CONNECTED_COMPONENTS_OF];
      ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF];
      FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `closed_in top (c:A->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `closed_in (subtopology top X) (c:A->bool)` THEN
    REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `top closure_of (c:A->bool) = c`
     (fun th -> ONCE_REWRITE_TAC[GSYM th]) THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [SUBGOAL_THEN `top closure_of (c:A->bool) SUBSET t` MP_TAC THENL
         [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`top:A topology`; `c:A->bool`] CLOSURE_OF_SUBSET_TOPSPACE) THEN
        UNDISCH_TAC `top closure_of (c:A->bool) INTER S = {}` THEN
        UNDISCH_TAC `topspace top DIFF S = (X:A->bool)` THEN
        UNDISCH_TAC `c:A->bool = t INTER X` THEN SET_TAC[];
        MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET]];
      REWRITE_TAC[CLOSED_IN_CLOSURE_OF]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `cn:A->bool`; `c:A->bool`] CONNECTED_IN_CLOPEN_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((cn:A->bool) INTER c = {})` THEN UNDISCH_TAC `~((cn:A->bool) INTER S = {})` THEN
  UNDISCH_TAC `(c:A->bool) SUBSET X` THEN EXPAND_TAC "X" THEN SET_TAC[]);;

(* The connected-space case.                                                 *)

let P2HN_COMPONENT_CLOSURE_MEETS = prove
 (`!top (S:A->bool) c.
     connected_space top /\ locally_connected_space top /\ closed_in top S /\
     ~(S = {}) /\
     c IN connected_components_of (subtopology top (topspace top DIFF S))
     ==> ~(top closure_of c INTER S = {})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `S:A->bool`; `c:A->bool`; `topspace top:A->bool`]
    P2HN_COMPONENT_CLOSURE_MEETS_CONN) THEN
  ASM_REWRITE_TAC[CONNECTED_IN_TOPSPACE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NONEMPTY_CONNECTED_COMPONENTS_OF) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN
  UNDISCH_TAC `~(S:A->bool = {})` THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]);;

let P2HN_SIDE_COLLAR = prove
 (`!top atlas (e:real^3->A) c.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ connected_space top /\
     mfd_neck_chart top atlas e /\
     c IN connected_components_of
            (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
     ==> IMAGE e (annulus (&1 / &2) (&1)) SUBSET c \/
         IMAGE e (annulus (&1) (&2)) SUBSET c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC P2HN_SIDE_COLLAR_GEN THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2HN_COMPONENT_CLOSURE_MEETS THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_neck_chart top atlas (e:real^3->A)` THEN
  REWRITE_TAC[mfd_neck_chart] THEN DISCH_TAC THEN
  STRIP_ASSUME_TAC P2HN_SPHERE_IN_ANNULUS THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[GEO_MANIFOLD_LOCALLY_PATH_CONNECTED;
                  LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE];
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2HN_PARAM_IMAGE_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus (&1 / &2) (&2):real^3->bool`] THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE];
    REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC]);;

(* Ends of a parametrized annulus are not relatively compact in its image. *)

let P2HN_TUBE_END_INNER = prove
 (`!top atlas (E:real^3->A) r1 r2 rho K.
     mfd_param top atlas (annulus r1 r2) E /\ &0 <= r1 /\ r1 < rho /\ rho <= r2 /\
     compact_in top K /\ IMAGE E (annulus r1 rho) SUBSET K /\
     K SUBSET IMAGE E (annulus r1 r2)
     ==> F`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `E':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `compact(IMAGE (E':A->real^3) K)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology top (IMAGE (E:real^3->A) (annulus r1 r2))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(annulus r1 rho:real^3->bool) SUBSET IMAGE (E':A->real^3) K /\
                IMAGE (E':A->real^3) K SUBSET annulus r1 r2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      EXISTS_TAC `(E:real^3->A) y` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `(y:real^3) IN annulus r1 rho` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `IMAGE (E:real^3->A) (annulus r1 rho) SUBSET K` THEN
        ASM SET_TAC[]];
      UNDISCH_TAC `IMAGE (E':A->real^3) (IMAGE (E:real^3->A) (annulus r1 r2)) = annulus r1 r2` THEN
      UNDISCH_TAC `K SUBSET IMAGE (E:real^3->A) (annulus r1 r2)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `r1 % basis 1 IN IMAGE (E':A->real^3) K` MP_TAC THENL
   [MP_TAC(ISPECL [`r1 % basis 1:real^3`; `IMAGE (E':A->real^3) K`] CLOSED_APPROACHABLE) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    EXISTS_TAC `(r1 + min (d / &2) ((rho - r1) / &2)) % basis 1:real^3` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        is_binary "SUBSET" (concl th) &&
        can (find_term ((=) `rho:real`)) (concl th))) THEN
      SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[dist; GSYM VECTOR_SUB_RDISTRIB] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r1 % basis 1 IN (annulus r1 r2:real^3->bool)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
  ASM_REAL_ARITH_TAC);;

let P2HN_TUBE_END_OUTER = prove
 (`!top atlas (E:real^3->A) r1 r2 rho K.
     mfd_param top atlas (annulus r1 r2) E /\ &0 <= r1 /\ r1 <= rho /\ rho < r2 /\
     compact_in top K /\ IMAGE E (annulus rho r2) SUBSET K /\
     K SUBSET IMAGE E (annulus r1 r2)
     ==> F`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `E':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `compact(IMAGE (E':A->real^3) K)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology top (IMAGE (E:real^3->A) (annulus r1 r2))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(annulus rho r2:real^3->bool) SUBSET IMAGE (E':A->real^3) K /\
                IMAGE (E':A->real^3) K SUBSET annulus r1 r2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      EXISTS_TAC `(E:real^3->A) y` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `(y:real^3) IN annulus rho r2` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `IMAGE (E:real^3->A) (annulus rho r2) SUBSET K` THEN
        ASM SET_TAC[]];
      UNDISCH_TAC `IMAGE (E':A->real^3) (IMAGE (E:real^3->A) (annulus r1 r2)) = annulus r1 r2` THEN
      UNDISCH_TAC `K SUBSET IMAGE (E:real^3->A) (annulus r1 r2)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `r2 % basis 1 IN IMAGE (E':A->real^3) K` MP_TAC THENL
   [MP_TAC(ISPECL [`r2 % basis 1:real^3`; `IMAGE (E':A->real^3) K`] CLOSED_APPROACHABLE) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    EXISTS_TAC `(r2 - min (d / &2) ((r2 - rho) / &2)) % basis 1:real^3` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        is_binary "SUBSET" (concl th) &&
        can (find_term ((=) `rho:real`)) (concl th))) THEN
      SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[dist; GSYM VECTOR_SUB_RDISTRIB] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r2 % basis 1 IN (annulus r1 r2:real^3->bool)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
  ASM_REAL_ARITH_TAC);;

(* The collar annulus of a neck. *)

let P2HN_NECK_DOM_COLLAR = prove
 (`!eps. &0 < eps /\ eps <= &1 / &4
         ==> (annulus (&1 / &2) (&2):real^3->bool) SUBSET rfs_neck_dom eps`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_neck_dom] THEN
  ABBREV_TAC `t = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&1 <= t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC REAL_INV_1_LE THEN
    SUBGOAL_THEN `sqrt(&2) <= &2 /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * &1 / &4` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= exp t /\ exp(--t) <= &1 / &2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_EXP_LE_X) THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_NEG] THEN
    SUBST1_TAC(REAL_ARITH `&1 / &2 = inv(&2)`) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC);;

(* The central sphere lies in the closures of both collar halves. *)

let P2HN_SPHERE_CLOSURE_ANNULI = prove
 (`sphere(vec 0:real^3,&1) SUBSET closure(annulus (&1 / &2) (&1)) /\
   sphere(vec 0:real^3,&1) SUBSET closure(annulus (&1) (&2))`,
  REWRITE_TAC[SUBSET; IN_SPHERE_0; CLOSURE_APPROACHABLE] THEN
  CONJ_TAC THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THENL
   [EXISTS_TAC `(&1 - min (d / &2) (&1 / &4)) % w:real^3`;
    EXISTS_TAC `(&1 + min (d / &2) (&1 / &4)) % w:real^3`] THEN
  REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL; dist;
              VECTOR_ARITH `a % (w:real^3) - w = (a - &1) % w`] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC);;

let P2HN_NECK_SPHERE_IN_CLOSURES = prove
 (`!top atlas (e:real^3->A).
     mfd_neck_chart top atlas e
     ==> IMAGE e (sphere(vec 0,&1)) SUBSET top closure_of (IMAGE e (annulus (&1 / &2) (&1))) /\
         IMAGE e (sphere(vec 0,&1)) SUBSET top closure_of (IMAGE e (annulus (&1) (&2)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_neck_chart] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  STRIP_ASSUME_TAC P2HN_SPHERE_IN_ANNULUS THEN STRIP_ASSUME_TAC P2HN_SPHERE_CLOSURE_ANNULI THEN
  CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
   [EXISTS_TAC `IMAGE (e:real^3->A)
                  ((subtopology euclidean (annulus (&1 / &2) (&2))) closure_of
                   annulus (&1 / &2) (&1))`;
    EXISTS_TAC `IMAGE (e:real^3->A)
                  ((subtopology euclidean (annulus (&1 / &2) (&2))) closure_of
                   annulus (&1) (&2))`] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC IMAGE_SUBSET THEN
     REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
     ASM_SIMP_TAC[SET_RULE `(t:real^3->bool) SUBSET s ==> s INTER t = t`] THEN ASM SET_TAC[];
     MATCH_MP_TAC CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET THEN ASM_REWRITE_TAC[]]));;

(* If every point is the centre of an eps-neck and neck spheres separate,   *)
(* no component of the complement of a neck sphere has compact closure:     *)
(* its closure would lie in a tube of APX_A19 whose end separated from the  *)
(* other end by the sphere lies in that component.                          *)

let P2HN_THREE_COMPONENTS = prove
 (`!top (c:A->bool) c1 c2 I1 I2.
     c IN connected_components_of top /\ c1 IN connected_components_of top /\
     c2 IN connected_components_of top /\ ~(c1 = c2) /\ ~(I1 = {}) /\ ~(I2 = {}) /\
     (I1 SUBSET c \/ I2 SUBSET c) /\ (I1 SUBSET c1 \/ I2 SUBSET c1) /\
     (I1 SUBSET c2 \/ I2 SUBSET c2)
     ==> c = c1 \/ c = c2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `top:A topology` CONNECTED_COMPONENTS_OF_OVERLAP) THEN
  DISCH_THEN(fun ov -> MP_TAC(SPECL [`c:A->bool`; `c1:A->bool`] ov) THEN
                       MP_TAC(SPECL [`c:A->bool`; `c2:A->bool`] ov) THEN
                       MP_TAC(SPECL [`c1:A->bool`; `c2:A->bool`] ov)) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* General form: only the points of the closure of c need to be neck        *)
(* centres, and the closure of c meets the sphere.                           *)

let P2HN_NECK_SIDE_NONCOMPACT_GEN = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps x0 e c.
       &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ riemannian_metric atlas g /\
       apx_sphere_sep top atlas /\
       (!x. x IN top closure_of c ==> ?e. rfs_neck (top,atlas) g eps x e) /\
       rfs_neck (top,atlas) g eps x0 e /\
       c IN connected_components_of
              (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1)))) /\
       ~(top closure_of c INTER IMAGE e (sphere(vec 0,&1)) = {})
       ==> ~compact_in top (top closure_of c)`,
  MP_TAC(REWRITE_RULE[APX_A19_STATEMENT] (ISPEC `(:A)` APX_A19)) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A19"))) THEN
  EXISTS_TAC `min eps1 (&1 / &4)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x0:A`; `e:real^3->A`; `c:A->bool`] THEN
  ABBREV_TAC `S = IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `Xs = topspace top DIFF (S:A->bool)` THEN
  STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_neck_chart top atlas (e:real^3->A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x0 (e:real^3->A)` THEN
    REWRITE_TAC[rfs_neck; mfd_neck_chart] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS] THEN MATCH_MP_TAC P2HN_NECK_DOM_COLLAR THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the closure X of c, a compact connected set of neck centres *)
  ABBREV_TAC `X = top closure_of (c:A->bool)` THEN
  SUBGOAL_THEN `connected_in top (X:A->bool) /\ ~(X = {}) /\ X SUBSET topspace top /\
                (c:A->bool) SUBSET X`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `connected_in top (c:A->bool) /\ ~(c = {}) /\ c SUBSET topspace top`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_IN_CONNECTED_COMPONENTS_OF) THEN
        SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY];
        ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF];
        FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]];
      ALL_TAC] THEN
    EXPAND_TAC "X" THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[CONNECTED_IN_CLOSURE_OF];
      MP_TAC(ISPECL [`top:A topology`; `c:A->bool`] CLOSURE_OF_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE];
      ASM_SIMP_TAC[CLOSURE_OF_SUBSET]];
    ALL_TAC] THEN
  USE_THEN "A19" (MP_TAC o SPECL
    [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`;
     `\x (e:real^3->A). rfs_neck (top,atlas) (g:A->real^3^3) eps x e`; `X:A->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:int`; `b:int`; `xs:int->A`; `es:int->real^3->A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `r2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(X:A->bool) SUBSET IMAGE (E:real^3->A) (annulus r1 r2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "apx_chain_union")) (concl th))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
    fst(dest_const t) = "apx_chain_union")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [apx_tube]) THEN
  (* the neck sphere lies in X *)
  SUBGOAL_THEN `(S:A->bool) SUBSET X` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `e:real^3->A`; `c:A->bool`] P2HN_SIDE_COLLAR_GEN) THEN
    ANTS_TAC THENL [EXPAND_TAC "S" THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `e:real^3->A`] P2HN_NECK_SPHERE_IN_CLOSURES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN EXPAND_TAC "X" THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `top closure_of IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))`;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `top closure_of IMAGE (e:real^3->A) (annulus (&1) (&2))`] THEN
    ASM_SIMP_TAC[CLOSURE_OF_MONO];
    ALL_TAC] THEN
  (* the ends of the tube are separated by the sphere *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`x0:A`; `e:real^3->A`] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ends_sep"))
        (concl th))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[apx_ends_sep] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho1:real` (X_CHOOSE_THEN `rho2:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `p = (E:real^3->A)(((r1 + rho1) / &2) % basis 1)` THEN
  ABBREV_TAC `q = (E:real^3->A)(((rho2 + r2) / &2) % basis 1)` THEN
  SUBGOAL_THEN `(p:A) IN IMAGE (E:real^3->A) (annulus r1 rho1) /\ (q:A) IN IMAGE E (annulus rho2 r2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN EXPAND_TAC "q" THEN CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:A`; `q:A`]) THEN ASM_REWRITE_TAC[apx_separates] THEN
  STRIP_TAC THEN
  (* the ends lie in the complement of S and are connected *)
  SUBGOAL_THEN
   `!t. t SUBSET annulus r1 r2 /\ connected t /\ DISJOINT t (annulus rho1 rho2)
        ==> connected_in (subtopology top Xs) (IMAGE (E:real^3->A) t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2HN_PARAM_IMAGE_CONNECTED THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                            `annulus r1 r2:real^3->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `annulus r1 r2:real^3->bool`; `E:real^3->A`; `t:real^3->bool`;
                   `annulus rho1 rho2:real^3->bool`] P2HN_PARAM_IMAGE_DISJOINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `annulus r1 r2:real^3->bool`; `E:real^3->A`; `t:real^3->bool`]
      MFD_PARAM_IMAGE_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Xs" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* c is the component of p or of q *)
  SUBGOAL_THEN `(p:A) IN topspace(subtopology top Xs) /\ (q:A) IN topspace(subtopology top Xs)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN EXPAND_TAC "Xs" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `connected_component_of (subtopology top Xs) (p:A) IN
      connected_components_of (subtopology top Xs) /\
    connected_component_of (subtopology top Xs) (q:A) IN
      connected_components_of (subtopology top Xs) /\
    (p:A) IN connected_component_of (subtopology top Xs) p /\
    (q:A) IN connected_component_of (subtopology top Xs) q /\
    ~((q:A) IN connected_component_of (subtopology top Xs) p)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF] THEN
    REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `cp = connected_component_of (subtopology top Xs) (p:A)` THEN
  ABBREV_TAC `cq = connected_component_of (subtopology top Xs) (q:A)` THEN
  (* the closures of cp and cq meet S, through the connected tube *)
  SUBGOAL_THEN `locally_connected_space (top:A topology) /\ closed_in top (S:A->bool) /\
                connected_in top (IMAGE (E:real^3->A) (annulus r1 r2)) /\ ~(S:A->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[GEO_MANIFOLD_LOCALLY_PATH_CONNECTED;
                    LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "S" THEN MATCH_MP_TAC P2HN_PARAM_IMAGE_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                            `annulus (&1 / &2) (&2):real^3->bool`] THEN
      REWRITE_TAC[COMPACT_SPHERE; P2HN_SPHERE_IN_ANNULUS] THEN
      UNDISCH_TAC `mfd_neck_chart top atlas (e:real^3->A)` THEN SIMP_TAC[mfd_neck_chart];
      MATCH_MP_TAC P2HN_PARAM_IMAGE_CONNECTED THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                            `annulus r1 r2:real^3->bool`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL; P2HN_ANNULUS_CONNECTED];
      EXPAND_TAC "S" THEN REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^3->A) (annulus r1 rho1) SUBSET IMAGE E (annulus r1 r2) /\
                IMAGE E (annulus rho2 r2) SUBSET IMAGE E (annulus r1 r2) /\
                IMAGE E (annulus rho1 rho2) SUBSET IMAGE E (annulus r1 r2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(top closure_of (cp:A->bool) INTER S = {}) /\
                ~(top closure_of (cq:A->bool) INTER S = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2HN_COMPONENT_CLOSURE_MEETS_CONN THEN
    EXISTS_TAC `IMAGE (E:real^3->A) (annulus r1 r2)` THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC(SET_RULE `!x:A a b c. x IN a /\ x IN c /\ a SUBSET b ==> ~(b INTER c = {})`) THEN
       ASM_MESON_TAC[];
       MATCH_MP_TAC(SET_RULE `!a b (s:A->bool). ~(s = {}) /\ s SUBSET a /\ a SUBSET b
                                                ==> ~(b INTER s = {})`) THEN
       EXISTS_TAC `IMAGE (E:real^3->A) (annulus rho1 rho2)` THEN ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `c:A->bool = cp \/ c = cq` MP_TAC THENL
   [MATCH_MP_TAC P2HN_THREE_COMPONENTS THEN
    MAP_EVERY EXISTS_TAC [`subtopology top (Xs:A->bool)`;
                          `IMAGE (e:real^3->A) (annulus (&1 / &2) (&1))`;
                          `IMAGE (e:real^3->A) (annulus (&1) (&2))`] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `e:real^3->A`] P2HN_SIDE_COLLAR_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
      MP_TAC(SPEC `c:A->bool` th) THEN MP_TAC(SPEC `cp:A->bool` th) THEN
      MP_TAC(SPEC `cq:A->bool` th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((q:A) IN cp)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN CONJ_TAC THENL
     [EXISTS_TAC `&3 / &4 % basis 1:real^3`; EXISTS_TAC `&3 / &2 % basis 1:real^3`] THEN
    SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= r1 /\ rho1 <= r2 /\ r1 <= rho2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC P2HN_TUBE_END_INNER THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `E:real^3->A`; `r1:real`; `r2:real`; `rho1:real`; `X:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `c:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `subtopology top (Xs:A->bool)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[P2HN_ANNULUS_CONNECTED] THEN
      REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; annulus;
                  IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC P2HN_TUBE_END_OUTER THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `E:real^3->A`; `r1:real`; `r2:real`; `rho2:real`; `X:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `c:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `subtopology top (Xs:A->bool)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[P2HN_ANNULUS_CONNECTED] THEN
      REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; annulus;
                  IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `q:A` THEN ASM_REWRITE_TAC[]]]);;

(* The connected form, every point a neck centre.                            *)

let P2HN_NECK_SIDE_NONCOMPACT = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps x0 e c.
       &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ riemannian_metric atlas g /\
       apx_sphere_sep top atlas /\ connected_space top /\
       (!x. x IN topspace top ==> ?e. rfs_neck (top,atlas) g eps x e) /\
       rfs_neck (top,atlas) g eps x0 e /\
       c IN connected_components_of
              (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
       ==> ~compact_in top (top closure_of c)`,
  X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gen"))
    (INST_TYPE [`:A`,`:A`] P2HN_NECK_SIDE_NONCOMPACT_GEN) THEN
  EXISTS_TAC `min eps0 (&1 / &4)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `x0:A`; `e:real^3->A`; `c:A->bool`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  USE_THEN "gen" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x0:A`; `e:real^3->A`; `c:A->bool`]) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `c:A->bool`] CLOSURE_OF_SUBSET_TOPSPACE) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2HN_COMPONENT_CLOSURE_MEETS THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x0 (e:real^3->A)` THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[GEO_MANIFOLD_LOCALLY_PATH_CONNECTED;
                  LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE];
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2HN_PARAM_IMAGE_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    REWRITE_TAC[P2HN_SPHERE_IN_ANNULUS] THEN MATCH_MP_TAC P2HN_NECK_DOM_COLLAR THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC]);;


let P2HN_NECK_CHART_OF_NECK = prove
 (`!top atlas (g:A->real^3^3) eps x e.
     rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &4
     ==> smooth_manifold_atlas top atlas /\ mfd_neck_chart top atlas e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck; mfd_neck_chart] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
  EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
  MATCH_MP_TAC P2HN_NECK_DOM_COLLAR THEN ASM_REWRITE_TAC[]);;

(* Two ends in the form of the hypothesis of P2C_REQ_TWO_ENDS_NO_CAP.       *)

let P2HN_TWO_ENDS = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) eps x0 e.
       &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\ riemannian_metric atlas g /\
       apx_sphere_sep top atlas /\ connected_space top /\
       (!x. x IN topspace top ==> ?e. rfs_neck (top,atlas) g eps x e) /\
       rfs_neck (top,atlas) g eps x0 e
       ==> ?K U1 U2. compact_in top K /\
                     U1 IN connected_components_of (subtopology top (topspace top DIFF K)) /\
                     U2 IN connected_components_of (subtopology top (topspace top DIFF K)) /\
                     ~(U1 = U2) /\ ~compact_in top (top closure_of U1) /\
                     ~compact_in top (top closure_of U2)`,
  X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "side"))
    P2HN_NECK_SIDE_NONCOMPACT THEN
  EXISTS_TAC `min eps1 (&1 / &4)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x0:A`; `e:real^3->A`] P2HN_NECK_CHART_OF_NECK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `S = IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  SUBGOAL_THEN `apx_separates top (S:A->bool) ((e:real^3->A)(&3 / &4 % basis 1)) (e(&4 / &3 % basis 1))`
  MP_TAC THENL
   [EXPAND_TAC "S" THEN UNDISCH_TAC `apx_sphere_sep top (atlas:((A->bool)#(A->real^3))->bool)` THEN
    REWRITE_TAC[apx_sphere_sep] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[apx_separates] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`S:A->bool`;
    `connected_component_of (subtopology top (topspace top DIFF S))
                            ((e:real^3->A)(&3 / &4 % basis 1))`;
    `connected_component_of (subtopology top (topspace top DIFF S))
                            ((e:real^3->A)(&4 / &3 % basis 1))`] THEN
  ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF; TOPSPACE_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC P2HN_PARAM_IMAGE_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus (&1 / &2) (&2):real^3->bool`] THEN
    REWRITE_TAC[COMPACT_SPHERE; P2HN_SPHERE_IN_ANNULUS] THEN
    ASM_MESON_TAC[mfd_neck_chart];
    ASM SET_TAC[];
    ASM SET_TAC[];
    DISCH_TAC THEN
    UNDISCH_TAC `~connected_component_of (subtopology top (topspace top DIFF S))
                    ((e:real^3->A)(&3 / &4 % basis 1)) (e(&4 / &3 % basis 1))` THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM IN] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL] THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
    USE_THEN "side" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `eps:real`; `x0:A`; `e:real^3->A`] THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF; TOPSPACE_SUBTOPOLOGY] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    USE_THEN "side" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                          `eps:real`; `x0:A`; `e:real^3->A`] THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF; TOPSPACE_SUBTOPOLOGY] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]]);;

