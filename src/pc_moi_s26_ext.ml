(* ========================================================================= *)
(* pc_moi_s26_ext: Moise 26.4 in open subsets of real^3 (GTM 47, pp.192-193) *)
(* from the loop theorem.  Main theorem EXT : |- MOI_S26_EXT                 *)
(* (pc_moi_s2628_stmt).  A loop on a closed connected surface M = |c| in an  *)
(* open set u, null in u but not in M, gives a PL disk in u meeting M        *)
(* exactly in its rim, which is not contractible in M.  Route: the PL        *)
(* singular disk f of PL_FILL, a compact neighbourhood W of M and f(T), the  *)
(* cut of W along M, a bicollar of M with two generic levels; among the      *)
(* level circles of f in the triangle one is essential in its level with the *)
(* fewest circles inside it (minimality in place of the book's induction on  *)
(* the number of circles); filling the inessential circles inside it gives a *)
(* null-homotopy off the open band, on one side of M; the loop pushed to M   *)
(* is null in that part and essential in M, and the loop theorem in that     *)
(* part gives the disk.                                                      *)
(* ========================================================================= *)

needs "src/pc_moi_s2628_stmt.ml";;
needs "src/pc_moi_fnd_bicol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* PL circles in the plane: Jordan facts, the closed disk j UNION           *)
(* inside j as the image of the unit disk, nesting of disjoint circles, and *)
(* Janiszewski for finitely many disjoint disks.                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S6E_JORDAN = prove
 (`!j:real^2->bool.
     pl_sphere 1 j
     ==> compact j /\ connected j /\ ~(j = {}) /\
         open (inside j) /\ connected (inside j) /\ bounded (inside j) /\
         ~(inside j = {}) /\
         open (outside j) /\ connected (outside j) /\ ~(outside j = {}) /\
         inside j INTER outside j = {} /\ inside j INTER j = {} /\
         outside j INTER j = {} /\
         inside j UNION outside j = (:real^2) DIFF j /\
         frontier (inside j) = j /\ frontier (outside j) = j /\
         closure (inside j) = j UNION inside j /\
         compact (j UNION inside j) /\ connected (j UNION inside j) /\
         (:real^2) DIFF (j UNION inside j) = outside j /\
         frontier (j UNION inside j) = j`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PL_SPHERE_1_POLYGON) THEN
  DISCH_THEN(X_CHOOSE_THEN `pp:(real^2)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `polygonal_path (pp:(real^2)list)` MOI_PL2_FRONTIER_JORDAN_REGION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `polygonal_path (pp:(real^2)list)` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `path (polygonal_path (pp:(real^2)list))` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (j:real^2->bool) /\ connected j /\ ~(j = {})`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      concl th = `path_image (polygonal_path (pp:(real^2)list)) = j`)) THEN
    ASM_SIMP_TAC[COMPACT_PATH_IMAGE; CONNECTED_PATH_IMAGE; PATH_IMAGE_NONEMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `path_image (polygonal_path (pp:(real^2)list)) = j`)) THEN
  ASM_REWRITE_TAC[INSIDE_NO_OVERLAP; OUTSIDE_NO_OVERLAP] THEN
  SUBGOAL_THEN `closure (inside j) = (j:real^2->bool) UNION inside j` ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `closure (inside j) = (j:real^2->bool) UNION inside j`)) THEN
    ASM_REWRITE_TAC[COMPACT_CLOSURE];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `closure (inside j) = (j:real^2->bool) UNION inside j`)) THEN
    ASM_SIMP_TAC[CONNECTED_CLOSURE];
    MP_TAC(ISPEC `j:real^2->bool` INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `j:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
    MP_TAC(ISPEC `j:real^2->bool` INSIDE_UNION_OUTSIDE) THEN
    MP_TAC(ISPEC `j:real^2->bool` OUTSIDE_NO_OVERLAP) THEN SET_TAC[]]);;

let MOI_S6E_DISK = prove
 (`!j:real^2->bool.
     pl_sphere 1 j
     ==> ?h h'. homeomorphism (cball(vec 0:real^2,&1),j UNION inside j) (h,h') /\
                IMAGE h (sphere(vec 0:real^2,&1)) = j`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_JORDAN) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[PL_SCHOENFLIES_2_STATEMENT] PL_SCHOENFLIES_2)) THEN
  REWRITE_TAC[pl_ball; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `a:real^2->real^2`
    (X_CHOOSE_THEN `a':real^2->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `convex (k:real^2->bool) /\ compact k /\ ~(interior k = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
      SUBGOAL_THEN `aff_dim (k:real^2->bool) = &(dimindex(:2))` MP_TAC THENL
       [REWRITE_TAC[DIMINDEX_2] THEN ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
      ASM_MESON_TAC[AFF_DIM_NONEMPTY_INTERIOR_EQ; SIMPLEX_IMP_CONVEX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `vec 0:real^2`; `&1`] HOMEOMORPHIC_CONVEX_COMPACT_CBALL) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^2->real^2` (X_CHOOSE_TAC `b':real^2->real^2`)) THEN
  MAP_EVERY EXISTS_TAC [`(a:real^2->real^2) o (b:real^2->real^2)`;
                        `(b':real^2->real^2) o (a':real^2->real^2)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN
  MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `k:real^2->bool`; `b:real^2->real^2`;
                 `b':real^2->real^2`] MOI_PL2_HOMEOMORPHISM_FRONTIER) THEN
  ASM_SIMP_TAC[CLOSED_CBALL; COMPACT_IMP_CLOSED; FRONTIER_CBALL] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `(j:real^2->bool) UNION inside j`; `a:real^2->real^2`;
                 `a':real^2->real^2`] MOI_PL2_HOMEOMORPHISM_FRONTIER) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[]);;

let MOI_S6E_SIDE_OF = prove
 (`!j k:real^2->bool.
     pl_sphere 1 j /\ connected k /\ DISJOINT k j
     ==> k SUBSET inside j \/ k SUBSET outside j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_JORDAN) THEN
  ASM_CASES_TAC `(k:real^2->bool) SUBSET inside j` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k INTER inside j = {}:real^2->bool` THENL
   [UNDISCH_TAC `k INTER inside j = {}:real^2->bool` THEN
    UNDISCH_TAC `DISJOINT (k:real^2->bool) j` THEN
    UNDISCH_TAC `inside j UNION outside j = (:real^2) DIFF j` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `inside j:real^2->bool`] CONNECTED_INTER_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((k:real^2->bool) SUBSET inside j)` THEN
  UNDISCH_TAC `DISJOINT (k:real^2->bool) j` THEN SET_TAC[]);;

let MOI_S6E_NEST_IN = prove
 (`!j j':real^2->bool.
     pl_sphere 1 j /\ pl_sphere 1 j' /\ j' SUBSET inside j
     ==> j' UNION inside j' SUBSET inside j /\ j SUBSET outside j'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_JORDAN o check (fun th ->
    concl th = `pl_sphere 1 (j:real^2->bool)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_JORDAN o check (fun th ->
    concl th = `pl_sphere 1 (j':real^2->bool)`)) THEN
  SUBGOAL_THEN `inside j' SUBSET inside (j:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_INSIDE_COMPACT_CONNECTED THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`j':real^2->bool`; `j:real^2->bool`] MOI_S6E_SIDE_OF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(j':real^2->bool) SUBSET inside j` THEN
    UNDISCH_TAC `inside j INTER j = {}:real^2->bool` THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(j:real^2->bool) SUBSET inside j'` THEN
  UNDISCH_TAC `inside j' SUBSET inside (j:real^2->bool)` THEN
  UNDISCH_TAC `inside j INTER j = {}:real^2->bool` THEN
  UNDISCH_TAC `~(j:real^2->bool = {})` THEN SET_TAC[]);;

let MOI_S6E_NEST_OUT = prove
 (`!j j':real^2->bool.
     pl_sphere 1 j /\ pl_sphere 1 j' /\ j' SUBSET outside j /\ j SUBSET outside j'
     ==> DISJOINT (j UNION inside j) (j' UNION inside j')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_JORDAN o check (fun th ->
    concl th = `pl_sphere 1 (j:real^2->bool)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_JORDAN o check (fun th ->
    concl th = `pl_sphere 1 (j':real^2->bool)`)) THEN
  MP_TAC(ISPECL [`j':real^2->bool`; `(j:real^2->bool) UNION inside j`] MOI_S6E_SIDE_OF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(j':real^2->bool) SUBSET outside j` THEN
    UNDISCH_TAC `inside j INTER outside j = {}:real^2->bool` THEN
    UNDISCH_TAC `outside j INTER j = {}:real^2->bool` THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `(j:real^2->bool) UNION inside j SUBSET inside j'` THEN
    UNDISCH_TAC `(j:real^2->bool) SUBSET outside j'` THEN
    UNDISCH_TAC `inside j' INTER outside j' = {}:real^2->bool` THEN
    UNDISCH_TAC `~(j:real^2->bool = {})` THEN SET_TAC[];
    UNDISCH_TAC `(j:real^2->bool) UNION inside j SUBSET outside j'` THEN
    UNDISCH_TAC `inside j' INTER outside j' = {}:real^2->bool` THEN
    UNDISCH_TAC `outside j' INTER j' = {}:real^2->bool` THEN SET_TAC[]]);;

let MOI_S6E_JANISZEWSKI_FINITE = prove
 (`!(u:real^2->bool) kk.
     open u /\ connected u /\ FINITE kk /\
     (!k. k IN kk ==> compact k /\ k SUBSET u /\ connected ((:real^2) DIFF k)) /\
     pairwise DISJOINT kk
     ==> connected (u DIFF UNIONS kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `u DIFF UNIONS kk =
                (:real^2) DIFF (((:real^2) DIFF u) UNION UNIONS kk)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `pairwise DISJOINT (kk:(real^2->bool)->bool)` THEN
  UNDISCH_TAC `!k. k IN kk ==> compact k /\ k SUBSET u /\
                              connected ((:real^2) DIFF k)` THEN
  UNDISCH_TAC `FINITE (kk:(real^2->bool)->bool)` THEN
  SPEC_TAC(`kk:(real^2->bool)->bool`,`kk:(real^2->bool)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_0; UNION_EMPTY] THEN
    SUBGOAL_THEN `(:real^2) DIFF ((:real^2) DIFF u) = u` SUBST1_TAC THENL
     [SET_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:real^2->bool`; `kk:(real^2->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[FORALL_IN_INSERT; PAIRWISE_INSERT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((:real^2) DIFF u) UNION UNIONS (k INSERT kk) =
    k UNION (((:real^2) DIFF u) UNION UNIONS kk)` SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_INSERT] THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC JANISZEWSKI_CONNECTED THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[GSYM OPEN_CLOSED]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    SUBGOAL_THEN `k INTER UNIONS kk = {}:real^2->bool` ASSUME_TAC THENL
     [REWRITE_TAC[INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `t:real^2->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `DISJOINT (k:real^2->bool) t` MP_TAC THENL
       [ASM_MESON_TAC[]; SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `k INTER (((:real^2) DIFF u) UNION UNIONS kk) = {}`
      (fun th -> REWRITE_TAC[th; CONNECTED_EMPTY]) THEN
    UNDISCH_TAC `k INTER UNIONS kk = {}:real^2->bool` THEN
    UNDISCH_TAC `(k:real^2->bool) SUBSET u` THEN SET_TAC[];
    USE_THEN "ih" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Finite families of disjoint PL circles inside a compact connected        *)
(* set c0 of the plane: the outermost ones, their disks, the region between *)
(* them, a minimal member for any property, and pasting maps over the       *)
(* outermost disks.                                                          *)
(* ------------------------------------------------------------------------- *)

let moi_s6e_circles = new_definition
 `moi_s6e_circles (cc:(real^2->bool)->bool) <=>
    FINITE cc /\ pairwise DISJOINT cc /\ (!j. j IN cc ==> pl_sphere 1 j)`;;

let moi_s6e_outer = new_definition
 `moi_s6e_outer (cc:(real^2->bool)->bool) (c0:real^2->bool) =
    {j | j IN cc /\ j SUBSET inside c0 /\
         ~(?j'. j' IN cc /\ j' SUBSET inside c0 /\ j SUBSET inside j')}`;;

let MOI_S6E_KIN = prove
 (`!(c0:real^2->bool) j.
     compact c0 /\ connected c0 /\ pl_sphere 1 j /\ j SUBSET inside c0
     ==> j UNION inside j SUBSET inside c0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_JORDAN) THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN
  MATCH_MP_TAC INSIDE_INSIDE_COMPACT_CONNECTED THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED]);;

let MOI_S6E_CIRCLE_PAIR = prove
 (`!cc (j1:real^2->bool) j2.
     moi_s6e_circles cc /\ j1 IN cc /\ j2 IN cc /\ j1 SUBSET j2 UNION inside j2
     ==> j1 = j2 \/ j1 UNION inside j1 SUBSET inside j2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s6e_circles; pairwise] THEN STRIP_TAC THEN
  ASM_CASES_TAC `j1:real^2->bool = j2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DISJOINT (j1:real^2->bool) j2` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(j1:real^2->bool) SUBSET inside j2` ASSUME_TAC THENL
   [UNDISCH_TAC `(j1:real^2->bool) SUBSET j2 UNION inside j2` THEN
    UNDISCH_TAC `DISJOINT (j1:real^2->bool) j2` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j2:real^2->bool`; `j1:real^2->bool`] MOI_S6E_NEST_IN) THEN
  ASM_SIMP_TAC[]);;

let MOI_S6E_OUTER_COVER = prove
 (`!cc (c0:real^2->bool) j.
     moi_s6e_circles cc /\ compact c0 /\ connected c0 /\ j IN cc /\ j SUBSET inside c0
     ==> ?j'. j' IN moi_s6e_outer cc c0 /\ j SUBSET j' UNION inside j'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6e_circles]) THEN
  SUBGOAL_THEN
   `!n (jj:real^2->bool).
      jj IN cc /\ jj SUBSET inside c0 /\
      CARD {j'' | j'' IN cc /\ j'' SUBSET inside c0 /\ jj SUBSET inside j''} = n
      ==> ?j'. j' IN moi_s6e_outer cc c0 /\ jj SUBSET j' UNION inside j'`
  (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `jj:real^2->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(jj:real^2->bool) IN moi_s6e_outer cc c0` THENL
   [EXISTS_TAC `jj:real^2->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?j3:real^2->bool. j3 IN cc /\ j3 SUBSET inside c0 /\ jj SUBSET inside j3`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~((jj:real^2->bool) IN moi_s6e_outer cc c0)` THEN
    ASM_REWRITE_TAC[moi_s6e_outer; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (jj:real^2->bool) /\ pl_sphere 1 (j3:real^2->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`j3:real^2->bool`; `jj:real^2->bool`] MOI_S6E_NEST_IN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `CARD {j'' | j'' IN cc /\ j'' SUBSET inside c0 /\ (j3:real^2->bool) SUBSET inside j''}`) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CARD_PSUBSET THEN
    ASM_SIMP_TAC[FINITE_RESTRICT] THEN REWRITE_TAC[PSUBSET_ALT] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `j4:real^2->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`j4:real^2->bool`; `j3:real^2->bool`] MOI_S6E_NEST_IN) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(jj:real^2->bool) SUBSET inside j3` THEN SET_TAC[];
      EXISTS_TAC `j3:real^2->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_JORDAN o check (fun th ->
        concl th = `pl_sphere 1 (j3:real^2->bool)`)) THEN
      UNDISCH_TAC `inside j3 INTER j3 = {}:real^2->bool` THEN
      UNDISCH_TAC `~(j3:real^2->bool = {})` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `j3:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j':real^2->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`cc:(real^2->bool)->bool`; `j3:real^2->bool`; `j':real^2->bool`]
    MOI_S6E_CIRCLE_PAIR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(j':real^2->bool) IN moi_s6e_outer cc c0` THEN
    REWRITE_TAC[moi_s6e_outer; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `j3:real^2->bool = j'`)) THEN
    UNDISCH_TAC `(jj:real^2->bool) SUBSET inside j'` THEN SET_TAC[];
    UNDISCH_TAC `(jj:real^2->bool) SUBSET inside j3` THEN
    UNDISCH_TAC `(j3:real^2->bool) UNION inside j3 SUBSET inside j'` THEN
    SET_TAC[]]);;

let MOI_S6E_OUTER_DISJOINT = prove
 (`!cc (c0:real^2->bool) j1 j2.
     moi_s6e_circles cc /\
     j1 IN moi_s6e_outer cc c0 /\ j2 IN moi_s6e_outer cc c0 /\ ~(j1 = j2)
     ==> DISJOINT (j1 UNION inside j1) (j2 UNION inside j2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s6e_outer; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6e_circles]) THEN
  SUBGOAL_THEN `pl_sphere 1 (j1:real^2->bool) /\ pl_sphere 1 (j2:real^2->bool) /\
                DISJOINT j1 j2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pairwise]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S6E_NEST_OUT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`j1:real^2->bool`; `j2:real^2->bool`] MOI_S6E_SIDE_OF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_S6E_JORDAN]; ASM_MESON_TAC[DISJOINT_SYM]];
      ASM_MESON_TAC[]];
    MP_TAC(ISPECL [`j2:real^2->bool`; `j1:real^2->bool`] MOI_S6E_SIDE_OF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_S6E_JORDAN];
      ASM_MESON_TAC[]]]);;

let MOI_S6E_MIN_CIRCLE = prove
 (`!cc (E:(real^2->bool)->bool) j.
     moi_s6e_circles cc /\ j IN cc /\ E j
     ==> ?j'. j' IN cc /\ E j' /\
              !j''. j'' IN cc /\ j'' SUBSET inside j' ==> ~E j''`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6e_circles]) THEN
  SUBGOAL_THEN
   `!n (jj:real^2->bool).
      jj IN cc /\ E jj /\ CARD {j'' | j'' IN cc /\ j'' SUBSET inside jj} = n
      ==> ?j'. j' IN cc /\ E j' /\
               !j''. j'' IN cc /\ j'' SUBSET inside j' ==> ~E j''`
  (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `jj:real^2->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `!j''. j'' IN cc /\ j'' SUBSET inside jj ==> ~(E:(real^2->bool)->bool) j''`
  THENL [EXISTS_TAC `jj:real^2->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j1:real^2->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  SUBGOAL_THEN `pl_sphere 1 (jj:real^2->bool) /\ pl_sphere 1 (j1:real^2->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`jj:real^2->bool`; `j1:real^2->bool`] MOI_S6E_NEST_IN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CARD {j'' | j'' IN cc /\ j'' SUBSET inside (j1:real^2->bool)}`) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CARD_PSUBSET THEN
    ASM_SIMP_TAC[FINITE_RESTRICT] THEN REWRITE_TAC[PSUBSET_ALT] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `j4:real^2->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(j1:real^2->bool) UNION inside j1 SUBSET inside jj` THEN
      UNDISCH_TAC `(j4:real^2->bool) SUBSET inside j1` THEN SET_TAC[];
      EXISTS_TAC `j1:real^2->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_JORDAN o check (fun th ->
        concl th = `pl_sphere 1 (j1:real^2->bool)`)) THEN
      UNDISCH_TAC `inside j1 INTER j1 = {}:real^2->bool` THEN
      UNDISCH_TAC `~(j1:real^2->bool = {})` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `j1:real^2->bool`) THEN ASM_REWRITE_TAC[]);;

let MOI_S6E_FILLED_COMPACT = prove
 (`!c0:real^2->bool.
     compact c0
     ==> compact (c0 UNION inside c0) /\ c0 UNION inside c0 = (:real^2) DIFF outside c0`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `c0 UNION inside c0 = (:real^2) DIFF outside c0` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c0:real^2->bool` INSIDE_UNION_OUTSIDE) THEN
    MP_TAC(ISPEC `c0:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
    MP_TAC(ISPEC `c0:real^2->bool` OUTSIDE_NO_OVERLAP) THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[BOUNDED_UNION] THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; BOUNDED_INSIDE];
    REWRITE_TAC[GSYM OPEN_CLOSED] THEN ASM_SIMP_TAC[OPEN_OUTSIDE; COMPACT_IMP_CLOSED]]);;

let MOI_S6E_OUTER_FACTS = prove
 (`!cc (c0:real^2->bool).
     moi_s6e_circles cc /\ compact c0 /\ connected c0
     ==> FINITE (moi_s6e_outer cc c0) /\ moi_s6e_outer cc c0 SUBSET cc /\
         ~(c0 IN moi_s6e_outer cc c0) /\
         (!j. j IN moi_s6e_outer cc c0
              ==> pl_sphere 1 j /\ j SUBSET inside c0 /\
                  j UNION inside j SUBSET inside c0 /\
                  compact (j UNION inside j) /\
                  connected ((:real^2) DIFF (j UNION inside j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6e_circles]) THEN
  SUBGOAL_THEN `moi_s6e_outer cc (c0:real^2->bool) SUBSET cc` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s6e_outer; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j:real^2->bool. j IN moi_s6e_outer cc c0
                     ==> pl_sphere 1 j /\ j SUBSET inside c0 /\
                         j UNION inside j SUBSET inside c0 /\
                         compact (j UNION inside j) /\
                         connected ((:real^2) DIFF (j UNION inside j))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:real^2->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pl_sphere 1 (j:real^2->bool) /\ j SUBSET inside c0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(j:real^2->bool) IN moi_s6e_outer cc c0` THEN
      REWRITE_TAC[moi_s6e_outer; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_JORDAN) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S6E_KIN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c0:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_JORDAN) THEN
  UNDISCH_TAC `(c0:real^2->bool) SUBSET inside c0` THEN
  UNDISCH_TAC `inside c0 INTER c0 = {}:real^2->bool` THEN
  UNDISCH_TAC `~(c0:real^2->bool = {})` THEN SET_TAC[]);;

let MOI_S6E_REGION_MISS = prove
 (`!cc (c0:real^2->bool) j.
     moi_s6e_circles cc /\ compact c0 /\ connected c0 /\ j IN cc /\
     (j SUBSET inside c0 \/ DISJOINT j (inside c0))
     ==> DISJOINT j (inside c0 DIFF UNIONS {k UNION inside k | k IN moi_s6e_outer cc c0})`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  STRIP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MP_TAC(ISPECL [`cc:(real^2->bool)->bool`; `c0:real^2->bool`; `j:real^2->bool`]
    MOI_S6E_OUTER_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j':real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(j':real^2->bool) UNION inside j' SUBSET
                UNIONS {k UNION inside k | k IN moi_s6e_outer cc c0}` MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!a:real^2->bool f. a IN f ==> a SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `j':real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(j:real^2->bool) SUBSET j' UNION inside j'` THEN SET_TAC[]);;

let MOI_S6E_REGION_CONNECTED = prove
 (`!cc (c0:real^2->bool).
     moi_s6e_circles cc /\ compact c0 /\ connected c0 /\ connected (inside c0)
     ==> connected (inside c0 DIFF UNIONS {k UNION inside k | k IN moi_s6e_outer cc c0})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cc:(real^2->bool)->bool`; `c0:real^2->bool`] MOI_S6E_OUTER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S6E_JANISZEWSKI_FINITE THEN
  ASM_SIMP_TAC[OPEN_INSIDE; COMPACT_IMP_CLOSED; SIMPLE_IMAGE; FINITE_IMAGE] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:real^2->bool` THEN DISCH_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `j1:real^2->bool` THEN DISCH_TAC THEN
  X_GEN_TAC `j2:real^2->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j1:real^2->bool = j2` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_S6E_OUTER_DISJOINT THEN
  MAP_EVERY EXISTS_TAC [`cc:(real^2->bool)->bool`; `c0:real^2->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S6E_PASTE = prove
 (`!cc (c0:real^2->bool) (f:real^2->real^3) G.
     moi_s6e_circles cc /\ compact c0 /\ connected c0 /\
     f continuous_on (c0 UNION inside c0) /\
     (!j. j IN moi_s6e_outer cc c0
          ==> (G j) continuous_on (j UNION inside j) /\ (!x. x IN j ==> G j x = f x))
     ==> ?g. g continuous_on (c0 UNION inside c0) /\
             (!x. x IN c0 UNION
                       (inside c0 DIFF UNIONS {k UNION inside k | k IN moi_s6e_outer cc c0})
                  ==> g x = f x) /\
             (!j x. j IN moi_s6e_outer cc c0 /\ x IN j UNION inside j ==> g x = G j x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cc:(real^2->bool)->bool`; `c0:real^2->bool`] MOI_S6E_OUTER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c0:real^2->bool` MOI_S6E_FILLED_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `!j1 j2:real^2->bool. j1 IN moi_s6e_outer cc c0 /\ j2 IN moi_s6e_outer cc c0 /\
                         ~(j1 = j2) ==> DISJOINT (j1 UNION inside j1) (j2 UNION inside j2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S6E_OUTER_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`cc:(real^2->bool)->bool`; `c0:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j:real^2->bool. j IN moi_s6e_outer cc c0 ==> j INTER inside j = {}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `pl_sphere 1 (j:real^2->bool)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_JORDAN) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`subtopology euclidean ((c0:real^2->bool) UNION inside c0)`;
    `euclidean:(real^3)topology`;
    `\i:real^2->bool. if i = c0 then (f:real^2->real^3) else G i`;
    `\i:real^2->bool. if i = c0
                      then ((c0:real^2->bool) UNION inside c0) DIFF
                           UNIONS {inside k | k IN moi_s6e_outer cc c0}
                      else i UNION inside i`;
    `(c0:real^2->bool) INSERT moi_s6e_outer cc c0`] PASTING_LEMMA_EXISTS_CLOSED) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; FINITE_INSERT] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_INSERT] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      ASM_CASES_TAC `?k:real^2->bool. k IN moi_s6e_outer cc c0 /\ x IN inside k` THENL
       [FIRST_X_ASSUM(X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `k:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]];
        EXISTS_TAC `c0:real^2->bool` THEN REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
        ASM_MESON_TAC[]];
      REWRITE_TAC[FORALL_IN_INSERT] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; CONTINUOUS_MAP_EUCLIDEAN] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC CLOSED_DIFF THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
          MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
          X_GEN_TAC `k:real^2->bool` THEN DISCH_TAC THEN
          SUBGOAL_THEN `pl_sphere 1 (k:real^2->bool)`
           (fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_S6E_JORDAN th)) THEN
          ASM_MESON_TAC[];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `(c0:real^2->bool) UNION inside c0` THEN ASM_REWRITE_TAC[] THEN
          SET_TAC[]];
        X_GEN_TAC `j:real^2->bool` THEN DISCH_TAC THEN
        SUBGOAL_THEN `~(j:real^2->bool = c0)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; CONTINUOUS_MAP_EUCLIDEAN] THEN
        SUBGOAL_THEN `(j:real^2->bool) UNION inside j SUBSET c0 UNION inside c0` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
          SUBGOAL_THEN `((c0:real^2->bool) UNION inside c0) INTER (j UNION inside j) =
                        j UNION inside j` SUBST1_TAC THENL
           [ASM SET_TAC[]; ASM_SIMP_TAC[]]]];
      REWRITE_TAC[FORALL_IN_INSERT; IN_INSERT; IN_INTER] THEN
      MAP_EVERY X_GEN_TAC [`i1:real^2->bool`; `i2:real^2->bool`; `x:real^2`] THEN
      ASM_CASES_TAC `i1:real^2->bool = c0` THEN ASM_CASES_TAC `i2:real^2->bool = c0` THEN
      ASM_REWRITE_TAC[] THENL
       [STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i2:real^2->bool` o check (fun th ->
          is_forall(concl th) &&
          can (find_term ((=) `G:(real^2->bool)->real^2->real^3`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o GSYM o CONJUNCT2) THEN
        UNDISCH_TAC `(x:real^2) IN i2 UNION inside i2` THEN
        UNDISCH_TAC `(x:real^2) IN (c0 UNION inside c0) DIFF
                     UNIONS {inside k | k IN moi_s6e_outer cc c0}` THEN
        REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; IN_UNION] THEN ASM_MESON_TAC[];
        STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i1:real^2->bool` o check (fun th ->
          is_forall(concl th) &&
          can (find_term ((=) `G:(real^2->bool)->real^2->real^3`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
        UNDISCH_TAC `(x:real^2) IN i1 UNION inside i1` THEN
        UNDISCH_TAC `(x:real^2) IN (c0 UNION inside c0) DIFF
                     UNIONS {inside k | k IN moi_s6e_outer cc c0}` THEN
        REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; IN_UNION] THEN ASM_MESON_TAC[];
        STRIP_TAC THEN ASM_CASES_TAC `i1:real^2->bool = i2` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`i1:real^2->bool`; `i2:real^2->bool`] o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^2->real^3` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `c0:real^2->bool`]) THEN
    REWRITE_TAC[IN_INSERT; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^2) IN c0 UNION
                 (inside c0 DIFF UNIONS {k UNION inside k | k IN moi_s6e_outer cc c0})` THEN
    REWRITE_TAC[IN_UNION; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
    MP_TAC(ISPEC `c0:real^2->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`j:real^2->bool`; `x:real^2`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `j:real^2->bool`]) THEN
    SUBGOAL_THEN `~(j:real^2->bool = c0)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Loops and disks.  The unit circle loop (as in HOL's                       *)
(* HOMOTOPIC_CIRCLEMAPS_IMP_HOMOTOPIC_LOOPS); a map on a disk j UNION        *)
(* inside j makes its boundary loop null in the image set, and a null       *)
(* boundary loop extends over the disk (NULLHOMOTOPIC_FROM_SPHERE_EXTENSION).*)
(* The boundary loop of the standard triangle likewise.                      *)
(* ------------------------------------------------------------------------- *)

let moi_s6e_circ = new_definition
 `moi_s6e_circ = cexp o (\t. Cx(&2 * pi * drop t) * ii)`;;

let MOI_S6E_CIRC = prove
 (`path moi_s6e_circ /\ pathstart moi_s6e_circ = Cx(&1) /\
   pathfinish moi_s6e_circ = Cx(&1) /\
   path_image moi_s6e_circ = sphere(vec 0,&1) /\
   homotopic_loops (cball(vec 0,&1)) moi_s6e_circ (linepath(Cx(&1),Cx(&1))) /\
   !z. z IN sphere(vec 0,&1) ==> moi_s6e_circ (lift(Arg z / (&2 * pi))) = z`,
  SUBGOAL_THEN `path moi_s6e_circ /\ pathstart moi_s6e_circ = Cx(&1) /\
                pathfinish moi_s6e_circ = Cx(&1) /\
                path_image moi_s6e_circ = sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `moi_s6e_circ = circlepath(Cx(&0),&1)` SUBST1_TAC THENL
     [REWRITE_TAC[moi_s6e_circ; CIRCLEPATH; FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
      REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_MUL_LID] THEN AP_TERM_TAC THEN
      REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    REWRITE_TAC[PATH_CIRCLEPATH; PATHSTART_CIRCLEPATH; PATHFINISH_CIRCLEPATH] THEN
    SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_POS; COMPLEX_ADD_LID; COMPLEX_VEC_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `cball(vec 0:complex,&1)` SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY) THEN
    SIMP_TAC[CONVEX_IMP_SIMPLY_CONNECTED; CONVEX_CBALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL] THEN
    REWRITE_TAC[IN_CBALL_0; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_s6e_circ; o_THM; LIFT_DROP] THEN
  SUBGOAL_THEN `&2 * pi * Arg z / (&2 * pi) = Arg z` SUBST1_TAC THENL
   [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2(CONJUNCT2(SPEC `z:complex` ARG))] THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LID] THEN AP_TERM_TAC THEN
  REWRITE_TAC[COMPLEX_MUL_SYM]);;

let MOI_S6E_LOOP_NULL_BASE = prove
 (`!s (p:real^1->real^N) a.
     homotopic_loops s p (linepath(a,a))
     ==> homotopic_loops s p (linepath(pathstart p,pathstart p))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_PATHS_NULL) THEN
  DISCH_TAC THEN MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
  ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ASM_MESON_TAC[HOMOTOPIC_LOOPS_IMP_LOOP]);;

let MOI_S6E_DISK_NULL = prove
 (`!(h:real^2->real^2) h' j (g:real^2->real^N) s.
     homeomorphism (cball(vec 0,&1),j UNION inside j) (h,h') /\
     g continuous_on (j UNION inside j) /\ IMAGE g (j UNION inside j) SUBSET s
     ==> path ((g o h) o moi_s6e_circ) /\
         pathfinish ((g o h) o moi_s6e_circ) = pathstart ((g o h) o moi_s6e_circ) /\
         homotopic_loops s ((g o h) o moi_s6e_circ)
           (linepath(pathstart ((g o h) o moi_s6e_circ),
                     pathstart ((g o h) o moi_s6e_circ)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g o (h:real^2->real^2)) continuous_on cball(vec 0,&1) /\
                IMAGE (g o h) (cball(vec 0,&1)) SUBSET (s:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s6e_circ`; `linepath(Cx(&1),Cx(&1))`; `(g:real^2->real^N) o (h:real^2->real^2)`;
                 `cball(vec 0:real^2,&1)`; `s:real^N->bool`]
    HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[MOI_S6E_CIRC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((g:real^2->real^N) o (h:real^2->real^2)) o linepath(Cx(&1),Cx(&1)) =
                linepath((g o h) (Cx(&1)),(g o h) (Cx(&1)))` ASSUME_TAC THENL
   [REWRITE_TAC[LINEPATH_REFL; FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `pathstart (((g:real^2->real^N) o (h:real^2->real^2)) o moi_s6e_circ) = (g o h) (Cx(&1))`
  ASSUME_TAC THENL [REWRITE_TAC[PATHSTART_COMPOSE; MOI_S6E_CIRC]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN REWRITE_TAC[MOI_S6E_CIRC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL];
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; MOI_S6E_CIRC];
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homotopic_loops (s:real^N->bool) (((g:real^2->real^N) o (h:real^2->real^2)) o moi_s6e_circ)
                   (((g:real^2->real^N) o (h:real^2->real^2)) o linepath(Cx(&1),Cx(&1)))` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S6E_NULL_DISK = prove
 (`!(h:real^2->real^2) h' j (q:real^2->real^N) s a.
     homeomorphism (cball(vec 0,&1),j UNION inside j) (h,h') /\
     IMAGE h (sphere(vec 0,&1)) = j /\
     q continuous_on j /\ IMAGE q j SUBSET s /\
     homotopic_loops s ((q o h) o moi_s6e_circ) (linepath(a,a))
     ==> ?G. G continuous_on (j UNION inside j) /\
             IMAGE G (j UNION inside j) SUBSET s /\
             !x. x IN j ==> G x = q x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_HOMOTOPIC_CIRCLEMAPS o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "homotopic_loops")) (concl th) &&
    not (is_imp (concl th)))) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `?c. homotopic_with (\x. T)
          (subtopology euclidean (sphere(vec 0,&1)),subtopology euclidean s)
          ((q:real^2->real^N) o (h:real^2->real^2)) (\x. c)`
  MP_TAC THENL
   [EXISTS_TAC `a:real^N` THEN
    MATCH_MP_TAC(INST_TYPE [`:complex`,`:A`; `:real^N`,`:B`] HOMOTOPIC_WITH_EQ) THEN
    MAP_EVERY EXISTS_TAC
     [`(((q:real^2->real^N) o (h:real^2->real^2)) o moi_s6e_circ) o (\z. lift(Arg z / (&2 * pi)))`;
      `linepath(a:real^N,a) o (\z. lift(Arg z / (&2 * pi)))`] THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[o_THM; LINEPATH_REFL; MOI_S6E_CIRC];
    ALL_TAC] THEN
  REWRITE_TAC[NULLHOMOTOPIC_FROM_SPHERE_EXTENSION] THEN
  DISCH_THEN(X_CHOOSE_THEN `G0:real^2->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(G0:real^2->real^N) o (h':real^2->real^2)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?z. z IN sphere(vec 0:real^2,&1) /\ x = (h:real^2->real^2) z`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(h':real^2->real^2) (h z) = z` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SPHERE_SUBSET_CBALL; SUBSET];
      ASM_SIMP_TAC[o_THM]]]);;

(* The standard triangle T (local copies of the elementary facts; the loop   *)
(* theorem statement files with MOI_LTD_... are not loaded here).            *)

let MOI_S6E_TRIANGLE = prove
 (`compact std_triangle /\ convex std_triangle /\ ~(interior std_triangle = {}) /\
   relative_frontier std_triangle SUBSET std_triangle /\
   relative_frontier std_triangle SUBSET closure (relative_interior std_triangle) /\
   connected (relative_interior std_triangle) /\
   compact (relative_frontier std_triangle) /\
   connected (relative_frontier std_triangle) /\
   ~(relative_frontier std_triangle = {}) /\
   inside (relative_frontier std_triangle) = relative_interior std_triangle /\
   relative_frontier std_triangle UNION inside (relative_frontier std_triangle) =
   std_triangle /\
   path std_triangle_loop /\ pathstart std_triangle_loop = vec 0 /\
   pathfinish std_triangle_loop = vec 0 /\
   path_image std_triangle_loop = relative_frontier std_triangle`,
  SUBGOAL_THEN `~collinear {vec 0:real^2, basis 1, basis 2}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_3_2D; VEC_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact std_triangle /\ convex std_triangle` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[std_triangle; CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC POLYTOPE_IMP_COMPACT THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(interior std_triangle = {})` ASSUME_TAC THENL
   [SUBGOAL_THEN `aff_dim std_triangle = &(dimindex(:2))` MP_TAC THENL
     [REWRITE_TAC[std_triangle; AFF_DIM_CONVEX_HULL; DIMINDEX_2] THEN
      SUBGOAL_THEN `~affine_dependent {vec 0:real^2, basis 1, basis 2}` ASSUME_TAC THENL
       [ASM_MESON_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
      ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
      SUBGOAL_THEN `CARD {vec 0:real^2, basis 1, basis 2} = 3` SUBST1_TAC THENL
       [UNDISCH_TAC `~collinear {vec 0:real^2, basis 1, basis 2}` THEN
        REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN STRIP_TAC THEN
        SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
        ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
        INT_ARITH_TAC];
      ASM_MESON_TAC[AFF_DIM_NONEMPTY_INTERIOR_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier std_triangle = frontier std_triangle /\
                relative_interior std_triangle = interior std_triangle`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; RELATIVE_INTERIOR_NONEMPTY_INTERIOR];
    ALL_TAC] THEN
  SUBGOAL_THEN `path std_triangle_loop /\ pathstart std_triangle_loop = vec 0 /\
                pathfinish std_triangle_loop = vec 0 /\
                path_image std_triangle_loop = relative_frontier std_triangle`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[std_triangle_loop] THEN
    REWRITE_TAC[std_triangle] THEN ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    SIMP_TAC[PATH_JOIN; PATH_LINEPATH; PATHSTART_JOIN; PATHFINISH_JOIN;
             PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_JOIN;
             PATH_IMAGE_LINEPATH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inside (frontier std_triangle) = interior std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_FRONTIER_EQ_INTERIOR THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `relative_frontier std_triangle = frontier std_triangle`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `relative_interior std_triangle = interior std_triangle`)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ASM_SIMP_TAC[CONVEX_CLOSURE_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERIOR];
    MATCH_MP_TAC COMPACT_FRONTIER THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `path_image std_triangle_loop = frontier std_triangle`)) THEN
    ASM_SIMP_TAC[CONNECTED_PATH_IMAGE];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `path_image std_triangle_loop = frontier std_triangle`)) THEN
    REWRITE_TAC[PATH_IMAGE_NONEMPTY];
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    MP_TAC(ISPEC `std_triangle` INTERIOR_SUBSET) THEN SET_TAC[]]);;

let MOI_S6E_TRI_NULL = prove
 (`!(f:real^2->real^N) g s.
     f continuous_on std_triangle /\
     g continuous_on std_triangle /\ IMAGE g std_triangle SUBSET s /\
     (!x. x IN relative_frontier std_triangle ==> g x = f x)
     ==> homotopic_loops s (f o std_triangle_loop)
           (linepath(pathstart (f o std_triangle_loop),pathstart (f o std_triangle_loop)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `compact std_triangle /\ convex std_triangle /\ path std_triangle_loop /\
    pathstart std_triangle_loop = vec 0 /\ pathfinish std_triangle_loop = vec 0 /\
    path_image std_triangle_loop = relative_frontier std_triangle /\
    relative_frontier std_triangle SUBSET std_triangle`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S6E_TRIANGLE]; ALL_TAC] THEN
  SUBGOAL_THEN `homotopic_loops std_triangle std_triangle_loop (linepath(vec 0,vec 0))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `std_triangle` SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY) THEN
    ASM_SIMP_TAC[CONVEX_IMP_SIMPLY_CONNECTED] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `std_triangle_loop` PATHSTART_IN_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`std_triangle_loop`; `linepath(vec 0:real^2,vec 0)`; `g:real^2->real^N`;
                 `std_triangle`; `s:real^N->bool`] HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(g:real^2->real^N) o linepath(vec 0,vec 0) = linepath(g(vec 0),g(vec 0))`
  SUBST1_TAC THENL [REWRITE_TAC[LINEPATH_REFL; FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `pathstart ((f:real^2->real^N) o std_triangle_loop) = (g:real^2->real^N)(vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[PATHSTART_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPEC `std_triangle_loop` PATHSTART_IN_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(g:real^2->real^N) o std_triangle_loop` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN
  REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `IMAGE (f:real^2->real^N) (relative_frontier std_triangle) =
                  IMAGE g (relative_frontier std_triangle)` SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!f g:real^2->real^N s. (!x. x IN s ==> g x = f x) ==> IMAGE f s = IMAGE g s`) THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `path_image std_triangle_loop = relative_frontier std_triangle`)) THEN
    REWRITE_TAC[path_image] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The bicollar of M: the open strip is open (local copy of                  *)
(* MOI_S6LV_STRIP_OPEN of pc_moi_s26_level, same hypotheses), levels, the    *)
(* closed band, retractions.                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S6E_OPEN_UNIT = prove
 (`open {t:real^1 | --(&1) < drop t /\ drop t < &1}`,
  SUBGOAL_THEN `{t:real^1 | --(&1) < drop t /\ drop t < &1} = interval(--vec 1,vec 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC];
    REWRITE_TAC[OPEN_INTERVAL]]);;

let MOI_S6E_STRIP_OPEN = prove
 (`!(c:(real^3->bool)->bool) w (rho:real^(3,1)finite_sum->real^3) rho'.
     FINITE c /\ combinatorial_manifold 2 c /\ moi_s26_bicollar (UNIONS c) w rho rho'
     ==> open (IMAGE rho (UNIONS c PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^3->bool)->bool` SURF_CHARTS) THEN
  ASM_SIMP_TAC[MOI_S8TA_CM_CMB] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o CONJUNCT2)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIFF_EMPTY] THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_s26_bicollar (UNIONS c) w (rho:real^(3,1)finite_sum->real^3) rho'` THEN
  REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  ABBREV_TAC `J = {t:real^1 | --(&1) < drop t /\ drop t < &1}` THEN
  SUBGOAL_THEN `open (J:real^1->bool) /\ J SUBSET interval[--vec 1,vec 1]`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[MOI_S6E_OPEN_UNIT] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [OPEN_SUBOPEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`z:real^3`; `t:real^1`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s28_locally_r2")) (concl th))) THEN
  ASM_REWRITE_TAC[moi_s28_locally_r2; homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `phi:real^3->real^2`
      (X_CHOOSE_TAC `phi':real^2->real^3`))))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (A:real^3->bool,(:real^2)) (phi,phi')`) (concl th))) THEN
  SUBGOAL_THEN `(A:real^3->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  ABBREV_TAC
   `Fm = \q:real^(2,1)finite_sum.
          (rho:real^(3,1)finite_sum->real^3) (pastecart (phi'(fstcart q)) (sndcart q))` THEN
  EXISTS_TAC `IMAGE (Fm:real^(2,1)finite_sum->real^3) ((:real^2) PCROSS J)` THEN
  SUBGOAL_THEN
   `!q. q IN (:real^2) PCROSS J
        ==> pastecart ((phi':real^2->real^3)(fstcart q)) (sndcart q) IN
            UNIONS c PCROSS interval[--vec 1:real^1,vec 1]`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART; IN_UNIV] THEN
    REPEAT STRIP_TAC THENL
     [UNDISCH_TAC `(A:real^3->bool) SUBSET UNIONS c` THEN
      UNDISCH_TAC `IMAGE (phi':real^2->real^3) (:real^2) = A` THEN SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN_GEN THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_2; DIMINDEX_1; DIMINDEX_3; LE_REFL] THEN
    REWRITE_TAC[ARITH] THEN
    SUBGOAL_THEN `open ((:real^2) PCROSS (J:real^1->bool))` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Fm" THEN
      SUBGOAL_THEN
       `(\q:real^(2,1)finite_sum.
          (rho:real^(3,1)finite_sum->real^3) (pastecart (phi'(fstcart q)) (sndcart q))) =
        rho o (\q. pastecart ((phi':real^2->real^3)(fstcart q)) (sndcart q))`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
        SUBGOAL_THEN
         `(\q:real^(2,1)finite_sum. (phi':real^2->real^3)(fstcart q)) = phi' o fstcart`
        SUBST1_TAC THENL [REWRITE_TAC[o_DEF; ETA_AX]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `UNIONS (c:(real^3->bool)->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN FIRST_ASSUM ACCEPT_TAC];
      EXPAND_TAC "Fm" THEN REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV;
        FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`a1:real^2`; `t1:real^1`; `a2:real^2`; `t2:real^1`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       `!p1 p2. p1 IN UNIONS c PCROSS interval[--vec 1:real^1,vec 1] /\
                p2 IN UNIONS c PCROSS interval[--vec 1,vec 1] /\
                (rho:real^(3,1)finite_sum->real^3) p1 = rho p2 ==> p1 = p2`
      (LABEL_TAC "rinj") THENL
       [MP_TAC(ASSUME `!x. x IN UNIONS c PCROSS interval[--vec 1:real^1,vec 1]
                           ==> (rho':real^3->real^(3,1)finite_sum)
                                 ((rho:real^(3,1)finite_sum->real^3) x) = x`) THEN
        MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `!a1 a2:real^2. (phi':real^2->real^3) a1 = phi' a2 ==> a1 = a2`
      (LABEL_TAC "pinj") THENL
       [MP_TAC(ASSUME `!y. y IN (:real^2)
                           ==> (phi:real^3->real^2) ((phi':real^2->real^3) y) = y`) THEN
        REWRITE_TAC[IN_UNIV] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!a:real^2 s:real^1. s IN J
            ==> pastecart ((phi':real^2->real^3) a) s IN
                UNIONS c PCROSS interval[--vec 1:real^1,vec 1]`
      (LABEL_TAC "mem") THENL
       [REPEAT STRIP_TAC THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN
        MAP_EVERY UNDISCH_TAC
         [`(s:real^1) IN J`; `(J:real^1->bool) SUBSET interval[--vec 1,vec 1]`;
          `(A:real^3->bool) SUBSET UNIONS c`; `IMAGE (phi':real^2->real^3) (:real^2) = A`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `pastecart ((phi':real^2->real^3) a1) (t1:real^1) = pastecart (phi' a2) t2`
      MP_TAC THENL
       [USE_THEN "rinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THEN USE_THEN "mem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[PASTECART_INJ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[PASTECART_INJ] THEN
      USE_THEN "pinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `pastecart ((phi:real^3->real^2) z) (t:real^1)` THEN
    EXPAND_TAC "Fm" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS; IN_UNIV] THEN
    ASM_SIMP_TAC[];
    EXPAND_TAC "Fm" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART;
      PASTECART_IN_PCROSS; IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`a:real^2`; `s:real^1`] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `pastecart ((phi':real^2->real^3) a) (s:real^1)` THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    MAP_EVERY UNDISCH_TAC
     [`(s:real^1) IN J`; `{t:real^1 | --(&1) < drop t /\ drop t < &1} = J`;
      `(A:real^3->bool) SUBSET UNIONS c`; `IMAGE (phi':real^2->real^3) (:real^2) = A`] THEN
    SET_TAC[]]);;


let moi_s6e_cband = new_definition
 `moi_s6e_cband (m:real^N->bool) (p:real^(N,1)finite_sum->real^N) (e:real) =
    IMAGE p (m PCROSS interval[lift(--e),lift e])`;;

let MOI_S6E_BC_FACTS = prove
 (`!(m:real^3->bool) w (rho:real^(3,1)finite_sum->real^3) rho'.
     moi_s26_bicollar m w rho rho'
     ==> rho continuous_on (m PCROSS interval[--vec 1,vec 1]) /\
         IMAGE rho (m PCROSS interval[--vec 1,vec 1]) = w /\
         rho' continuous_on w /\
         IMAGE rho' w = m PCROSS interval[--vec 1,vec 1] /\
         (!x. x IN m PCROSS interval[--vec 1,vec 1] ==> rho' (rho x) = x) /\
         (!y. y IN w ==> rho (rho' y) = y) /\
         (!x. x IN m ==> rho (pastecart x (vec 0)) = x)`,
  REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism; homeomorphism] THEN MESON_TAC[]);;

(* Membership in a slab of the bicollar through the collar coordinate.       *)

let MOI_S6E_IN_SLAB = prove
 (`!(m:real^3->bool) w (rho:real^(3,1)finite_sum->real^3) rho' s y.
     moi_s26_bicollar m w rho rho' /\ s SUBSET interval[--vec 1,vec 1]
     ==> (y IN IMAGE rho (m PCROSS s) <=> y IN w /\ sndcart(rho' y) IN s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_BC_FACTS) THEN
  EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `pastecart (x:real^3) (t:real^1) IN m PCROSS interval[--vec 1,vec 1]`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SNDCART_PASTECART] THEN
    UNDISCH_TAC `IMAGE (rho:real^(3,1)finite_sum->real^3)
                   (m PCROSS interval[--vec 1,vec 1]) = w` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN `(rho':real^3->real^(3,1)finite_sum) y IN m PCROSS interval[--vec 1,vec 1]`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBST1_TAC(SYM(ISPEC `(rho':real^3->real^(3,1)finite_sum) y` PASTECART_FST_SND)) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(rho':real^3->real^(3,1)finite_sum) y` THEN
    ASM_SIMP_TAC[] THEN
    SUBST1_TAC(SYM(ISPEC `(rho':real^3->real^(3,1)finite_sum) y` PASTECART_FST_SND)) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS]]);;

let MOI_S6E_BAND = prove
 (`!(c:(real^3->bool)->bool) w (rho:real^(3,1)finite_sum->real^3) rho' e.
     FINITE c /\ combinatorial_manifold 2 c /\ moi_s26_bicollar (UNIONS c) w rho rho' /\
     &0 < e /\ e < &1
     ==> compact (UNIONS c) /\
         compact (moi_s26_level (UNIONS c) rho e) /\
         compact (moi_s26_level (UNIONS c) rho (--e)) /\
         DISJOINT (moi_s26_level (UNIONS c) rho e) (moi_s26_level (UNIONS c) rho (--e)) /\
         compact (moi_s6e_cband (UNIONS c) rho e) /\
         moi_s6e_cband (UNIONS c) rho e SUBSET w /\
         moi_s26_level (UNIONS c) rho e SUBSET moi_s6e_cband (UNIONS c) rho e /\
         moi_s26_level (UNIONS c) rho (--e) SUBSET moi_s6e_cband (UNIONS c) rho e /\
         open (moi_s26_strip (UNIONS c) rho (--e) e) /\
         moi_s26_strip (UNIONS c) rho (--e) e SUBSET moi_s6e_cband (UNIONS c) rho e /\
         (!y. y IN moi_s6e_cband (UNIONS c) rho e
              ==> y IN moi_s26_strip (UNIONS c) rho (--e) e \/
                  y IN moi_s26_level (UNIONS c) rho e \/
                  y IN moi_s26_level (UNIONS c) rho (--e)) /\
         DISJOINT (moi_s26_strip (UNIONS c) rho (--e) e)
                  (moi_s26_level (UNIONS c) rho e UNION
                   moi_s26_level (UNIONS c) rho (--e)) /\
         UNIONS c SUBSET moi_s26_strip (UNIONS c) rho (--e) e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_BC_FACTS) THEN
  SUBGOAL_THEN `compact (UNIONS (c:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FSA_CM_SC o
      CONJ (ASSUME `FINITE (c:(real^3->bool)->bool)`)) THEN
    REWRITE_TAC[simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  ABBREV_TAC `M = UNIONS (c:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN
   `{lift e} SUBSET interval[--vec 1,vec 1] /\ {lift(--e)} SUBSET interval[--vec 1,vec 1] /\
    interval[lift(--e),lift e] SUBSET interval[--vec 1,vec 1] /\
    {x:real^1 | --e < drop x /\ drop x < e} SUBSET interval[--vec 1,vec 1] /\
    {x:real^1 | --(&1) < drop x /\ drop x < &1} SUBSET interval[--vec 1,vec 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SING; IN_ELIM_THM; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN TRY(DISCH_THEN SUBST1_TAC) THEN
    REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_s26_level; moi_s26_strip; moi_s6e_cband] THEN
  ASM_SIMP_TAC[MOI_S6E_IN_SLAB; SUBSET; DISJOINT; EXTENSION; IN_INTER; IN_UNION;
               NOT_IN_EMPTY; IN_SING; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP; DROP_NEG] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_SING] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; PCROSS_MONO; SUBSET_REFL];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_SING] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; PCROSS_MONO; SUBSET_REFL];
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `sndcart ((rho':real^3->real^(3,1)finite_sum) y) = lift e` THEN
    ASM_REWRITE_TAC[LIFT_EQ] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; PCROSS_MONO; SUBSET_REFL];
    GEN_TAC THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC;
    GEN_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; DROP_NEG] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; DROP_NEG] THEN
    ASM_CASES_TAC `(y:real^3) IN w` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pastecart (x:real^3) (vec 0:real^1) IN M PCROSS interval[--vec 1,vec 1]`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(rho':real^3->real^(3,1)finite_sum) x = pastecart x (vec 0)` ASSUME_TAC THENL
     [SUBGOAL_THEN `x = (rho:real^(3,1)finite_sum->real^3) (pastecart x (vec 0))`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
       [ASM_SIMP_TAC[]; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SNDCART_PASTECART; DROP_VEC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (rho:real^(3,1)finite_sum->real^3)
                     (M PCROSS interval[--vec 1,vec 1]) = w` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `pastecart (x:real^3) (vec 0:real^1)` THEN ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC]] THEN
  (* openness of the strip (-e,e) *)
  SUBGOAL_THEN
   `IMAGE (rho:real^(3,1)finite_sum->real^3) (M PCROSS {x:real^1 | --e < drop x /\ drop x < e}) =
    {y | y IN IMAGE rho (M PCROSS {t:real^1 | --(&1) < drop t /\ drop t < &1}) /\
         (sndcart o (rho':real^3->real^(3,1)finite_sum)) y IN interval(lift(--e),lift e)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM] THEN X_GEN_TAC `y:real^3` THEN
    ASM_SIMP_TAC[MOI_S6E_IN_SLAB; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP; DROP_NEG] THEN
    ASM_CASES_TAC `(y:real^3) IN w` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[OPEN_INTERVAL; ETA_AX] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (rho:real^(3,1)finite_sum->real^3)
                     (M PCROSS interval[--vec 1,vec 1]) = w` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL];
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]];
    EXPAND_TAC "M" THEN MATCH_MP_TAC MOI_S6E_STRIP_OPEN THEN
    EXISTS_TAC `w:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `rho':real^3->real^(3,1)finite_sum` THEN ASM_REWRITE_TAC[]]);;

(* Retraction of the closed band onto the level t, and the collar homotopy  *)
(* from a loop on a level to its projection on m.                           *)

let MOI_S6E_RETRACT = prove
 (`!(m:real^3->bool) w (rho:real^(3,1)finite_sum->real^3) rho' e t.
     moi_s26_bicollar m w rho rho' /\ e <= &1 /\ abs t <= &1
     ==> (\y. rho (pastecart (fstcart (rho' y)) (lift t))) continuous_on
         moi_s6e_cband m rho e /\
         IMAGE (\y. rho (pastecart (fstcart (rho' y)) (lift t))) (moi_s6e_cband m rho e)
           SUBSET moi_s26_level m rho t /\
         (!y. y IN moi_s26_level m rho t
              ==> rho (pastecart (fstcart (rho' y)) (lift t)) = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_BC_FACTS) THEN
  SUBGOAL_THEN `interval[lift(--e),lift e] SUBSET interval[--vec 1:real^1,vec 1] /\
                {lift t} SUBSET interval[--vec 1:real^1,vec 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SING; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
    CONJ_TAC THEN GEN_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s6e_cband m rho e SUBSET (w:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s6e_cband] THEN
    UNDISCH_TAC `IMAGE (rho:real^(3,1)finite_sum->real^3)
                   (m PCROSS interval[--vec 1:real^1,vec 1]) = w` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN w ==> fstcart((rho':real^3->real^(3,1)finite_sum) y) IN m`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(rho':real^3->real^(3,1)finite_sum) y IN m PCROSS interval[--vec 1:real^1,vec 1]`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBST1_TAC(SYM(ISPEC `(rho':real^3->real^(3,1)finite_sum) y` PASTECART_FST_SND)) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; ETA_AX] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(m:real^3->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ASM SET_TAC[]]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; moi_s26_level] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[moi_s26_level; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                IN_SING] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `s:real^1`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `pastecart (x:real^3) (lift t) IN m PCROSS interval[--vec 1:real^1,vec 1]`
    ASSUME_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[FSTCART_PASTECART]]);;

let MOI_S6E_COLLAR_HOMOTOPY = prove
 (`!(m:real^3->bool) w (rho:real^(3,1)finite_sum->real^3) rho' t (g:real^1->real^3).
     moi_s26_bicollar m w rho rho' /\ abs t <= &1 /\
     path g /\ pathfinish g = pathstart g /\ path_image g SUBSET moi_s26_level m rho t
     ==> homotopic_loops (IMAGE rho (m PCROSS segment[vec 0,lift t]))
           g ((\y. fstcart (rho' y)) o g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_BC_FACTS) THEN
  SUBGOAL_THEN `segment[vec 0,lift t] SUBSET interval[--vec 1:real^1,vec 1] /\
                {lift t} SUBSET interval[--vec 1:real^1,vec 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_1; SUBSET; IN_SING; IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
    CONJ_TAC THEN GEN_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN interval[vec 0,vec 1]
        ==> fstcart((rho':real^3->real^(3,1)finite_sum) (g u)) IN m /\
            rho (pastecart (fstcart(rho' (g u))) (lift t)) = (g:real^1->real^3) u /\
            rho' (g u) = pastecart (fstcart(rho' (g u))) (lift t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^1->real^3) u IN moi_s26_level m rho t` MP_TAC THENL
     [UNDISCH_TAC `path_image (g:real^1->real^3) SUBSET moi_s26_level m rho t` THEN
      REWRITE_TAC[path_image] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_s26_level; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `pastecart (x:real^3) (lift t) IN m PCROSS interval[--vec 1:real^1,vec 1]`
    ASSUME_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[FSTCART_PASTECART];
    ALL_TAC] THEN
  REWRITE_TAC[homotopic_loops] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) HOMOTOPIC_WITH_EUCLIDEAN_ALT w)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[pathstart; pathfinish] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(vec 0:real^1) IN interval[vec 0,vec 1] /\ (vec 1:real^1) IN interval[vec 0,vec 1]`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  EXISTS_TAC
   `\z:real^(1,1)finite_sum.
      (rho:real^(3,1)finite_sum->real^3)
        (pastecart (fstcart ((rho':real^3->real^(3,1)finite_sum) (g (sndcart z))))
                   ((&1 - drop(fstcart z)) % lift t))` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_SUB_REFL; VECTOR_MUL_LID; VECTOR_MUL_LZERO; o_THM] THEN
  SUBGOAL_THEN
   `!z:real^(1,1)finite_sum.
      z IN interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]
      ==> pastecart (fstcart ((rho':real^3->real^(3,1)finite_sum) (g (sndcart z))))
                    ((&1 - drop(fstcart z)) % lift t) IN m PCROSS segment[vec 0,lift t]`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `u:real^1`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_SEGMENT] THEN
    EXISTS_TAC `&1 - drop s` THEN
    UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `(\z:real^(1,1)finite_sum. fstcart ((rho':real^3->real^(3,1)finite_sum) (g (sndcart z)))) =
          fstcart o rho' o (g:real^1->real^3) o sndcart`
        SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
        SUBGOAL_THEN
         `IMAGE ((g:real^1->real^3) o sndcart)
                (interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1]) SUBSET w`
        ASSUME_TAC THENL
         [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                      SNDCART_PASTECART; o_THM] THEN
          MAP_EVERY X_GEN_TAC [`s:real^1`; `u:real^1`] THEN STRIP_TAC THEN
          SUBGOAL_THEN `(g:real^1->real^3) u IN moi_s26_level m rho t` MP_TAC THENL
           [UNDISCH_TAC `path_image (g:real^1->real^3) SUBSET moi_s26_level m rho t` THEN
            REWRITE_TAC[path_image] THEN ASM SET_TAC[];
            REWRITE_TAC[moi_s26_level] THEN
            UNDISCH_TAC `IMAGE (rho:real^(3,1)finite_sum->real^3)
                           (m PCROSS interval[--vec 1:real^1,vec 1]) = w` THEN
            DISCH_THEN(SUBST1_TAC o SYM) THEN
            MATCH_MP_TAC(SET_RULE `!s t f:real^(3,1)finite_sum->real^3 x.
                s SUBSET t ==> x IN IMAGE f s ==> x IN IMAGE f t`) THEN
            MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL]];
          ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [ALL_TAC; SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART]] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [ALL_TAC;
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^3->bool` THEN
          ASM_REWRITE_TAC[]] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[path]; ALL_TAC] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                    SNDCART_PASTECART] THEN MESON_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP; LIFT_NUM] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        SIMP_TAC[CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; ETA_AX]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(m:real^3->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^(1,1)finite_sum` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(m:real^3->bool) PCROSS segment[vec 0,lift t] SUBSET
                    m PCROSS interval[--vec 1:real^1,vec 1]` MP_TAC THENL
       [MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^(1,1)finite_sum` THEN
    DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `fstcart((rho':real^3->real^(3,1)finite_sum) ((g:real^1->real^3) u)) IN m`
      (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[pathstart; pathfinish] THEN
    UNDISCH_TAC `pathfinish (g:real^1->real^3) = pathstart g` THEN
    REWRITE_TAC[pathstart; pathfinish] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The minimality argument (in place of the book's induction on the         *)
(* number of level circles), abstractly: a map f on the triangle whose      *)
(* preimage of two disjoint closed levels is a finite family of disjoint    *)
(* circles, an open band bo inside a closed band be with be minus bo the     *)
(* levels, retractions of be onto the levels and onto m0.  If the boundary  *)
(* loop does not extend into m0, some circle j0 is essential in its level   *)
(* while f|j0 extends over the disk of j0 off bo.                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S6E_CONN_SPLIT = prove
 (`!s u v:real^N->bool.
     connected s /\ open u /\ open v /\ s SUBSET u UNION v /\ u INTER v INTER s = {}
     ==> s SUBSET u \/ s SUBSET v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `v:real^N->bool`] o
    REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let moi_s6e_lev = new_definition
 `moi_s6e_lev (f:real^2->real^3) (lp:real^3->bool) lm (j:real^2->bool) =
    if IMAGE f j SUBSET lp then lp else lm`;;

let moi_s6e_ext = new_definition
 `moi_s6e_ext (f:real^2->real^3) (j:real^2->bool) (s:real^3->bool) <=>
    ?g. g continuous_on (j UNION inside j) /\ IMAGE g (j UNION inside j) SUBSET s /\
        !x. x IN j ==> g x = f x`;;

let MOI_S6E_CIRCLE_LEVEL = prove
 (`!(f:real^2->real^3) cc lp lm j.
     f continuous_on std_triangle /\ moi_s6e_circles cc /\
     (!j. j IN cc ==> j SUBSET relative_interior std_triangle) /\
     (!x. x IN std_triangle ==> (f x IN lp UNION lm <=> x IN UNIONS cc)) /\
     closed lp /\ closed lm /\ DISJOINT lp lm /\ j IN cc
     ==> IMAGE f j SUBSET moi_s6e_lev f lp lm j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected (j:real^2->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `pl_sphere 1 (j:real^2->bool)` (fun th ->
      MP_TAC(MATCH_MP MOI_S6E_JORDAN th)) THENL
     [ASM_MESON_TAC[moi_s6e_circles]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^2->bool) SUBSET std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `relative_interior std_triangle` THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^3) j SUBSET lp UNION lm` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN std_triangle` ASSUME_TAC THENL
     [UNDISCH_TAC `(j:real^2->bool) SUBSET std_triangle` THEN
      UNDISCH_TAC `(x:real^2) IN j` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2) IN UNIONS cc` MP_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `j:real^2->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `UNIONS (cc:(real^2->bool)->bool)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (f:real^2->real^3) j)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s6e_lev] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`IMAGE (f:real^2->real^3) j`; `(:real^3) DIFF lm`; `(:real^3) DIFF lp`]
    MOI_S6E_CONN_SPLIT) THEN
  ASM_REWRITE_TAC[GSYM closed] THEN
  MAP_EVERY UNDISCH_TAC
   [`IMAGE (f:real^2->real^3) j SUBSET lp UNION lm`; `DISJOINT (lp:real^3->bool) lm`;
    `~(IMAGE (f:real^2->real^3) j SUBSET lp)`] THEN
  SET_TAC[]);;

let MOI_S6E_FILL = prove
 (`!(f:real^2->real^3) cc c0 lp lm.
     moi_s6e_circles cc /\ compact c0 /\ connected c0 /\
     f continuous_on (c0 UNION inside c0) /\
     (!j. j IN moi_s6e_outer cc c0 ==> moi_s6e_ext f j (moi_s6e_lev f lp lm j))
     ==> ?g. g continuous_on (c0 UNION inside c0) /\
             IMAGE g (c0 UNION inside c0) SUBSET
               IMAGE f (c0 UNION
                        (inside c0 DIFF UNIONS {k UNION inside k | k IN moi_s6e_outer cc c0}))
               UNION lp UNION lm /\
             (!x. x IN c0 ==> g x = f x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[moi_s6e_ext] o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s6e_ext")) (concl th))) THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `G:(real^2->bool)->real^2->real^3`) THEN
  MP_TAC(ISPECL [`cc:(real^2->bool)->bool`; `c0:real^2->bool`; `f:real^2->real^3`;
                 `G:(real^2->bool)->real^2->real^3`] MOI_S6E_PASTE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^2->real^3` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_UNION]] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  ASM_CASES_TAC
   `?k:real^2->bool. k IN moi_s6e_outer cc c0 /\ x IN k UNION inside k` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(g:real^2->real^3) x = (G:(real^2->bool)->real^2->real^3) k x` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE ((G:(real^2->bool)->real^2->real^3) k) (k UNION inside k) SUBSET
                  moi_s6e_lev f lp lm k` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_s6e_lev] THEN COND_CASES_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN c0 UNION
                (inside c0 DIFF UNIONS {k UNION inside k | k IN moi_s6e_outer cc c0})`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNION; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^3) x = f x` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
  ASM_REWRITE_TAC[]);;

(* The region inside a container c0 off the outermost disks maps into bo or *)
(* misses be.                                                                *)

let MOI_S6E_REGION_SIDE = prove
 (`!(f:real^2->real^3) cc c0 lp lm bo be.
     f continuous_on std_triangle /\ moi_s6e_circles cc /\
     compact c0 /\ connected c0 /\ connected (inside c0) /\
     c0 UNION inside c0 SUBSET std_triangle /\
     (!j. j IN cc ==> j SUBSET inside c0 \/ DISJOINT j (inside c0)) /\
     (!x. x IN std_triangle ==> (f x IN lp UNION lm <=> x IN UNIONS cc)) /\
     open bo /\ closed be /\ bo SUBSET be /\ be SUBSET bo UNION lp UNION lm
     ==> IMAGE f (inside c0 DIFF UNIONS {k UNION inside k | k IN moi_s6e_outer cc c0})
           SUBSET bo \/
         IMAGE f (inside c0 DIFF UNIONS {k UNION inside k | k IN moi_s6e_outer cc c0})
           SUBSET (:real^3) DIFF be`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `A0 = inside c0 DIFF UNIONS {k UNION inside k | k IN moi_s6e_outer cc c0}` THEN
  SUBGOAL_THEN `(A0:real^2->bool) SUBSET std_triangle` ASSUME_TAC THENL
   [EXPAND_TAC "A0" THEN
    UNDISCH_TAC `(c0:real^2->bool) UNION inside c0 SUBSET std_triangle` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (A0:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A0" THEN MATCH_MP_TAC MOI_S6E_REGION_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (A0:real^2->bool) (UNIONS cc)` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `j:real^2->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`cc:(real^2->bool)->bool`; `c0:real^2->bool`; `j:real^2->bool`]
      MOI_S6E_REGION_MISS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S6E_CONN_SPLIT THEN
  ASM_REWRITE_TAC[GSYM closed] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((f:real^2->real^3) x IN lp UNION lm)` MP_TAC THENL
     [SUBGOAL_THEN `(x:real^2) IN std_triangle /\ ~(x IN UNIONS cc)` MP_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(x:real^2) IN A0`; `(A0:real^2->bool) SUBSET std_triangle`;
          `DISJOINT (A0:real^2->bool) (UNIONS cc)`] THEN SET_TAC[];
        ASM_MESON_TAC[]];
      UNDISCH_TAC `(be:real^3->bool) SUBSET bo UNION lp UNION lm` THEN SET_TAC[]];
    UNDISCH_TAC `(bo:real^3->bool) SUBSET be` THEN SET_TAC[]]);;

let MOI_S6E_TRI_C0 = prove
 (`compact (relative_frontier std_triangle) /\ connected (relative_frontier std_triangle) /\
   ~(relative_frontier std_triangle = {}) /\
   connected (inside (relative_frontier std_triangle)) /\
   relative_frontier std_triangle SUBSET closure (inside (relative_frontier std_triangle)) /\
   relative_frontier std_triangle UNION inside (relative_frontier std_triangle) = std_triangle /\
   relative_interior std_triangle SUBSET inside (relative_frontier std_triangle)`,
  REWRITE_TAC[MOI_S6E_TRIANGLE; SUBSET_REFL]);;

let MOI_S6E_CORE_T = prove
 (`!(f:real^2->real^3) cc lp lm bo be m0 r0.
     f continuous_on std_triangle /\ moi_s6e_circles cc /\
     (!j. j IN cc ==> j SUBSET relative_interior std_triangle) /\
     (!x. x IN std_triangle ==> (f x IN lp UNION lm <=> x IN UNIONS cc)) /\
     open bo /\ closed be /\ bo SUBSET be /\ lp SUBSET be /\ lm SUBSET be /\
     be SUBSET bo UNION lp UNION lm /\
     IMAGE f (relative_frontier std_triangle) SUBSET m0 /\ m0 SUBSET bo /\
     r0 continuous_on be /\ IMAGE r0 be SUBSET m0 /\ (!y. y IN m0 ==> r0 y = y) /\
     (!j. j IN cc ==> moi_s6e_ext f j (moi_s6e_lev f lp lm j))
     ==> ?g. g continuous_on std_triangle /\ IMAGE g std_triangle SUBSET m0 /\
             !x. x IN relative_frontier std_triangle ==> g x = f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC MOI_S6E_TRI_C0 THEN
  SUBGOAL_THEN `!j:real^2->bool. j IN cc ==> j SUBSET inside (relative_frontier std_triangle)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:real^2->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `relative_interior std_triangle` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c0 = relative_frontier std_triangle` THEN
  MP_TAC(ISPECL [`f:real^2->real^3`; `cc:(real^2->bool)->bool`; `c0:real^2->bool`;
                 `lp:real^3->bool`; `lm:real^3->bool`] MOI_S6E_FILL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:real^2->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(j:real^2->bool) IN moi_s6e_outer cc c0` THEN
    REWRITE_TAC[moi_s6e_outer; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^2->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^2->real^3`; `cc:(real^2->bool)->bool`; `c0:real^2->bool`;
                 `lp:real^3->bool`; `lm:real^3->bool`; `bo:real^3->bool`; `be:real^3->bool`]
    MOI_S6E_REGION_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN
    X_GEN_TAC `j:real^2->bool` THEN DISCH_TAC THEN DISJ1_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `A0 = inside c0 DIFF UNIONS {k UNION inside k | k IN moi_s6e_outer cc c0}` THEN
  SUBGOAL_THEN `~(IMAGE (f:real^2->real^3) A0 SUBSET (:real^3) DIFF be)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o check (fun th ->
      concl th = `~(c0:real^2->bool = {})`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `x0:real^2`) THEN
    SUBGOAL_THEN `(f:real^2->real^3) x0 IN bo` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^2->real^3) c0 SUBSET m0` THEN
      UNDISCH_TAC `(m0:real^3->bool) SUBSET bo` THEN
      UNDISCH_TAC `(x0:real^2) IN c0` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x0:real^2) IN std_triangle` ASSUME_TAC THENL
     [UNDISCH_TAC `(c0:real^2->bool) UNION inside c0 = std_triangle` THEN
      UNDISCH_TAC `(x0:real^2) IN c0` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `open (bo:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^2->real^3) x0`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(f:real^2->real^3) continuous_on std_triangle` THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `x0:real^2`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `closed (UNIONS {k UNION inside k | k IN moi_s6e_outer cc (c0:real^2->bool)})`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`cc:(real^2->bool)->bool`; `c0:real^2->bool`] MOI_S6E_OUTER_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE; COMPACT_IMP_CLOSED];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((x0:real^2) IN UNIONS {k UNION inside k | k IN moi_s6e_outer cc c0})`
    ASSUME_TAC THENL
     [REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `k:real^2->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`cc:(real^2->bool)->bool`; `c0:real^2->bool`] MOI_S6E_OUTER_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `k:real^2->bool` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      MP_TAC(ISPEC `c0:real^2->bool` INSIDE_NO_OVERLAP) THEN
      MAP_EVERY UNDISCH_TAC [`(x0:real^2) IN c0`; `(x0:real^2) IN k UNION inside k`;
        `(k:real^2->bool) UNION inside k SUBSET inside c0`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?d2. &0 < d2 /\
           !y:real^2. dist(y,x0) < d2
                      ==> ~(y IN UNIONS {k UNION inside k | k IN moi_s6e_outer cc c0})`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `closed (UNIONS {k UNION inside k | k IN moi_s6e_outer cc (c0:real^2->bool)})` THEN
      REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `x0:real^2`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d2:real` THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x0:real^2) IN closure (inside c0)` MP_TAC THENL
     [UNDISCH_TAC `(c0:real^2->bool) SUBSET closure (inside c0)` THEN
      UNDISCH_TAC `(x0:real^2) IN c0` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `min d1 d2:real`) THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^2) IN A0` ASSUME_TAC THENL
     [EXPAND_TAC "A0" THEN REWRITE_TAC[IN_DIFF] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^2) IN std_triangle` ASSUME_TAC THENL
     [UNDISCH_TAC `(c0:real^2->bool) UNION inside c0 = std_triangle` THEN
      UNDISCH_TAC `(y:real^2) IN inside c0` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^3) y IN bo` ASSUME_TAC THENL
     [UNDISCH_TAC `ball((f:real^2->real^3) x0,eps) SUBSET bo` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    UNDISCH_TAC `(f:real^2->real^3) y IN bo` THEN
    UNDISCH_TAC `(bo:real^3->bool) SUBSET be` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `(r0:real^3->real^3) o (g1:real^2->real^3)` THEN
  SUBGOAL_THEN `IMAGE (g1:real^2->real^3) std_triangle SUBSET be` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(c0:real^2->bool) UNION inside c0 = std_triangle`)) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^2->real^3) (c0 UNION A0) UNION lp UNION lm` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (f:real^2->real^3) A0 SUBSET bo`; `IMAGE (f:real^2->real^3) c0 SUBSET m0`;
      `(m0:real^3->bool) SUBSET bo`; `(bo:real^3->bool) SUBSET be`;
      `(lp:real^3->bool) SUBSET be`; `(lm:real^3->bool) SUBSET be`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [UNDISCH_TAC `(g1:real^2->real^3) continuous_on (c0 UNION inside c0)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `be:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (r0:real^3->real^3) be` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(g1:real^2->real^3) x = f x` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3) c0 SUBSET m0` THEN
    UNDISCH_TAC `(x:real^2) IN c0` THEN SET_TAC[]]);;

let MOI_S6E_CORE_J = prove
 (`!(f:real^2->real^3) cc lp lm bo be rp rm j0.
     f continuous_on std_triangle /\ moi_s6e_circles cc /\
     (!j. j IN cc ==> j SUBSET relative_interior std_triangle) /\
     (!x. x IN std_triangle ==> (f x IN lp UNION lm <=> x IN UNIONS cc)) /\
     closed lp /\ closed lm /\ DISJOINT lp lm /\
     open bo /\ closed be /\ bo SUBSET be /\ lp SUBSET be /\ lm SUBSET be /\
     be SUBSET bo UNION lp UNION lm /\ DISJOINT bo (lp UNION lm) /\
     rp continuous_on be /\ IMAGE rp be SUBSET lp /\ (!y. y IN lp ==> rp y = y) /\
     rm continuous_on be /\ IMAGE rm be SUBSET lm /\ (!y. y IN lm ==> rm y = y) /\
     j0 IN cc /\ ~moi_s6e_ext f j0 (moi_s6e_lev f lp lm j0) /\
     (!j. j IN cc /\ j SUBSET inside j0 ==> moi_s6e_ext f j (moi_s6e_lev f lp lm j))
     ==> ?g. g continuous_on (j0 UNION inside j0) /\
             IMAGE g (j0 UNION inside j0) SUBSET
               (IMAGE f std_triangle UNION lp UNION lm) DIFF bo /\
             !x. x IN j0 ==> g x = f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 1 (j0:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s6e_circles]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (j0:real^2->bool) /\ connected j0 /\ connected (inside j0) /\
                inside j0 INTER j0 = {}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S6E_JORDAN (ASSUME `pl_sphere 1 (j0:real^2->bool)`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j0:real^2->bool) UNION inside j0 SUBSET std_triangle` ASSUME_TAC THENL
   [STRIP_ASSUME_TAC MOI_S6E_TRI_C0 THEN
    MP_TAC(ISPECL [`relative_frontier std_triangle`; `j0:real^2->bool`] MOI_S6E_KIN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `relative_interior std_triangle` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `relative_frontier std_triangle UNION inside (relative_frontier std_triangle) =
                 std_triangle` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j:real^2->bool. j IN cc ==> j SUBSET inside j0 \/ DISJOINT j (inside j0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:real^2->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j:real^2->bool = j0` THENL
     [DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `inside j0 INTER j0 = {}:real^2->bool` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`j0:real^2->bool`; `j:real^2->bool`] MOI_S6E_SIDE_OF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `pl_sphere 1 (j:real^2->bool)` (fun th ->
          MP_TAC(MATCH_MP MOI_S6E_JORDAN th)) THENL
         [ASM_MESON_TAC[moi_s6e_circles]; SIMP_TAC[]];
        ASM_MESON_TAC[moi_s6e_circles; pairwise]];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    MP_TAC(MATCH_MP MOI_S6E_JORDAN (ASSUME `pl_sphere 1 (j0:real^2->bool)`)) THEN
    UNDISCH_TAC `(j:real^2->bool) SUBSET outside j0` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^3`; `cc:(real^2->bool)->bool`; `j0:real^2->bool`;
                 `lp:real^3->bool`; `lm:real^3->bool`] MOI_S6E_FILL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `j:real^2->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(j:real^2->bool) IN moi_s6e_outer cc j0` THEN
      REWRITE_TAC[moi_s6e_outer; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^2->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^2->real^3`; `cc:(real^2->bool)->bool`; `j0:real^2->bool`;
                 `lp:real^3->bool`; `lm:real^3->bool`; `bo:real^3->bool`; `be:real^3->bool`]
    MOI_S6E_REGION_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `A0 = inside j0 DIFF UNIONS {k UNION inside k | k IN moi_s6e_outer cc j0}` THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^3) j0 SUBSET moi_s6e_lev f lp lm j0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S6E_CIRCLE_LEVEL THEN EXISTS_TAC `cc:(real^2->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s6e_lev (f:real^2->real^3) lp lm j0 SUBSET lp UNION lm` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s6e_lev] THEN COND_CASES_TAC THEN SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [(* the band case: the retraction to the level of j0 makes j0 inessential *)
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    UNDISCH_TAC `~moi_s6e_ext (f:real^2->real^3) j0 (moi_s6e_lev f lp lm j0)` THEN
    REWRITE_TAC[moi_s6e_ext] THEN
    SUBGOAL_THEN `IMAGE (g1:real^2->real^3) (j0 UNION inside j0) SUBSET be` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (f:real^2->real^3) (j0 UNION A0) UNION lp UNION lm` THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (f:real^2->real^3) A0 SUBSET bo`;
        `IMAGE (f:real^2->real^3) j0 SUBSET moi_s6e_lev f lp lm j0`;
        `moi_s6e_lev (f:real^2->real^3) lp lm j0 SUBSET lp UNION lm`;
        `(bo:real^3->bool) SUBSET be`; `(lp:real^3->bool) SUBSET be`;
        `(lm:real^3->bool) SUBSET be`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?r:real^3->real^3. r continuous_on be /\
                         IMAGE r be SUBSET moi_s6e_lev (f:real^2->real^3) lp lm j0 /\
                         (!y. y IN moi_s6e_lev f lp lm j0 ==> r y = y)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[moi_s6e_lev] THEN COND_CASES_TAC THENL
       [EXISTS_TAC `rp:real^3->real^3`; EXISTS_TAC `rm:real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `(r:real^3->real^3) o (g1:real^2->real^3)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `be:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (r:real^3->real^3) be` THEN ASM_SIMP_TAC[IMAGE_SUBSET];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(g1:real^2->real^3) x = f x` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^3) j0 SUBSET moi_s6e_lev f lp lm j0` THEN
      UNDISCH_TAC `(x:real^2) IN j0` THEN SET_TAC[]];
    (* the outer case *)
    EXISTS_TAC `g1:real^2->real^3` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^2->real^3) (j0 UNION A0) UNION lp UNION lm` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE (f:real^2->real^3) (j0 UNION A0) SUBSET IMAGE f std_triangle`
    MP_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN EXPAND_TAC "A0" THEN
      UNDISCH_TAC `(j0:real^2->bool) UNION inside j0 SUBSET std_triangle` THEN SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (f:real^2->real^3) A0 SUBSET (:real^3) DIFF be`;
      `IMAGE (f:real^2->real^3) j0 SUBSET moi_s6e_lev f lp lm j0`;
      `moi_s6e_lev (f:real^2->real^3) lp lm j0 SUBSET lp UNION lm`;
      `(bo:real^3->bool) SUBSET be`; `DISJOINT (bo:real^3->bool) (lp UNION lm)`] THEN
    SET_TAC[]]);;

let MOI_S6E_CORE = prove
 (`!(f:real^2->real^3) cc lp lm bo be m0 r0 rp rm.
     f continuous_on std_triangle /\ moi_s6e_circles cc /\
     (!j. j IN cc ==> j SUBSET relative_interior std_triangle) /\
     (!x. x IN std_triangle ==> (f x IN lp UNION lm <=> x IN UNIONS cc)) /\
     closed lp /\ closed lm /\ DISJOINT lp lm /\
     open bo /\ closed be /\ bo SUBSET be /\ lp SUBSET be /\ lm SUBSET be /\
     be SUBSET bo UNION lp UNION lm /\ DISJOINT bo (lp UNION lm) /\
     IMAGE f (relative_frontier std_triangle) SUBSET m0 /\ m0 SUBSET bo /\
     r0 continuous_on be /\ IMAGE r0 be SUBSET m0 /\ (!y. y IN m0 ==> r0 y = y) /\
     rp continuous_on be /\ IMAGE rp be SUBSET lp /\ (!y. y IN lp ==> rp y = y) /\
     rm continuous_on be /\ IMAGE rm be SUBSET lm /\ (!y. y IN lm ==> rm y = y) /\
     ~(?g. g continuous_on std_triangle /\ IMAGE g std_triangle SUBSET m0 /\
           !x. x IN relative_frontier std_triangle ==> g x = f x)
     ==> ?j0 g. j0 IN cc /\ ~moi_s6e_ext f j0 (moi_s6e_lev f lp lm j0) /\
                g continuous_on (j0 UNION inside j0) /\
                IMAGE g (j0 UNION inside j0) SUBSET
                  (IMAGE f std_triangle UNION lp UNION lm) DIFF bo /\
                !x. x IN j0 ==> g x = f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?j. j IN cc /\ ~moi_s6e_ext (f:real^2->real^3) j (moi_s6e_lev f lp lm j)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`]) THEN
    UNDISCH_TAC `~(?g. g continuous_on std_triangle /\ IMAGE g std_triangle SUBSET m0 /\
                       !x. x IN relative_frontier std_triangle ==> g x = (f:real^2->real^3) x)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S6E_CORE_T THEN
    MAP_EVERY EXISTS_TAC [`cc:(real^2->bool)->bool`; `lp:real^3->bool`; `lm:real^3->bool`;
                          `bo:real^3->bool`; `be:real^3->bool`; `r0:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`cc:(real^2->bool)->bool`;
                 `\j:real^2->bool. ~moi_s6e_ext (f:real^2->real^3) j (moi_s6e_lev f lp lm j)`;
                 `j:real^2->bool`] MOI_S6E_MIN_CIRCLE)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j0:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^2->real^3`; `cc:(real^2->bool)->bool`; `lp:real^3->bool`;
                 `lm:real^3->bool`; `bo:real^3->bool`; `be:real^3->bool`;
                 `rp:real^3->real^3`; `rm:real^3->real^3`; `j0:real^2->bool`]
    MOI_S6E_CORE_J) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`j0:real^2->bool`; `g:real^2->real^3`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The sides of the surface, the halves of the bicollar, M as a            *)
(* component of the frontier of a part of the cut, and Moise 26.4.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S6E_SURF_SIDES = prove
 (`!m:real^3->bool k.
     closed m /\ connected k /\ DISJOINT k m
     ==> k SUBSET inside m \/ k SUBSET outside m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S6E_CONN_SPLIT THEN
  ASM_SIMP_TAC[OPEN_INSIDE; OPEN_OUTSIDE] THEN
  MP_TAC(ISPEC `m:real^3->bool` INSIDE_UNION_OUTSIDE) THEN
  MP_TAC(ISPEC `m:real^3->bool` INSIDE_INTER_OUTSIDE) THEN
  UNDISCH_TAC `DISJOINT (k:real^3->bool) m` THEN SET_TAC[]);;

let MOI_S6E_SLAB_FACTS = prove
 (`!(m:real^3->bool) w (rho:real^(3,1)finite_sum->real^3) rho' a b.
     moi_s26_bicollar m w rho rho' /\ closed m /\
     segment[a,b] SUBSET interval[--vec 1,vec 1] /\ ~(vec 0 IN segment[a,b])
     ==> connected m ==> connected (IMAGE rho (m PCROSS segment[a,b])) /\
         DISJOINT (IMAGE rho (m PCROSS segment[a,b])) m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_BC_FACTS) THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONNECTED_PCROSS; CONNECTED_SEGMENT] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(m:real^3->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE;
              EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
  X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `s:real^1`
    STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  SUBGOAL_THEN `pastecart (x:real^3) (s:real^1) IN m PCROSS interval[--vec 1,vec 1] /\
                pastecart (y:real^3) (vec 0:real^1) IN m PCROSS interval[--vec 1,vec 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PASTECART_IN_PCROSS] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN m`; `(s:real^1) IN segment[a,b]`;
        `segment[a,b] SUBSET interval[--vec 1:real^1,vec 1]`] THEN SET_TAC[];
      ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (x:real^3) (s:real^1) = pastecart y (vec 0)` MP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(rho':real^3->real^(3,1)finite_sum) (rho (pastecart (x:real^3) (s:real^1)))` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(rho':real^3->real^(3,1)finite_sum) (rho (pastecart (y:real^3) (vec 0:real^1)))` THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN ASM_SIMP_TAC[]; ASM_SIMP_TAC[]];
    REWRITE_TAC[PASTECART_INJ] THEN ASM_MESON_TAC[]]);;

let MOI_S6E_HALF_SIDE = prove
 (`!(m:real^3->bool) w (rho:real^(3,1)finite_sum->real^3) rho' sg.
     moi_s26_bicollar m w rho rho' /\ connected m /\ ~(m = {}) /\ closed m /\
     (sg = &1 \/ sg = -- &1)
     ==> ?X. (X = inside m \/ X = outside m) /\
             !t. &0 < t /\ t <= &1 ==> moi_s26_level m rho (sg * t) SUBSET X`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t <= &1
        ==> segment[lift(sg * t),lift sg] SUBSET interval[--vec 1:real^1,vec 1] /\
            ~(vec 0 IN segment[lift(sg * t),lift sg])`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[SEGMENT_1; LIFT_DROP] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th))) THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP; DROP_NEG; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t <= &1
        ==> connected (IMAGE (rho:real^(3,1)finite_sum->real^3)
                         (m PCROSS segment[lift(sg * t),lift sg])) /\
            DISJOINT (IMAGE rho (m PCROSS segment[lift(sg * t),lift sg])) m /\
            moi_s26_level m rho (sg * t) SUBSET
              IMAGE rho (m PCROSS segment[lift(sg * t),lift sg]) /\
            moi_s26_level m rho sg SUBSET IMAGE rho (m PCROSS segment[lift(sg * t),lift sg])`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`m:real^3->bool`; `w:real^3->bool`; `rho:real^(3,1)finite_sum->real^3`;
                   `rho':real^3->real^(3,1)finite_sum`; `lift(sg * t)`; `lift sg`]
      MOI_S6E_SLAB_FACTS) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[moi_s26_level] THEN CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SING_SUBSET; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_s26_level (m:real^3->bool) rho sg = {})` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s26_level; IMAGE_EQ_EMPTY; PCROSS_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `&1` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "connected")) (concl th))) THEN
  REWRITE_TAC[REAL_LT_01; REAL_LE_REFL; REAL_MUL_RID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:real^3->bool`;
                 `IMAGE (rho:real^(3,1)finite_sum->real^3) (m PCROSS segment[lift sg,lift sg])`]
    MOI_S6E_SURF_SIDES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [EXISTS_TAC `inside m:real^3->bool`; EXISTS_TAC `outside m:real^3->bool`] THEN
  REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "connected")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:real^3->bool`;
                 `IMAGE (rho:real^(3,1)finite_sum->real^3) (m PCROSS segment[lift(sg * t),lift sg])`]
    MOI_S6E_SURF_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `m:real^3->bool` INSIDE_INTER_OUTSIDE) THEN
  MAP_EVERY UNDISCH_TAC
   [`~(moi_s26_level (m:real^3->bool) rho sg = {})`;
    `moi_s26_level (m:real^3->bool) rho sg SUBSET
     IMAGE rho (m PCROSS segment[lift sg,lift sg])`;
    `moi_s26_level (m:real^3->bool) rho sg SUBSET
     IMAGE rho (m PCROSS segment[lift(sg * t),lift sg])`;
    `moi_s26_level (m:real^3->bool) rho (sg * t) SUBSET
     IMAGE rho (m PCROSS segment[lift(sg * t),lift sg])`] THEN
  TRY(UNDISCH_TAC `IMAGE (rho:real^(3,1)finite_sum->real^3) (m PCROSS segment[lift sg,lift sg])
                   SUBSET inside m`) THEN
  TRY(UNDISCH_TAC `IMAGE (rho:real^(3,1)finite_sum->real^3) (m PCROSS segment[lift sg,lift sg])
                   SUBSET outside m`) THEN
  SET_TAC[]);;

let MOI_S6E_FRONTIER_COMPONENT = prove
 (`!(m:real^3->bool) bdw y.
     closed m /\ connected m /\ ~(m = {}) /\ closed bdw /\ open y /\ DISJOINT m bdw
     ==> m IN components ((bdw DIFF y) UNION m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_COMPONENTS_MAXIMAL] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `c':real^3->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c':real^3->bool`; `(:real^3) DIFF (bdw DIFF y)`; `(:real^3) DIFF m`]
    MOI_S6E_CONN_SPLIT) THEN
  ASM_REWRITE_TAC[GSYM closed] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[CLOSED_DIFF]; ALL_TAC] THEN
    UNDISCH_TAC `(c':real^3->bool) SUBSET (bdw DIFF y) UNION m` THEN
    UNDISCH_TAC `DISJOINT (m:real^3->bool) bdw` THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(c':real^3->bool) SUBSET (bdw DIFF y) UNION m`; `(m:real^3->bool) SUBSET c'`;
    `~(m:real^3->bool = {})`] THEN
  SET_TAC[]);;

(* The essential loop of a circle j0 on the level t, pushed to m.            *)

let MOI_S6E_LOOP = prove
 (`!(m:real^3->bool) w (rho:real^(3,1)finite_sum->real^3) rho' t
    (f:real^2->real^3) j0 g p.
     moi_s26_bicollar m w rho rho' /\ abs t <= &1 /\
     pl_sphere 1 j0 /\ f continuous_on (j0 UNION inside j0) /\
     IMAGE f j0 SUBSET moi_s26_level m rho t /\
     ~moi_s6e_ext f j0 (moi_s26_level m rho t) /\
     g continuous_on (j0 UNION inside j0) /\ (!x. x IN j0 ==> g x = f x) /\
     IMAGE g (j0 UNION inside j0) SUBSET p /\
     IMAGE rho (m PCROSS segment[vec 0,lift t]) SUBSET p
     ==> ?b. path b /\ path_image b SUBSET m /\ pathfinish b = pathstart b /\
             homotopic_loops p b (linepath(pathstart b,pathstart b)) /\
             ~homotopic_loops m b (linepath(pathstart b,pathstart b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_BC_FACTS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^2->real^2` (X_CHOOSE_THEN `h':real^2->real^2`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_S6E_DISK) THEN
  SUBGOAL_THEN `(j0:real^2->bool) SUBSET j0 UNION inside j0` ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s26_level m rho t SUBSET (w:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s26_level] THEN
    UNDISCH_TAC `IMAGE (rho:real^(3,1)finite_sum->real^3)
                   (m PCROSS interval[--vec 1:real^1,vec 1]) = w` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SING_SUBSET; IN_INTERVAL_1; LIFT_DROP; DROP_NEG; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN w ==> fstcart((rho':real^3->real^(3,1)finite_sum) y) IN m`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(rho':real^3->real^(3,1)finite_sum) y IN m PCROSS interval[--vec 1,vec 1]`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBST1_TAC(SYM(ISPEC `(rho':real^3->real^(3,1)finite_sum) y` PASTECART_FST_SND)) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the loop gam = f o h o circ on the level *)
  MP_TAC(ISPECL [`h:real^2->real^2`; `h':real^2->real^2`; `j0:real^2->bool`;
                 `f:real^2->real^3`; `IMAGE (f:real^2->real^3) (j0 UNION inside j0)`]
    MOI_S6E_DISK_NULL) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `path_image (((f:real^2->real^3) o (h:real^2->real^2)) o moi_s6e_circ) =
                IMAGE f j0` ASSUME_TAC THENL
   [REWRITE_TAC[PATH_IMAGE_COMPOSE; MOI_S6E_CIRC; IMAGE_o] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:real^3->bool`; `w:real^3->bool`; `rho:real^(3,1)finite_sum->real^3`;
                 `rho':real^3->real^(3,1)finite_sum`; `t:real`;
                 `((f:real^2->real^3) o (h:real^2->real^2)) o moi_s6e_circ`]
    MOI_S6E_COLLAR_HOMOTOPY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `gam = ((f:real^2->real^3) o (h:real^2->real^2)) o moi_s6e_circ` THEN
  EXISTS_TAC `(\y. fstcart((rho':real^3->real^(3,1)finite_sum) y)) o (gam:real^1->real^3)` THEN
  SUBGOAL_THEN
   `path ((\y. fstcart((rho':real^3->real^(3,1)finite_sum) y)) o (gam:real^1->real^3)) /\
    pathfinish ((\y. fstcart(rho' y)) o gam) = pathstart ((\y. fstcart(rho' y)) o gam)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[PATH_IMAGE_COMPOSE; SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(y:real^3) IN path_image gam`; `path_image (gam:real^1->real^3) = IMAGE (f:real^2->real^3) j0`;
      `IMAGE (f:real^2->real^3) j0 SUBSET moi_s26_level m rho t`;
      `moi_s26_level m rho t SUBSET (w:real^3->bool)`] THEN
    SET_TAC[];
    (* null in p *)
    MATCH_MP_TAC MOI_S6E_LOOP_NULL_BASE THEN
    EXISTS_TAC `pathstart ((g o (h:real^2->real^2)) o moi_s6e_circ):real^3` THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN EXISTS_TAC `gam:real^1->real^3` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN
      MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN
      EXISTS_TAC `IMAGE (rho:real^(3,1)finite_sum->real^3) (m PCROSS segment[vec 0,lift t])` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `((g:real^2->real^3) o (h:real^2->real^2)) o moi_s6e_circ` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`path_image (gam:real^1->real^3) = IMAGE (f:real^2->real^3) j0`;
          `IMAGE (g:real^2->real^3) (j0 UNION inside j0) SUBSET p`;
          `!x:real^2. x IN j0 ==> g x = (f:real^2->real^3) x`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN EXPAND_TAC "gam" THEN
      REWRITE_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      SUBGOAL_THEN `moi_s6e_circ u IN sphere(vec 0,&1)` MP_TAC THENL
       [REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_S6E_CIRC))))] THEN
        REWRITE_TAC[path_image] THEN ASM SET_TAC[];
        ASM SET_TAC[]];
      MP_TAC(ISPECL [`h:real^2->real^2`; `h':real^2->real^2`; `j0:real^2->bool`;
                     `g:real^2->real^3`; `p:real^3->bool`] MOI_S6E_DISK_NULL) THEN
      ASM_SIMP_TAC[]];
    (* not null in m *)
    DISCH_TAC THEN
    UNDISCH_TAC `~moi_s6e_ext (f:real^2->real^3) j0 (moi_s26_level m rho t)` THEN
    REWRITE_TAC[moi_s6e_ext] THEN
    MP_TAC(ISPECL [`h:real^2->real^2`; `h':real^2->real^2`; `j0:real^2->bool`;
                   `(\y. fstcart((rho':real^3->real^(3,1)finite_sum) y)) o (f:real^2->real^3)`;
                   `m:real^3->bool`;
                   `pathstart ((\y. fstcart((rho':real^3->real^(3,1)finite_sum) y)) o
                               (gam:real^1->real^3))`]
      MOI_S6E_NULL_DISK) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
          SUBGOAL_THEN `(\y. fstcart((rho':real^3->real^(3,1)finite_sum) y)) = fstcart o rho'`
          SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
          SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^3->bool` THEN
          ASM_REWRITE_TAC[] THEN
          MAP_EVERY UNDISCH_TAC
           [`IMAGE (f:real^2->real^3) j0 SUBSET moi_s26_level m rho t`;
            `moi_s26_level m rho t SUBSET (w:real^3->bool)`] THEN
          SET_TAC[]];
        REWRITE_TAC[IMAGE_o; SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `x:real^2` THEN
        DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        MAP_EVERY UNDISCH_TAC
         [`(x:real^2) IN j0`; `IMAGE (f:real^2->real^3) j0 SUBSET moi_s26_level m rho t`;
          `moi_s26_level m rho t SUBSET (w:real^3->bool)`] THEN
        SET_TAC[];
        UNDISCH_TAC `homotopic_loops (m:real^3->bool)
                       ((\y. fstcart((rho':real^3->real^(3,1)finite_sum) y)) o gam)
                       (linepath(pathstart ((\y. fstcart(rho' y)) o gam),
                                 pathstart ((\y. fstcart(rho' y)) o gam)))` THEN
        EXPAND_TAC "gam" THEN REWRITE_TAC[o_ASSOC]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `G:real^2->real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`m:real^3->bool`; `w:real^3->bool`; `rho:real^(3,1)finite_sum->real^3`;
                   `rho':real^3->real^(3,1)finite_sum`; `&1`; `t:real`] MOI_S6E_RETRACT) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
    EXISTS_TAC `(\x. (rho:real^(3,1)finite_sum->real^3) (pastecart x (lift t))) o
                (G:real^2->real^3)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(m:real^3->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                        LIFT_DROP; DROP_NEG; DROP_VEC] THEN
        X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`(x:real^2) IN j0 UNION inside j0`;
            `IMAGE (G:real^2->real^3) (j0 UNION inside j0) SUBSET m`] THEN SET_TAC[];
          ASM_REAL_ARITH_TAC]];
      REWRITE_TAC[IMAGE_o; SUBSET; FORALL_IN_IMAGE; moi_s26_level; o_THM] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING] THEN
      MAP_EVERY UNDISCH_TAC
       [`(x:real^2) IN j0 UNION inside j0`;
        `IMAGE (G:real^2->real^3) (j0 UNION inside j0) SUBSET m`] THEN SET_TAC[];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      ASM_SIMP_TAC[o_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`(x:real^2) IN j0`; `IMAGE (f:real^2->real^3) j0 SUBSET moi_s26_level m rho t`] THEN
      SET_TAC[]]]);;

(* The loop theorem in a part wx of the cut whose boundary is m together    *)
(* with a closed set missing m: the disk meets m exactly in its rim.        *)

let MOI_S6E_FINISH = prove
 (`!(wx:(real^3->bool)->bool) (m:real^3->bool) bdw y u b.
     LOOP_THEOREM_3_STATEMENT /\ FINITE wx /\
     combinatorial_manifold_with_boundary 3 wx /\
     complex_boundary wx = (bdw DIFF y) UNION m /\
     closed m /\ connected m /\ ~(m = {}) /\ closed bdw /\ open y /\ DISJOINT m bdw /\
     UNIONS wx SUBSET u /\
     path b /\ path_image b SUBSET m /\ pathfinish b = pathstart b /\
     homotopic_loops (UNIONS wx) b (linepath(pathstart b,pathstart b)) /\
     ~homotopic_loops m b (linepath(pathstart b,pathstart b))
     ==> ?(k:real^3->bool) d f g.
           &2 simplex k /\ pl_homeomorphism (k,d) (f,g) /\ d SUBSET u /\
           d INTER m = IMAGE f (relative_frontier k) /\
           ~(?a. homotopic_with (\h. T)
                   (subtopology euclidean (IMAGE f (relative_frontier k)),
                    subtopology euclidean m) (\x. x) (\x. a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier (UNIONS (wx:(real^3->bool)->bool)) = (bdw DIFF y) UNION m`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `wx:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^3->bool) IN components (frontier (UNIONS (wx:(real^3->bool)->bool)))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S6E_FRONTIER_COMPONENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `LOOP_THEOREM_3_STATEMENT` THEN REWRITE_TAC[LOOP_THEOREM_3_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`wx:(real^3->bool)->bool`; `m:real^3->bool`; `b:real^1->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS (wx:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_homeomorphism")) (concl th))) THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier (k:real^3->bool) SUBSET k` ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    SUBGOAL_THEN `closed (k:real^3->bool)` (fun th -> SIMP_TAC[th; CLOSURE_CLOSED]) THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]; SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`d INTER frontier (UNIONS (wx:(real^3->bool)->bool)) =
     IMAGE (f:real^3->real^3) (relative_frontier k)`;
    `IMAGE (f:real^3->real^3) (relative_frontier k) SUBSET m`;
    `IMAGE (f:real^3->real^3) k = d`; `relative_frontier (k:real^3->bool) SUBSET k`;
    `frontier (UNIONS (wx:(real^3->bool)->bool)) = (bdw DIFF y) UNION m`] THEN
  SET_TAC[]);;


(* Moise 26.4 in open subsets of real^3 from the loop theorem, 26.6, the    *)
(* bicollar, the compact neighbourhood, the cut, the PL singular disk, the  *)
(* level circles and the invariance of combinatorial surfaces.              *)

let MOI_S6E_LEVEL0 = prove
 (`!(m:real^3->bool) w (rho:real^(3,1)finite_sum->real^3) rho'.
     moi_s26_bicollar m w rho rho' ==> moi_s26_level m rho (&0) = m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_BC_FACTS) THEN
  REWRITE_TAC[moi_s26_level; LIFT_NUM; EXTENSION; IN_IMAGE; EXISTS_PASTECART;
              PASTECART_IN_PCROSS; IN_SING] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`y:real^3`; `vec 0:real^1`] THEN ASM_SIMP_TAC[]]);;

let MOI_S6E_COLLAR_REGION = prove
 (`!(m:real^3->bool) w (rho:real^(3,1)finite_sum->real^3) rho' sg e X.
     moi_s26_bicollar m w rho rho' /\ (sg = &1 \/ sg = -- &1) /\ &0 < e /\ e <= &1 /\
     (!t. &0 < t /\ t <= &1 ==> moi_s26_level m rho (sg * t) SUBSET X)
     ==> IMAGE rho (m PCROSS segment[vec 0,lift(sg * e)]) SUBSET X UNION m`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_BC_FACTS) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `s:real^1`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real^1 = vec 0` THENL
   [ASM_SIMP_TAC[IN_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `?t. &0 < t /\ t <= &1 /\ s = lift(sg * t)` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `sg * drop s` THEN
    UNDISCH_TAC `(s:real^1) IN segment[vec 0,lift(sg * e)]` THEN
    UNDISCH_TAC `~(s:real^1 = vec 0)` THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; SEGMENT_1; LIFT_DROP] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th))) THEN
    COND_CASES_TAC THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s26_level")) (concl th))) THEN
  ASM_REWRITE_TAC[moi_s26_level; SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING]);;

let S26_EXT = prove
 (MOI_S26_EXT,
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "bic")
   (CONJUNCTS_THEN2 (LABEL_TAC "nbhd")
   (CONJUNCTS_THEN2 (LABEL_TAC "cut")
   (CONJUNCTS_THEN2 (LABEL_TAC "fill")
   (CONJUNCTS_THEN2 (LABEL_TAC "lev") (LABEL_TAC "inv")))))))) THEN
  REWRITE_TAC[MOISE_264_OPEN_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3->bool`; `c:(real^3->bool)->bool`; `p:real^1->real^3`] THEN
  STRIP_TAC THEN
  (* the surface *)
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool) /\ compact (UNIONS c) /\
                closed (UNIONS c) /\ ~(UNIONS c = {})` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FSA_CM_SC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `compact (UNIONS (c:(real^3->bool)->bool))` ASSUME_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_COMPACT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    MP_TAC(ISPEC `p:real^1->real^3` PATH_IMAGE_NONEMPTY) THEN
    UNDISCH_TAC `path_image (p:real^1->real^3) SUBSET UNIONS c` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the PL singular disk *)
  USE_THEN "fill" (MP_TAC o SPECL [`c:(real^3->bool)->bool`; `u:real^3->bool`;
                                   `p:real^1->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PL_MAP_ON_IMP_CONTINUOUS_ON) THEN
  SUBGOAL_THEN `compact (IMAGE (f:real^2->real^3) std_triangle)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[MOI_S6E_TRIANGLE]; ALL_TAC] THEN
  (* the compact neighbourhood W *)
  USE_THEN "nbhd" (MP_TAC o SPECL [`u:real^3->bool`;
    `UNIONS c UNION IMAGE (f:real^2->real^3) std_triangle`; `c:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_UNION] THEN
    UNDISCH_TAC `UNIONS (c:(real^3->bool)->bool) SUBSET u` THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3) std_triangle SUBSET u` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:(real^3->bool)->bool` (X_CHOOSE_THEN `s:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `lf_simplicial_complex (W:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (c:(real^3->bool)->bool) SUBSET interior (UNIONS W) /\
                IMAGE (f:real^2->real^3) std_triangle SUBSET interior (UNIONS W) /\
                interior (UNIONS (W:(real^3->bool)->bool)) SUBSET UNIONS W`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_SUBSET] THEN
    UNDISCH_TAC `UNIONS (c:(real^3->bool)->bool) UNION IMAGE f std_triangle SUBSET
                 interior (UNIONS W)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* s is a combinatorial surface *)
  SUBGOAL_THEN `FINITE (s:(real^3->bool)->bool) /\ simplicial_complex s` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(s:(real^3->bool)->bool) SUBSET W` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
    SUBGOAL_THEN `FINITE (s:(real^3->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `lf_simplicial_complex (s:(real^3->bool)->bool)` MP_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_SUBCOMPLEX THEN EXISTS_TAC `W:(real^3->bool)->bool` THEN
      ASM_MESON_TAC[simplicial_subcomplex];
      REWRITE_TAC[lf_simplicial_complex; simplicial_complex] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (s:(real^3->bool)->bool)` ASSUME_TAC THENL
   [USE_THEN "inv" (MP_TAC o SPECL [`c:(real^3->bool)->bool`; `s:(real^3->bool)->bool`;
                                    `\x:real^3. x`; `\x:real^3. x`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MOI_S8TA_CM_CMB; HOMEOMORPHISM_ID];
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* M misses Bd W *)
  SUBGOAL_THEN `DISJOINT (UNIONS c) (complex_boundary (W:(real^3->bool)->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`W:(real^3->bool)->bool`; `x:real^3`] MOI_FM3_CB_NOT_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `UNIONS (c:(real^3->bool)->bool) SUBSET interior (UNIONS W)` THEN
    UNDISCH_TAC `(x:real^3) IN UNIONS c` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the cut of W along M *)
  USE_THEN "cut" (MP_TAC o SPECL [`W:(real^3->bool)->bool`; `s:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:(real^3->bool)->bool` (X_CHOOSE_THEN `w2:(real^3->bool)->bool`
    (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `UNIONS (s:(real^3->bool)->bool) = UNIONS c`]))) THEN
  (* the bicollar of M in interior |W| *)
  USE_THEN "bic" (fun th -> MP_TAC(MP th (ASSUME `MOISE_266_STATEMENT`))) THEN
  DISCH_THEN(MP_TAC o SPECL [`c:(real^3->bool)->bool`; `interior (UNIONS (W:(real^3->bool)->bool))`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_INTERIOR]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `wb:real^3->bool` (X_CHOOSE_THEN `rho:real^(3,1)finite_sum->real^3`
    (X_CHOOSE_THEN `rho':real^3->real^(3,1)finite_sum` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `moi_s26_bicollar (UNIONS c) wb rho (rho':real^3->real^(3,1)finite_sum)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[moi_s26_bicollar]; ALL_TAC] THEN
  (* two generic levels and their circles *)
  USE_THEN "lev" (MP_TAC o SPECL [`c:(real^3->bool)->bool`; `wb:real^3->bool`;
    `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`;
    `f:real^2->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `cc:(real^2->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `wb:real^3->bool`;
    `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`; `e:real`]
    MOI_S6E_BAND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS (c:(real^3->bool)->bool)`; `wb:real^3->bool`;
    `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`]
    MOI_S6E_LEVEL0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`UNIONS (c:(real^3->bool)->bool)`; `wb:real^3->bool`;
    `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`; `e:real`;
    `e:real`] MOI_S6E_RETRACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (c:(real^3->bool)->bool)`; `wb:real^3->bool`;
    `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`; `e:real`;
    `--e:real`] MOI_S6E_RETRACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (c:(real^3->bool)->bool)`; `wb:real^3->bool`;
    `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`; `e:real`;
    `&0`] MOI_S6E_RETRACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN
  (* the boundary loop does not extend into M *)
  SUBGOAL_THEN
   `~(?g. g continuous_on std_triangle /\ IMAGE g std_triangle SUBSET UNIONS c /\
          !x. x IN relative_frontier std_triangle ==> g x = (f:real^2->real^3) x)`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^2->real^3`; `g:real^2->real^3`; `UNIONS (c:(real^3->bool)->bool)`]
      MOI_S6E_TRI_NULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~homotopic_loops (UNIONS c) (p:real^1->real^3)
                                  (linepath(pathstart p,pathstart p))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S6E_LOOP_NULL_BASE THEN
    EXISTS_TAC `pathstart ((f:real^2->real^3) o std_triangle_loop)` THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(f:real^2->real^3) o std_triangle_loop` THEN
    ASM_MESON_TAC[HOMOTOPIC_LOOPS_SYM];
    ALL_TAC] THEN
  (* the minimal essential level circle *)
  MP_TAC(ISPECL [`f:real^2->real^3`; `cc:(real^2->bool)->bool`;
    `moi_s26_level (UNIONS c) (rho:real^(3,1)finite_sum->real^3) e`;
    `moi_s26_level (UNIONS c) (rho:real^(3,1)finite_sum->real^3) (--e)`;
    `moi_s26_strip (UNIONS c) (rho:real^(3,1)finite_sum->real^3) (--e) e`;
    `moi_s6e_cband (UNIONS c) (rho:real^(3,1)finite_sum->real^3) e`;
    `UNIONS (c:(real^3->bool)->bool)`;
    `\y. (rho:real^(3,1)finite_sum->real^3)
           (pastecart (fstcart ((rho':real^3->real^(3,1)finite_sum) y)) (lift (&0)))`;
    `\y. (rho:real^(3,1)finite_sum->real^3)
           (pastecart (fstcart ((rho':real^3->real^(3,1)finite_sum) y)) (lift e))`;
    `\y. (rho:real^(3,1)finite_sum->real^3)
           (pastecart (fstcart ((rho':real^3->real^(3,1)finite_sum) y)) (lift (--e)))`]
    MOI_S6E_CORE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; moi_s6e_circles] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o GEN_REWRITE_RULE I [EXTENSION] o check (fun th ->
        is_eq(concl th) &&
        can (find_term ((=) `UNIONS (cc:(real^2->bool)->bool)`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      REWRITE_TAC[SUBSET; IN_UNION] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j0:real^2->bool` (X_CHOOSE_THEN `g:real^2->real^3`
    STRIP_ASSUME_TAC)) THEN
  (* the level of j0 and its side X of M *)
  SUBGOAL_THEN `pl_sphere 1 (j0:real^2->bool) /\ j0 SUBSET relative_interior std_triangle`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?sg. (sg = &1 \/ sg = -- &1) /\
         moi_s6e_lev (f:real^2->real^3)
           (moi_s26_level (UNIONS c) (rho:real^(3,1)finite_sum->real^3) e)
           (moi_s26_level (UNIONS c) rho (--e)) j0 =
         moi_s26_level (UNIONS c) rho (sg * e)`
  (X_CHOOSE_THEN `sg:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
   [REWRITE_TAC[moi_s6e_lev] THEN COND_CASES_TAC THENL
     [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_MUL_LID];
      EXISTS_TAC `-- &1` THEN REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^3) j0 SUBSET
                moi_s26_level (UNIONS c) (rho:real^(3,1)finite_sum->real^3) (sg * e)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s6e_lev")) (concl th) &&
      is_eq(concl th))) THEN
    MATCH_MP_TAC MOI_S6E_CIRCLE_LEVEL THEN EXISTS_TAC `cc:(real^2->bool)->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; moi_s6e_circles] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o GEN_REWRITE_RULE I [EXTENSION] o check (fun th ->
      is_eq(concl th) &&
      can (find_term ((=) `UNIONS (cc:(real^2->bool)->bool)`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~moi_s6e_ext (f:real^2->real^3) j0
                  (moi_s26_level (UNIONS c) (rho:real^(3,1)finite_sum->real^3) (sg * e))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s6e_lev")) (concl th) &&
      is_eq(concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (c:(real^3->bool)->bool)`; `wb:real^3->bool`;
    `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`; `sg:real`]
    MOI_S6E_HALF_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  (* the filled disk lies on the side X, in |W| *)
  SUBGOAL_THEN `(j0:real^2->bool) UNION inside j0 SUBSET std_triangle` ASSUME_TAC THENL
   [STRIP_ASSUME_TAC MOI_S6E_TRI_C0 THEN
    MP_TAC(ISPECL [`relative_frontier std_triangle`; `j0:real^2->bool`] MOI_S6E_KIN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `relative_interior std_triangle` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `relative_frontier std_triangle UNION inside (relative_frontier std_triangle) =
                 std_triangle` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s26_level (UNIONS c) (rho:real^(3,1)finite_sum->real^3) (sg * e) SUBSET X`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^3) (j0 UNION inside j0) SUBSET X` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS (c:(real^3->bool)->bool)`;
                   `IMAGE (g:real^2->real^3) (j0 UNION inside j0)`] MOI_S6E_SURF_SIDES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(MATCH_MP MOI_S6E_JORDAN (ASSUME `pl_sphere 1 (j0:real^2->bool)`)) THEN
        SIMP_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`IMAGE (g:real^2->real^3) (j0 UNION inside j0) SUBSET
           (IMAGE f std_triangle UNION moi_s26_level (UNIONS c) rho e UNION
            moi_s26_level (UNIONS c) rho (--e)) DIFF moi_s26_strip (UNIONS c) rho (--e) e`;
          `UNIONS (c:(real^3->bool)->bool) SUBSET moi_s26_strip (UNIONS c) rho (--e) e`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(IMAGE (g:real^2->real^3) (j0 UNION inside j0) INTER X = {})` MP_TAC THENL
     [MP_TAC(MATCH_MP MOI_S6E_JORDAN (ASSUME `pl_sphere 1 (j0:real^2->bool)`)) THEN
      STRIP_TAC THEN
      UNDISCH_TAC `~(j0:real^2->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `x0:real^2`) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(f:real^2->real^3) x0` THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x0:real^2` THEN
        ASM_SIMP_TAC[IN_UNION];
        MAP_EVERY UNDISCH_TAC
         [`(x0:real^2) IN j0`;
          `IMAGE (f:real^2->real^3) j0 SUBSET moi_s26_level (UNIONS c) rho (sg * e)`;
          `moi_s26_level (UNIONS c) (rho:real^(3,1)finite_sum->real^3) (sg * e) SUBSET X`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPEC `UNIONS (c:(real^3->bool)->bool)` INSIDE_INTER_OUTSIDE) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `X:real^3->bool`)) (concl th))) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^3) (j0 UNION inside j0) SUBSET UNIONS W` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE (g:real^2->real^3) (j0 UNION inside j0) SUBSET
       (IMAGE f std_triangle UNION moi_s26_level (UNIONS c) rho e UNION
        moi_s26_level (UNIONS c) rho (--e)) DIFF moi_s26_strip (UNIONS c) rho (--e) e`;
      `IMAGE (f:real^2->real^3) std_triangle SUBSET interior (UNIONS W)`;
      `interior (UNIONS (W:(real^3->bool)->bool)) SUBSET UNIONS W`;
      `moi_s26_level (UNIONS c) (rho:real^(3,1)finite_sum->real^3) e SUBSET
       moi_s6e_cband (UNIONS c) rho e`;
      `moi_s26_level (UNIONS c) (rho:real^(3,1)finite_sum->real^3) (--e) SUBSET
       moi_s6e_cband (UNIONS c) rho e`;
      `moi_s6e_cband (UNIONS c) (rho:real^(3,1)finite_sum->real^3) e SUBSET wb`;
      `(wb:real^3->bool) SUBSET interior (UNIONS W)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the part wx of the cut on the side X *)
  SUBGOAL_THEN
   `?wx (Y:real^3->bool).
      (Y = inside (UNIONS c) \/ Y = outside (UNIONS c)) /\ DISJOINT X Y /\
      FINITE wx /\ combinatorial_manifold_with_boundary 3 wx /\
      UNIONS wx = UNIONS W DIFF Y /\
      complex_boundary wx = (complex_boundary W DIFF Y) UNION UNIONS c`
  (X_CHOOSE_THEN `wx:(real^3->bool)->bool` (X_CHOOSE_THEN `Y:real^3->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC))) THENL
   [MP_TAC(ISPEC `UNIONS (c:(real^3->bool)->bool)` INSIDE_INTER_OUTSIDE) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `X:real^3->bool`)) (concl th))) THENL
     [MAP_EVERY EXISTS_TAC [`w1:(real^3->bool)->bool`; `outside (UNIONS (c:(real^3->bool)->bool))`];
      MAP_EVERY EXISTS_TAC [`w2:(real^3->bool)->bool`; `inside (UNIONS (c:(real^3->bool)->bool))`]] THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `W:(real^3->bool)->bool` THEN
     ASM_MESON_TAC[simplicial_subcomplex]);
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (UNIONS (c:(real^3->bool)->bool)) Y /\ open (Y:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `Y:real^3->bool`)) (concl th))) THEN
    ASM_SIMP_TAC[OPEN_INSIDE; OPEN_OUTSIDE] THEN
    REWRITE_TAC[DISJOINT] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP; OUTSIDE_NO_OVERLAP];
    ALL_TAC] THEN
  (* the essential loop pushed to M is null in wx *)
  MP_TAC(ISPECL [`UNIONS (c:(real^3->bool)->bool)`; `wb:real^3->bool`;
    `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`; `sg * e:real`;
    `f:real^2->real^3`; `j0:real^2->bool`; `g:real^2->real^3`;
    `UNIONS (wx:(real^3->bool)->bool)`] MOI_S6E_LOOP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th) &&
        can (find_term ((=) `sg:real`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (g:real^2->real^3) (j0 UNION inside j0) SUBSET X`;
        `IMAGE (g:real^2->real^3) (j0 UNION inside j0) SUBSET UNIONS W`;
        `DISJOINT (X:real^3->bool) Y`] THEN
      SET_TAC[];
      MP_TAC(ISPECL [`UNIONS (c:(real^3->bool)->bool)`; `wb:real^3->bool`;
        `rho:real^(3,1)finite_sum->real^3`; `rho':real^3->real^(3,1)finite_sum`; `sg:real`;
        `e:real`; `X:real^3->bool`] MOI_S6E_COLLAR_REGION) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE (rho:real^(3,1)finite_sum->real^3)
                      (UNIONS c PCROSS segment[vec 0,lift(sg * e)]) SUBSET wb`
      MP_TAC THENL
       [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6E_BC_FACTS) THEN
        UNDISCH_TAC `IMAGE (rho:real^(3,1)finite_sum->real^3)
                       (UNIONS c PCROSS interval[--vec 1:real^1,vec 1]) = wb` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
        REWRITE_TAC[SEGMENT_1; LIFT_DROP; DROP_VEC] THEN
        FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th) &&
          can (find_term ((=) `sg:real`)) (concl th))) THEN
        COND_CASES_TAC THEN
        REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP; DROP_NEG; DROP_VEC] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`DISJOINT (X:real^3->bool) Y`; `DISJOINT (UNIONS (c:(real^3->bool)->bool)) Y`;
        `(wb:real^3->bool) SUBSET interior (UNIONS W)`;
        `interior (UNIONS (W:(real^3->bool)->bool)) SUBSET UNIONS W`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^1->real^3` STRIP_ASSUME_TAC) THEN
  (* the loop theorem in wx *)
  MATCH_MP_TAC MOI_S6E_FINISH THEN
  MAP_EVERY EXISTS_TAC [`wx:(real^3->bool)->bool`; `complex_boundary (W:(real^3->bool)->bool)`;
                        `Y:real^3->bool`; `b:real^1->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `W:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC[FRONTIER_CLOSED];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS (W:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

