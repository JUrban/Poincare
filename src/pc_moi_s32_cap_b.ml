(* ========================================================================= *)
(* pc_moi_s32_cap_b: disk surgery at the centre of a pseudo-cell (Moise      *)
(* 32.4, pp.228-229).  Main theorem CAP_SURGERY : |- MOI_S32_CAP_SURGERY     *)
(* (statement file pc_moi_s3032_stmt.ml).  From the CAP_SETUP data (a small  *)
(* PL ball c crossing the pseudo-cell e in finitely many polygons inside a   *)
(* small disk dz around the centre p): a polygon of frontier c INTER e       *)
(* around p bounds an irreducible disk of frontier c, which is cleared of    *)
(* the other polygons by inmost splittings (planar Jordan-Schoenflies in the *)
(* chart of dz, POLY_DISK, push-offs in DISK_CHART boxes).                   *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_s34_h1.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_tube3.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Jordan curves in the plane.  The closed domain of a Jordan            *)
(* curve, nesting of disjoint Jordan curves, and nonseparation by a finite   *)
(* union of closed domains of pairwise disjoint Jordan curves.               *)
(* ------------------------------------------------------------------------- *)

let MOI_S3C2_JORDAN = prove
 (`!c:real^2->bool.
     c homeomorphic sphere(vec 0:real^2,&1)
     ==> ~(inside c = {}) /\ open(inside c) /\ connected(inside c) /\
         open(outside c) /\ connected(outside c) /\
         bounded(inside c) /\ ~bounded(outside c) /\
         inside c INTER outside c = {} /\ inside c UNION outside c = (:real^2) DIFF c /\
         frontier(inside c) = c /\ frontier(outside c) = c /\ compact c /\ connected c`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:real^2->bool`; `vec 0:real^2`; `&1`]
    HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^2` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_SIMP_TAC[JORDAN_INSIDE_OUTSIDE; COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH;
               CONNECTED_PATH_IMAGE]);;

let MOI_S3C2_JORDAN_DISK = prove
 (`!c:real^2->bool.
     c homeomorphic sphere(vec 0:real^2,&1)
     ==> ?k k'. homeomorphism ((:real^2),(:real^2)) (k,k') /\
                IMAGE k (sphere(vec 0,&1)) = c /\
                IMAGE k (cball(vec 0,&1)) = c UNION inside c /\
                IMAGE k (ball(vec 0,&1)) = inside c`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:real^2->bool`; `vec 0:real^2`; `&1`]
    HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(c:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `f':real^2->real^2`
    ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`circlepath(vec 0:real^2,&1)`; `h:real^1->real^2`;
                 `f:real^2->real^2`; `f':real^2->real^2`] JORDAN_SCHOENFLIES) THEN
  ASM_SIMP_TAC[SIMPLE_PATH_CIRCLEPATH; PATH_IMAGE_CIRCLEPATH; REAL_POS; REAL_OF_NUM_EQ;
               ARITH_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->real^2` (X_CHOOSE_THEN `k':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:real^2->real^2`; `k':real^2->real^2`] THEN
  ASM_REWRITE_TAC[GSYM INSIDE_SPHERE] THEN
  REWRITE_TAC[GSYM SPHERE_UNION_BALL; IMAGE_UNION; INSIDE_SPHERE] THEN
  ASM_REWRITE_TAC[GSYM INSIDE_SPHERE]);;

let MOI_S3C2_CONNECTED_SIDE = prove
 (`!c s:real^2->bool.
     c homeomorphic sphere(vec 0:real^2,&1) /\ connected s /\ DISJOINT s c
     ==> s SUBSET inside c \/ s SUBSET outside c`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3C2_JORDAN) THEN
  ASM_CASES_TAC `(s:real^2->bool) SUBSET inside c` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `s INTER inside c:real^2->bool = {}` THENL
   [UNDISCH_TAC `inside c UNION outside c = (:real^2) DIFF c` THEN
    UNDISCH_TAC `DISJOINT (s:real^2->bool) c` THEN
    UNDISCH_TAC `s INTER inside c:real^2->bool = {}` THEN SET_TAC[];
    MP_TAC(ISPECL [`s:real^2->bool`; `inside c:real^2->bool`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (s:real^2->bool) c` THEN SET_TAC[]]);;

let MOI_S3C2_CLOSED_DOMAIN = prove
 (`!c:real^2->bool.
     c homeomorphic sphere(vec 0:real^2,&1)
     ==> compact (c UNION inside c) /\ connected (c UNION inside c) /\
         c UNION inside c = (:real^2) DIFF outside c /\
         closure (outside c) = c UNION outside c`,
  GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3C2_JORDAN) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k:real^2->real^2` (X_CHOOSE_THEN `k':real^2->real^2`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_S3C2_JORDAN_DISK) THEN
  REWRITE_TAC[UNION_WITH_INSIDE] THEN
  SUBGOAL_THEN `closure(outside c) = c UNION outside (c:real^2->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(:real^2) DIFF outside c = IMAGE (k:real^2->real^2) (cball(vec 0,&1))`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[UNION_WITH_INSIDE]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^2->real^2) continuous_on cball(vec 0,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[homeomorphism];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; CONNECTED_CONTINUOUS_IMAGE; COMPACT_CBALL;
               CONNECTED_CBALL]);;

let MOI_S3C2_NEST_INSIDE = prove
 (`!c1 c2:real^2->bool.
     c1 homeomorphic sphere(vec 0:real^2,&1) /\ c2 homeomorphic sphere(vec 0:real^2,&1) /\
     DISJOINT c1 c2 /\ c1 SUBSET inside c2
     ==> c1 UNION inside c1 SUBSET inside c2 /\ c2 SUBSET outside c1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3C2_JORDAN o
    check (fun th -> rand(rator(concl th)) = `c1:real^2->bool`)) THEN
  MP_TAC(ISPEC `c2:real^2->bool` MOI_S3C2_JORDAN) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `c1:real^2->bool` MOI_S3C2_CLOSED_DOMAIN) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `outside c2 SUBSET outside (c1:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c1:real^2->bool`; `outside c2:real^2->bool`] MOI_S3C2_CONNECTED_SIDE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `c1 SUBSET inside (c2:real^2->bool)` THEN
      UNDISCH_TAC `inside c2 INTER outside c2 = {}:real^2->bool` THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[BOUNDED_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `c2 SUBSET outside (c1:real^2->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `c2 SUBSET closure(outside (c1:real^2->bool))` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(outside (c2:real^2->bool))` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `frontier(outside c2) = (c2:real^2->bool)` THEN
        REWRITE_TAC[frontier] THEN SET_TAC[];
        MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (c1:real^2->bool) c2` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN
  MAP_EVERY UNDISCH_TAC
   [`inside c2 UNION outside c2 = (:real^2) DIFF c2`;
    `inside c1 INTER outside c1 = {}:real^2->bool`;
    `outside c2 SUBSET outside (c1:real^2->bool)`;
    `c2 SUBSET outside (c1:real^2->bool)`] THEN
  SET_TAC[]);;

let MOI_S3C2_NEST = prove
 (`!c1 c2:real^2->bool.
     c1 homeomorphic sphere(vec 0:real^2,&1) /\ c2 homeomorphic sphere(vec 0:real^2,&1) /\
     DISJOINT c1 c2
     ==> c1 UNION inside c1 SUBSET inside c2 \/ c2 UNION inside c2 SUBSET inside c1 \/
         DISJOINT (c1 UNION inside c1) (c2 UNION inside c2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (c2:real^2->bool) c1` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `c1:real^2->bool` MOI_S3C2_JORDAN) THEN
  MP_TAC(ISPEC `c2:real^2->bool` MOI_S3C2_JORDAN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c2:real^2->bool`; `c1:real^2->bool`] MOI_S3C2_CONNECTED_SIDE) THEN
  MP_TAC(ISPECL [`c1:real^2->bool`; `c2:real^2->bool`] MOI_S3C2_CONNECTED_SIDE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [DISJ1_TAC THEN
    MP_TAC(ISPECL [`c1:real^2->bool`; `c2:real^2->bool`] MOI_S3C2_NEST_INSIDE) THEN
    ASM_SIMP_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN
    MP_TAC(ISPECL [`c2:real^2->bool`; `c1:real^2->bool`] MOI_S3C2_NEST_INSIDE) THEN
    ASM_SIMP_TAC[];
    DISJ1_TAC THEN
    MP_TAC(ISPECL [`c1:real^2->bool`; `c2:real^2->bool`] MOI_S3C2_NEST_INSIDE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN
  MP_TAC(ISPEC `c1:real^2->bool` MOI_S3C2_CLOSED_DOMAIN) THEN
  MP_TAC(ISPEC `c2:real^2->bool` MOI_S3C2_CLOSED_DOMAIN) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c1:real^2->bool`; `c2 UNION inside c2:real^2->bool`]
    MOI_S3C2_CONNECTED_SIDE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `c1 SUBSET outside (c2:real^2->bool)` THEN
    UNDISCH_TAC `c2 UNION inside c2 = (:real^2) DIFF outside c2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c2:real^2->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `frontier(inside c2) = (c2:real^2->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FRONTIER_EQ_EMPTY; BOUNDED_EMPTY; NOT_BOUNDED_UNIV];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `c2 SUBSET outside (c1:real^2->bool)` THEN
    UNDISCH_TAC `c2 UNION inside c2 SUBSET inside (c1:real^2->bool)` THEN
    UNDISCH_TAC `inside c1 INTER outside c1 = {}:real^2->bool` THEN
    UNDISCH_TAC `~(c2:real^2->bool = {})` THEN SET_TAC[];
    UNDISCH_TAC `c2 UNION inside c2 SUBSET outside (c1:real^2->bool)` THEN
    UNDISCH_TAC `c1 UNION inside c1 = (:real^2) DIFF outside c1` THEN SET_TAC[]]);;

let MOI_S3C2_JORDAN_NONEMPTY = prove
 (`!c:real^2->bool. c homeomorphic sphere(vec 0:real^2,&1) ==> ~(c = {})`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `(p ==> ~q) <=> (q ==> ~p)`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[HOMEOMORPHIC_EMPTY] THEN
  REWRITE_TAC[SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC);;

let MOI_S3C2_INNERMOST = prove
 (`!ff:(real^2->bool)->bool.
     FINITE ff /\ ~(ff = {}) /\ (!c. c IN ff ==> c homeomorphic sphere(vec 0:real^2,&1))
     ==> ?c0. c0 IN ff /\ !c. c IN ff ==> ~(c UNION inside c SUBSET inside c0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\c c':real^2->bool. c IN ff /\ c' IN ff /\ c UNION inside c SUBSET inside c'`
    WF_FINITE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `c:real^2->bool` THEN
      ASM_CASES_TAC `(c:real^2->bool) IN ff` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `c:real^2->bool` INSIDE_NO_OVERLAP) THEN
      MP_TAC(ISPEC `c:real^2->bool` MOI_S3C2_JORDAN_NONEMPTY) THEN ASM_SIMP_TAC[] THEN
      SET_TAC[];
      SET_TAC[];
      GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ff:(real^2->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[WF] THEN DISCH_THEN(MP_TAC o SPEC `\c:real^2->bool. c IN ff`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]);;

let MOI_S3C2_DOMAINS_NONSEP = prove
 (`!ff:(real^2->bool)->bool.
     FINITE ff /\ (!c. c IN ff ==> c homeomorphic sphere(vec 0:real^2,&1)) /\
     pairwise DISJOINT ff
     ==> connected ((:real^2) DIFF UNIONS (IMAGE (\c. c UNION inside c) ff))`,
  SUBGOAL_THEN
   `!n ff:(real^2->bool)->bool.
      CARD ff = n /\ FINITE ff /\ (!c. c IN ff ==> c homeomorphic sphere(vec 0:real^2,&1)) /\
      pairwise DISJOINT ff
      ==> connected ((:real^2) DIFF UNIONS (IMAGE (\c. c UNION inside c) ff))`
  (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `ff:(real^2->bool)->bool = {}` SUBST1_TAC THENL
     [ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; DIFF_EMPTY; CONNECTED_UNIV];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(ff:(real^2->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `CARD(ff:(real^2->bool)->bool) = SUC n` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `ff:(real^2->bool)->bool` MOI_S3C2_INNERMOST) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `connected ((:real^2) DIFF
                 UNIONS (IMAGE (\c. c UNION inside c) (ff DELETE (c0:real^2->bool))))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[CARD_DELETE] THEN ARITH_TAC;
      ASM_SIMP_TAC[FINITE_DELETE];
      ASM_SIMP_TAC[IN_DELETE];
      UNDISCH_TAC `pairwise DISJOINT (ff:(real^2->bool)->bool)` THEN
      REWRITE_TAC[pairwise; IN_DELETE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c0:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S3C2_CLOSED_DOMAIN
    (ASSUME `(c0:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)`)) THEN
  MP_TAC(MATCH_MP MOI_S3C2_JORDAN
    (ASSUME `(c0:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)`)) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ff = (c0:real^2->bool) INSERT (ff DELETE c0)` SUBST1_TAC THENL
   [UNDISCH_TAC `(c0:real^2->bool) IN ff` THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN
  MATCH_MP_TAC JANISZEWSKI_CONNECTED THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DELETE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_DELETE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MP_TAC(ISPEC `x:real^2->bool` MOI_S3C2_CLOSED_DOMAIN) THEN ASM_SIMP_TAC[];
    ASM_CASES_TAC `?c:real^2->bool. c IN ff DELETE c0 /\
                                    c0 UNION inside c0 SUBSET inside c` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `c1:real^2->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(c0 UNION inside c0) INTER
                    UNIONS (IMAGE (\c. c UNION inside c) (ff DELETE c0)) =
                    c0 UNION inside (c0:real^2->bool)` SUBST1_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!a b s:(real^2->bool)->bool.
           a SUBSET b /\ b IN s ==> a INTER UNIONS s = a`) THEN
        EXISTS_TAC `c1 UNION inside (c1:real^2->bool)` THEN CONJ_TAC THENL
         [UNDISCH_TAC `c0 UNION inside c0 SUBSET inside (c1:real^2->bool)` THEN SET_TAC[];
          REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `c1:real^2->bool` THEN ASM_REWRITE_TAC[]];
        FIRST_ASSUM ACCEPT_TAC];
      SUBGOAL_THEN `(c0 UNION inside c0) INTER
                    UNIONS (IMAGE (\c. c UNION inside c) (ff DELETE c0)) = {}:real^2->bool`
        (fun th -> REWRITE_TAC[th; CONNECTED_EMPTY]) THEN
      REWRITE_TAC[SET_RULE `!a s:(real^2->bool)->bool.
         a INTER UNIONS s = {} <=> !b. b IN s ==> DISJOINT a b`] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_DELETE] THEN
      X_GEN_TAC `c:real^2->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`c0:real^2->bool`; `c:real^2->bool`] MOI_S3C2_NEST) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[] THEN
        UNDISCH_TAC `pairwise DISJOINT (ff:(real^2->bool)->bool)` THEN
        REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THENL
       [ASM_MESON_TAC[IN_DELETE];
        ASM_MESON_TAC[]]];
    UNDISCH_TAC `c0 UNION inside c0 = (:real^2) DIFF outside c0` THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SET_RULE `(:real^2) DIFF ((:real^2) DIFF s) = s`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;


(* ------------------------------------------------------------------------- *)
(* 2. The setting (pseudo-cell e, rim j, centre p, radius d, the cap data of *)
(* moi_s32_cap_data), the central circles and the disks of e bounded by the  *)
(* circles of ff, read in the planar chart (fz,gz) of dz.                   *)
(* ------------------------------------------------------------------------- *)

let moi_s3c2_setting =
  let args = [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
              `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
              `gz:real^3->real^2`; `ff:(real^3->bool)->bool`] in
  let ty = itlist (fun a t -> mk_fun_ty (type_of a) t) args bool_ty in
  new_definition
   (mk_eq(list_mk_comb(mk_var("moi_s3c2_setting",ty),args),
          mk_conj(`pseudo_cell (e:real^3->bool) j p /\ &0 < d`, moi_s32_cap_data)));;

let moi_s3c2_central = new_definition
 `moi_s3c2_central (gz:real^3->real^2) (jj:real^3->bool) <=>
    vec 0 IN inside (IMAGE gz jj)`;;

let moi_s3c2_disk = new_definition
 `moi_s3c2_disk (fz:real^2->real^3) (gz:real^3->real^2) (jj:real^3->bool) =
    IMAGE fz (IMAGE gz jj UNION inside (IMAGE gz jj))`;;

(* Images of open subsets of the open unit disk are open in e (invariance   *)
(* of domain through the chart e DIFF j of the pseudo-cell).                 *)

let MOI_S3C2_CHART_OPEN = prove
 (`!(e:real^3->bool) j dz (fz:real^2->real^3) gz u.
     closed j /\ (e DIFF j) homeomorphic ball(vec 0:real^2,&1) /\
     homeomorphism (cball(vec 0,&1),dz) (fz,gz) /\ dz SUBSET e DIFF j /\
     open u /\ u SUBSET ball(vec 0,&1)
     ==> open_in (subtopology euclidean e) (IMAGE fz u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic] o check (fun th ->
    concl th = `((e:real^3->bool) DIFF j) homeomorphic ball(vec 0:real^2,&1)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^2` (X_CHOOSE_TAC `h':real^2->real^3`)) THEN
  SUBGOAL_THEN `u SUBSET cball(vec 0:real^2,&1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`vec 0:real^2`; `&1`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (fz:real^2->real^3) u SUBSET e DIFF j` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (cball(vec 0,&1),dz)
                   ((fz:real^2->real^3),(gz:real^3->real^2))` THEN
    REWRITE_TAC[homeomorphism] THEN
    UNDISCH_TAC `dz SUBSET (e:real^3->bool) DIFF j` THEN
    UNDISCH_TAC `u SUBSET cball(vec 0:real^2,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE ((h:real^3->real^2) o (fz:real^2->real^3)) u)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `cball(vec 0:real^2,&1)` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[homeomorphism];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(e:real^3->bool) DIFF j` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[homeomorphism]];
      REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(fz:real^2->real^3) x = fz y` MP_TAC THENL
       [UNDISCH_TAC `homeomorphism (e DIFF j,ball(vec 0:real^2,&1))
                       ((h:real^3->real^2),(h':real^2->real^3))` THEN
        REWRITE_TAC[homeomorphism] THEN
        UNDISCH_TAC `IMAGE (fz:real^2->real^3) u SUBSET e DIFF j` THEN
        UNDISCH_TAC `(x:real^2) IN u` THEN UNDISCH_TAC `(y:real^2) IN u` THEN
        UNDISCH_TAC `(h:real^3->real^2) ((fz:real^2->real^3) x) = h (fz y)` THEN
        SET_TAC[];
        UNDISCH_TAC `homeomorphism (cball(vec 0,&1),dz)
                       ((fz:real^2->real^3),(gz:real^3->real^2))` THEN
        REWRITE_TAC[homeomorphism] THEN
        UNDISCH_TAC `u SUBSET cball(vec 0:real^2,&1)` THEN
        UNDISCH_TAC `(x:real^2) IN u` THEN UNDISCH_TAC `(y:real^2) IN u` THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean ((e:real^3->bool) DIFF j))
                        (IMAGE (fz:real^2->real^3) u)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (fz:real^2->real^3) u =
                  IMAGE (h':real^2->real^3) (IMAGE ((h:real^3->real^2) o fz) u)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `homeomorphism (e DIFF j,ball(vec 0:real^2,&1))
                     ((h:real^3->real^2),(h':real^2->real^3))` THEN
      REWRITE_TAC[homeomorphism; IMAGE_o] THEN
      UNDISCH_TAC `IMAGE (fz:real^2->real^3) u SUBSET e DIFF j` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`h:real^3->real^2`; `ball(vec 0:real^2,&1)`] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homeomorphism (e DIFF j,ball(vec 0:real^2,&1))
                   ((h:real^3->real^2),(h':real^2->real^3))` THEN
    REWRITE_TAC[homeomorphism; IMAGE_o] THEN
    UNDISCH_TAC `IMAGE (fz:real^2->real^3) u SUBSET e DIFF j` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `(e:real^3->bool) DIFF j` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(e:real^3->bool) DIFF j = e INTER ((:real^3) DIFF j)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed]);;

let MOI_S3C2_BASICS = prove
 (`!e j p d c dz (fz:real^2->real^3) gz ff.
     moi_s3c2_setting e j p d c dz fz gz ff
     ==> compact c /\ compact j /\ closed e /\ j SUBSET e /\ p IN e /\ ~(p IN j) /\
         frontier c SUBSET c /\ ~(p IN frontier c) /\ pl_sphere 2 (frontier c) /\
         interior c = inside (frontier c) /\ c = frontier c UNION inside (frontier c) /\
         dz SUBSET e DIFF j /\ dz SUBSET ball(p,d) /\
         IMAGE fz (cball(vec 0,&1)) = dz /\
         IMAGE fz (ball(vec 0,&1)) SUBSET dz /\
         (!x. x IN cball(vec 0,&1) ==> gz (fz x) = x) /\
         (!y. y IN dz ==> fz (gz y) = y) /\
         fz continuous_on cball(vec 0,&1) /\
         (e DIFF j) homeomorphic ball(vec 0:real^2,&1) /\
         closed j /\ p IN interior c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3c2_setting; pseudo_cell] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5C_PL_BALL_3_FILL) THEN
  SUBGOAL_THEN `compact (j:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`j:real^3->bool`; `sphere(vec 0:real^2,&1)`]
      HOMEOMORPHIC_COMPACTNESS) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE]; ALL_TAC] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; FRONTIER_SUBSET_COMPACT] THEN
  UNDISCH_TAC `homeomorphism (cball(vec 0,&1),dz)
                 ((fz:real^2->real^3),(gz:real^3->real^2))` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `closure((e:real^3->bool) DIFF j) = e` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[CLOSED_CLOSURE];
    UNDISCH_TAC `(p:real^3) IN e DIFF j` THEN SET_TAC[];
    UNDISCH_TAC `(p:real^3) IN e DIFF j` THEN SET_TAC[];
    REWRITE_TAC[frontier; IN_DIFF] THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `dz SUBSET ((e:real^3->bool) DIFF j) INTER ball(p,d)` THEN SET_TAC[];
    UNDISCH_TAC `dz SUBSET ((e:real^3->bool) DIFF j) INTER ball(p,d)` THEN SET_TAC[];
    UNDISCH_TAC `IMAGE (fz:real^2->real^3) (cball(vec 0,&1)) = dz` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[BALL_SUBSET_CBALL]]);;

let MOI_S3C2_CHART_INV = prove
 (`!dz (fz:real^2->real^3) gz s.
     homeomorphism (cball(vec 0,&1),dz) (fz,gz) /\ s SUBSET IMAGE fz (ball(vec 0,&1))
     ==> IMAGE gz s SUBSET ball(vec 0,&1) /\ IMAGE fz (IMAGE gz s) = s /\
         s SUBSET dz /\ IMAGE gz s homeomorphic s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] BALL_SUBSET_CBALL) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(s:real^3->bool) SUBSET dz` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (fz:real^2->real^3) (cball(vec 0,&1)) = dz` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(s:real^3->bool) SUBSET IMAGE fz (ball(vec 0:real^2,&1))` THEN
    UNDISCH_TAC `ball(vec 0:real^2,&1) SUBSET cball(vec 0,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (gz:real^3->real^2) s SUBSET ball(vec 0,&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^3->bool) SUBSET IMAGE fz (ball(vec 0:real^2,&1))` THEN
    UNDISCH_TAC `!x:real^2. x IN cball(vec 0,&1) ==> (gz:real^3->real^2) (fz x) = x` THEN
    UNDISCH_TAC `ball(vec 0:real^2,&1) SUBSET cball(vec 0,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (fz:real^2->real^3) (IMAGE gz s) = s` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^3->bool) SUBSET dz` THEN
    UNDISCH_TAC `!y:real^3. y IN dz ==> (fz:real^2->real^3) (gz y) = y` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[homeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`fz:real^2->real^3`; `gz:real^3->real^2`] THEN
  MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
  MAP_EVERY EXISTS_TAC [`cball(vec 0:real^2,&1)`; `dz:real^3->bool`] THEN
  ASM_REWRITE_TAC[homeomorphism] THEN
  UNDISCH_TAC `IMAGE (gz:real^3->real^2) s SUBSET ball(vec 0,&1)` THEN
  UNDISCH_TAC `ball(vec 0:real^2,&1) SUBSET cball(vec 0,&1)` THEN SET_TAC[]);;

let MOI_S3C2_CIRCLE = prove
 (`!e j p d c dz (fz:real^2->real^3) gz ff jj.
     moi_s3c2_setting e j p d c dz fz gz ff /\ jj IN ff
     ==> jj SUBSET frontier c /\ jj SUBSET e /\ jj SUBSET IMAGE fz (ball(vec 0,&1)) /\
         jj SUBSET dz /\ IMAGE gz jj SUBSET ball(vec 0,&1) /\
         IMAGE fz (IMAGE gz jj) = jj /\
         IMAGE gz jj homeomorphic sphere(vec 0:real^2,&1) /\
         compact jj /\ ~(jj = {}) /\ ~(p IN jj) /\ pl_sphere 1 jj`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3C2_BASICS) THEN
  UNDISCH_TAC `moi_s3c2_setting e j p d c dz (fz:real^2->real^3) gz ff` THEN
  REWRITE_TAC[moi_s3c2_setting; pseudo_cell] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 1 (jj:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(jj:real^3->bool) SUBSET frontier c INTER e` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(jj:real^3->bool) IN ff` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(jj:real^3->bool) SUBSET IMAGE fz (ball(vec 0:real^2,&1))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `c INTER e SUBSET IMAGE (fz:real^2->real^3) (ball(vec 0,&1))` THEN
    UNDISCH_TAC `frontier c SUBSET (c:real^3->bool)` THEN
    UNDISCH_TAC `(jj:real^3->bool) SUBSET frontier c INTER e` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dz:real^3->bool`; `fz:real^2->real^3`; `gz:real^3->real^2`;
                 `jj:real^3->bool`] MOI_S3C2_CHART_INV) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(jj:real^3->bool) homeomorphic sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4U_PL_SPHERE1_CIRCLE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [UNDISCH_TAC `(jj:real^3->bool) SUBSET frontier c INTER e` THEN SET_TAC[];
    UNDISCH_TAC `(jj:real^3->bool) SUBSET frontier c INTER e` THEN SET_TAC[];
    MATCH_MP_TAC(ISPECL [`IMAGE (gz:real^3->real^2) jj`; `jj:real^3->bool`;
                         `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_TRANS) THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(ISPECL [`jj:real^3->bool`; `sphere(vec 0:real^2,&1)`]
      HOMEOMORPHIC_COMPACTNESS) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE];
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `({}:real^3->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
    REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `~((p:real^3) IN frontier c)` THEN
    UNDISCH_TAC `(jj:real^3->bool) SUBSET frontier c INTER e` THEN SET_TAC[]]);;

let MOI_S3C2_IMAGE_DIFF_INJ = prove
 (`!(f:real^2->real^3) s a b.
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     a SUBSET s /\ b SUBSET s /\ a INTER b = {}
     ==> IMAGE f (a UNION b) DIFF IMAGE f a = IMAGE f b`,
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_IMAGE; IN_UNION; IN_INTER; NOT_IN_EMPTY;
              SUBSET] THEN
  MESON_TAC[]);;

(* A Jordan curve C of the open unit disk: its closed inside is carried by  *)
(* fz to a closed topological disk of e bounded by IMAGE fz C, whose         *)
(* interior is open in e, and whose boundary is adherent to both sides.     *)

let MOI_S3C2_CHART_DISK = prove
 (`!(e:real^3->bool) j dz (fz:real^2->real^3) gz cc.
     closed j /\ (e DIFF j) homeomorphic ball(vec 0:real^2,&1) /\
     homeomorphism (cball(vec 0,&1),dz) (fz,gz) /\ dz SUBSET e DIFF j /\
     cc homeomorphic sphere(vec 0:real^2,&1) /\ cc SUBSET ball(vec 0,&1)
     ==> cc UNION inside cc SUBSET ball(vec 0,&1) /\
         compact (IMAGE fz (cc UNION inside cc)) /\
         IMAGE fz cc SUBSET IMAGE fz (cc UNION inside cc) /\
         IMAGE fz (cc UNION inside cc) SUBSET IMAGE fz (ball(vec 0,&1)) /\
         IMAGE fz (cc UNION inside cc) DIFF IMAGE fz cc = IMAGE fz (inside cc) /\
         open_in (subtopology euclidean e) (IMAGE fz (inside cc)) /\
         IMAGE fz cc SUBSET closure (IMAGE fz (inside cc)) /\
         IMAGE fz cc SUBSET closure (e DIFF IMAGE fz (cc UNION inside cc)) /\
         disk_with_boundary (IMAGE fz (cc UNION inside cc)) (IMAGE fz cc) /\
         (!x. x IN cball(vec 0,&1)
              ==> (fz x IN IMAGE fz (cc UNION inside cc) <=> x IN cc UNION inside cc))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `cc:real^2->bool` MOI_S3C2_JORDAN) THEN
  MP_TAC(ISPEC `cc:real^2->bool` MOI_S3C2_CLOSED_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC
    (filter (fun t -> not (is_eq (concl t) && is_comb (lhs (concl t)) &&
                           is_comb (rator (lhs (concl t))) &&
                           rator (rator (lhs (concl t))) = `(UNION):(real^2->bool)->(real^2->bool)->(real^2->bool)`))
            (CONJUNCTS th)))) THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] BALL_SUBSET_CBALL) THEN DISCH_TAC THEN
  SUBGOAL_THEN `inside cc SUBSET ball(vec 0:real^2,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN ASM_REWRITE_TAC[CONVEX_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `cc UNION inside cc SUBSET ball(vec 0:real^2,&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `inside cc SUBSET ball(vec 0:real^2,&1)` THEN
    UNDISCH_TAC `cc SUBSET ball(vec 0:real^2,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cc UNION inside cc SUBSET cball(vec 0:real^2,&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `cc UNION inside cc SUBSET ball(vec 0:real^2,&1)` THEN
    UNDISCH_TAC `ball(vec 0:real^2,&1) SUBSET cball(vec 0,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `homeomorphism (cball(vec 0,&1),dz)
                 ((fz:real^2->real^3),(gz:real^3->real^2))` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism] th)) THEN
  SUBGOAL_THEN `!x y:real^2. x IN cball(vec 0,&1) /\ y IN cball(vec 0,&1) /\
                             (fz:real^2->real^3) x = fz y ==> x = y`
  (LABEL_TAC "inj") THENL
   [UNDISCH_TAC `!x:real^2. x IN cball(vec 0,&1) ==> (gz:real^3->real^2) (fz x) = x` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN cball(vec 0,&1)
                  ==> ((fz:real^2->real^3) x IN IMAGE fz (cc UNION inside cc) <=>
                       x IN cc UNION inside cc)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `x:real^2 = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
      USE_THEN "inj" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `cc UNION inside cc SUBSET cball(vec 0:real^2,&1)` THEN
      UNDISCH_TAC `(y:real^2) IN cc UNION inside cc` THEN SET_TAC[];
      DISCH_TAC THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(fz:real^2->real^3) continuous_on (cc UNION inside cc)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `cball(vec 0:real^2,&1)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3C2_IMAGE_DIFF_INJ THEN
    EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
    CONJ_TAC THENL [USE_THEN "inj" ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `cc:real^2->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `cc UNION inside cc SUBSET cball(vec 0:real^2,&1)` THEN SET_TAC[];
    MATCH_MP_TAC MOI_S3C2_CHART_OPEN THEN
    MAP_EVERY EXISTS_TAC [`j:real^3->bool`; `dz:real^3->bool`; `gz:real^3->real^2`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `cc SUBSET closure(inside cc:real^2->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `frontier(inside cc:real^2->bool) = cc` THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (fz:real^2->real^3) (closure(inside cc))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    REWRITE_TAC[CLOSED_CBALL] THEN
    UNDISCH_TAC `cc UNION inside cc SUBSET cball(vec 0:real^2,&1)` THEN SET_TAC[];
    ABBREV_TAC `w = outside cc INTER ball(vec 0:real^2,&1)` THEN
    SUBGOAL_THEN `cc SUBSET closure(w:real^2->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(vec 0:real^2,&1) INTER closure(outside cc)` THEN CONJ_TAC THENL
       [UNDISCH_TAC `cc SUBSET ball(vec 0:real^2,&1)` THEN
        UNDISCH_TAC `frontier(outside cc:real^2->bool) = cc` THEN
        REWRITE_TAC[frontier] THEN SET_TAC[];
        MATCH_MP_TAC OPEN_INTER_CLOSURE_SUBSET THEN REWRITE_TAC[OPEN_BALL]];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (fz:real^2->real^3) (closure w)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
      REWRITE_TAC[CLOSED_CBALL] THEN EXPAND_TAC "w" THEN
      UNDISCH_TAC `ball(vec 0:real^2,&1) SUBSET cball(vec 0,&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(e:real^3->bool) DIFF IMAGE (fz:real^2->real^3) (cc UNION inside cc)` THEN
    REWRITE_TAC[CLOSURE_SUBSET] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN
    X_GEN_TAC `x:real^2` THEN EXPAND_TAC "w" THEN REWRITE_TAC[IN_INTER] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `dz SUBSET (e:real^3->bool) DIFF j` THEN
      UNDISCH_TAC `IMAGE (fz:real^2->real^3) (cball(vec 0,&1)) = dz` THEN
      UNDISCH_TAC `ball(vec 0:real^2,&1) SUBSET cball(vec 0,&1)` THEN
      UNDISCH_TAC `(x:real^2) IN ball(vec 0,&1)` THEN SET_TAC[];
      SUBGOAL_THEN `(x:real^2) IN cball(vec 0,&1)` ASSUME_TAC THENL
       [UNDISCH_TAC `ball(vec 0:real^2,&1) SUBSET cball(vec 0,&1)` THEN
        UNDISCH_TAC `(x:real^2) IN ball(vec 0,&1)` THEN SET_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM((fun th ->
          REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^2) IN cball(vec 0,&1)`)]) o
        check (fun th -> can (term_match []
          `!x:real^2. x IN cball(vec 0,&1) ==> (P x <=> Q x)`) (concl th))) THEN
      MP_TAC(ISPEC `cc:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
      MP_TAC(ISPEC `cc:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
      UNDISCH_TAC `(x:real^2) IN outside cc` THEN SET_TAC[]];
    MP_TAC(ISPEC `cc:real^2->bool` MOI_S3C2_JORDAN_DISK) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^2->real^2` (X_CHOOSE_THEN `k':real^2->real^2`
      STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism; IN_UNIV] o
      check (fun th -> concl th =
        `homeomorphism ((:real^2),(:real^2)) ((k:real^2->real^2),(k':real^2->real^2))`)) THEN
    REWRITE_TAC[disk_with_boundary] THEN
    MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `(fz:real^2->real^3) o (k:real^2->real^2)`;
                   `IMAGE (fz:real^2->real^3) (cc UNION inside cc)`]
      HOMEOMORPHISM_COMPACT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL; IMAGE_o] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN REWRITE_TAC[o_THM] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `(k:real^2->real^2) x = k y` MP_TAC THENL
         [USE_THEN "inj" MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `IMAGE (k:real^2->real^2) (cball(vec 0,&1)) = cc UNION inside cc` THEN
          UNDISCH_TAC `cc UNION inside cc SUBSET cball(vec 0:real^2,&1)` THEN
          UNDISCH_TAC `(x:real^2) IN cball(vec 0,&1)` THEN
          UNDISCH_TAC `(y:real^2) IN cball(vec 0,&1)` THEN SET_TAC[];
          DISCH_THEN(MP_TAC o AP_TERM `k':real^2->real^2`) THEN ASM_REWRITE_TAC[]]];
      DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^2`) THEN
      MAP_EVERY EXISTS_TAC [`(fz:real^2->real^3) o (k:real^2->real^2)`; `g:real^3->real^2`] THEN
      ASM_REWRITE_TAC[IMAGE_o]]]);;


(* ------------------------------------------------------------------------- *)
(* 3. The disks D(J) = moi_s3c2_disk fz gz J of e bounded by the circles of  *)
(* ff, their nesting, and their local structure at the boundary (crossing    *)
(* charts), which makes the non-central ones PL disks (POLY_DISK).          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3C2_DISK = prove
 (`!e j p d c dz (fz:real^2->real^3) gz ff jj.
     moi_s3c2_setting e j p d c dz fz gz ff /\ jj IN ff
     ==> compact (moi_s3c2_disk fz gz jj) /\
         jj SUBSET moi_s3c2_disk fz gz jj /\
         moi_s3c2_disk fz gz jj SUBSET dz /\
         moi_s3c2_disk fz gz jj SUBSET e /\
         moi_s3c2_disk fz gz jj SUBSET ball(p,d) /\
         DISJOINT (moi_s3c2_disk fz gz jj) j /\
         moi_s3c2_disk fz gz jj DIFF jj = IMAGE fz (inside (IMAGE gz jj)) /\
         open_in (subtopology euclidean e) (moi_s3c2_disk fz gz jj DIFF jj) /\
         jj SUBSET closure (moi_s3c2_disk fz gz jj DIFF jj) /\
         jj SUBSET closure (e DIFF moi_s3c2_disk fz gz jj) /\
         disk_with_boundary (moi_s3c2_disk fz gz jj) jj /\
         (p IN moi_s3c2_disk fz gz jj <=> moi_s3c2_central gz jj) /\
         IMAGE gz jj UNION inside (IMAGE gz jj) SUBSET ball(vec 0,&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3C2_BASICS) THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
    MOI_S3C2_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (cball(vec 0,&1),dz) ((fz:real^2->real^3),(gz:real^3->real^2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3c2_setting e j p d c dz (fz:real^2->real^3) gz ff` THEN
    REWRITE_TAC[moi_s3c2_setting] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(fz:real^2->real^3) (vec 0) = p` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3c2_setting e j p d c dz (fz:real^2->real^3) gz ff` THEN
    REWRITE_TAC[moi_s3c2_setting] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `dz:real^3->bool`;
                 `fz:real^2->real^3`; `gz:real^3->real^2`; `IMAGE (gz:real^3->real^2) jj`]
    MOI_S3C2_CHART_DISK) THEN
  ASM_REWRITE_TAC[moi_s3c2_disk] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS];
    UNDISCH_TAC `dz SUBSET (e:real^3->bool) DIFF j` THEN
    UNDISCH_TAC `IMAGE (fz:real^2->real^3) (IMAGE (gz:real^3->real^2) jj UNION
                   inside (IMAGE gz jj)) SUBSET
                 IMAGE fz (ball(vec 0,&1))` THEN
    UNDISCH_TAC `IMAGE (fz:real^2->real^3) (ball(vec 0,&1)) SUBSET dz` THEN SET_TAC[];
    UNDISCH_TAC `dz SUBSET (ball(p:real^3,d))` THEN
    UNDISCH_TAC `IMAGE (fz:real^2->real^3) (IMAGE (gz:real^3->real^2) jj UNION
                   inside (IMAGE gz jj)) SUBSET
                 IMAGE fz (ball(vec 0,&1))` THEN
    UNDISCH_TAC `IMAGE (fz:real^2->real^3) (ball(vec 0,&1)) SUBSET dz` THEN SET_TAC[];
    UNDISCH_TAC `dz SUBSET (e:real^3->bool) DIFF j` THEN
    UNDISCH_TAC `IMAGE (fz:real^2->real^3) (IMAGE (gz:real^3->real^2) jj UNION
                   inside (IMAGE gz jj)) SUBSET
                 IMAGE fz (ball(vec 0,&1))` THEN
    UNDISCH_TAC `IMAGE (fz:real^2->real^3) (ball(vec 0,&1)) SUBSET dz` THEN SET_TAC[];
    REWRITE_TAC[moi_s3c2_central] THEN
    SUBGOAL_THEN `~((vec 0:real^2) IN IMAGE (gz:real^3->real^2) jj)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((p:real^3) IN jj)` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (fz:real^2->real^3) (IMAGE gz jj) = jj` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(fz:real^2->real^3) (vec 0) = p` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(fz:real^2->real^3) (vec 0) = p` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^2` o check (fun th ->
      can (term_match [] `!x:real^2. x IN cball(vec 0,&1) ==> (P x <=> Q x)`) (concl th))) THEN
    REWRITE_TAC[CENTRE_IN_CBALL; REAL_POS] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[IN_UNION]]);;

let MOI_S3C2_DISK_AVOID = prove
 (`!e j p d c dz (fz:real^2->real^3) gz ff jj jj1.
     moi_s3c2_setting e j p d c dz fz gz ff /\ jj IN ff /\ jj1 IN ff /\ ~(jj = jj1) /\
     ~(IMAGE gz jj UNION inside (IMAGE gz jj) SUBSET inside (IMAGE gz jj1))
     ==> DISJOINT jj (moi_s3c2_disk fz gz jj1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3C2_BASICS) THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
    MOI_S3C2_CIRCLE) THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj1:real^3->bool`]
    MOI_S3C2_CIRCLE) THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj1:real^3->bool`]
    MOI_S3C2_DISK) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (jj:real^3->bool) jj1` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3c2_setting e j p d c dz (fz:real^2->real^3) gz ff` THEN
    REWRITE_TAC[moi_s3c2_setting; pairwise] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (gz:real^3->real^2) jj) (IMAGE gz jj1)` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (jj:real^3->bool) jj1` THEN
    UNDISCH_TAC `(jj:real^3->bool) SUBSET dz` THEN
    UNDISCH_TAC `(jj1:real^3->bool) SUBSET dz` THEN
    UNDISCH_TAC `!y:real^3. y IN dz ==> (fz:real^2->real^3) (gz y) = y` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY; SUBSET] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (gz:real^3->real^2) jj)
                         (IMAGE gz jj1 UNION inside (IMAGE gz jj1))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (gz:real^3->real^2) jj`; `IMAGE (gz:real^3->real^2) jj1`]
      MOI_S3C2_NEST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `IMAGE (gz:real^3->real^2) jj` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `~(IMAGE (gz:real^3->real^2) jj UNION inside (IMAGE gz jj) SUBSET
                   inside (IMAGE gz jj1))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (fz:real^2->real^3) (IMAGE gz jj) = jj` THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
  REWRITE_TAC[moi_s3c2_disk] THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] BALL_SUBSET_CBALL) THEN
  UNDISCH_TAC `IMAGE (gz:real^3->real^2) jj SUBSET ball(vec 0,&1)` THEN
  UNDISCH_TAC `IMAGE (gz:real^3->real^2) jj1 UNION inside (IMAGE gz jj1) SUBSET
               ball(vec 0,&1)` THEN
  UNDISCH_TAC `DISJOINT (IMAGE (gz:real^3->real^2) jj)
                        (IMAGE gz jj1 UNION inside (IMAGE gz jj1))` THEN
  UNDISCH_TAC `!x:real^2. x IN cball(vec 0,&1) ==> (gz:real^3->real^2) (fz x) = x` THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY; SUBSET] THEN
  MESON_TAC[]);;

let MOI_S3C2_CENTRAL_NEST = prove
 (`!(gz:real^3->real^2) jj jj1.
     IMAGE gz jj UNION inside (IMAGE gz jj) SUBSET inside (IMAGE gz jj1) /\
     moi_s3c2_central gz jj
     ==> moi_s3c2_central gz jj1`,
  REWRITE_TAC[moi_s3c2_central] THEN SET_TAC[]);;

(* Shrinking a chart at x to a ball image inside a given neighbourhood.     *)

let MOI_S3C2_CHART_SHRINK = prove
 (`!(u0:real^3->bool) (f:real^3->real^3) g w (x:real^3).
     open u0 /\ open (IMAGE f u0) /\ pl_homeomorphism (u0,IMAGE f u0) (f,g) /\
     f x = vec 0 /\ open w /\ x IN w /\ w SUBSET u0
     ==> ?r. &0 < r /\
             open (IMAGE g (ball(vec 0,r))) /\ x IN IMAGE g (ball(vec 0,r)) /\
             IMAGE g (ball(vec 0,r)) SUBSET w /\
             homeomorphism (IMAGE g (ball(vec 0,r)),ball(vec 0,r)) (f,g) /\
             pl_map_on (IMAGE g (ball(vec 0,r))) f /\ pl_map_on (ball(vec 0,r)) g /\
             (!a. IMAGE f (a INTER IMAGE g (ball(vec 0,r))) =
                  IMAGE f (a INTER u0) INTER ball(vec 0,r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (u0,IMAGE (f:real^3->real^3) u0) (f,(g:real^3->real^3)) /\
                pl_map_on u0 f /\ pl_map_on (IMAGE f u0) g`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (u0,IMAGE (f:real^3->real^3) u0) (f,(g:real^3->real^3))` THEN
    REWRITE_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o check (fun th ->
    concl th = `homeomorphism (u0,IMAGE (f:real^3->real^3) u0) (f,(g:real^3->real^3))`)) THEN
  SUBGOAL_THEN `open (IMAGE (f:real^3->real^3) w)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^3->real^3) u0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `u0:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]
    (ASSUME `open (IMAGE (f:real^3->real^3) w)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^3`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `(f:real^3->real^3) x = vec 0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) (ball(vec 0,r)) =
                {z | z IN u0 /\ (f:real^3->real^3) z IN ball(vec 0,r)}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) w` THEN
    UNDISCH_TAC `(w:real^3->bool) SUBSET u0` THEN
    UNDISCH_TAC `!x:real^3. x IN u0 ==> (g:real^3->real^3) (f x) = x` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN
    UNDISCH_TAC `(w:real^3->bool) SUBSET u0` THEN UNDISCH_TAC `(x:real^3) IN w` THEN
    SET_TAC[];
    UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) w` THEN
    UNDISCH_TAC `(w:real^3->bool) SUBSET u0` THEN
    UNDISCH_TAC `!x:real^3. x IN u0 ==> (g:real^3->real^3) (f x) = x` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN MESON_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`u0:real^3->bool`; `IMAGE (f:real^3->real^3) u0`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) w` THEN
      UNDISCH_TAC `(w:real^3->bool) SUBSET u0` THEN SET_TAC[];
      UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) w` THEN
      UNDISCH_TAC `(w:real^3->bool) SUBSET u0` THEN
      UNDISCH_TAC `!y:real^3. y IN IMAGE (f:real^3->real^3) u0 ==> f ((g:real^3->real^3) y) = y` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; SUBSET] THEN MESON_TAC[]];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `u0:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_OPEN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_BALL]];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `IMAGE (f:real^3->real^3) u0` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_BALL] THEN
    UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) w` THEN
    UNDISCH_TAC `(w:real^3->bool) SUBSET u0` THEN SET_TAC[];
    GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!x:real^3. x IN u0 ==> (g:real^3->real^3) (f x) = x` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_INTER] THEN MESON_TAC[]]);;

let moi_s3c2_half_tac =
  REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN
  MP_TAC(REAL_ARITH `(&0 < (y:real^3)$1 \/ y$1 < &0 \/ y$1 = &0) /\
                     (y$1 <= &0 <=> y$1 < &0 \/ y$1 = &0) /\
                     (&0 <= y$1 <=> &0 < y$1 \/ y$1 = &0) /\
                     ~(&0 < y$1 /\ y$1 < &0) /\ ~(&0 < y$1 /\ y$1 = &0) /\
                     ~(y$1 < &0 /\ y$1 = &0)`) THEN
  CONV_TAC TAUT;;

(* In a chart where ee is the plane y2 = 0 and jj the line y1 = y2 = 0, a   *)
(* set dd between jj and ee whose interior dd DIFF jj and exterior ee DIFF  *)
(* dd are open in ee, both adherent to x, is one of the two closed halves.  *)

let MOI_S3C2_HALF_PLANES = prove
 (`!(u:real^3->bool) r (f:real^3->real^3) g ee dd jj (x:real^3).
     homeomorphism (u,ball(vec 0,r)) (f,g) /\ x IN u /\ open u /\
     IMAGE f (ee INTER u) = ball(vec 0,r) INTER {y | y$2 = &0} /\
     IMAGE f (jj INTER u) = ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0} /\
     jj SUBSET dd /\ dd SUBSET ee /\
     open_in (subtopology euclidean ee) (dd DIFF jj) /\
     open_in (subtopology euclidean ee) (ee DIFF dd) /\
     x IN closure (dd DIFF jj) /\ x IN closure (ee DIFF dd)
     ==> IMAGE f (dd INTER u) = ball(vec 0,r) INTER {y | y$2 = &0 /\ y$1 <= &0} \/
         IMAGE f (dd INTER u) = ball(vec 0,r) INTER {y | y$2 = &0 /\ &0 <= y$1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o check (fun th ->
    concl th = `homeomorphism (u,ball(vec 0,r)) ((f:real^3->real^3),(g:real^3->real^3))`)) THEN
  ABBREV_TAC `hp = ball(vec 0:real^3,r) INTER {y | y$2 = &0 /\ &0 < y$1}` THEN
  ABBREV_TAC `hm = ball(vec 0:real^3,r) INTER {y | y$2 = &0 /\ y$1 < &0}` THEN
  ABBREV_TAC `dset = IMAGE (f:real^3->real^3) (dd INTER u)` THEN
  SUBGOAL_THEN `!a:real^3->bool. a INTER u = IMAGE (g:real^3->real^3) (IMAGE f (a INTER u))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    UNDISCH_TAC `!x:real^3. x IN u ==> (g:real^3->real^3) (f x) = x` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ee INTER u = IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {y | y$2 = &0}) /\
                jj INTER u = IMAGE g (ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0})`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^3->real^3) (ee INTER u) = ball(vec 0,r) INTER {y | y$2 = &0}` THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) (jj INTER u) =
                 ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0}` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. s SUBSET ball(vec 0,r)
                  ==> IMAGE (f:real^3->real^3) (IMAGE g s) = s /\ IMAGE g s SUBSET u`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) (ball(vec 0,r)) = u` THEN
    UNDISCH_TAC `!y:real^3. y IN ball(vec 0,r) ==> (f:real^3->real^3) (g y) = y` THEN
    UNDISCH_TAC `(s:real^3->bool) SUBSET ball(vec 0,r)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(hp:real^3->bool) SUBSET ball(vec 0,r) /\ (hm:real^3->bool) SUBSET ball(vec 0,r) /\
                (dset:real^3->bool) SUBSET ball(vec 0,r)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hp"; "hm"; "dset"] THEN REPEAT CONJ_TAC THENL
     [SET_TAC[]; SET_TAC[];
      UNDISCH_TAC `IMAGE (f:real^3->real^3) u = ball(vec 0,r)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(IMAGE (g:real^3->real^3) hp) /\ connected(IMAGE g hm)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,r)` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    MATCH_MP_TAC CONVEX_CONNECTED THEN MAP_EVERY EXPAND_TAC ["hp"; "hm"] THEN
    REWRITE_TAC[SET_RULE `{y:real^3 | P y /\ Q y} = {y | P y} INTER {y | Q y}`] THEN
    REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CONVEX_BALL; CONVEX_STANDARD_HYPERPLANE; CONVEX_HALFSPACE_COMPONENT_LT] THEN
    REWRITE_TAC[GSYM real_gt; CONVEX_HALFSPACE_COMPONENT_GT];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,r) INTER {y | y$2 = &0} =
                hp UNION hm UNION (ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0})`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hp"; "hm"] THEN moi_s3c2_half_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. s SUBSET hp UNION hm
                  ==> IMAGE (g:real^3->real^3) s SUBSET (dd DIFF jj) UNION (ee DIFF dd)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:real^3->bool) SUBSET ball(vec 0,r) INTER {y | y$2 = &0} /\
                  s INTER (ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0}) = {}`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["hp"; "hm"] THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET hp UNION hm` THEN
      MAP_EVERY EXPAND_TAC ["hp"; "hm"] THEN
      REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      MESON_TAC[REAL_LT_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^3->real^3) y IN ee INTER u` ASSUME_TAC THENL
     [UNDISCH_TAC `ee INTER u = IMAGE (g:real^3->real^3) (ball(vec 0,r) INTER {y | y$2 = &0})` THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET ball(vec 0,r) INTER {y | y$2 = &0}` THEN
      UNDISCH_TAC `(y:real^3) IN s` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((g:real^3->real^3) y IN jj)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(f:real^3->real^3) ((g:real^3->real^3) y) IN IMAGE f (jj INTER u)`
        MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `(g:real^3->real^3) y IN ee INTER u` THEN
        UNDISCH_TAC `(g:real^3->real^3) y IN jj` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(f:real^3->real^3) (g y) = y` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `(s:real^3->bool) SUBSET ball(vec 0,r) INTER {y | y$2 = &0}` THEN
        UNDISCH_TAC `(y:real^3) IN s` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(s:real^3->bool) INTER
                   (ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0}) = {}` THEN
      UNDISCH_TAC `(y:real^3) IN s` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(g:real^3->real^3) y IN ee INTER u` THEN
    UNDISCH_TAC `~((g:real^3->real^3) y IN jj)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. s SUBSET hp UNION hm /\ connected (IMAGE (g:real^3->real^3) s)
                  ==> IMAGE g s SUBSET dd DIFF jj \/ IMAGE g s SUBSET ee DIFF dd`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S5C_CONN_TWO_OPEN_IN THEN
    EXISTS_TAC `ee:real^3->bool` THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(dd:real^3->bool) SUBSET ee` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^3->bool` o check (fun th ->
        can (term_match [] `!s:real^3->bool. s SUBSET hp UNION hm ==> P s`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  (* transfer to the ball side *)
  SUBGOAL_THEN `!s:real^3->bool. s SUBSET ball(vec 0,r)
                  ==> (IMAGE (g:real^3->real^3) s SUBSET dd DIFF jj ==> s SUBSET dset) /\
                      (IMAGE g s SUBSET ee DIFF dd ==> s INTER dset = {})`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "dset" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^3->bool` o check (fun th ->
      can (term_match [] `!s:real^3->bool. s SUBSET ball(vec 0,r) ==> P s`) (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^3->real^3) (IMAGE g s) = s` THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) s SUBSET u` THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) s SUBSET dd DIFF jj` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (g:real^3->real^3) s SUBSET ee DIFF dd` THEN
      UNDISCH_TAC `!x:real^3. x IN u ==> (g:real^3->real^3) (f x) = x` THEN
      UNDISCH_TAC `!y:real^3. y IN ball(vec 0,r) ==> (f:real^3->real^3) (g y) = y` THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET ball(vec 0,r)` THEN
      REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_IMAGE; IN_DIFF; NOT_IN_EMPTY] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((hp:real^3->bool) SUBSET dset \/ hp INTER dset = {}) /\
                ((hm:real^3->bool) SUBSET dset \/ hm INTER dset = {})`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `hp:real^3->bool` o check (fun th ->
        can (term_match [] `!s:real^3->bool. s SUBSET hp UNION hm /\ Q s ==> P s`)
        (concl th))) THEN
      ASM_REWRITE_TAC[SUBSET_UNION];
      FIRST_X_ASSUM(MP_TAC o SPEC `hm:real^3->bool` o check (fun th ->
        can (term_match [] `!s:real^3->bool. s SUBSET hp UNION hm /\ Q s ==> P s`)
        (concl th))) THEN
      ASM_REWRITE_TAC[SUBSET_UNION]] THEN
    FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `hp:real^3->bool` th) THEN
      MP_TAC(SPEC `hm:real^3->bool` th)) o check (fun th ->
        can (term_match [] `!s:real^3->bool. s SUBSET ball(vec 0,r) ==> P s /\ Q s`)
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,r) INTER {y | y$1 = &0 /\ y$2 = &0} SUBSET dset /\
                (dset:real^3->bool) SUBSET ball(vec 0,r) INTER {y | y$2 = &0}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dset" THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^3->real^3) (jj INTER u) =
                   ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0}` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `(jj:real^3->bool) SUBSET dd` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (f:real^3->real^3) (ee INTER u) = ball(vec 0,r) INTER {y | y$2 = &0}` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `(dd:real^3->bool) SUBSET ee` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the two degenerate cases are impossible *)
  SUBGOAL_THEN `~((hp:real^3->bool) INTER dset = {} /\ (hm:real^3->bool) INTER dset = {})` ASSUME_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `u INTER (dd DIFF jj) = {}:real^3->bool` MP_TAC THENL
     [ALL_TAC;
      DISCH_TAC THEN
      MP_TAC(ISPECL [`u:real^3->bool`; `(dd:real^3->bool) DIFF jj`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN closure (dd DIFF jj)` THEN
      UNDISCH_TAC `(x:real^3) IN u` THEN SET_TAC[]] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:real^3->real^3) z IN dset` ASSUME_TAC THENL
     [EXPAND_TAC "dset" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((f:real^3->real^3) z IN
                   ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0})` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^3->real^3) (jj INTER u) =
                   ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0}` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `z':real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `z:real^3 = z'` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `(f:real^3->real^3) z IN dset` THEN
    UNDISCH_TAC `dset SUBSET ball(vec 0:real^3,r) INTER {y | y$2 = &0}` THEN
    UNDISCH_TAC `ball(vec 0:real^3,r) INTER {y | y$2 = &0} =
                 hp UNION hm UNION (ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0})` THEN
    UNDISCH_TAC `(hp:real^3->bool) INTER dset = {}` THEN
    UNDISCH_TAC `(hm:real^3->bool) INTER dset = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((hp:real^3->bool) SUBSET dset /\ (hm:real^3->bool) SUBSET dset)` ASSUME_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `u INTER (ee DIFF dd) = {}:real^3->bool` MP_TAC THENL
     [ALL_TAC;
      DISCH_TAC THEN
      MP_TAC(ISPECL [`u:real^3->bool`; `(ee:real^3->bool) DIFF dd`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN closure (ee DIFF dd)` THEN
      UNDISCH_TAC `(x:real^3) IN u` THEN SET_TAC[]] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:real^3->real^3) z IN dset` MP_TAC THENL
     [SUBGOAL_THEN `(f:real^3->real^3) z IN ball(vec 0,r) INTER {y | y$2 = &0}` MP_TAC THENL
       [UNDISCH_TAC `IMAGE (f:real^3->real^3) (ee INTER u) = ball(vec 0,r) INTER {y | y$2 = &0}` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[IN_INTER];
        ALL_TAC] THEN
      UNDISCH_TAC `ball(vec 0:real^3,r) INTER {y | y$2 = &0} =
                   hp UNION hm UNION (ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0})` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `ball(vec 0:real^3,r) INTER {y | y$1 = &0 /\ y$2 = &0} SUBSET dset` THEN
      UNDISCH_TAC `(hp:real^3->bool) SUBSET dset` THEN
      UNDISCH_TAC `(hm:real^3->bool) SUBSET dset` THEN SET_TAC[];
      EXPAND_TAC "dset" THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `z':real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `z:real^3 = z'` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,r) INTER {y | y$2 = &0 /\ y$1 <= &0} =
                hm UNION (ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0}) /\
                ball(vec 0:real^3,r) INTER {y | y$2 = &0 /\ &0 <= y$1} =
                hp UNION (ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0})`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["hp"; "hm"] THEN moi_s3c2_half_tac;
    ALL_TAC] THEN
  UNDISCH_TAC `dset SUBSET ball(vec 0:real^3,r) INTER {y | y$2 = &0}` THEN
  UNDISCH_TAC `ball(vec 0:real^3,r) INTER {y | y$2 = &0} =
               hp UNION hm UNION (ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0})` THEN
  DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `ball(vec 0:real^3,r) INTER {y | y$1 = &0 /\ y$2 = &0} SUBSET dset` THEN
  UNDISCH_TAC `~((hp:real^3->bool) SUBSET dset /\ (hm:real^3->bool) SUBSET dset)` THEN
  UNDISCH_TAC `~((hp:real^3->bool) INTER dset = {} /\ (hm:real^3->bool) INTER dset = {})` THEN
  UNDISCH_TAC `(hp:real^3->bool) SUBSET dset \/ hp INTER dset = {}` THEN
  UNDISCH_TAC `(hm:real^3->bool) SUBSET dset \/ hm INTER dset = {}` THEN
  SUBGOAL_THEN `(hp:real^3->bool) INTER hm = {} /\
                (hp:real^3->bool) INTER (ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0}) = {} /\
                (hm:real^3->bool) INTER (ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0}) = {}`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["hp"; "hm"] THEN moi_s3c2_half_tac;
    ALL_TAC] THEN
  SET_TAC[]);;

(* The crossing chart of frontier c at a point x of a circle jj of ff,      *)
(* shrunk to a ball inside a given neighbourhood w of x: e is the plane     *)
(* y2 = 0, jj the line y1 = y2 = 0 and D(jj) one closed half of the plane.  *)

let MOI_S3C2_EDGE_RAW = prove
 (`!e j p d c dz (fz:real^2->real^3) gz ff jj x w.
     moi_s3c2_setting e j p d c dz fz gz ff /\ jj IN ff /\ x IN jj /\ open w /\ x IN w
     ==> ?u r (f:real^3->real^3) g.
           open u /\ x IN u /\ u SUBSET w /\ &0 < r /\
           homeomorphism (u,ball(vec 0,r)) (f,g) /\
           pl_map_on u f /\ pl_map_on (ball(vec 0,r)) g /\ f x = vec 0 /\
           IMAGE f (e INTER u) = ball(vec 0,r) INTER {y | y$2 = &0} /\
           IMAGE f (jj INTER u) = ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0} /\
           (IMAGE f (moi_s3c2_disk fz gz jj INTER u) =
            ball(vec 0,r) INTER {y | y$2 = &0 /\ y$1 <= &0} \/
            IMAGE f (moi_s3c2_disk fz gz jj INTER u) =
            ball(vec 0,r) INTER {y | y$2 = &0 /\ &0 <= y$1})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3C2_BASICS) THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
    MOI_S3C2_CIRCLE) THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
    MOI_S3C2_DISK) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `dd = moi_s3c2_disk (fz:real^2->real^3) gz jj` THEN
  SUBGOAL_THEN `FINITE (ff:(real^3->bool)->bool) /\ pairwise DISJOINT ff /\
                frontier c INTER e = UNIONS ff /\ DISJOINT c (j:real^3->bool) /\
                (!x:real^3. x IN frontier c INTER e
                            ==> pl_crossing_at (frontier c) ((e DIFF j) DELETE p) x)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3c2_setting e j p d c dz (fz:real^2->real^3) gz ff` THEN
    REWRITE_TAC[moi_s3c2_setting] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
    can (term_match [] `!x:real^3. x IN s ==> pl_crossing_at a b x`) (concl th))) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(jj:real^3->bool) SUBSET frontier c` THEN
    UNDISCH_TAC `(jj:real^3->bool) SUBSET e` THEN UNDISCH_TAC `(x:real^3) IN jj` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pl_crossing_at] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `w1 = (w INTER u0) INTER ((:real^3) DIFF (j UNION {p:real^3} UNION
                    UNIONS (ff DELETE jj)))` THEN
  SUBGOAL_THEN `~((x:real^3) IN j) /\ ~(x = p) /\
                ~((x:real^3) IN UNIONS (ff DELETE jj))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `DISJOINT c (j:real^3->bool)` THEN
      UNDISCH_TAC `frontier c SUBSET (c:real^3->bool)` THEN
      UNDISCH_TAC `(jj:real^3->bool) SUBSET frontier c` THEN
      UNDISCH_TAC `(x:real^3) IN jj` THEN SET_TAC[];
      UNDISCH_TAC `~((p:real^3) IN jj)` THEN UNDISCH_TAC `(x:real^3) IN jj` THEN
      MESON_TAC[];
      REWRITE_TAC[IN_UNIONS; IN_DELETE; NOT_EXISTS_THM] THEN
      X_GEN_TAC `k:real^3->bool` THEN STRIP_TAC THEN
      UNDISCH_TAC `pairwise DISJOINT (ff:(real^3->bool)->bool)` THEN
      REWRITE_TAC[pairwise] THEN
      DISCH_THEN(MP_TAC o SPECL [`k:real^3->bool`; `jj:real^3->bool`]) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN jj` THEN UNDISCH_TAC `(x:real^3) IN k` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS (ff DELETE (jj:real^3->bool)))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
    X_GEN_TAC `k:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                   `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                   `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `k:real^3->bool`]
      MOI_S3C2_CIRCLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (w1:real^3->bool) /\ (x:real^3) IN w1 /\ w1 SUBSET u0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w1" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_INTER THEN ASM_SIMP_TAC[OPEN_INTER] THEN
      REWRITE_TAC[GSYM closed] THEN
      REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_SING];
      ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; IN_UNION; IN_SING];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u0:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                 `w1:real^3->bool`; `x:real^3`] MOI_S3C2_CHART_SHRINK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `uu = IMAGE (g:real^3->real^3) (ball(vec 0,r))` THEN
  SUBGOAL_THEN `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u0` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (uu,ball(vec 0:real^3,r)) ((f:real^3->real^3),g)` THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) uu = ball(vec 0,r)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    UNDISCH_TAC `(uu:real^3->bool) SUBSET w1` THEN
    UNDISCH_TAC `(w1:real^3->bool) SUBSET u0` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `e INTER uu = ((e DIFF j) DELETE p) INTER (uu:real^3->bool) /\
                jj INTER uu = (frontier c INTER ((e DIFF j) DELETE p)) INTER uu`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(uu:real^3->bool) SUBSET w1` THEN EXPAND_TAC "w1" THEN
    UNDISCH_TAC `frontier c INTER e = UNIONS (ff:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `(jj:real^3->bool) IN ff` THEN
    REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_DIFF; IN_DELETE; IN_UNIV; IN_UNION;
                IN_SING; IN_UNIONS] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t:real^3->bool. s SUBSET u0 /\ t SUBSET u0
                  ==> IMAGE (f:real^3->real^3) (s INTER t) = IMAGE f s INTER IMAGE f t`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (u0,IMAGE (f:real^3->real^3) u0) (f,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `!x:real^3. x IN u0 ==> (g:real^3->real^3) (f x) = x` THEN
    UNDISCH_TAC `(s:real^3->bool) SUBSET u0` THEN UNDISCH_TAC `(t:real^3->bool) SUBSET u0` THEN
    REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^3->real^3) (e INTER uu) = ball(vec 0,r) INTER {y | y$2 = &0} /\
    IMAGE f (jj INTER uu) = ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `e INTER uu = ((e DIFF j) DELETE p) INTER (uu:real^3->bool)` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ASSUME `!a:real^3->bool. IMAGE (f:real^3->real^3) (a INTER uu) =
                                           IMAGE f (a INTER u0) INTER ball(vec 0,r)`] THEN
      UNDISCH_TAC `IMAGE (f:real^3->real^3) (((e DIFF j) DELETE p) INTER u0) =
                   IMAGE f u0 INTER {y | y$2 = &0}` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u0` THEN SET_TAC[];
      UNDISCH_TAC `jj INTER uu = (frontier c INTER ((e DIFF j) DELETE p)) INTER (uu:real^3->bool)` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ASSUME `!a:real^3->bool. IMAGE (f:real^3->real^3) (a INTER uu) =
                                           IMAGE f (a INTER u0) INTER ball(vec 0,r)`] THEN
      SUBGOAL_THEN `IMAGE (f:real^3->real^3) ((frontier c INTER ((e DIFF j) DELETE p)) INTER u0) =
                    IMAGE f (frontier c INTER u0) INTER IMAGE f (((e DIFF j) DELETE p) INTER u0)`
      SUBST1_TAC THENL
       [SUBGOAL_THEN `(frontier c INTER ((e DIFF j) DELETE p)) INTER u0 =
                      (frontier c INTER u0) INTER (((e DIFF j) DELETE p) INTER (u0:real^3->bool))`
        SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!s t:real^3->bool. s SUBSET u0 /\ t SUBSET u0 ==> P s t`)
          (concl th))) THEN
        SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (f:real^3->real^3) (((e DIFF j) DELETE p) INTER u0) =
                   IMAGE f u0 INTER {y | y$2 = &0}` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `IMAGE (f:real^3->real^3) (frontier c INTER u0) =
                   IMAGE f u0 INTER {y | y$1 = &0}` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `ball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u0` THEN SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`uu:real^3->bool`; `r:real`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [UNDISCH_TAC `(uu:real^3->bool) SUBSET w1` THEN EXPAND_TAC "w1" THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3C2_HALF_PLANES THEN
  MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `e:real^3->bool`; `jj:real^3->bool`;
                        `x:real^3`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [SUBGOAL_THEN `(e:real^3->bool) DIFF dd = e INTER ((:real^3) DIFF dd)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[GSYM closed] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    UNDISCH_TAC `(jj:real^3->bool) SUBSET closure (dd DIFF jj)` THEN
    UNDISCH_TAC `(x:real^3) IN jj` THEN SET_TAC[];
    UNDISCH_TAC `(jj:real^3->bool) SUBSET closure (e DIFF dd)` THEN
    UNDISCH_TAC `(x:real^3) IN jj` THEN SET_TAC[]]);;

let MOI_S3C2_REFLECT1 = prove
 (`!r. homeomorphism (ball(vec 0:real^3,r),ball(vec 0,r))
                     (reflect_along (basis 1),reflect_along (basis 1)) /\
       pl_map_on (ball(vec 0:real^3,r)) (reflect_along (basis 1)) /\
       reflect_along (basis 1) (vec 0:real^3) = vec 0 /\
       IMAGE (reflect_along (basis 1)) (ball(vec 0:real^3,r) INTER {y | y$2 = &0}) =
         ball(vec 0,r) INTER {y | y$2 = &0} /\
       IMAGE (reflect_along (basis 1))
             (ball(vec 0:real^3,r) INTER {y | y$1 = &0 /\ y$2 = &0}) =
         ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0} /\
       IMAGE (reflect_along (basis 1))
             (ball(vec 0:real^3,r) INTER {y | y$2 = &0 /\ &0 <= y$1}) =
         ball(vec 0,r) INTER {y | y$2 = &0 /\ y$1 <= &0}`,
  GEN_TAC THEN
  SUBGOAL_THEN `!y:real^3. (reflect_along (basis 1) y)$1 = --(y$1) /\
                           (reflect_along (basis 1) y)$2 = y$2`
  ASSUME_TAC THENL
   [SIMP_TAC[REFLECT_ALONG_BASIS_COMPONENT; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. IMAGE (reflect_along (basis 1)) s =
                                 {y | reflect_along (basis 1) y IN s}`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[REFLECT_ALONG_INVOLUTION];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism; REFLECT_ALONG_INVOLUTION] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_REFLECT_ALONG] THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL_0; NORM_REFLECT_ALONG];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^3. reflect_along (basis 1) x + vec 0` THEN
    CONJ_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
    SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_BALL; LINEAR_REFLECT_ALONG; ETA_AX];
    MATCH_MP_TAC(ISPEC `reflect_along (basis 1):real^3->real^3` LINEAR_0) THEN
    REWRITE_TAC[LINEAR_REFLECT_ALONG];
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_BALL_0; NORM_REFLECT_ALONG];
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_BALL_0; NORM_REFLECT_ALONG] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_BALL_0; NORM_REFLECT_ALONG] THEN
    GEN_TAC THEN REAL_ARITH_TAC]);;

let MOI_S3C2_EDGE = prove
 (`!e j p d c dz (fz:real^2->real^3) gz ff jj x w.
     moi_s3c2_setting e j p d c dz fz gz ff /\ jj IN ff /\ x IN jj /\ open w /\ x IN w
     ==> ?u r (f:real^3->real^3) g.
           open u /\ x IN u /\ u SUBSET w /\ &0 < r /\
           homeomorphism (u,ball(vec 0,r)) (f,g) /\
           pl_map_on u f /\ pl_map_on (ball(vec 0,r)) g /\ f x = vec 0 /\
           IMAGE f (e INTER u) = ball(vec 0,r) INTER {y | y$2 = &0} /\
           IMAGE f (jj INTER u) = ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0} /\
           IMAGE f (moi_s3c2_disk fz gz jj INTER u) =
           ball(vec 0,r) INTER {y | y$2 = &0 /\ y$1 <= &0}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S3C2_EDGE_RAW) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `r:real`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `r:real`] THENL
   [MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `r:real` MOI_S3C2_REFLECT1) THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`reflect_along (basis 1) o (f:real^3->real^3)`;
                        `(g:real^3->real^3) o reflect_along (basis 1)`] THEN
  ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `ball(vec 0:real^3,r)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `ball(vec 0:real^3,r)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[homeomorphism; SUBSET_REFL];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `ball(vec 0:real^3,r)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[homeomorphism; SUBSET_REFL]]);;

let MOI_S3C2_HALF_POLYHEDRON = prove
 (`polyhedron {y:real^3 | y$2 = &0 /\ y$1 <= &0}`,
  REWRITE_TAC[SET_RULE `{y:real^3 | P y /\ Q y} = {y | P y} INTER {y | Q y}`] THEN
  MATCH_MP_TAC POLYHEDRON_INTER THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`basis 2:real^3`; `&0`] POLYHEDRON_HYPERPLANE);
    MP_TAC(ISPECL [`basis 1:real^3`; `&0`] POLYHEDRON_HALFSPACE_LE)] THEN
  SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]);;

(* A non-central disk D(jj) misses the centre and is locally polyhedral:    *)
(* near interior points it is e, near points of jj the half plane of the   *)
(* edge chart; so it is a PL 2-cell with boundary jj (POLY_DISK).          *)

let MOI_S3C2_DISK_LOCPOLY = prove
 (`!e j p d c dz (fz:real^2->real^3) gz ff jj.
     moi_s3c2_setting e j p d c dz fz gz ff /\ jj IN ff /\ ~moi_s3c2_central gz jj
     ==> locally_polyhedral (moi_s3c2_disk fz gz jj)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
    MOI_S3C2_DISK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `locally_polyhedral ((e DIFF j) DELETE (p:real^3))` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3c2_setting e j p d c dz (fz:real^2->real^3) gz ff` THEN
    REWRITE_TAC[moi_s3c2_setting; pseudo_cell] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  ONCE_REWRITE_TAC[PL_MAP_ON_LOCAL] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^3) IN jj` THENL
   [MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                   `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                   `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`;
                   `x:real^3`; `(:real^3)`] MOI_S3C2_EDGE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `r:real`
      (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
        STRIP_ASSUME_TAC)))) THEN
    EXISTS_TAC `u:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `moi_s3c2_disk (fz:real^2->real^3) gz jj INTER u =
                  {z | z IN u /\ (f:real^3->real^3) z IN {y | y$2 = &0 /\ y$1 <= &0}}`
    SUBST1_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^3->real^3) (moi_s3c2_disk fz gz jj INTER u) =
                   ball(vec 0,r) INTER {y | y$2 = &0 /\ y$1 <= &0}` THEN
      UNDISCH_TAC `homeomorphism (u,ball(vec 0:real^3,r)) ((f:real^3->real^3),g)` THEN
      REWRITE_TAC[homeomorphism] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
      MESON_TAC[];
      MATCH_MP_TAC MOI_PTR_LOCALLY_POLYHEDRAL_PL_PREIMAGE THEN
      ASM_REWRITE_TAC[MOI_S3C2_HALF_POLYHEDRON]];
    ALL_TAC] THEN
  MP_TAC(GEN_REWRITE_RULE I [OPEN_IN_OPEN] (ASSUME
    `open_in (subtopology euclidean e)
             (moi_s3c2_disk (fz:real^2->real^3) gz jj DIFF jj)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `moi_s3c2_disk (fz:real^2->real^3) gz jj DIFF jj = e INTER w` THEN
    UNDISCH_TAC `(x:real^3) IN moi_s3c2_disk fz gz jj` THEN
    UNDISCH_TAC `~((x:real^3) IN jj)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s3c2_disk (fz:real^2->real^3) gz jj INTER w =
                ((e DIFF j) DELETE p) INTER w`
  SUBST1_TAC THENL
   [UNDISCH_TAC `moi_s3c2_disk (fz:real^2->real^3) gz jj DIFF jj = e INTER w` THEN
    UNDISCH_TAC `~((p:real^3) IN moi_s3c2_disk fz gz jj)` THEN
    UNDISCH_TAC `DISJOINT (moi_s3c2_disk (fz:real^2->real^3) gz jj) j` THEN
    UNDISCH_TAC `moi_s3c2_disk (fz:real^2->real^3) gz jj SUBSET e` THEN
    UNDISCH_TAC `(jj:real^3->bool) SUBSET moi_s3c2_disk fz gz jj` THEN
    REWRITE_TAC[EXTENSION; SUBSET; DISJOINT; IN_INTER; IN_DIFF; IN_DELETE; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN ASM_REWRITE_TAC[]]);;

let MOI_S3C2_POLY_DISK = moi_std_csq (moi_n3 MOI_S30_POLY_DISK);;

let MOI_S3C2_DISK_PL = prove
 (mk_imp(MOI_S3C2_POLY_DISK,
   `!e j p d c dz (fz:real^2->real^3) gz ff jj.
      moi_s3c2_setting e j p d c dz fz gz ff /\ jj IN ff /\ ~moi_s3c2_central gz jj
      ==> pl_cell_with_boundary 2 (moi_s3c2_disk fz gz jj) jj`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
    MOI_S3C2_DISK) THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
    MOI_S3C2_DISK_LOCPOLY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `disk_with_boundary (moi_s3c2_disk (fz:real^2->real^3) gz jj) jj` THEN
  REWRITE_TAC[disk_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->real^3` (X_CHOOSE_THEN `k':real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S3C2_POLY_DISK)) THEN
  EXISTS_TAC `k':real^3->real^2` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `jj = IMAGE (k:real^2->real^3) (sphere(vec 0,&1))` THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

(* Near a point of jj, e minus D(jj) is a connected half plane adherent to  *)
(* every point of jj nearby (the input of the one-sidedness argument).     *)

let MOI_S3C2_EDGE_SIDE = prove
 (`!e j p d c dz (fz:real^2->real^3) gz ff jj x w.
     moi_s3c2_setting e j p d c dz fz gz ff /\ jj IN ff /\ x IN jj /\ open w /\ x IN w
     ==> ?u. open u /\ x IN u /\ u SUBSET w /\
             connected ((e INTER u) DIFF moi_s3c2_disk fz gz jj) /\
             jj INTER u SUBSET closure ((e INTER u) DIFF moi_s3c2_disk fz gz jj)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S3C2_EDGE) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `r:real`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `u:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o check (fun th ->
    concl th = `homeomorphism (u,ball(vec 0:real^3,r)) ((f:real^3->real^3),g)`)) THEN
  ABBREV_TAC `hp = ball(vec 0:real^3,r) INTER {y | y$2 = &0 /\ &0 < y$1}` THEN
  SUBGOAL_THEN `(e INTER u) DIFF moi_s3c2_disk (fz:real^2->real^3) gz jj =
                IMAGE (g:real^3->real^3) hp`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3)
                 (IMAGE f (e INTER u) DIFF IMAGE f (moi_s3c2_disk fz gz jj INTER u))` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `!x:real^3. x IN u ==> (g:real^3->real^3) (f x) = x` THEN
      REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTER; IN_IMAGE] THEN MESON_TAC[];
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN EXPAND_TAC "hp" THEN
      REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN
      MP_TAC(REAL_ARITH `(y:real^3)$1 <= &0 <=> ~(&0 < y$1)`) THEN CONV_TAC TAUT];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,r)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "hp" THEN SET_TAC[];
      MATCH_MP_TAC CONVEX_CONNECTED THEN EXPAND_TAC "hp" THEN
      REWRITE_TAC[SET_RULE `{y:real^3 | P y /\ Q y} = {y | P y} INTER {y | Q y}`] THEN
      REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[CONVEX_BALL; CONVEX_STANDARD_HYPERPLANE] THEN
      REWRITE_TAC[GSYM real_gt; CONVEX_HALFSPACE_COMPONENT_GT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `jj INTER u = IMAGE (g:real^3->real^3)
                 (ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0})`
  SUBST1_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^3->real^3) (jj INTER u) =
                 ball(vec 0,r) INTER {y | y$1 = &0 /\ y$2 = &0}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `!x:real^3. x IN u ==> (g:real^3->real^3) (f x) = x` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  ABBREV_TAC `rho = (norm(y:real^3) + r) / &2` THEN
  SUBGOAL_THEN `norm(y:real^3) < rho /\ rho < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN UNDISCH_TAC `(y:real^3) IN ball(vec 0,r)` THEN
    REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN closure (hp INTER cball(vec 0,rho))` ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_APPROACHABLE] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    ABBREV_TAC `sg = min (t / &2) ((rho - norm(y:real^3)) / &2)` THEN
    SUBGOAL_THEN `&0 < sg /\ sg < t /\ norm(y:real^3) + sg < rho` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "sg" THEN UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `norm(y:real^3) < rho` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `y + sg % basis 1:real^3` THEN
    SUBGOAL_THEN `norm(y + sg % basis 1:real^3) < rho` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(y:real^3) + norm(sg % basis 1:real^3)` THEN
      REWRITE_TAC[NORM_TRIANGLE] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      UNDISCH_TAC `&0 < sg` THEN UNDISCH_TAC `norm(y:real^3) + sg < rho` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "hp" THEN
    SIMP_TAC[IN_INTER; IN_ELIM_THM; IN_BALL_0; IN_CBALL_0; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH; dist;
             VECTOR_ARITH `(y + a) - y:real^N = a`; NORM_MUL; NORM_BASIS] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < sg` THEN UNDISCH_TAC `sg < t` THEN
    UNDISCH_TAC `norm(y + sg % basis 1:real^3) < rho` THEN UNDISCH_TAC `rho < r` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) (closure (hp INTER cball(vec 0,rho))) SUBSET
                closure (IMAGE g hp)`
  MP_TAC THENL
   [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,r)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(vec 0:real^3,rho)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_CBALL; INTER_SUBSET];
        REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN
        UNDISCH_TAC `rho < r` THEN REAL_ARITH_TAC];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (g:real^3->real^3) hp` THEN
      REWRITE_TAC[CLOSURE_SUBSET] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* 4. PATCH_PUSH: pushing a PL disk patch D of a PL disk G off the closed   *)
(* set E in a DISK_CHART box of (G,D), when E approaches D from one side    *)
(* only.  The dent is the graph of a PL bump over the middle square.        *)
(* ------------------------------------------------------------------------- *)

let moi_s3c2_bump = new_definition
 `moi_s3c2_bump (h:real) (x:real^3) =
    x + (h * max (&0) (&7 / &8 - max (abs(x$1)) (abs(x$2)))) % basis 3`;;

let moi_s3c2_o7 = new_definition
 `moi_s3c2_o7 = {x:real^3 | x IN moi_s35_mid /\ max (abs(x$1)) (abs(x$2)) < &7 / &8}`;;

let MOI_S3C2_PL_PHI = prove
 (`!s:real^3->bool.
     locally_polyhedral s
     ==> pl_map_on s (\x. lift(max (&0) (&7 / &8 - max (abs(x$1)) (abs(x$2)))))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k. pl_map_on s (\x:real^3. lift(x$k)) /\
                    pl_map_on s (\x:real^3. lift(--(x$k)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC MOI_PTR_PL_MAP_ON_LINEAR THEN
    ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT] THEN
    REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC[REAL_NEG_ADD; REAL_MUL_RNEG; LIFT_ADD; LIFT_CMUL; LIFT_NEG] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. pl_map_on s (\x:real^3. lift(abs(x$k)))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^3. lift(max (drop(lift(x$k))) (drop(lift(--(x$k)))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LIFT_DROP] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC PL_MAP_ON_LIFT_MAX THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on s (\x:real^3. lift(max (abs(x$1)) (abs(x$2))))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^3. lift(max (drop(lift(abs(x$1)))) (drop(lift(abs(x$2)))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LIFT_DROP];
      MATCH_MP_TAC PL_MAP_ON_LIFT_MAX THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on s (\x:real^3. lift(&7 / &8 - max (abs(x$1)) (abs(x$2))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^3. (\x. lift(&7 / &8)) x +
                          (\x. --(&1) % lift(max (abs(x$1)) (abs(x$2)))) x` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN REPEAT STRIP_TAC THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC PL_MAP_ON_ADD THEN ASM_SIMP_TAC[PL_MAP_ON_CONST] THEN
      MATCH_MP_TAC PL_MAP_ON_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `\x:real^3. lift(max (drop(lift(&0)))
                              (drop(lift(&7 / &8 - max (abs(x$1)) (abs(x$2))))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIFT_DROP];
    MATCH_MP_TAC PL_MAP_ON_LIFT_MAX THEN ASM_SIMP_TAC[PL_MAP_ON_CONST]]);;

let MOI_S3C2_MID_FACTS = prove
 (`polytope moi_s35_mid /\ compact moi_s35_mid /\ locally_polyhedral moi_s35_mid /\
   moi_s35_mid SUBSET moi_s35_cube /\ moi_s30_inner SUBSET moi_s35_mid /\
   compact moi_s35_cube /\ polytope moi_s35_cube /\
   (!x:real^3. x IN moi_s35_cube <=>
               abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ abs(x$3) <= &1) /\
   (!x:real^3. x IN moi_s35_mid <=> abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ x$3 = &0) /\
   (!x:real^3. x IN moi_s30_inner <=>
               abs(x$1) <= &1 / &2 /\ abs(x$2) <= &1 / &2 /\ x$3 = &0)`,
  SUBGOAL_THEN `!x:real^3. x IN moi_s35_cube <=>
                           abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ abs(x$3) <= &1`
  (LABEL_TAC "cube") THENL
   [REWRITE_TAC[moi_s35_cube; IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
                VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s35_mid <=>
                           abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ x$3 = &0`
  (LABEL_TAC "mid") THENL
   [REWRITE_TAC[moi_s35_mid; IN_ELIM_THM] THEN USE_THEN "cube" (fun th -> REWRITE_TAC[th]) THEN
    GEN_TAC THEN ASM_CASES_TAC `(x:real^3)$3 = &0` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s30_inner <=>
                           abs(x$1) <= &1 / &2 /\ abs(x$2) <= &1 / &2 /\ x$3 = &0`
  (LABEL_TAC "inner") THENL
   [REWRITE_TAC[moi_s30_inner; IN_ELIM_THM] THEN USE_THEN "mid" (fun th -> REWRITE_TAC[th]) THEN
    GEN_TAC THEN ASM_CASES_TAC `(x:real^3)$3 = &0` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope (moi_s35_cube:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_cube; POLYTOPE_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `polytope (moi_s35_mid:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `moi_s35_mid = moi_s35_cube INTER {x:real^3 | basis 3 dot x = &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_s35_mid; EXTENSION; IN_INTER; IN_ELIM_THM] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH];
      MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
      ASM_REWRITE_TAC[POLYHEDRON_HYPERPLANE]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT; LOCALLY_POLYHEDRAL_POLYTOPE] THEN
  REWRITE_TAC[SUBSET] THEN
  USE_THEN "cube" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "mid" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "inner" (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3C2_BOX_COORDS = prove
 (`(!x:real^3. x IN moi_s35_cube <=>
               abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ abs(x$3) <= &1) /\
   (!x:real^3. x IN moi_s35_mid <=> abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ x$3 = &0) /\
   (!x:real^3. x IN moi_s30_inner <=>
               abs(x$1) <= &1 / &2 /\ abs(x$2) <= &1 / &2 /\ x$3 = &0)`,
  REWRITE_TAC[MOI_S3C2_MID_FACTS]);;

let MOI_S3C2_HQ = prove
 (`!h m. &0 < h /\ h <= &1 / &2 /\ &0 <= m
         ==> &0 <= h * max (&0) (&7 / &8 - m) /\
             h * max (&0) (&7 / &8 - m) <= h /\
             h * max (&0) (&7 / &8 - m) <= &1 / &2 /\
             (m < &7 / &8 ==> &0 < h * max (&0) (&7 / &8 - m))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= max (&0) (&7 / &8 - m) /\ max (&0) (&7 / &8 - m) <= &1 /\
                (m < &7 / &8 ==> &0 < max (&0) (&7 / &8 - m))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 <= m` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h * max (&0) (&7 / &8 - m) <= h` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < h` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < h` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `h * max (&0) (&7 / &8 - m) <= h` THEN
    UNDISCH_TAC `h <= &1 / &2` THEN REAL_ARITH_TAC;
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[]]);;

let MOI_S3C2_BUMP = prove
 (`!h. &0 < h /\ h <= &1 / &2
       ==> pl_map_on moi_s35_mid (moi_s3c2_bump h) /\
           (!x. x IN moi_s35_mid ==> moi_s3c2_bump h x IN moi_s35_cube) /\
           (!x. x IN moi_s35_mid /\ ~(x IN moi_s3c2_o7) ==> moi_s3c2_bump h x = x) /\
           (!x. x IN moi_s3c2_o7
                ==> &0 < (moi_s3c2_bump h x)$3 /\ (moi_s3c2_bump h x)$3 <= h) /\
           (!x y. x IN moi_s35_mid /\ y IN moi_s35_mid /\
                  moi_s3c2_bump h x = moi_s3c2_bump h y ==> x = y) /\
           moi_s30_inner SUBSET moi_s3c2_o7 /\ moi_s3c2_o7 SUBSET moi_s35_mid`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. (moi_s3c2_bump h x)$1 = x$1 /\ (moi_s3c2_bump h x)$2 = x$2 /\
                           (moi_s3c2_bump h x)$3 =
                           x$3 + h * max (&0) (&7 / &8 - max (abs(x$1)) (abs(x$2)))`
  ASSUME_TAC THENL
   [SIMP_TAC[moi_s3c2_bump; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_ASSUME_TAC MOI_S3C2_MID_FACTS THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s3c2_bump] THEN
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^3. (\x. x) x +
       ((\t:real^1. drop t % (h % basis 3:real^3)) o
        (\x:real^3. lift(max (&0) (&7 / &8 - max (abs(x$1)) (abs(x$2)))))) x` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[moi_s3c2_bump; o_THM; LIFT_DROP; VECTOR_MUL_ASSOC] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_SYM];
      ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_ADD THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID]; ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[MOI_S3C2_PL_PHI; SUBSET_UNIV] THEN
    MATCH_MP_TAC MOI_PTR_PL_MAP_ON_LINEAR THEN
    SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
    X_GEN_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_ADD_LID] THEN
    MP_TAC(SPECL [`h:real`; `max (abs((x:real^3)$1)) (abs(x$2))`] MOI_S3C2_HQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[moi_s3c2_o7; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `max (&0) (&7 / &8 - max (abs((x:real^3)$1)) (abs(x$2))) = &0`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `~(max (abs((x:real^3)$1)) (abs(x$2)) < &7 / &8)` MP_TAC THENL
       [ASM_MESON_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[moi_s3c2_o7; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID] THEN
    MP_TAC(SPECL [`h:real`; `max (abs((x:real^3)$1)) (abs(x$2))`] MOI_S3C2_HQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `moi_s3c2_bump h (x:real^3) = moi_s3c2_bump h y`)) THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; moi_s3c2_o7; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; moi_s3c2_o7; IN_ELIM_THM] THEN MESON_TAC[]]);;

let moi_s3c2_dentmap = new_definition
 `moi_s3c2_dentmap (psi:real^3->real^3) (phi:real^3->real^3) h (x:real^3) =
    if x IN IMAGE psi moi_s35_mid then psi (moi_s3c2_bump h (phi x)) else x`;;

let moi_s3c2_dented = new_definition
 `moi_s3c2_dented (g:real^3->bool) (psi:real^3->real^3) h =
    (g DIFF IMAGE psi moi_s3c2_o7) UNION IMAGE (psi o moi_s3c2_bump h) moi_s35_mid`;;

let MOI_S3C2_BOX_OPEN = prove
 (`!(psi:real^3->real^3) phi u.
     pl_homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi) /\
     open u /\ u SUBSET moi_s35_cube
     ==> open (IMAGE psi u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(u:real^3->bool) SUBSET moi_s35_cube` THEN
    UNDISCH_TAC `!x:real^3. x IN moi_s35_cube ==> (phi:real^3->real^3) (psi x) = x` THEN
    REWRITE_TAC[SUBSET] THEN MESON_TAC[]]);;

let MOI_S3C2_BOX_SETS = prove
 (`?u7:real^3->bool.
     open u7 /\ u7 SUBSET moi_s35_cube /\ moi_s35_mid INTER u7 = moi_s3c2_o7 /\
     open (interval(--vec 1:real^3,vec 1)) /\
     interval(--vec 1:real^3,vec 1) SUBSET moi_s35_cube /\
     {x:real^3 | x IN moi_s35_mid /\ max (abs(x$1)) (abs(x$2)) <= &7 / &8} SUBSET
     interval(--vec 1,vec 1) /\
     moi_s30_inner SUBSET interval(--vec 1:real^3,vec 1) /\
     compact {x:real^3 | x IN moi_s35_mid /\ max (abs(x$1)) (abs(x$2)) <= &7 / &8} /\
     moi_s3c2_o7 SUBSET
     {x:real^3 | x IN moi_s35_mid /\ max (abs(x$1)) (abs(x$2)) <= &7 / &8}`,
  STRIP_ASSUME_TAC MOI_S3C2_MID_FACTS THEN
  EXISTS_TAC `interval(vector[--(&7 / &8); --(&7 / &8); --(&1)]:real^3,
                       vector[&7 / &8; &7 / &8; &1])` THEN
  REWRITE_TAC[OPEN_INTERVAL] THEN
  SUBGOAL_THEN `!x:real^3. x IN interval(--vec 1,vec 1) <=>
                           abs(x$1) < &1 /\ abs(x$2) < &1 /\ abs(x$3) < &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
                VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN interval(vector[--(&7 / &8); --(&7 / &8); --(&1)],
                                         vector[&7 / &8; &7 / &8; &1]) <=>
                           abs(x$1) < &7 / &8 /\ abs(x$2) < &7 / &8 /\ abs(x$3) < &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:real^3 | x IN moi_s35_mid /\ max (abs(x$1)) (abs(x$2)) <= &7 / &8} =
    interval[vector[--(&7 / &8); --(&7 / &8); &0], vector[&7 / &8; &7 / &8; &0]]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL; OPEN_INTERVAL] THEN
  REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; moi_s3c2_o7; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3C2_DENT_HOMEO = prove
 (`!gs (psi:real^3->real^3) phi h.
     compact gs /\
     pl_homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi) /\
     IMAGE psi moi_s35_cube INTER gs = IMAGE psi moi_s35_mid /\
     &0 < h /\ h <= &1 / &2
     ==> (?psi'. homeomorphism (gs,moi_s3c2_dented gs psi h)
                               (moi_s3c2_dentmap psi phi h,psi')) /\
         (!x. x IN gs /\ ~(x IN IMAGE psi moi_s3c2_o7)
              ==> moi_s3c2_dentmap psi phi h x = x) /\
         closed (gs DIFF IMAGE psi moi_s3c2_o7) /\
         IMAGE psi moi_s3c2_o7 SUBSET IMAGE psi moi_s35_mid /\
         IMAGE psi moi_s35_mid SUBSET gs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `h:real` MOI_S3C2_BUMP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s35_mid SUBSET moi_s35_cube /\ compact moi_s35_mid /\
                compact moi_s35_cube`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[MOI_S3C2_MID_FACTS]; ALL_TAC] THEN
  STRIP_ASSUME_TAC MOI_S3C2_BOX_SETS THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o check (fun th ->
    concl th = `pl_homeomorphism (moi_s35_cube,IMAGE (psi:real^3->real^3) moi_s35_cube)
                                 (psi,(phi:real^3->real^3))`)) THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s35_cube ==> (phi:real^3->real^3) (psi x) = x`
  (LABEL_TAC "inv1") THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `mm = IMAGE (psi:real^3->real^3) moi_s35_mid` THEN
  SUBGOAL_THEN `mm SUBSET (gs:real^3->bool) /\ IMAGE (psi:real^3->real^3) moi_s3c2_o7 SUBSET mm`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube INTER gs = mm` THEN SET_TAC[];
      EXPAND_TAC "mm" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (psi:real^3->real^3) u7)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3C2_BOX_OPEN THEN EXISTS_TAC `phi:real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gs:real^3->bool) INTER IMAGE psi u7 = IMAGE (psi:real^3->real^3) moi_s3c2_o7`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube INTER gs = mm` THEN
    EXPAND_TAC "mm" THEN
    UNDISCH_TAC `moi_s35_mid INTER u7 = moi_s3c2_o7` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(u7:real^3->bool) SUBSET moi_s35_cube` THEN
    UNDISCH_TAC `moi_s35_mid SUBSET moi_s35_cube` THEN
    UNDISCH_TAC `!x:real^3. x IN moi_s35_cube ==> (phi:real^3->real^3) (psi x) = x` THEN
    REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed ((gs:real^3->bool) DIFF IMAGE psi moi_s3c2_o7)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(gs:real^3->bool) DIFF IMAGE psi moi_s3c2_o7 = gs DIFF IMAGE psi u7`
    SUBST1_TAC THENL
     [UNDISCH_TAC `(gs:real^3->bool) INTER IMAGE psi u7 = IMAGE (psi:real^3->real^3) moi_s3c2_o7` THEN
      SET_TAC[];
      MATCH_MP_TAC CLOSED_DIFF THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN gs /\ ~(x IN IMAGE (psi:real^3->real^3) moi_s3c2_o7)
                    ==> moi_s3c2_dentmap psi phi h x = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN REWRITE_TAC[moi_s3c2_dentmap] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN mm` THEN EXPAND_TAC "mm" THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~((z:real^3) IN moi_s3c2_o7)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((x:real^3) IN IMAGE psi moi_s3c2_o7)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(phi:real^3->real^3) x = z` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "inv1" MATCH_MP_TAC THEN
      UNDISCH_TAC `moi_s35_mid SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `(z:real^3) IN moi_s35_mid` THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_s3c2_dentmap (psi:real^3->real^3) phi h =
                (\x. if x IN mm then psi (moi_s3c2_bump h (phi x)) else x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_s3c2_dentmap] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`gs:real^3->bool`; `moi_s3c2_dentmap (psi:real^3->real^3) phi h`;
                 `moi_s3c2_dented gs (psi:real^3->real^3) h`] HOMEOMORPHISM_COMPACT) THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> ((p ==> q) ==> r)`) THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `gs = mm UNION ((gs:real^3->bool) DIFF IMAGE psi moi_s3c2_o7)`
    (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
     [UNDISCH_TAC `mm SUBSET (gs:real^3->bool)` THEN
      UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s3c2_o7 SUBSET mm` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\x:real^3. x IN mm`;
                   `\x:real^3. (psi:real^3->real^3) (moi_s3c2_bump h ((phi:real^3->real^3) x))`;
                   `\x:real^3. x`; `mm:real^3->bool`;
                   `(gs:real^3->bool) DIFF IMAGE psi moi_s3c2_o7`] CONTINUOUS_ON_CASES) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "mm" THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(\x. (psi:real^3->real^3) (moi_s3c2_bump h ((phi:real^3->real^3) x))) =
                    (psi o moi_s3c2_bump h) o phi`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube` THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "mm" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SUBGOAL_THEN `IMAGE (phi:real^3->real^3) mm = moi_s35_mid` SUBST1_TAC THENL
       [EXPAND_TAC "mm" THEN REWRITE_TAC[GSYM IMAGE_o] THEN
        MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^3. x) moi_s35_mid` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (f:real^3->real^3) x = gs x)
                                 ==> IMAGE f s = IMAGE gs s`) THEN
          REWRITE_TAC[o_THM] THEN
          UNDISCH_TAC `moi_s35_mid SUBSET moi_s35_cube` THEN ASM SET_TAC[];
          REWRITE_TAC[IMAGE_ID]];
        ALL_TAC] THEN
      ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_DIFF] THEN
      ASM_CASES_TAC `(x:real^3) IN mm` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `!x. x IN gs /\ ~(x IN IMAGE (psi:real^3->real^3) moi_s3c2_o7)
                       ==> moi_s3c2_dentmap psi phi h x = x` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[moi_s3c2_dented] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^3) IN mm` THEN ASM_REWRITE_TAC[] THENL
       [UNDISCH_TAC `(x:real^3) IN mm` THEN EXPAND_TAC "mm" THEN REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(phi:real^3->real^3) x = z` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[] THEN USE_THEN "inv1" MATCH_MP_TAC THEN
          UNDISCH_TAC `moi_s35_mid SUBSET moi_s35_cube` THEN
          UNDISCH_TAC `(z:real^3) IN moi_s35_mid` THEN SET_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN REWRITE_TAC[IN_IMAGE; o_THM] THEN
        EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_UNION; IN_DIFF] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s3c2_o7 SUBSET mm` THEN
        UNDISCH_TAC `~((x:real^3) IN mm)` THEN SET_TAC[]];
      REWRITE_TAC[SUBSET; IN_UNION; IN_DIFF] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THENL
       [EXISTS_TAC `y:real^3` THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
        UNDISCH_TAC `!x. x IN gs /\ ~(x IN IMAGE (psi:real^3->real^3) moi_s3c2_o7)
                         ==> moi_s3c2_dentmap psi phi h x = x` THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
        MESON_TAC[];
        UNDISCH_TAC `(y:real^3) IN IMAGE ((psi:real^3->real^3) o moi_s3c2_bump h) moi_s35_mid` THEN
        REWRITE_TAC[IN_IMAGE; o_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `(psi:real^3->real^3) z` THEN
        SUBGOAL_THEN `(psi:real^3->real^3) z IN mm` ASSUME_TAC THENL
         [EXPAND_TAC "mm" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `(phi:real^3->real^3) (psi z) = z` (fun th -> REWRITE_TAC[th]) THEN
          USE_THEN "inv1" MATCH_MP_TAC THEN
          UNDISCH_TAC `moi_s35_mid SUBSET moi_s35_cube` THEN
          UNDISCH_TAC `(z:real^3) IN moi_s35_mid` THEN SET_TAC[];
          UNDISCH_TAC `mm SUBSET (gs:real^3->bool)` THEN
          UNDISCH_TAC `(psi:real^3->real^3) z IN mm` THEN SET_TAC[]]]];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    SUBGOAL_THEN `!z:real^3. z IN mm
                    ==> (phi:real^3->real^3) z IN moi_s35_mid /\ psi (phi z) = z /\
                        moi_s3c2_bump h (phi z) IN moi_s35_cube`
    ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "mm" THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(phi:real^3->real^3) z = w` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "inv1" MATCH_MP_TAC THEN
        UNDISCH_TAC `moi_s35_mid SUBSET moi_s35_cube` THEN
        UNDISCH_TAC `(w:real^3) IN moi_s35_mid` THEN SET_TAC[];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM(ACCEPT_TAC o SYM o check (fun t ->
          concl t = `z:real^3 = (psi:real^3->real^3) w`));
        MATCH_MP_TAC(ASSUME `!x:real^3. x IN moi_s35_mid
                               ==> moi_s3c2_bump h x IN moi_s35_cube`) THEN
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `!z:real^3. z IN moi_s35_cube ==> (psi:real^3->real^3) z IN mm \/
                             ~(psi z IN gs)`
    ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube INTER gs = mm` THEN
      UNDISCH_TAC `(z:real^3) IN moi_s35_cube` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:real^3) IN mm` THEN ASM_CASES_TAC `(y:real^3) IN mm` THEN
    ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `moi_s3c2_bump h ((phi:real^3->real^3) x) IN moi_s35_cube /\
                    moi_s3c2_bump h ((phi:real^3->real^3) y) IN moi_s35_cube`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `moi_s3c2_bump h ((phi:real^3->real^3) x) = moi_s3c2_bump h (phi y)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `(phi:real^3->real^3) (psi (moi_s3c2_bump h (phi x)))` THEN
        CONJ_TAC THENL
         [CONV_TAC SYM_CONV THEN USE_THEN "inv1" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          ASM_REWRITE_TAC[] THEN USE_THEN "inv1" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `(phi:real^3->real^3) x = phi y` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!x y:real^3. x IN moi_s35_mid /\ y IN moi_s35_mid /\
                               moi_s3c2_bump h x = moi_s3c2_bump h y ==> x = y`) (concl th))) THEN
        ASM_SIMP_TAC[];
        ASM_MESON_TAC[]];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `moi_s3c2_bump h ((phi:real^3->real^3) x)` o check (fun th ->
        can (term_match [] `!z:real^3. z IN moi_s35_cube ==> P z \/ Q z`) (concl th))) THEN
      ASM_SIMP_TAC[];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `moi_s3c2_bump h ((phi:real^3->real^3) y)` o check (fun th ->
        can (term_match [] `!z:real^3. z IN moi_s35_cube ==> P z \/ Q z`) (concl th))) THEN
      ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]]);;

let MOI_S3C2_DENT = prove
 (`!gs jg (psi:real^3->real^3) phi h.
     pl_cell_with_boundary 2 gs jg /\
     pl_homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi) /\
     IMAGE psi moi_s35_cube INTER gs = IMAGE psi moi_s35_mid /\
     DISJOINT jg (IMAGE psi moi_s35_cube) /\
     &0 < h /\ h <= &1 / &2
     ==> pl_cell_with_boundary 2 (moi_s3c2_dented gs psi h) jg`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `gs:real^3->bool`; `jg:real^3->bool`] MOI_S5C_CELL_COMPACT2) THEN
  MP_TAC(ISPECL [`2`; `gs:real^3->bool`; `jg:real^3->bool`] MOI_S5C_CELL_POLYHEDRON) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`gs:real^3->bool`; `psi:real^3->real^3`; `phi:real^3->real^3`; `h:real`]
    MOI_S3C2_DENT_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi':real^3->real^3`) STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `h:real` MOI_S3C2_BUMP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC MOI_S3C2_BOX_SETS THEN
  SUBGOAL_THEN `moi_s35_mid SUBSET moi_s35_cube /\ polytope moi_s35_mid /\
                locally_polyhedral moi_s35_mid`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[MOI_S3C2_MID_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube)
                  ((psi:real^3->real^3),(phi:real^3->real^3)) /\
                pl_map_on moi_s35_cube psi /\ pl_map_on (IMAGE psi moi_s35_cube) phi`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube)
                   ((psi:real^3->real^3),(phi:real^3->real^3))` THEN
    REWRITE_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  ABBREV_TAC `mm = IMAGE (psi:real^3->real^3) moi_s35_mid` THEN
  ABBREV_TAC `k7 = {x:real^3 | x IN moi_s35_mid /\ max (abs(x$1)) (abs(x$2)) <= &7 / &8}` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o check (fun th ->
    concl th = `homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube)
                  ((psi:real^3->real^3),(phi:real^3->real^3))`)) THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s35_cube ==> (phi:real^3->real^3) (psi x) = x`
  (LABEL_TAC "inv1") THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `locally_polyhedral (mm:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN EXPAND_TAC "mm" THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
     [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{moi_s35_mid:real^3->bool}` THEN
      REWRITE_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on mm (((psi:real^3->real^3) o moi_s3c2_bump h) o (phi:real^3->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `moi_s35_mid:real^3->bool` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "mm" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `moi_s35_cube:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      EXPAND_TAC "mm" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(phi:real^3->real^3) (psi z) = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
      USE_THEN "inv1" MATCH_MP_TAC THEN
      UNDISCH_TAC `moi_s35_mid SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `(z:real^3) IN moi_s35_mid` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->real^3) (interval(--vec 1,vec 1)) SUBSET
                IMAGE psi moi_s35_cube /\
                open (IMAGE (psi:real^3->real^3) (interval(--vec 1,vec 1))) /\
                IMAGE (psi:real^3->real^3) k7 SUBSET IMAGE psi (interval(--vec 1,vec 1)) /\
                IMAGE (psi:real^3->real^3) moi_s3c2_o7 SUBSET IMAGE psi k7 /\
                closed (IMAGE (psi:real^3->real^3) k7)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3C2_BOX_OPEN THEN EXISTS_TAC `phi:real^3->real^3` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(k7:real^3->bool) SUBSET interval(--vec 1,vec 1)` THEN
      UNDISCH_TAC `interval(--vec 1:real^3,vec 1) SUBSET moi_s35_cube` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (gs:real^3->bool) (moi_s3c2_dentmap psi phi h)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_MAP_ON_LOCAL] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^3) IN IMAGE (psi:real^3->real^3) k7` THENL
     [EXISTS_TAC `IMAGE (psi:real^3->real^3) (interval(--vec 1,vec 1))` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN IMAGE (psi:real^3->real^3) k7` THEN
        UNDISCH_TAC `IMAGE (psi:real^3->real^3) k7 SUBSET IMAGE psi (interval(--vec 1,vec 1))` THEN
        SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `((psi:real^3->real^3) o moi_s3c2_bump h) o (phi:real^3->real^3)` THEN
      SUBGOAL_THEN `(gs:real^3->bool) INTER IMAGE (psi:real^3->real^3) (interval(--vec 1,vec 1)) SUBSET mm`
      ASSUME_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!a b c m:real^3->bool.
           b INTER a = m /\ c SUBSET b ==> a INTER c SUBSET m`) THEN
        EXISTS_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(y:real^3) IN mm` ASSUME_TAC THENL
         [UNDISCH_TAC `(y:real^3) IN gs INTER IMAGE (psi:real^3->real^3) (interval(--vec 1,vec 1))` THEN
          UNDISCH_TAC `(gs:real^3->bool) INTER IMAGE (psi:real^3->real^3) (interval(--vec 1,vec 1)) SUBSET mm` THEN
          SET_TAC[];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[moi_s3c2_dentmap; o_THM];
        MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `mm:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
        ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]];
      EXISTS_TAC `(:real^3) DIFF IMAGE (psi:real^3->real^3) k7` THEN
      ASM_REWRITE_TAC[GSYM closed; IN_DIFF; IN_UNIV] THEN
      MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\x:real^3. x` THEN CONJ_TAC THENL
       [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV] THEN STRIP_TAC THEN
        BETA_TAC THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!x:real^3. x IN gs /\ ~(x IN IMAGE psi moi_s3c2_o7)
                                         ==> moi_s3c2_dentmap psi phi h x = x`) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s3c2_o7 SUBSET IMAGE psi k7` THEN
        UNDISCH_TAC `~((y:real^3) IN IMAGE (psi:real^3->real^3) k7)` THEN SET_TAC[];
        REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
        MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
        ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; GSYM closed]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (moi_s3c2_dentmap psi phi h) jg = (jg:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `!y:real^3. y IN jg ==> moi_s3c2_dentmap psi phi h y = y` ASSUME_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x:real^3. x IN gs /\ ~(x IN IMAGE psi moi_s3c2_o7)
                                       ==> moi_s3c2_dentmap psi phi h x = x`) (concl th))) THEN
      UNDISCH_TAC `(jg:real^3->bool) SUBSET gs` THEN
      UNDISCH_TAC `DISJOINT (jg:real^3->bool) (IMAGE psi moi_s35_cube)` THEN
      UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s3c2_o7 SUBSET IMAGE psi k7` THEN
      UNDISCH_TAC `IMAGE (psi:real^3->real^3) k7 SUBSET IMAGE psi (interval(--vec 1,vec 1))` THEN
      UNDISCH_TAC `IMAGE (psi:real^3->real^3) (interval(--vec 1,vec 1)) SUBSET
                   IMAGE psi moi_s35_cube` THEN
      UNDISCH_TAC `(y:real^3) IN jg` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^3. x) jg` THEN
    REWRITE_TAC[IMAGE_ID] THEN
    UNDISCH_TAC `!y:real^3. y IN jg ==> moi_s3c2_dentmap psi phi h y = y` THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (moi_s3c2_dentmap psi phi h) jg = (jg:real^3->bool)` THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  MATCH_MP_TAC MOI_S5C_CELL_PLH THEN
  MAP_EVERY EXISTS_TAC [`gs:real^3->bool`; `psi':real^3->real^3`] THEN
  ASM_REWRITE_TAC[pl_homeomorphism] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
    MAP_EVERY EXISTS_TAC [`gs:real^3->bool`; `moi_s3c2_dentmap psi phi h`] THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `pl_cell_with_boundary 2 gs (jg:real^3->bool)` THEN
    REWRITE_TAC[pl_cell_with_boundary] THEN MESON_TAC[]]);;

(* One-sidedness: E approaches the patch D from one open half-box only.     *)

let MOI_S3C2_CONN_OPEN2 = prove
 (`!s e1 e2:real^3->bool.
     connected s /\ open e1 /\ open e2 /\ s SUBSET e1 UNION e2 /\ e1 INTER e2 = {}
     ==> s SUBSET e1 \/ s SUBSET e2`,
  REWRITE_TAC[connected; NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`e1:real^3->bool`; `e2:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3C2_PUSH_SIDE = prove
 (`!(psi:real^3->real^3) phi ee dd jd.
     pl_homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi) /\
     IMAGE psi moi_s30_inner = dd /\
     ee INTER IMAGE psi moi_s35_mid SUBSET dd /\
     connected jd /\ closed jd /\ jd SUBSET dd /\
     (!x. x IN dd DIFF jd ==> ?u. open u /\ x IN u /\ ee INTER u SUBSET dd) /\
     (!x w. x IN jd /\ open w /\ x IN w
            ==> ?u. open u /\ x IN u /\ u SUBSET w /\
                    connected ((ee INTER u) DIFF dd) /\
                    jd INTER u SUBSET closure ((ee INTER u) DIFF dd))
     ==> dd INTER closure (ee INTER IMAGE psi {x | x IN moi_s35_cube /\ &0 < x$3}) = {} \/
         dd INTER closure (ee INTER IMAGE psi {x | x IN moi_s35_cube /\ x$3 < &0}) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC MOI_S3C2_BOX_SETS THEN
  SUBGOAL_THEN `moi_s35_mid SUBSET moi_s35_cube /\ moi_s30_inner SUBSET moi_s35_mid`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[MOI_S3C2_MID_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s35_cube /\ x$3 = &0 ==> x IN moi_s35_mid`
  ASSUME_TAC THENL [REWRITE_TAC[moi_s35_mid; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o check (fun th ->
    concl th = `pl_homeomorphism (moi_s35_cube,IMAGE (psi:real^3->real^3) moi_s35_cube)
                                 (psi,(phi:real^3->real^3))`)) THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s35_cube ==> (phi:real^3->real^3) (psi x) = x`
  (LABEL_TAC "inv1") THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `bp = IMAGE (psi:real^3->real^3) {x | x IN moi_s35_cube /\ &0 < x$3}` THEN
  ABBREV_TAC `bm = IMAGE (psi:real^3->real^3) {x | x IN moi_s35_cube /\ x$3 < &0}` THEN
  ABBREV_TAC `op = IMAGE (psi:real^3->real^3)
                     (interval(--vec 1,vec 1) INTER {x | &0 < x$3})` THEN
  ABBREV_TAC `om = IMAGE (psi:real^3->real^3)
                     (interval(--vec 1,vec 1) INTER {x | x$3 < &0})` THEN
  ABBREV_TAC `oo = IMAGE (psi:real^3->real^3) (interval(--vec 1,vec 1))` THEN
  SUBGOAL_THEN `open (op:real^3->bool) /\ open (om:real^3->bool) /\ open (oo:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["op"; "om"; "oo"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC MOI_S3C2_BOX_OPEN THEN EXISTS_TAC `phi:real^3->real^3` THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[OPEN_INTER; OPEN_INTERVAL; OPEN_HALFSPACE_COMPONENT_LT;
             OPEN_HALFSPACE_COMPONENT_GT; GSYM real_gt] THEN
    UNDISCH_TAC `interval(--vec 1:real^3,vec 1) SUBSET moi_s35_cube` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:real^3->bool.
                  a SUBSET moi_s35_cube /\ b SUBSET moi_s35_cube /\ a INTER b = {}
                  ==> IMAGE (psi:real^3->real^3) a INTER IMAGE psi b = {}`
  (LABEL_TAC "disj") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "inv1" MP_TAC THEN
    UNDISCH_TAC `(a:real^3->bool) SUBSET moi_s35_cube` THEN
    UNDISCH_TAC `(b:real^3->bool) SUBSET moi_s35_cube` THEN
    UNDISCH_TAC `(a:real^3->bool) INTER b = {}` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY; SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s30_inner SUBSET moi_s35_cube /\
                moi_s30_inner INTER {x:real^3 | x IN moi_s35_cube /\ &0 < x$3} = {} /\
                moi_s30_inner INTER {x:real^3 | x IN moi_s35_cube /\ x$3 < &0} = {} /\
                {x:real^3 | x IN moi_s35_cube /\ &0 < x$3} INTER
                {x | x IN moi_s35_cube /\ x$3 < &0} = {}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY; moi_s30_inner; moi_s35_mid] THEN
    REWRITE_TAC[SUBSET; moi_s30_inner; moi_s35_mid; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN TRY(MESON_TAC[]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(op:real^3->bool) SUBSET bp /\ (om:real^3->bool) SUBSET bm /\
                bp INTER bm = {} /\ (dd:real^3->bool) INTER bp = {} /\ dd INTER bm = {} /\
                (dd:real^3->bool) SUBSET oo`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["op"; "om"; "oo"; "bp"; "bm"; "dd"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `interval(--vec 1:real^3,vec 1) SUBSET moi_s35_cube` THEN SET_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `interval(--vec 1:real^3,vec 1) SUBSET moi_s35_cube` THEN SET_TAC[];
      USE_THEN "disj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      USE_THEN "disj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      USE_THEN "disj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(oo:real^3->bool) DIFF IMAGE psi moi_s35_mid SUBSET op UNION om`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["op"; "om"; "oo"] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    DISJ_CASES_TAC(REAL_ARITH `&0 < (z:real^3)$3 \/ z$3 < &0 \/ z$3 = &0`) THENL
     [DISCH_TAC THEN DISJ1_TAC THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(DISJ_CASES_TAC) THENL
       [DISCH_TAC THEN DISJ2_TAC THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
        DISCH_THEN(MP_TAC o SPEC `z:real^3` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
        REWRITE_TAC[] THEN
        SUBGOAL_THEN `(z:real^3) IN moi_s35_mid` (fun th -> REWRITE_TAC[th]) THEN
        UNDISCH_TAC `!x:real^3. x IN moi_s35_cube /\ x$3 = &0 ==> x IN moi_s35_mid` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `interval(--vec 1:real^3,vec 1) SUBSET moi_s35_cube` THEN
        UNDISCH_TAC `(z:real^3) IN interval(--vec 1,vec 1)` THEN SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(op:real^3->bool) INTER om = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `(op:real^3->bool) SUBSET bp` THEN UNDISCH_TAC `(om:real^3->bool) SUBSET bm` THEN
    UNDISCH_TAC `(bp:real^3->bool) INTER bm = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN jd
               ==> ?u. open u /\ x IN u /\
                       ((ee INTER u) DIFF dd SUBSET op \/ (ee INTER u) DIFF dd SUBSET om) /\
                       jd INTER u SUBSET closure ((ee INTER u) DIFF dd)`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `oo:real^3->bool`] o check (fun th ->
      can (term_match [] `!x w:real^3->bool. x IN jd /\ open w /\ x IN w ==> P x w`)
      (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(dd:real^3->bool) SUBSET oo` THEN UNDISCH_TAC `(jd:real^3->bool) SUBSET dd` THEN
      UNDISCH_TAC `(x:real^3) IN jd` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^3->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3C2_CONN_OPEN2 THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(oo:real^3->bool) DIFF IMAGE psi moi_s35_mid SUBSET op UNION om` THEN
    UNDISCH_TAC `(u:real^3->bool) SUBSET oo` THEN
    UNDISCH_TAC `(ee:real^3->bool) INTER IMAGE psi moi_s35_mid SUBSET dd` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `jd INTER closure (ee INTER bp) = {} \/
                jd INTER closure ((ee:real^3->bool) INTER bm) = {}`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `jd:real^3->bool` CONNECTED_CLOSED) THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`closure ((ee:real^3->bool) INTER bp)`;
                               `closure ((ee:real^3->bool) INTER bm)`]) THEN
    REWRITE_TAC[CLOSED_CLOSURE] THEN
    MATCH_MP_TAC(TAUT `a /\ b /\ (c <=> c') /\ (d <=> d')
                       ==> ~(a /\ b /\ ~c /\ ~d) ==> c' \/ d'`) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      USE_THEN "loc" (MP_TAC o C MP (ASSUME `(x:real^3) IN jd`) o SPEC `x:real^3`) THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THENL
       [DISJ1_TAC; DISJ2_TAC] THEN
      MATCH_MP_TAC(SET_RULE `!x:real^3 s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `closure ((ee INTER u) DIFF (dd:real^3->bool))` THEN
      (CONJ_TAC THENL
        [UNDISCH_TAC `jd INTER u SUBSET closure ((ee INTER u) DIFF (dd:real^3->bool))` THEN
         UNDISCH_TAC `(x:real^3) IN u` THEN UNDISCH_TAC `(x:real^3) IN jd` THEN SET_TAC[];
         MATCH_MP_TAC SUBSET_CLOSURE]) THENL
       [UNDISCH_TAC `(ee INTER u) DIFF (dd:real^3->bool) SUBSET op` THEN
        UNDISCH_TAC `(op:real^3->bool) SUBSET bp` THEN SET_TAC[];
        UNDISCH_TAC `(ee INTER u) DIFF (dd:real^3->bool) SUBSET om` THEN
        UNDISCH_TAC `(om:real^3->bool) SUBSET bm` THEN SET_TAC[]];
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      USE_THEN "loc" (MP_TAC o C MP (ASSUME `(x:real^3) IN jd`) o SPEC `x:real^3`) THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
      MP_TAC(ISPECL [`u:real^3->bool`; `(ee:real^3->bool) INTER bp`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      MP_TAC(ISPECL [`u:real^3->bool`; `(ee:real^3->bool) INTER bm`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(u INTER closure ((ee:real^3->bool) INTER bp) = {}) /\
                    ~(u INTER closure ((ee:real^3->bool) INTER bm) = {})`
      (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `(x:real^3) IN closure (ee INTER bp)` THEN
        UNDISCH_TAC `(x:real^3) IN closure (ee INTER bm)` THEN
        UNDISCH_TAC `(x:real^3) IN u` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(bp:real^3->bool) INTER bm = {}` THEN
      UNDISCH_TAC `(dd:real^3->bool) INTER bp = {}` THEN
      UNDISCH_TAC `(dd:real^3->bool) INTER bm = {}` THEN
      UNDISCH_TAC `(op:real^3->bool) SUBSET bp` THEN UNDISCH_TAC `(om:real^3->bool) SUBSET bm` THEN
      UNDISCH_TAC `(ee INTER u) DIFF (dd:real^3->bool) SUBSET op \/
                   (ee INTER u) DIFF dd SUBSET om` THEN
      SET_TAC[];
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!b:real^3->bool. (dd:real^3->bool) INTER b = {} /\ jd INTER closure (ee INTER b) = {}
                  ==> dd INTER closure (ee INTER b) = {}`
  MP_TAC THENL
   [X_GEN_TAC `b:real^3->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^3` THEN
    STRIP_TAC THEN ASM_CASES_TAC `(x:real^3) IN jd` THENL
     [UNDISCH_TAC `jd INTER closure ((ee:real^3->bool) INTER b) = {}` THEN
      UNDISCH_TAC `(x:real^3) IN jd` THEN
      UNDISCH_TAC `(x:real^3) IN closure (ee INTER b)` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th -> concl th =
      `!x:real^3. x IN dd DIFF jd ==> ?u. open u /\ x IN u /\ ee INTER u SUBSET dd`)) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`u:real^3->bool`; `(ee:real^3->bool) INTER b`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `a /\ ~b ==> ~(b <=> a)`) THEN CONJ_TAC THENL
     [UNDISCH_TAC `(ee:real^3->bool) INTER u SUBSET dd` THEN
      UNDISCH_TAC `(dd:real^3->bool) INTER b = {}` THEN SET_TAC[];
      UNDISCH_TAC `(x:real^3) IN closure (ee INTER b)` THEN
      UNDISCH_TAC `(x:real^3) IN u` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `bp:real^3->bool` th) THEN
                       MP_TAC(SPEC `bm:real^3->bool` th)) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `jd INTER closure (ee INTER bp) = {} \/
               jd INTER closure ((ee:real^3->bool) INTER bm) = {}` THEN
  MESON_TAC[]);;

let MOI_S3C2_BOX_FLIP = prove
 (`!(psi:real^3->real^3) phi.
     pl_homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi)
     ==> pl_homeomorphism (moi_s35_cube,IMAGE (psi o reflect_along (basis 3)) moi_s35_cube)
                          (psi o reflect_along (basis 3),reflect_along (basis 3) o phi) /\
         IMAGE (psi o reflect_along (basis 3)) moi_s35_cube = IMAGE psi moi_s35_cube /\
         IMAGE (psi o reflect_along (basis 3)) moi_s35_mid = IMAGE psi moi_s35_mid /\
         IMAGE (psi o reflect_along (basis 3)) moi_s30_inner = IMAGE psi moi_s30_inner /\
         IMAGE (psi o reflect_along (basis 3)) {x | x IN moi_s35_cube /\ &0 < x$3} =
         IMAGE psi {x | x IN moi_s35_cube /\ x$3 < &0}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!y:real^3. (reflect_along (basis 3) y)$1 = y$1 /\
                           (reflect_along (basis 3) y)$2 = y$2 /\
                           (reflect_along (basis 3) y)$3 = --(y$3)`
  ASSUME_TAC THENL
   [SIMP_TAC[REFLECT_ALONG_BASIS_COMPONENT; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. IMAGE (reflect_along (basis 3)) s =
                                 {y | reflect_along (basis 3) y IN s}`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[REFLECT_ALONG_INVOLUTION];
    ALL_TAC] THEN
  MP_TAC MOI_S3C2_MID_FACTS THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (reflect_along (basis 3)) moi_s35_cube = moi_s35_cube /\
    IMAGE (reflect_along (basis 3)) moi_s35_mid = moi_s35_mid /\
    IMAGE (reflect_along (basis 3)) moi_s30_inner = moi_s30_inner /\
    IMAGE (reflect_along (basis 3)) {x:real^3 | x IN moi_s35_cube /\ &0 < x$3} =
    {x | x IN moi_s35_cube /\ x$3 < &0}`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN GEN_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_s35_cube:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism; REFLECT_ALONG_INVOLUTION] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_REFLECT_ALONG] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_PTR_PL_MAP_ON_LINEAR THEN
  ASM_SIMP_TAC[LINEAR_REFLECT_ALONG; LOCALLY_POLYHEDRAL_POLYTOPE]);;

let MOI_S3C2_PUSH_HEIGHT = prove
 (`!(psi:real^3->real^3) phi ee dd.
     pl_homeomorphism (moi_s35_cube,IMAGE psi moi_s35_cube) (psi,phi) /\ closed ee /\
     ee INTER IMAGE psi moi_s35_mid SUBSET dd /\
     dd INTER closure (ee INTER IMAGE psi {x | x IN moi_s35_cube /\ &0 < x$3}) = {}
     ==> ?h. &0 < h /\ h <= &1 / &2 /\
             !x. x IN moi_s35_cube /\ &0 < x$3 /\ x$3 <= h ==> ~(psi x IN ee)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact moi_s35_mid /\ compact moi_s35_cube /\
                moi_s35_mid SUBSET moi_s35_cube`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[MOI_S3C2_MID_FACTS]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o check (fun th ->
    concl th = `pl_homeomorphism (moi_s35_cube,IMAGE (psi:real^3->real^3) moi_s35_cube)
                                 (psi,(phi:real^3->real^3))`)) THEN
  ABBREV_TAC `kk = closure ((ee:real^3->bool) INTER
                            IMAGE psi {x | x IN moi_s35_cube /\ &0 < x$3})` THEN
  SUBGOAL_THEN `(kk:real^3->bool) SUBSET ee /\ closed kk` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s35_mid:real^3->bool`;
                 `{x:real^3 | x IN moi_s35_cube /\ (psi:real^3->real^3) x IN kk}`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      UNDISCH_TAC `(dd:real^3->bool) INTER kk = {}` THEN
      UNDISCH_TAC `(ee:real^3->bool) INTER IMAGE psi moi_s35_mid SUBSET dd` THEN
      UNDISCH_TAC `(kk:real^3->bool) SUBSET ee` THEN
      SUBGOAL_THEN `(psi:real^3->real^3) x IN IMAGE psi moi_s35_mid` MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(psi:real^3->real^3) x IN kk` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (del / &2) (&1 / &2)` THEN
  CONJ_TAC THENL [UNDISCH_TAC `&0 < del` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(psi:real^3->real^3) x IN kk` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x - (x:real^3)$3 % basis 3`; `x:real^3`] o check (fun th ->
    can (term_match [] `!x y:real^3. x IN moi_s35_mid /\ y IN s ==> d <= dist(x,y)`)
    (concl th))) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `(x - (x:real^3)$3 % basis 3) IN moi_s35_mid` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `(x:real^3) IN moi_s35_cube` THEN REWRITE_TAC[MOI_S3C2_BOX_COORDS] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[dist; VECTOR_ARITH `(x - a) - x:real^N = --a`; NORM_NEG; NORM_MUL] THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
  UNDISCH_TAC `&0 < (x:real^3)$3` THEN UNDISCH_TAC `(x:real^3)$3 <= min (del / &2) (&1 / &2)` THEN
  UNDISCH_TAC `&0 < del` THEN REAL_ARITH_TAC);;

let MOI_S3C2_CELL_RIM = prove
 (`!d j:real^3->bool.
     pl_cell_with_boundary 2 d j ==> connected j /\ compact j /\ j SUBSET d /\ compact d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `d:real^3->bool`; `j:real^3->bool`] MOI_S5C_CELL_COMPACT2) THEN
  MP_TAC(ISPECL [`2`; `d:real^3->bool`; `j:real^3->bool`] MOI_S5C_CELL_COMPACT) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `pl_cell_with_boundary 2 d (j:real^3->bool)` THEN
  REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
    MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN INT_ARITH_TAC]]);;

let MOI_S3C2_DISK_CHART = moi_std_csq MOI_S30_DISK_CHART;;

(* PATCH_PUSH: a PL disk gs containing the PL disk patch dd of the closed    *)
(* set ee in its interior, where gs meets ee only in dd and a closed set tt  *)
(* away from dd, and ee is a half plane near the rim of dd, is replaced by a *)
(* PL disk with the same rim, inside gs UNION vv, meeting ee off dd only.    *)

let MOI_S3C2_PATCH_PUSH = prove
 (mk_imp(MOI_S3C2_DISK_CHART,
  `!gs jg dd jd ee tt vv:real^3->bool.
     pl_cell_with_boundary 2 gs jg /\ pl_cell_with_boundary 2 dd jd /\
     dd SUBSET gs /\ DISJOINT dd jg /\
     closed ee /\ dd SUBSET ee /\
     closed tt /\ DISJOINT dd tt /\ gs INTER ee SUBSET dd UNION tt /\
     open vv /\ dd SUBSET vv /\
     (!x. x IN dd DIFF jd ==> ?u. open u /\ x IN u /\ ee INTER u SUBSET dd) /\
     (!x w. x IN jd /\ open w /\ x IN w
            ==> ?u. open u /\ x IN u /\ u SUBSET w /\
                    connected ((ee INTER u) DIFF dd) /\
                    jd INTER u SUBSET closure ((ee INTER u) DIFF dd))
     ==> ?gs'. pl_cell_with_boundary 2 gs' jg /\ gs' SUBSET gs UNION vv /\
               gs' INTER ee = (gs INTER ee) DIFF dd`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`gs:real^3->bool`; `jg:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `jd:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `v1 = (vv:real^3->bool) INTER ((:real^3) DIFF tt) INTER ((:real^3) DIFF jg)` THEN
  SUBGOAL_THEN `open (v1:real^3->bool) /\ dd SUBSET v1 /\ v1 SUBSET vv /\
                DISJOINT v1 tt /\ DISJOINT v1 jg`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v1" THEN REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED];
      UNDISCH_TAC `(dd:real^3->bool) SUBSET vv` THEN UNDISCH_TAC `DISJOINT (dd:real^3->bool) tt` THEN
      UNDISCH_TAC `DISJOINT (dd:real^3->bool) jg` THEN SET_TAC[];
      SET_TAC[]; SET_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`gs:real^3->bool`; `jg:real^3->bool`; `dd:real^3->bool`;
                                `jd:real^3->bool`; `v1:real^3->bool`] o
    check (fun th -> concl th = MOI_S3C2_DISK_CHART)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^3` (X_CHOOSE_THEN `phi:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(ee:real^3->bool) INTER IMAGE psi moi_s35_mid SUBSET dd` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube INTER gs = IMAGE psi moi_s35_mid` THEN
    UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET v1` THEN
    UNDISCH_TAC `DISJOINT (v1:real^3->bool) tt` THEN
    UNDISCH_TAC `(gs:real^3->bool) INTER ee SUBSET dd UNION tt` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?psi0 phi0:real^3->real^3.
      pl_homeomorphism (moi_s35_cube,IMAGE psi0 moi_s35_cube) (psi0,phi0) /\
      IMAGE psi0 moi_s35_cube = IMAGE psi moi_s35_cube /\
      IMAGE psi0 moi_s35_mid = IMAGE psi moi_s35_mid /\
      IMAGE psi0 moi_s30_inner = dd /\
      dd INTER closure (ee INTER IMAGE psi0 {x | x IN moi_s35_cube /\ &0 < x$3}) = {}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `closed (jd:real^3->bool)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    MP_TAC(ISPECL [`psi:real^3->real^3`; `phi:real^3->real^3`; `ee:real^3->bool`;
                   `dd:real^3->bool`; `jd:real^3->bool`] MOI_S3C2_PUSH_SIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`psi:real^3->real^3`; `phi:real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`psi:real^3->real^3`; `phi:real^3->real^3`] MOI_S3C2_BOX_FLIP) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`(psi:real^3->real^3) o reflect_along (basis 3)`;
                            `reflect_along (basis 3) o (phi:real^3->real^3)`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`psi0:real^3->real^3`; `phi0:real^3->real^3`; `ee:real^3->bool`;
                 `dd:real^3->bool`] MOI_S3C2_PUSH_HEIGHT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `moi_s3c2_dented gs (psi0:real^3->real^3) h` THEN
  MP_TAC(SPEC `h:real` MOI_S3C2_BUMP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3C2_DENT THEN EXISTS_TAC `phi0:real^3->real^3` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET v1` THEN
    UNDISCH_TAC `DISJOINT (v1:real^3->bool) jg` THEN SET_TAC[];
    REWRITE_TAC[moi_s3c2_dented] THEN
    MATCH_MP_TAC(SET_RULE `!g s t v:real^3->bool. t SUBSET v ==> (g DIFF s) UNION t SUBSET g UNION v`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (psi0:real^3->real^3) moi_s35_cube` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (psi:real^3->real^3) moi_s35_cube SUBSET v1` THEN
      UNDISCH_TAC `(v1:real^3->bool) SUBSET vv` THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o check (fun th ->
    concl th = `pl_homeomorphism (moi_s35_cube,IMAGE (psi0:real^3->real^3) moi_s35_cube)
                                 (psi0,(phi0:real^3->real^3))`)) THEN
  SUBGOAL_THEN `moi_s35_mid SUBSET moi_s35_cube` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3C2_MID_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(ee:real^3->bool) INTER IMAGE psi0 moi_s35_mid SUBSET dd` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((psi0:real^3->real^3) o moi_s3c2_bump h) moi_s35_mid INTER ee = {}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `s INTER t = {} <=> !y:real^3. y IN s ==> ~(y IN t)`] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(z:real^3) IN moi_s3c2_o7` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `moi_s3c2_bump h (z:real^3)` o check (fun th ->
        can (term_match [] `!x:real^3. x IN moi_s35_cube /\ &0 < x$3 /\ x$3 <= h
                                      ==> ~((psi0:real^3->real^3) x IN ee)`) (concl th))) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN ACCEPT_TAC];
      SUBGOAL_THEN `moi_s3c2_bump h z = (z:real^3)` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th =
          `!x:real^3. x IN moi_s35_mid /\ ~(x IN moi_s3c2_o7) ==> moi_s3c2_bump h x = x`)) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(psi0:real^3->real^3) z IN dd` MP_TAC THENL
       [UNDISCH_TAC `(ee:real^3->bool) INTER IMAGE psi0 moi_s35_mid SUBSET dd` THEN
        UNDISCH_TAC `(psi0:real^3->real^3) z IN ee` THEN
        SUBGOAL_THEN `(psi0:real^3->real^3) z IN IMAGE psi0 moi_s35_mid` MP_TAC THENL
         [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; SET_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (psi0:real^3->real^3) moi_s30_inner = dd` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `z:real^3 = w` SUBST_ALL_TAC THENL
       [SUBGOAL_THEN `(phi0:real^3->real^3) ((psi0:real^3->real^3) z) = phi0 (psi0 w)`
        MP_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(z:real^3) IN moi_s35_cube /\ (w:real^3) IN moi_s35_cube`
        STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `moi_s35_mid SUBSET moi_s35_cube` THEN
          UNDISCH_TAC `moi_s30_inner SUBSET moi_s3c2_o7` THEN
          UNDISCH_TAC `moi_s3c2_o7 SUBSET moi_s35_mid` THEN
          UNDISCH_TAC `(z:real^3) IN moi_s35_mid` THEN UNDISCH_TAC `(w:real^3) IN moi_s30_inner` THEN
          SET_TAC[];
          ASM_SIMP_TAC[]];
        UNDISCH_TAC `~((w:real^3) IN moi_s3c2_o7)` THEN
        UNDISCH_TAC `moi_s30_inner SUBSET moi_s3c2_o7` THEN
        UNDISCH_TAC `(w:real^3) IN moi_s30_inner` THEN SET_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s3c2_dented] THEN
  MATCH_MP_TAC(SET_RULE `!g e d q m b:real^3->bool.
     d SUBSET q /\ q SUBSET m /\ e INTER m SUBSET d /\ b INTER e = {}
     ==> ((g DIFF q) UNION b) INTER e = (g INTER e) DIFF d`) THEN
  EXISTS_TAC `IMAGE (psi0:real^3->real^3) moi_s35_mid` THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (psi0:real^3->real^3) moi_s30_inner = dd` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;


(* ------------------------------------------------------------------------- *)
(* 5. Surgery on PL 2-spheres: a small disk inside a disk, connected sets   *)
(* lie on one side of a splitting circle, the push on a sphere, and the     *)
(* innermost disk of a sphere with finitely many disjoint circles.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3C2_SMALL_DISK = prove
 (`!d j:real^3->bool.
     pl_cell_with_boundary 2 d j
     ==> ?d' j'. pl_cell_with_boundary 2 d' j' /\ d' SUBSET d /\ DISJOINT d' j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(relative_interior k:real^3->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; SIMPLEX_IMP_CONVEX; SIMPLEX_EMPTY;
                  INT_ARITH `~(&2:int = -- &1)`];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `{z:real^3}`] MOI_S4V_SHRINK_SIMPLEX) THEN
  ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:real^3->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (f:real^3->real^3) t2`;
                        `IMAGE (f:real^3->real^3) (relative_frontier t2)`] THEN
  SUBGOAL_THEN `(t2:real^3->bool) SUBSET k` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `relative_interior k:real^3->bool` THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`t2:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5C_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `d:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    UNDISCH_TAC `pl_homeomorphism (k,d) ((f:real^3->real^3),(g:real^3->real^3))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pl_homeomorphism (k,d) ((f:real^3->real^3),(g:real^3->real^3))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    SUBGOAL_THEN `relative_frontier k SUBSET (k:real^3->bool) /\
                  (t2:real^3->bool) INTER relative_frontier k = {}`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
        ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
        UNDISCH_TAC `(t2:real^3->bool) SUBSET relative_interior k` THEN
        REWRITE_TAC[relative_frontier] THEN SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `!x:real^3. x IN k ==> (g:real^3->real^3) (f x) = x` THEN
    UNDISCH_TAC `(t2:real^3->bool) SUBSET k` THEN
    UNDISCH_TAC `relative_frontier k SUBSET (k:real^3->bool)` THEN
    UNDISCH_TAC `(t2:real^3->bool) INTER relative_frontier k = {}` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY; SUBSET] THEN
    MESON_TAC[]]);;

let MOI_S3C2_SPLIT_SIDE = prove
 (`!d1 d2 j k:real^3->bool.
     closed d1 /\ closed d2 /\ d1 INTER d2 = j /\
     connected k /\ k SUBSET d1 UNION d2 /\ DISJOINT k j
     ==> k SUBSET d1 \/ k SUBSET d2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:real^3->bool` CONNECTED_CLOSED) THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`d1:real^3->bool`; `d2:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3C2_SPHERE_PUSH = prove
 (mk_imp(MOI_S3C2_DISK_CHART,
  `!s dd jd ee tt vv:real^3->bool.
     pl_sphere 2 s /\ pl_cell_with_boundary 2 dd jd /\ dd SUBSET s /\
     closed ee /\ dd SUBSET ee /\
     closed tt /\ DISJOINT dd tt /\ s INTER ee SUBSET dd UNION tt /\
     open vv /\ dd SUBSET vv /\
     (!x. x IN dd DIFF jd ==> ?u. open u /\ x IN u /\ ee INTER u SUBSET dd) /\
     (!x w. x IN jd /\ open w /\ x IN w
            ==> ?u. open u /\ x IN u /\ u SUBSET w /\
                    connected ((ee INTER u) DIFF dd) /\
                    jd INTER u SUBSET closure ((ee INTER u) DIFF dd))
     ==> ?s'. pl_sphere 2 s' /\ s' SUBSET s UNION vv /\
              s' INTER ee = (s INTER ee) DIFF dd`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `dd:real^3->bool`; `jd:real^3->bool`] DISK_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(s DIFF dd) UNION (jd:real^3->bool)`; `jd:real^3->bool`]
    MOI_S3C2_SMALL_DISK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `j1:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `j1:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
  MP_TAC(ISPECL [`dd:real^3->bool`; `jd:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(d1:real^3->bool) SUBSET s /\ DISJOINT d1 dd` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(d1:real^3->bool) SUBSET (s DIFF dd) UNION jd` THEN
    UNDISCH_TAC `DISJOINT (d1:real^3->bool) jd` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `d1:real^3->bool`; `j1:real^3->bool`] DISK_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `gs = (s DIFF d1) UNION (j1:real^3->bool)` THEN
  SUBGOAL_THEN `(dd:real^3->bool) SUBSET gs /\ DISJOINT dd j1 /\ gs SUBSET s /\
                gs INTER ee SUBSET dd UNION tt /\ gs INTER d1 = j1 /\ gs UNION d1 = s`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "gs" THEN
    UNDISCH_TAC `(dd:real^3->bool) SUBSET s` THEN UNDISCH_TAC `DISJOINT (d1:real^3->bool) dd` THEN
    UNDISCH_TAC `(j1:real^3->bool) SUBSET d1` THEN UNDISCH_TAC `(d1:real^3->bool) SUBSET s` THEN
    UNDISCH_TAC `s INTER ee SUBSET (dd:real^3->bool) UNION tt` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`gs:real^3->bool`; `j1:real^3->bool`; `dd:real^3->bool`;
     `jd:real^3->bool`; `ee:real^3->bool`; `tt:real^3->bool`; `vv DIFF (d1:real^3->bool)`] o
    MATCH_MP MOI_S3C2_PATCH_PUSH o check (fun th -> concl th = MOI_S3C2_DISK_CHART)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      UNDISCH_TAC `(dd:real^3->bool) SUBSET vv` THEN
      UNDISCH_TAC `DISJOINT (d1:real^3->bool) dd` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gs':real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gs' UNION (d1:real^3->bool)` THEN
  MP_TAC(ISPECL [`gs':real^3->bool`; `j1:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DISK_UNION THEN EXISTS_TAC `j1:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `gs' SUBSET gs UNION (vv DIFF (d1:real^3->bool))` THEN
    UNDISCH_TAC `(gs:real^3->bool) INTER d1 = j1` THEN
    UNDISCH_TAC `(j1:real^3->bool) SUBSET gs'` THEN
    UNDISCH_TAC `(j1:real^3->bool) SUBSET d1` THEN SET_TAC[];
    UNDISCH_TAC `gs' SUBSET gs UNION (vv DIFF (d1:real^3->bool))` THEN
    UNDISCH_TAC `(gs:real^3->bool) SUBSET s` THEN UNDISCH_TAC `(d1:real^3->bool) SUBSET s` THEN
    SET_TAC[];
    UNDISCH_TAC `gs' INTER ee = ((gs:real^3->bool) INTER ee) DIFF dd` THEN
    UNDISCH_TAC `(gs:real^3->bool) UNION d1 = s` THEN
    UNDISCH_TAC `DISJOINT (d1:real^3->bool) dd` THEN SET_TAC[]]);;

let MOI_S3C2_CIRCLE_CONN = prove
 (`!k:real^3->bool. pl_sphere 1 k ==> connected k /\ ~(k = {}) /\ compact k`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP MOI_S4U_PL_SPHERE1_CIRCLE) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:real^3->bool`; `sphere(vec 0:real^2,&1)`]
      HOMEOMORPHIC_CONNECTEDNESS) THEN
    ASM_SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_2; LE_REFL];
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `({}:real^3->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
    REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`k:real^3->bool`; `sphere(vec 0:real^2,&1)`]
      HOMEOMORPHIC_COMPACTNESS) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE]]);;

(* One reduction step towards an innermost disk: a disk a of s bounded by a *)
(* circle jj of gg containing another circle k of gg contains a disk e of s *)
(* bounded by k and missing jj.                                             *)

let MOI_S3C2_INNERMOST_STEP = prove
 (`!s gg a jj:real^3->bool.
     pl_sphere 2 s /\ (!k. k IN gg ==> pl_sphere 1 k /\ k SUBSET s) /\
     pairwise DISJOINT gg /\
     jj IN gg /\ pl_cell_with_boundary 2 a jj /\ a SUBSET s /\
     ~(a INTER UNIONS gg = jj)
     ==> ?e k. k IN gg /\ pl_cell_with_boundary 2 e k /\ e SUBSET s /\
               e SUBSET a /\ DISJOINT e jj`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `jj:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?k:real^3->bool. k IN gg /\ ~(k = jj) /\ ~(k INTER a = {})`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(a INTER UNIONS gg = jj:real^3->bool)` THEN
    UNDISCH_TAC `(jj:real^3->bool) SUBSET a` THEN UNDISCH_TAC `(jj:real^3->bool) IN gg` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; SUBSET; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (k:real^3->bool) jj` ASSUME_TAC THENL
   [UNDISCH_TAC `pairwise DISJOINT (gg:(real^3->bool)->bool)` THEN
    REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (k:real^3->bool) /\ k SUBSET s /\ pl_sphere 1 (jj:real^3->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3->bool`; `jj:real^3->bool`] DISK_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `ac = (s DIFF a) UNION (jj:real^3->bool)` THEN
  MP_TAC(ISPECL [`ac:real^3->bool`; `jj:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a UNION ac = s /\ a INTER ac = (jj:real^3->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ac" THEN
    UNDISCH_TAC `(jj:real^3->bool) SUBSET a` THEN UNDISCH_TAC `(a:real^3->bool) SUBSET s` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `k:real^3->bool` MOI_S3C2_CIRCLE_CONN) THEN
  MP_TAC(ISPEC `jj:real^3->bool` MOI_S3C2_CIRCLE_CONN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET a` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^3->bool`; `ac:real^3->bool`; `jj:real^3->bool`;
                   `k:real^3->bool`] MOI_S3C2_SPLIT_SIDE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      UNDISCH_TAC `a UNION ac = (s:real^3->bool)` THEN
      UNDISCH_TAC `(k:real^3->bool) SUBSET s` THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `~((k:real^3->bool) INTER a = {})` THEN
    UNDISCH_TAC `DISJOINT (k:real^3->bool) jj` THEN
    UNDISCH_TAC `a INTER ac = (jj:real^3->bool)` THEN
    UNDISCH_TAC `(k:real^3->bool) SUBSET ac` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `k:real^3->bool`] SPHERE_SPLIT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^3->bool` (X_CHOOSE_THEN `e2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?e:real^3->bool. pl_cell_with_boundary 2 e k /\ e SUBSET s /\ DISJOINT e jj`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e1:real^3->bool`; `k:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
    MP_TAC(ISPECL [`e2:real^3->bool`; `k:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`e1:real^3->bool`; `e2:real^3->bool`; `k:real^3->bool`; `jj:real^3->bool`]
      MOI_S3C2_SPLIT_SIDE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      UNDISCH_TAC `(e1:real^3->bool) UNION e2 = s` THEN
      UNDISCH_TAC `(jj:real^3->bool) SUBSET a` THEN UNDISCH_TAC `(a:real^3->bool) SUBSET s` THEN
      UNDISCH_TAC `DISJOINT (k:real^3->bool) jj` THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `e2:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [UNDISCH_TAC `(e1:real^3->bool) UNION e2 = s` THEN SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(e1:real^3->bool) INTER e2 = k` THEN
      UNDISCH_TAC `DISJOINT (k:real^3->bool) jj` THEN
      UNDISCH_TAC `(jj:real^3->bool) SUBSET e1` THEN SET_TAC[];
      EXISTS_TAC `e1:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [UNDISCH_TAC `(e1:real^3->bool) UNION e2 = s` THEN SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(e1:real^3->bool) INTER e2 = k` THEN
      UNDISCH_TAC `DISJOINT (k:real^3->bool) jj` THEN
      UNDISCH_TAC `(jj:real^3->bool) SUBSET e2` THEN SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e:real^3->bool`; `k:real^3->bool`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `k:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected (e:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S5C_CELL_CONNECTED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `ac:real^3->bool`; `jj:real^3->bool`;
                 `e:real^3->bool`] MOI_S3C2_SPLIT_SIDE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `a UNION ac = (s:real^3->bool)` THEN
    UNDISCH_TAC `(e:real^3->bool) SUBSET s` THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `(k:real^3->bool) SUBSET a` THEN UNDISCH_TAC `(k:real^3->bool) SUBSET e` THEN
  UNDISCH_TAC `~(k:real^3->bool = {})` THEN UNDISCH_TAC `DISJOINT (k:real^3->bool) jj` THEN
  UNDISCH_TAC `a INTER ac = (jj:real^3->bool)` THEN
  UNDISCH_TAC `(e:real^3->bool) SUBSET ac` THEN SET_TAC[]);;

(* A PL 2-sphere s with a nonempty finite family gg of disjoint PL circles  *)
(* has a disk bounded by one of them meeting UNIONS gg only in its rim (a   *)
(* disk of s bounded by a circle of gg with the fewest circles inside).     *)

let MOI_S3C2_INNERMOST_DISK = prove
 (`!s gg:(real^3->bool)->bool.
     pl_sphere 2 s /\ FINITE gg /\ ~(gg = {}) /\
     (!jj. jj IN gg ==> pl_sphere 1 jj /\ jj SUBSET s) /\ pairwise DISJOINT gg
     ==> ?a jj. jj IN gg /\ pl_cell_with_boundary 2 a jj /\ a SUBSET s /\
                a INTER UNIONS gg = jj`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k:real^3->bool. k IN gg ==> ~(k = {})` ASSUME_TAC THENL
   [X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `k:real^3->bool` MOI_S3C2_CIRCLE_CONN) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n a jj:real^3->bool.
      jj IN gg /\ pl_cell_with_boundary 2 a jj /\ a SUBSET s /\
      CARD {k | k IN gg /\ k SUBSET a} = n
      ==> ?a jj. jj IN gg /\ pl_cell_with_boundary 2 a jj /\ a SUBSET s /\
                 a INTER UNIONS gg = jj`
  ASSUME_TAC THENL
   [MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`a:real^3->bool`; `jj:real^3->bool`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `a INTER UNIONS gg = jj:real^3->bool` THENL
     [MAP_EVERY EXISTS_TAC [`a:real^3->bool`; `jj:real^3->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `gg:(real^3->bool)->bool`; `a:real^3->bool`;
                   `jj:real^3->bool`] MOI_S3C2_INNERMOST_STEP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` (X_CHOOSE_THEN `k:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `~(jj:real^3->bool = {})` ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME `!k:real^3->bool. k IN gg ==> ~(k = {})`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^3->bool`; `jj:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `CARD {k' | k' IN gg /\ k' SUBSET (e:real^3->bool)}`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `CARD {k | k IN gg /\ k SUBSET (a:real^3->bool)} = n` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CARD_PSUBSET THEN CONJ_TAC THENL
       [REWRITE_TAC[PSUBSET; SUBSET; IN_ELIM_THM; EXTENSION] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(e:real^3->bool) SUBSET a` THEN SET_TAC[];
          DISCH_THEN(MP_TAC o SPEC `jj:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `DISJOINT (e:real^3->bool) jj` THEN
          UNDISCH_TAC `(jj:real^3->bool) SUBSET a` THEN
          UNDISCH_TAC `~(jj:real^3->bool = {})` THEN SET_TAC[]];
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `gg:(real^3->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      DISCH_THEN(MP_TAC o SPECL [`e:real^3->bool`; `k:real^3->bool`]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `~(gg:(real^3->bool)->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `jj:real^3->bool`) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `jj:real^3->bool`] SPHERE_SPLIT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^3->bool` (X_CHOOSE_THEN `e2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CARD {k | k IN gg /\ k SUBSET (e1:real^3->bool)}`;
                                `e1:real^3->bool`; `jj:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `(e1:real^3->bool) UNION e2 = s` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 6. A central circle exists: otherwise the complement of the closed        *)
(* domains of the curves IMAGE gz J, retracted into the closed unit disk,    *)
(* is carried by fz to a connected set joining p (inside c) to fz(basis 1)   *)
(* (outside c) and missing frontier c.                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S3C2_CURVES = prove
 (`!e j p d c dz (fz:real^2->real^3) gz ff.
     moi_s3c2_setting e j p d c dz fz gz ff
     ==> FINITE (IMAGE (\jj. IMAGE gz jj) ff) /\
         (!cc. cc IN IMAGE (\jj. IMAGE gz jj) ff
               ==> cc homeomorphic sphere(vec 0:real^2,&1)) /\
         pairwise DISJOINT (IMAGE (\jj. IMAGE gz jj) ff)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3C2_BASICS) THEN
  SUBGOAL_THEN `FINITE (ff:(real^3->bool)->bool) /\ pairwise DISJOINT ff` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3c2_setting e j p d c dz (fz:real^2->real^3) gz ff` THEN
    REWRITE_TAC[moi_s3c2_setting] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                   `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                   `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
      MOI_S3C2_CIRCLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `j1:real^3->bool` THEN DISCH_TAC THEN
  X_GEN_TAC `j2:real^3->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(j1:real^3->bool = j2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(IMAGE (gz:real^3->real^2) j2 = IMAGE gz j2)` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (j1:real^3->bool) j2` ASSUME_TAC THENL
   [UNDISCH_TAC `pairwise DISJOINT (ff:(real^3->bool)->bool)` THEN
    REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `j1:real^3->bool`]
    MOI_S3C2_CIRCLE) THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `j2:real^3->bool`]
    MOI_S3C2_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `DISJOINT (j1:real^3->bool) j2` THEN
  UNDISCH_TAC `(j1:real^3->bool) SUBSET dz` THEN UNDISCH_TAC `(j2:real^3->bool) SUBSET dz` THEN
  UNDISCH_TAC `!y:real^3. y IN dz ==> (fz:real^2->real^3) (gz y) = y` THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY; SUBSET] THEN
  MESON_TAC[]);;

let MOI_S3C2_CENTRAL_EXISTS = prove
 (`!e j p d c dz (fz:real^2->real^3) gz ff.
     moi_s3c2_setting e j p d c dz fz gz ff
     ==> ?jj. jj IN ff /\ moi_s3c2_central gz jj`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3C2_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3C2_CURVES) THEN
  SUBGOAL_THEN `(fz:real^2->real^3) (vec 0) = p /\
                c INTER e SUBSET IMAGE fz (ball(vec 0,&1)) /\
                frontier c INTER e = UNIONS ff`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3c2_setting e j p d c dz (fz:real^2->real^3) gz ff` THEN
    REWRITE_TAC[moi_s3c2_setting] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?jj. jj IN ff /\ moi_s3c2_central (gz:real^3->real^2) jj` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`]) THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN
   `!jj. jj IN ff
         ==> IMAGE (gz:real^3->real^2) jj UNION inside (IMAGE gz jj) SUBSET ball(vec 0,&1) /\
             ~(vec 0 IN IMAGE gz jj UNION inside (IMAGE gz jj)) /\
             IMAGE (fz:real^2->real^3) (IMAGE gz jj) = jj`
  (LABEL_TAC "cd") THENL
   [X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                   `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                   `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
      MOI_S3C2_DISK) THEN
    MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                   `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                   `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
      MOI_S3C2_CIRCLE) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((p:real^3) IN jj)` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (fz:real^2->real^3) (IMAGE gz jj) = jj` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(fz:real^2->real^3) (vec 0) = p` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `jj:real^3->bool` o check (fun th ->
        can (term_match [] `!jj. jj IN ff ==> ~moi_s3c2_central gz jj`) (concl th))) THEN
      ASM_REWRITE_TAC[moi_s3c2_central]];
    ALL_TAC] THEN
  ABBREV_TAC `uu = (:real^2) DIFF UNIONS (IMAGE (\cc. cc UNION inside cc)
                                         (IMAGE (\jj. IMAGE (gz:real^3->real^2) jj) ff))` THEN
  SUBGOAL_THEN `connected (uu:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "uu" THEN MATCH_MP_TAC MOI_S3C2_DOMAINS_NONSEP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN uu <=>
                  !jj. jj IN ff ==> ~(x IN IMAGE (gz:real^3->real^2) jj UNION inside (IMAGE gz jj))`
  ASSUME_TAC THENL
   [EXPAND_TAC "uu" THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[IMAGE_o; GSYM IMAGE_o] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE; o_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ww = IMAGE (closest_point (cball(vec 0:real^2,&1))) uu` THEN
  SUBGOAL_THEN `connected (ww:real^2->bool) /\ ww SUBSET cball(vec 0,&1) /\
                (vec 0:real^2) IN ww /\ (basis 1:real^2) IN ww /\
                !jj w. jj IN ff /\ w IN ww
                       ==> ~(w IN IMAGE (gz:real^3->real^2) jj UNION inside (IMAGE gz jj))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!y:real^2. norm y = &1
                    ==> !jj. jj IN ff ==> ~(y IN IMAGE (gz:real^3->real^2) jj UNION
                                                  inside (IMAGE gz jj))`
    ASSUME_TAC THENL
     [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THEN
      USE_THEN "cd" (MP_TAC o C MP (ASSUME `(jj:real^3->bool) IN ff`) o SPEC `jj:real^3->bool`) THEN
      DISCH_THEN(MP_TAC o REWRITE_RULE[SUBSET] o CONJUNCT1) THEN
      DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
      ASM_REWRITE_TAC[IN_BALL_0; REAL_LT_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `!u:real^2. u IN uu
                    ==> closest_point (cball(vec 0,&1)) u IN cball(vec 0,&1) /\
                        !jj. jj IN ff
                             ==> ~(closest_point (cball(vec 0,&1)) u IN
                                   IMAGE (gz:real^3->real^2) jj UNION inside (IMAGE gz jj))`
    (LABEL_TAC "uf") THENL
     [X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSEST_POINT_IN_SET THEN
        REWRITE_TAC[CLOSED_CBALL; CBALL_EQ_EMPTY] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `(u:real^2) IN cball(vec 0,&1)` THENL
       [ASM_SIMP_TAC[CLOSEST_POINT_SELF] THEN
        UNDISCH_TAC `(u:real^2) IN uu` THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `u:real^2`] CLOSEST_POINT_IN_FRONTIER) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[CLOSED_CBALL; CBALL_EQ_EMPTY] THEN
          CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MP_TAC(ISPEC `cball(vec 0:real^2,&1)` INTERIOR_SUBSET) THEN ASM SET_TAC[];
          REWRITE_TAC[FRONTIER_CBALL; IN_SPHERE_0]]];
      ALL_TAC] THEN
    EXPAND_TAC "ww" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CLOSEST_POINT THEN
      REWRITE_TAC[CONVEX_CBALL; CLOSED_CBALL; CBALL_EQ_EMPTY] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CLOSEST_POINT_SELF THEN
        REWRITE_TAC[CENTRE_IN_CBALL] THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `basis 1:real^2` THEN
      SUBGOAL_THEN `norm(basis 1:real^2) = &1` ASSUME_TAC THENL
       [SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH]; ALL_TAC] THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CLOSEST_POINT_SELF THEN
        ASM_REWRITE_TAC[IN_CBALL_0; REAL_LE_REFL];
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THEN X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
      USE_THEN "uf" (MP_TAC o SPEC `u:real^2`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (fz:real^2->real^3) ww`; `c:real^3->bool`]
    CONNECTED_INTER_FRONTIER) THEN
  MATCH_MP_TAC(TAUT `a /\ b ==> (a ==> ~b) ==> F`) THEN
  SUBGOAL_THEN `(fz:real^2->real^3) continuous_on ww` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `p:real^3` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(fz:real^2->real^3) (vec 0) = p` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN
    EXISTS_TAC `(fz:real^2->real^3) (basis 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(fz:real^2->real^3) (basis 1) IN c INTER e` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `dz SUBSET (e:real^3->bool) DIFF j` THEN
      UNDISCH_TAC `IMAGE (fz:real^2->real^3) (cball(vec 0,&1)) = dz` THEN
      UNDISCH_TAC `(ww:real^2->bool) SUBSET cball(vec 0,&1)` THEN
      UNDISCH_TAC `(basis 1:real^2) IN ww` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `c INTER e SUBSET IMAGE (fz:real^2->real^3) (ball(vec 0,&1))` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `basis 1:real^2 = z` MP_TAC THENL
     [SUBGOAL_THEN `(gz:real^3->real^2) ((fz:real^2->real^3) (basis 1)) = gz (fz z)` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(basis 1:real^2) IN cball(vec 0,&1) /\ (z:real^2) IN cball(vec 0,&1)`
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[IN_CBALL_0; NORM_BASIS; DIMINDEX_2; ARITH; REAL_LE_REFL;
                     REAL_LT_IMP_LE];
        ASM_SIMP_TAC[]];
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      UNDISCH_TAC `norm(basis 1:real^2) < &1` THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH; REAL_LT_REFL]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN frontier c INTER e` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `dz SUBSET (e:real^3->bool) DIFF j` THEN
      UNDISCH_TAC `IMAGE (fz:real^2->real^3) (cball(vec 0,&1)) = dz` THEN
      UNDISCH_TAC `(ww:real^2->bool) SUBSET cball(vec 0,&1)` THEN
      UNDISCH_TAC `(w:real^2) IN ww` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `jj:real^3->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`jj:real^3->bool`; `w:real^2`] o check (fun th ->
      concl th = `!jj w. jj IN ff /\ w IN ww
                         ==> ~(w IN IMAGE (gz:real^3->real^2) jj UNION inside (IMAGE gz jj))`)) THEN
    ASM_REWRITE_TAC[IN_UNION] THEN
    SUBGOAL_THEN `(w:real^2) IN IMAGE (gz:real^3->real^2) jj` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(ww:real^2->bool) SUBSET cball(vec 0,&1)` THEN
    UNDISCH_TAC `(w:real^2) IN ww` THEN SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* 7. The surgery step on spheres, the induction, and CAP_SURGERY.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3C2_SURGERY_STEP = prove
 (mk_imp(mk_conj(MOI_S3C2_POLY_DISK, MOI_S3C2_DISK_CHART),
  `!e j p d c dz (fz:real^2->real^3) gz ff s gg jj1 jj0.
     moi_s3c2_setting e j p d c dz fz gz ff /\
     pl_sphere 2 s /\ s SUBSET ball(p,d) /\ gg SUBSET ff /\ s INTER e = UNIONS gg /\
     jj1 IN gg /\ ~moi_s3c2_central gz jj1 /\
     (!jj. jj IN gg /\ ~(jj = jj1) ==> DISJOINT jj (moi_s3c2_disk fz gz jj1)) /\
     jj0 IN gg /\ moi_s3c2_central gz jj0
     ==> ?s' gg'. pl_sphere 2 s' /\ s' SUBSET ball(p,d) /\ gg' SUBSET gg /\
                  jj0 IN gg' /\ ~(jj1 IN gg') /\ s' INTER e = UNIONS gg'`),
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3C2_BASICS) THEN
  SUBGOAL_THEN `FINITE (ff:(real^3->bool)->bool) /\ pairwise DISJOINT ff`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3c2_setting e j p d c dz (fz:real^2->real^3) gz ff` THEN
    REWRITE_TAC[moi_s3c2_setting] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (gg:(real^3->bool)->bool) /\ pairwise DISJOINT gg`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ff:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC PAIRWISE_MONO THEN EXISTS_TAC `ff:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `dd = moi_s3c2_disk (fz:real^2->real^3) gz jj1` THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj1:real^3->bool`]
    MOI_S3C2_DISK) THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj1:real^3->bool`]
    MOI_S3C2_CIRCLE) THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj1:real^3->bool`]
    (MP MOI_S3C2_DISK_PL (ASSUME MOI_S3C2_POLY_DISK))) THEN
  SUBGOAL_THEN `(jj1:real^3->bool) IN ff /\ (jj0:real^3->bool) IN ff` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!jj:real^3->bool. jj IN gg ==> pl_sphere 1 jj /\ jj SUBSET s /\ jj SUBSET e /\
                                              connected jj /\ compact jj /\ ~(jj = {})`
  (LABEL_TAC "circ") THENL
   [X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(jj:real^3->bool) IN ff` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                   `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                   `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
      MOI_S3C2_CIRCLE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `jj:real^3->bool` MOI_S3C2_CIRCLE_CONN) THEN ASM_SIMP_TAC[] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `s INTER e = UNIONS (gg:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `(jj:real^3->bool) IN gg` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(jj0:real^3->bool = jj1)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dd INTER s = (jj1:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(dd:real^3->bool) INTER s = dd INTER UNIONS gg` SUBST1_TAC THENL
       [UNDISCH_TAC `s INTER e = UNIONS (gg:(real^3->bool)->bool)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `(dd:real^3->bool) SUBSET e` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC)) THEN
      ASM_CASES_TAC `k:real^3->bool = jj1` THENL
       [UNDISCH_TAC `(y:real^3) IN k` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:real^3->bool` o check (fun th -> concl th =
        `!jj:real^3->bool. jj IN gg /\ ~(jj = jj1) ==> DISJOINT jj dd`)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN k` THEN UNDISCH_TAC `(y:real^3) IN dd` THEN SET_TAC[];
      USE_THEN "circ" (MP_TAC o C MP (ASSUME `(jj1:real^3->bool) IN gg`) o
                       SPEC `jj1:real^3->bool`) THEN
      UNDISCH_TAC `(jj1:real^3->bool) SUBSET dd` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `jj1:real^3->bool`] SPHERE_SPLIT) THEN
  ANTS_TAC THENL
   [USE_THEN "circ" (MP_TAC o C MP (ASSUME `(jj1:real^3->bool) IN gg`) o
                     SPEC `jj1:real^3->bool`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `jj1:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
  MP_TAC(ISPECL [`d2:real^3->bool`; `jj1:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!jj:real^3->bool. jj IN gg /\ ~(jj = jj1)
                  ==> (jj SUBSET d1 /\ DISJOINT jj d2) \/ (jj SUBSET d2 /\ DISJOINT jj d1)`
  (LABEL_TAC "side") THENL
   [X_GEN_TAC `jj:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `DISJOINT (jj:real^3->bool) jj1` ASSUME_TAC THENL
     [UNDISCH_TAC `pairwise DISJOINT (gg:(real^3->bool)->bool)` THEN
      REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "circ" (MP_TAC o C MP (ASSUME `(jj:real^3->bool) IN gg`) o
                     SPEC `jj:real^3->bool`) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`d1:real^3->bool`; `d2:real^3->bool`; `jj1:real^3->bool`;
                   `jj:real^3->bool`] MOI_S3C2_SPLIT_SIDE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      UNDISCH_TAC `(d1:real^3->bool) UNION d2 = s` THEN
      UNDISCH_TAC `(jj:real^3->bool) SUBSET s` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(d1:real^3->bool) INTER d2 = jj1` THEN
    UNDISCH_TAC `DISJOINT (jj:real^3->bool) jj1` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?di:real^3->bool. pl_cell_with_boundary 2 di jj1 /\ di SUBSET s /\
                  (jj0:real^3->bool) SUBSET di /\
                  (!jj. jj IN gg /\ ~(jj = jj1) ==> jj SUBSET di \/ DISJOINT jj di)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "side" (MP_TAC o C MP (CONJ (ASSUME `(jj0:real^3->bool) IN gg`)
                                          (ASSUME `~(jj0:real^3->bool = jj1)`)) o
                     SPEC `jj0:real^3->bool`) THEN
    STRIP_TAC THENL
     [EXISTS_TAC `d1:real^3->bool`; EXISTS_TAC `d2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [UNDISCH_TAC `(d1:real^3->bool) UNION d2 = s` THEN SET_TAC[]; ALL_TAC]) THEN
    X_GEN_TAC `jj:real^3->bool` THEN STRIP_TAC THEN
    USE_THEN "side" (MP_TAC o C MP (CONJ (ASSUME `(jj:real^3->bool) IN gg`)
                                        (ASSUME `~(jj:real^3->bool = jj1)`)) o
                     SPEC `jj:real^3->bool`) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`di:real^3->bool`; `jj1:real^3->bool`] MOI_S3C2_CELL_RIM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!jj:real^3->bool. jj IN gg DELETE jj1 ==> DISJOINT jj dd`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`di UNION dd:real^3->bool`; `dd:real^3->bool`; `jj1:real^3->bool`;
                `e:real^3->bool`; `UNIONS (gg DELETE (jj1:real^3->bool))`; `ball(p:real^3,d)`]
    (MP MOI_S3C2_SPHERE_PUSH (ASSUME MOI_S3C2_DISK_CHART))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(REWRITE_TAC[OPEN_BALL; SUBSET_UNION] THEN NO_TAC) THENL
     [MATCH_MP_TAC DISK_UNION THEN EXISTS_TAC `jj1:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `dd INTER s = (jj1:real^3->bool)` THEN
      UNDISCH_TAC `(di:real^3->bool) SUBSET s` THEN UNDISCH_TAC `(jj1:real^3->bool) SUBSET di` THEN
      UNDISCH_TAC `(jj1:real^3->bool) SUBSET dd` THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
      X_GEN_TAC `jj:real^3->bool` THEN STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      USE_THEN "circ" (MP_TAC o C MP (ASSUME `(jj:real^3->bool) IN gg`) o
                       SPEC `jj:real^3->bool`) THEN SIMP_TAC[];
      UNDISCH_TAC `!jj:real^3->bool. jj IN gg DELETE jj1 ==> DISJOINT jj dd` THEN SET_TAC[];
      UNDISCH_TAC `s INTER e = UNIONS (gg:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `(di:real^3->bool) SUBSET s` THEN UNDISCH_TAC `(jj1:real^3->bool) SUBSET dd` THEN
      UNDISCH_TAC `(jj1:real^3->bool) IN gg` THEN SET_TAC[];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      MP_TAC(GEN_REWRITE_RULE I [OPEN_IN_OPEN] (ASSUME
        `open_in (subtopology euclidean e) ((dd:real^3->bool) DIFF jj1)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `w:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(dd:real^3->bool) DIFF jj1 = e INTER w` THEN
      UNDISCH_TAC `(x:real^3) IN dd DIFF jj1` THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `w:real^3->bool`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                     `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                     `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj1:real^3->bool`;
                     `x:real^3`; `w:real^3->bool`] MOI_S3C2_EDGE_SIDE) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^3->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`s':real^3->bool`; `{jj:real^3->bool | jj IN gg /\ jj SUBSET di /\ ~(jj = jj1)}`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `s' SUBSET (di UNION dd) UNION ball(p:real^3,d)` THEN
    UNDISCH_TAC `(di:real^3->bool) SUBSET s` THEN
    UNDISCH_TAC `s SUBSET ball(p:real^3,d)` THEN
    UNDISCH_TAC `(dd:real^3->bool) SUBSET ball(p,d)` THEN SET_TAC[];
    SET_TAC[];
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIONS; IN_ELIM_THM; IN_UNION] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN UNIONS gg` MP_TAC THENL
       [UNDISCH_TAC `s INTER e = UNIONS (gg:(real^3->bool)->bool)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(di:real^3->bool) SUBSET s` THEN UNDISCH_TAC `(y:real^3) IN di` THEN
        SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `jj:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(jj:real^3->bool = jj1)` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~((y:real^3) IN dd)` THEN UNDISCH_TAC `(y:real^3) IN jj1` THEN
        UNDISCH_TAC `(jj1:real^3->bool) SUBSET dd` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `jj:real^3->bool` o check (fun th -> concl th =
        `!jj:real^3->bool. jj IN gg /\ ~(jj = jj1) ==> jj SUBSET di \/ DISJOINT jj di`)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN jj` THEN UNDISCH_TAC `(y:real^3) IN di` THEN SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `jj:real^3->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "circ" (MP_TAC o C MP (ASSUME `(jj:real^3->bool) IN gg`) o
                       SPEC `jj:real^3->bool`) THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `jj:real^3->bool` o check (fun th -> concl th =
        `!jj:real^3->bool. jj IN gg DELETE jj1 ==> DISJOINT jj dd`)) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN
      UNDISCH_TAC `(y:real^3) IN jj` THEN UNDISCH_TAC `(jj:real^3->bool) SUBSET di` THEN
      UNDISCH_TAC `(jj:real^3->bool) SUBSET e` THEN SET_TAC[]]]);;

let MOI_S3C2_SPHERE_INDUCT = prove
 (mk_imp(mk_conj(MOI_S3C2_POLY_DISK, MOI_S3C2_DISK_CHART),
  `!e j p d c dz (fz:real^2->real^3) gz ff.
     moi_s3c2_setting e j p d c dz fz gz ff
     ==> !n s gg. CARD gg = n /\ gg SUBSET ff /\ pl_sphere 2 s /\ s SUBSET ball(p,d) /\
                  s INTER e = UNIONS gg /\ (?jj0. jj0 IN gg /\ moi_s3c2_central gz jj0)
                  ==> ?a jj. jj IN ff /\ moi_s3c2_central gz jj /\
                             pl_cell_with_boundary 2 a jj /\ a SUBSET ball(p,d) /\
                             a INTER e = jj`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE (ff:(real^3->bool)->bool) /\ pairwise DISJOINT ff`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3c2_setting e j p d c dz (fz:real^2->real^3) gz ff` THEN
    REWRITE_TAC[moi_s3c2_setting] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `gg:(real^3->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `jj0:real^3->bool` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `FINITE (gg:(real^3->bool)->bool) /\ pairwise DISJOINT gg`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ff:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC PAIRWISE_MONO THEN EXISTS_TAC `ff:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `!jj:real^3->bool. jj IN gg ==> moi_s3c2_central gz jj` THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `gg:(real^3->bool)->bool`] MOI_S3C2_INNERMOST_DISK) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                     `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                     `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
        MOI_S3C2_CIRCLE) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]] THEN
      UNDISCH_TAC `s INTER e = UNIONS (gg:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `(jj:real^3->bool) IN gg` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^3->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `jj:real^3->bool` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      UNDISCH_TAC `a INTER UNIONS gg = (jj:real^3->bool)` THEN
      UNDISCH_TAC `s INTER e = UNIONS (gg:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `(a:real^3->bool) SUBSET s` THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP] o check (fun th ->
    concl th = `~(!jj:real^3->bool. jj IN gg ==> moi_s3c2_central gz jj)`)) THEN
  ABBREV_TAC `ncs = {jj:real^3->bool | jj IN gg /\ ~moi_s3c2_central gz jj}` THEN
  SUBGOAL_THEN `FINITE (ncs:(real^3->bool)->bool) /\ ~(ncs = {}) /\ ncs SUBSET gg /\
                !jj. jj IN ncs <=> jj IN gg /\ ~moi_s3c2_central gz jj`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ncs" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `gg:(real^3->bool)->bool` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      UNDISCH_TAC `?jj:real^3->bool. jj IN gg /\ ~moi_s3c2_central gz jj` THEN MESON_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\jj. IMAGE (gz:real^3->real^2) jj) ncs` MOI_S3C2_INNERMOST) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                   `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                   `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
      MOI_S3C2_CIRCLE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `jj1:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(jj1:real^3->bool) IN gg /\ ~moi_s3c2_central gz jj1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!jj:real^3->bool. jj IN gg /\ ~(jj = jj1)
                  ==> DISJOINT jj (moi_s3c2_disk fz gz jj1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `jj:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3C2_DISK_AVOID THEN
    MAP_EVERY EXISTS_TAC [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                          `c:real^3->bool`; `dz:real^3->bool`; `ff:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      ASM_CASES_TAC `moi_s3c2_central (gz:real^3->real^2) jj` THENL
       [DISCH_TAC THEN UNDISCH_TAC `~moi_s3c2_central (gz:real^3->real^2) jj1` THEN
        REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3C2_CENTRAL_NEST THEN
        EXISTS_TAC `jj:real^3->bool` THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> aconv (concl th)
          `!x:real^3->bool. x IN ncs ==> ~(IMAGE (gz:real^3->real^2) x UNION
                                           inside (IMAGE gz x) SUBSET inside (IMAGE gz jj1))`)) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `s:real^3->bool`;
                `gg:(real^3->bool)->bool`; `jj1:real^3->bool`; `jj0:real^3->bool`]
    (MP MOI_S3C2_SURGERY_STEP (ASSUME (mk_conj(MOI_S3C2_POLY_DISK, MOI_S3C2_DISK_CHART))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^3->bool` (X_CHOOSE_THEN `gg':(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CARD (gg':(real^3->bool)->bool)` o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `n:num`)) (concl th))) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `CARD (gg:(real^3->bool)->bool) = n` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET] THEN
    UNDISCH_TAC `(jj1:real^3->bool) IN gg` THEN UNDISCH_TAC `~((jj1:real^3->bool) IN gg')` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s':real^3->bool`; `gg':(real^3->bool)->bool`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[]; EXISTS_TAC `jj0:real^3->bool` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* CAP_SURGERY (Moise 32.4 with the disk of e inside ball(p,d)).            *)
(* ------------------------------------------------------------------------- *)

let CAP_SURGERY = prove
 (MOI_S32_CAP_SURGERY,
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE[GSYM moi_s3c2_setting] th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3C2_BASICS) THEN
  SUBGOAL_THEN `(c:real^3->bool) SUBSET ball(p,d) /\ frontier c INTER e = UNIONS ff`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3c2_setting e j p d c dz (fz:real^2->real^3) gz ff` THEN
    REWRITE_TAC[moi_s3c2_setting] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                `gz:real^3->real^2`; `ff:(real^3->bool)->bool`] MOI_S3C2_CENTRAL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `jj0:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                `gz:real^3->real^2`; `ff:(real^3->bool)->bool`]
    (MP MOI_S3C2_SPHERE_INDUCT
        (CONJ (ASSUME MOI_S3C2_POLY_DISK) (ASSUME MOI_S3C2_DISK_CHART)))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`CARD (ff:(real^3->bool)->bool)`; `frontier c:real^3->bool`;
                             `ff:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(c:real^3->bool) SUBSET ball(p,d)` THEN
      UNDISCH_TAC `frontier c SUBSET (c:real^3->bool)` THEN SET_TAC[];
      EXISTS_TAC `jj0:real^3->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3->bool` (X_CHOOSE_THEN `jj:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:real^3->bool`; `jj:real^3->bool`;
                        `moi_s3c2_disk (fz:real^2->real^3) gz jj`] THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
    MOI_S3C2_DISK) THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`;
                 `c:real^3->bool`; `dz:real^3->bool`; `fz:real^2->real^3`;
                 `gz:real^3->real^2`; `ff:(real^3->bool)->bool`; `jj:real^3->bool`]
    MOI_S3C2_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[IN_DIFF; SUBSET_INTER]);;

