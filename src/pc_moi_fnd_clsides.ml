(* ========================================================================= *)
(* pc_moi_fnd_clsides: the sides of a combinatorial surface with boundary K  *)
(* cut along a union of circles L by a relatively clopen partition K1, K2    *)
(* of the complement, each side accumulating on all of L.  Main theorem      *)
(* MOI_FCS_CLOPEN_SIDES, a piece of MOI_FND_SPLIT_ANNULUS_R3 (used in        *)
(* pc_moi_fnd_annnbhd).                                                      *)
(*                                                                           *)
(* The first parts follow pc_moi_fnd_bcollar.ml (moi_fcb_split ...           *)
(* MOI_FCB_SIDE_MANIFOLD), with the names MOI_FCB_ replaced by MOI_FCS_ and  *)
(* the hypothesis that the complement of L has exactly two components        *)
(* replaced by a relatively clopen partition (moi_fcs_split; only            *)
(* SPLIT_FACTS and TRI_SIDE change).  MOI_FCB_HULL_PAIR_OFF and              *)
(* MOI_FCB_DEG2_LINK are used from bcollar, and MOI_FCS_SPLIT_FCB derives    *)
(* the two-component splits of bcollar as a special case.                    *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_bcollar.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Clopen two-sided splits of a combinatorial surface with boundary K along  *)
(* a full subcomplex L of dimension at most 1 with all vertex degrees 2,     *)
(* disjoint from the boundary, by a relatively clopen partition K1, K2 of    *)
(* the complement, each side accumulating on L (moi_fcs_split, adapted from  *)
(* pc_moi_fnd_bcollar.ml; bcollar's moi_fcb_split with two components is the *)
(* special case).  A triangle minus L is connected, so it lies on exactly    *)
(* one side.                                                                 *)
(* ========================================================================= *)

let moi_fcs_split = new_definition
 `moi_fcs_split (K:(real^N->bool)->bool) L K1 K2 <=>
    FINITE K /\ combinatorial_manifold_with_boundary 2 K /\
    simplicial_subcomplex L K /\ (!s. s IN L ==> aff_dim s <= &1) /\
    (!v. {v} IN L ==> CARD {e | e IN L /\ aff_dim e = &1 /\ v IN e} = 2) /\
    (!q. q IN K ==> q INTER UNIONS L IN L /\ (q INTER UNIONS L) face_of q) /\
    DISJOINT (UNIONS L) (surface_boundary K) /\
    K1 UNION K2 = UNIONS K DIFF UNIONS L /\ DISJOINT K1 K2 /\
    open_in (subtopology euclidean (UNIONS K DIFF UNIONS L)) K1 /\
    open_in (subtopology euclidean (UNIONS K DIFF UNIONS L)) K2 /\
    UNIONS L SUBSET closure K1 /\ UNIONS L SUBSET closure K2`;;

let MOI_FCS_SPLIT_SYM = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcs_split K L K1 K2 ==> moi_fcs_split K L K2 K1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fcs_split] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FCS_SPLIT_FACTS = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcs_split K L K1 K2
     ==> lf_simplicial_complex K /\ simplicial_complex K /\
         FINITE L /\ simplicial_complex L /\ lf_simplicial_complex L /\
         L SUBSET K /\ UNIONS L SUBSET UNIONS K /\
         (!s. s IN L ==> aff_dim s <= &1) /\
         (!s. s IN K ==> compact s /\ convex s) /\
         (!s. s IN K ==> aff_dim s <= &2) /\
         open_in (subtopology euclidean (UNIONS K DIFF UNIONS L)) K1 /\
         open_in (subtopology euclidean (UNIONS K DIFF UNIONS L)) K2 /\
         closed_in (subtopology euclidean (UNIONS K DIFF UNIONS L)) K1 /\
         closed_in (subtopology euclidean (UNIONS K DIFF UNIONS L)) K2 /\
         K1 INTER K2 = {} /\
         K1 UNION K2 = UNIONS K DIFF UNIONS L /\
         compact (UNIONS K) /\ compact (UNIONS L)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fcs_split] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `(L:(real^N->bool)->bool) SUBSET K` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K ==> compact s /\ convex s` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_COMPACT; MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K ==> aff_dim s <= &2` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_DIM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(UNIONS K DIFF UNIONS L) DIFF K1 = K2:real^N->bool` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN ASM SET_TAC[];
    REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(UNIONS K DIFF UNIONS L) DIFF K2 = K1:real^N->bool` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN ASM SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]]);;

(* A triangle minus L is connected (star-shaped from a relative interior    *)
(* point) and contains the relative interior, so it lies on exactly one    *)
(* side.                                                                     *)

let MOI_FCS_TRI_SIDE = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 R.
     moi_fcs_split K L K1 K2 /\ R IN K /\ aff_dim R = &2
     ==> ~(relative_interior R = {}) /\
         relative_interior R SUBSET R DIFF UNIONS L /\
         (R DIFF UNIONS L SUBSET K1 \/ R DIFF UNIONS L SUBSET K2) /\
         ~(R DIFF UNIONS L SUBSET K1 /\ R DIFF UNIONS L SUBSET K2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcs_split]) THEN
  SUBGOAL_THEN `compact (R:real^N->bool) /\ convex R` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(R INTER UNIONS L = R:real^N->bool)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `aff_dim (R:real^N->bool) <= &1` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior R SUBSET R DIFF UNIONS (L:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`R INTER UNIONS (L:(real^N->bool)->bool)`; `R:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_SIMP_TAC[] THEN MP_TAC(ISPEC `R:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior R:real^N->bool = {})` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim ({}:real^N->bool) = &2` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^N`) THEN
  SUBGOAL_THEN `(c:real^N) IN R DIFF UNIONS L` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `connected (R DIFF UNIONS (L:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC STARLIKE_IMP_CONNECTED THEN REWRITE_TAC[starlike] THEN
    EXISTS_TAC `c:real^N` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
    MP_TAC(ISPECL [`R:real^N->bool`; `c:real^N`; `y:real^N`]
      IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `R:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
      UNDISCH_TAC `relative_interior R SUBSET R DIFF UNIONS (L:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(c:real^N) IN R DIFF UNIONS L` THEN
      UNDISCH_TAC `(y:real^N) IN R DIFF UNIONS L` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `R DIFF UNIONS L SUBSET UNIONS K DIFF UNIONS (L:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(R:real^N->bool) SUBSET UNIONS K` MP_TAC THENL
     [ASM SET_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_CASES_TAC `(c:real^N) IN K1` THENL
     [DISJ1_TAC THEN MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN
      EXISTS_TAC `UNIONS K DIFF UNIONS (L:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISJ2_TAC THEN MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN
      EXISTS_TAC `UNIONS K DIFF UNIONS (L:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN
    UNDISCH_TAC `(c:real^N) IN R DIFF UNIONS L` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* As in pc_moi_fnd_bcollar.ml, for moi_fcs_split: triangles cover, the      *)
(* sides are unions of closed triangles, they meet in L, local triangles,    *)
(* the sides are open, closures of triangles, the side complex.              *)
(* ========================================================================= *)

(* Every point of K lies in a triangle.                                      *)

let MOI_FCS_TRI_COVER = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 x.
     moi_fcs_split K L K1 K2 /\ x IN UNIONS K
     ==> ?R. R IN K /\ aff_dim R = &2 /\ x IN R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcs_split]) THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS K` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `q:real^N->bool`] MOI_FSB_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `R:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The closure of a side is the union of its triangles.                      *)


let MOI_FCS_SIDE_UNIONS = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcs_split K L K1 K2
     ==> closure K1 =
         UNIONS {R | R IN K /\ aff_dim R = &2 /\ R DIFF UNIONS L SUBSET K1} /\
         closure K1 DIFF UNIONS L = K1 /\
         closure K1 SUBSET UNIONS K`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  ABBREV_TAC `T1 = {R:real^N->bool | R IN K /\ aff_dim R = &2 /\
                                      R DIFF UNIONS L SUBSET K1}` THEN
  SUBGOAL_THEN `UNIONS (T1:(real^N->bool)->bool) SUBSET UNIONS K` ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS (T1:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[moi_fcs_split]; EXPAND_TAC "T1" THEN SET_TAC[]];
      EXPAND_TAC "T1" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K1:real^N->bool) SUBSET UNIONS T1` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS K DIFF UNIONS L` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `x:real^N`]
      MOI_FCS_TRI_COVER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
      MOI_FCS_TRI_SIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `R:real^N->bool` THEN
      EXPAND_TAC "T1" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN
      UNDISCH_TAC `R DIFF UNIONS L SUBSET (K2:real^N->bool)` THEN
      UNDISCH_TAC `(x:real^N) IN K1` THEN UNDISCH_TAC `(x:real^N) IN R` THEN
      UNDISCH_TAC `(x:real^N) IN UNIONS K DIFF UNIONS L` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS T1 SUBSET closure (K1:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `R:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
      MOI_FCS_TRI_SIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `compact (R:real^N->bool) /\ convex R` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `R = closure (relative_interior R:real^N->bool)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED;
                   COMPACT_IMP_CLOSED];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure K1 = UNIONS (T1:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF] THEN X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [EXPAND_TAC "T1" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN SET_TAC[];
    UNDISCH_TAC `(K1:real^N->bool) SUBSET UNIONS T1` THEN
    UNDISCH_TAC `K1 UNION K2:real^N->bool = UNIONS K DIFF UNIONS L` THEN
    SET_TAC[]]);;

(* The two closures meet in UNIONS L and cover UNIONS K.                     *)

let MOI_FCS_SIDES_MEET = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcs_split K L K1 K2
     ==> closure K1 INTER closure K2 = UNIONS L /\
         closure K1 UNION closure K2 = UNIONS K /\
         closure K1 INTER K2 = {} /\ K1 INTER closure K2 = {}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SIDE_UNIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SIDE_UNIONS o
    MATCH_MP MOI_FCS_SPLIT_SYM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcs_split]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET_INTER] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `closure K1 DIFF UNIONS L = (K1:real^N->bool)` THEN
      UNDISCH_TAC `closure K2 DIFF UNIONS L = (K2:real^N->bool)` THEN
      UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN SET_TAC[];
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[UNION_SUBSET] THEN
    CONJ_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `x:real^N`]
      MOI_FCS_TRI_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
      MOI_FCS_TRI_SIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[IN_UNION] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    EXISTS_TAC `R:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    UNDISCH_TAC `closure K1 DIFF UNIONS L = (K1:real^N->bool)` THEN
    UNDISCH_TAC `K1 UNION K2:real^N->bool = UNIONS K DIFF UNIONS L` THEN
    UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN SET_TAC[];
    UNDISCH_TAC `closure K2 DIFF UNIONS L = (K2:real^N->bool)` THEN
    UNDISCH_TAC `K1 UNION K2:real^N->bool = UNIONS K DIFF UNIONS L` THEN
    UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN SET_TAC[]]);;

let MOI_FCS_LOCAL_TRIS = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 x.
     moi_fcs_split K L K1 K2 /\ x IN UNIONS K
     ==> ?e. &0 < e /\
             !y. y IN UNIONS K /\ dist(x,y) < e
                 ==> ?R. R IN K /\ aff_dim R = &2 /\ x IN R /\ y IN R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  SUBGOAL_THEN
   `closed (UNIONS {R:real^N->bool | R IN K /\ aff_dim R = &2 /\ ~(x IN R)})`
  MP_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[moi_fcs_split]; SET_TAC[]];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `y:real^N`]
    MOI_FCS_TRI_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `R:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `ball(x:real^N,e) SUBSET
               (:real^N) DIFF UNIONS {R | R IN K /\ aff_dim R = &2 /\ ~(x IN R)}` THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `R:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* A side is open in UNIONS K.                                               *)

let MOI_FCS_SIDE_OPEN = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcs_split K L K1 K2 ==> open_in (subtopology euclidean (UNIONS K)) K1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS K DIFF UNIONS L` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `x:real^N`]
    MOI_FCS_LOCAL_TRIS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?e2. &0 < e2 /\ ball(x:real^N,e2) SUBSET (:real^N) DIFF UNIONS L`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open ((:real^N) DIFF UNIONS L)` MP_TAC THENL
     [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min e1 e2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; REAL_LT_MIN] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `e1:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
    MOI_FCS_TRI_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `~((y:real^N) IN UNIONS L)` MP_TAC THENL
     [UNDISCH_TAC `ball(x:real^N,e2) SUBSET (:real^N) DIFF UNIONS L` THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `R DIFF UNIONS L SUBSET (K1:real^N->bool)` THEN
      UNDISCH_TAC `(y:real^N) IN R` THEN SET_TAC[]];
    UNDISCH_TAC `R DIFF UNIONS L SUBSET (K2:real^N->bool)` THEN
    UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN
    UNDISCH_TAC `(x:real^N) IN K1` THEN UNDISCH_TAC `(x:real^N) IN R` THEN
    UNDISCH_TAC `(x:real^N) IN UNIONS K DIFF UNIONS L` THEN SET_TAC[]]);;

(* Triangles and the closures of the sides.                                  *)

let MOI_FCS_TRI_CLOSURE_SIDE = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 R.
     moi_fcs_split K L K1 K2 /\ R IN K /\ aff_dim R = &2
     ==> (R DIFF UNIONS L SUBSET K1 ==> R SUBSET closure K1) /\
         (R SUBSET closure K1 \/ R SUBSET closure K2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!K1' K2'. moi_fcs_split K L K1' K2' /\ R DIFF UNIONS L SUBSET K1'
              ==> R SUBSET closure (K1':real^N->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SIDE_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `R:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
    MOI_FCS_TRI_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `R SUBSET closure (K1:real^N->bool)` (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `K2:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `R SUBSET closure (K2:real^N->bool)` (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `K1:real^N->bool` THEN
      ASM_SIMP_TAC[MOI_FCS_SPLIT_SYM];
      DISCH_TAC THEN
      UNDISCH_TAC `~(R DIFF UNIONS L SUBSET K1 /\
                     R DIFF UNIONS L SUBSET (K2:real^N->bool))` THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_FCS_SIDE_TRI_AT = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fcs_split K L K1 K2 /\ w IN closure K1
     ==> ?R. R IN K /\ aff_dim R = &2 /\ w IN R /\ R SUBSET closure K1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SIDE_UNIONS) THEN
  UNDISCH_TAC `(w:real^N) IN closure K1` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `R:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
    MOI_FCS_TRI_CLOSURE_SIDE) THEN
  ASM_SIMP_TAC[]);;

(* The side complex.                                                         *)

let MOI_FCS_SIDE_COMPLEX = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcs_split K L K1 K2
     ==> simplicial_subcomplex {q | q IN K /\ q SUBSET closure K1} K /\
         FINITE {q | q IN K /\ q SUBSET closure K1} /\
         lf_simplicial_complex {q | q IN K /\ q SUBSET closure K1} /\
         UNIONS {q | q IN K /\ q SUBSET closure K1} = closure K1 /\
         L SUBSET {q | q IN K /\ q SUBSET closure K1}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcs_split]) THEN
  SUBGOAL_THEN `simplicial_subcomplex {q | q IN K /\ q SUBSET closure K1}
                                      (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; IN_ELIM_THM] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:real^N->bool`] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_FACE];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `x:real^N`]
      MOI_FCS_SIDE_TRI_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `R:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `q:real^N->bool` THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS L:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* Links off L: all triangles at a vertex off L lie on its side.             *)


(* ========================================================================= *)
(* As in pc_moi_fnd_bcollar.ml: links off L, link cover, links on L.         *)
(* MOI_FCB_HULL_PAIR_OFF and MOI_FCB_DEG2_LINK are used from                 *)
(* pc_moi_fnd_bcollar directly.                                              *)
(* ========================================================================= *)

let MOI_FCS_SIDE_LINK_OFF = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fcs_split K L K1 K2 /\ w IN closure K1 /\ ~(w IN UNIONS L)
     ==> simplicial_link {q | q IN K /\ q SUBSET closure K1} w =
         simplicial_link K w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcs_split]) THEN
  SUBGOAL_THEN `(w:real^N) IN K1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`] MOI_FCS_SIDE_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `closure K1 DIFF UNIONS L = (K1:real^N->bool)` THEN
    UNDISCH_TAC `(w:real^N) IN closure K1` THEN
    UNDISCH_TAC `~((w:real^N) IN UNIONS L)` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simplicial_link; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N->bool` THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSB_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
    MOI_FCS_TRI_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [ALL_TAC;
    UNDISCH_TAC `R DIFF UNIONS L SUBSET (K2:real^N->bool)` THEN
    UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN
    UNDISCH_TAC `(w:real^N) IN K1` THEN
    UNDISCH_TAC `~((w:real^N) IN UNIONS L)` THEN
    UNDISCH_TAC `(t:real^N->bool) SUBSET R` THEN
    UNDISCH_TAC `(w:real^N) IN t` THEN SET_TAC[]] THEN
  SUBGOAL_THEN `(R:real^N->bool) SUBSET closure K1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
      MOI_FCS_TRI_CLOSURE_SIDE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^N->bool) face_of R` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N->bool) SUBSET t` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    EXISTS_TAC `R:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[FACE_OF_TRANS]]]);;

(* Links of subcomplexes.                                                    *)

(* The link of a vertex of K is covered by its links in the two sides.       *)

let MOI_FCS_LINK_COVER = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fcs_split K L K1 K2 /\ {w} IN K
     ==> simplicial_link K w SUBSET
         simplicial_link {q | q IN K /\ q SUBSET closure K1} w UNION
         simplicial_link {q | q IN K /\ q SUBSET closure K2} w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcs_split]) THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N->bool` THEN
  REWRITE_TAC[simplicial_link; IN_UNION; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSB_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t:real^N->bool) face_of R` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N->bool) SUBSET R /\ x face_of R` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS; FACE_OF_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
    MOI_FCS_TRI_CLOSURE_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_TAC o CONJUNCT2) THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL
    [ASM SET_TAC[];
     EXISTS_TAC `R:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]));;

(* Points of L in the link of K lie in the link of L (fullness).             *)

let MOI_FCS_LINK_FULL = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fcs_split K L K1 K2 /\ {w} IN K /\ w IN UNIONS L
     ==> UNIONS L INTER UNIONS (simplicial_link K w) SUBSET
         UNIONS (simplicial_link L w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcs_split]) THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN UNIONS (simplicial_link K w)` THEN
  REWRITE_TAC[IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `q INTER UNIONS L IN (L:(real^N->bool)->bool) /\
    t INTER UNIONS L IN L /\ (q INTER UNIONS L) SUBSET (t INTER UNIONS L)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(q:real^N->bool) SUBSET t` MP_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `q INTER UNIONS L:real^N->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
  EXISTS_TAC `t INTER UNIONS L:real^N->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
  MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
  EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

(* A triangle of a side at w contributes a link edge off L.                 *)


let MOI_FCS_LINK_TRI = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w R.
     moi_fcs_split K L K1 K2 /\ {w} IN K /\ w IN UNIONS L /\
     R IN K /\ aff_dim R = &2 /\ w IN R /\ R SUBSET closure K1
     ==> ?e. e IN simplicial_link {q | q IN K /\ q SUBSET closure K1} w /\
             ~(e SUBSET UNIONS L) /\ e SUBSET R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcs_split]) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`; `R:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `(e:real^N->bool) IN K /\ ~(w IN e)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(e:real^N->bool) IN simplicial_link K w` THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) SUBSET R` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `R:real^N->bool`)) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(w:real^N) INSERT e` THEN
    REWRITE_TAC[HULL_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `R:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `R INTER UNIONS L = R:real^N->bool` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[INTER_SUBSET] THEN
      SUBGOAL_THEN `convex hull ((w:real^N) INSERT e) SUBSET R INTER UNIONS L`
      MP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
       [UNDISCH_TAC `(e:real^N->bool) SUBSET UNIONS L` THEN
        UNDISCH_TAC `(e:real^N->bool) SUBSET R` THEN
        UNDISCH_TAC `(w:real^N) IN R` THEN UNDISCH_TAC `(w:real^N) IN UNIONS L` THEN
        SET_TAC[];
        MATCH_MP_TAC FACE_OF_IMP_CONVEX THEN EXISTS_TAC `R:real^N->bool` THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim (R:real^N->bool) <= &1` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]]);;



(* Links on L: the link of a side at a vertex of L is one of the two arcs   *)
(* into which the two points of link_L cut the circle link_K.                *)

let MOI_FCS_SIDE_LINK_ON = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fcs_split K L K1 K2 /\ {w} IN K /\ w IN UNIONS L
     ==> pl_ball 1 (UNIONS (simplicial_link {q | q IN K /\ q SUBSET closure K1} w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SIDES_MEET) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcs_split]) THEN
  SUBGOAL_THEN `pl_sphere 1 (UNIONS (simplicial_link K (w:real^N)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FGB_CMB2_VERTEX_INT THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (UNIONS L) (surface_boundary (K:(real^N->bool)->bool))` THEN
    UNDISCH_TAC `(w:real^N) IN UNIONS L` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^N} IN L` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT1(MATCH_MP (ISPEC `{w:real^N}` (ASSUME
      `!q:real^N->bool. q IN K ==> q INTER UNIONS L IN L /\ (q INTER UNIONS L) face_of q`))
      (ASSUME `{w:real^N} IN K`))) THEN
    SUBGOAL_THEN `{w:real^N} INTER UNIONS L = {w}` SUBST1_TAC THENL
     [UNDISCH_TAC `(w:real^N) IN UNIONS L` THEN SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `w:real^N`] MOI_FCB_DEG2_LINK) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`]
    MOI_FCS_LINK_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`]
    MOI_FCS_LINK_FULL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`]
    MOI_FCS_SIDE_TRI_AT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K2:real^N->bool`; `K1:real^N->bool`; `w:real^N`]
    MOI_FCS_SIDE_TRI_AT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_FCS_SPLIT_SYM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R2:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`; `R1:real^N->bool`]
    MOI_FCS_LINK_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K2:real^N->bool`; `K1:real^N->bool`; `w:real^N`; `R2:real^N->bool`]
    MOI_FCS_LINK_TRI) THEN
  ASM_SIMP_TAC[MOI_FCS_SPLIT_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real^N->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `A = {q:real^N->bool | q IN K /\ q SUBSET closure K1}` THEN
  ABBREV_TAC `B = {q:real^N->bool | q IN K /\ q SUBSET closure K2}` THEN
  SUBGOAL_THEN `(L:(real^N->bool)->bool) SUBSET A /\ L SUBSET B /\ A SUBSET K /\
                B SUBSET K /\ UNIONS A SUBSET closure K1 /\ UNIONS B SUBSET closure K2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    UNDISCH_TAC `UNIONS L SUBSET closure (K1:real^N->bool)` THEN
    UNDISCH_TAC `UNIONS L SUBSET closure (K2:real^N->bool)` THEN
    UNDISCH_TAC `(L:(real^N->bool)->bool) SUBSET K` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_link L (w:real^N) SUBSET simplicial_link A w /\
                simplicial_link L (w:real^N) SUBSET simplicial_link B w /\
                simplicial_link A w SUBSET simplicial_link K w /\
                simplicial_link B w SUBSET simplicial_link K w /\
                simplicial_link A w SUBSET A /\ simplicial_link B w SUBSET B /\
                simplicial_link L w SUBSET L /\ simplicial_link K w SUBSET K`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FBC_LINK_SUBSET] THEN
    REWRITE_TAC[simplicial_link] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (simplicial_link K (w:real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LINK_FINITE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `closed (UNIONS (simplicial_link A (w:real^N))) /\
    closed (UNIONS (simplicial_link B (w:real^N)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `simplicial_link K (w:real^N)` THEN ASM_REWRITE_TAC[] THEN
        NO_TAC) THEN
    X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    SUBGOAL_THEN `(r:real^N->bool) IN K` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (simplicial_link A (w:real^N)) SUBSET closure K1 /\
    UNIONS (simplicial_link B w) SUBSET closure K2 /\
    UNIONS (simplicial_link A w) SUBSET UNIONS (simplicial_link K w) /\
    UNIONS (simplicial_link B w) SUBSET UNIONS (simplicial_link K w) /\
    UNIONS (simplicial_link L w) SUBSET UNIONS (simplicial_link A w) /\
    UNIONS (simplicial_link L w) SUBSET UNIONS (simplicial_link B w) /\
    UNIONS (simplicial_link L w) SUBSET UNIONS L /\
    UNIONS (simplicial_link K w) SUBSET
      UNIONS (simplicial_link A w) UNION UNIONS (simplicial_link B w) /\
    e1 SUBSET UNIONS (simplicial_link A w) /\
    e2 SUBSET UNIONS (simplicial_link B w)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS (A:(real^N->bool)->bool)` THEN
      ASM_SIMP_TAC[SUBSET_UNIONS];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS (B:(real^N->bool)->bool)` THEN
      ASM_SIMP_TAC[SUBSET_UNIONS];
      MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `simplicial_link K (w:real^N) SUBSET
                   simplicial_link A w UNION simplicial_link B w` THEN SET_TAC[];
      UNDISCH_TAC `(e1:real^N->bool) IN simplicial_link A w` THEN SET_TAC[];
      UNDISCH_TAC `(e2:real^N->bool) IN simplicial_link B w` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (simplicial_link B (w:real^N)) INTER UNIONS (simplicial_link A w) = {p,q}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS L INTER UNIONS (simplicial_link K (w:real^N))` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `closure K1 INTER closure K2 = UNIONS (L:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `UNIONS (simplicial_link A (w:real^N)) SUBSET closure K1` THEN
      UNDISCH_TAC `UNIONS (simplicial_link B (w:real^N)) SUBSET closure K2` THEN
      UNDISCH_TAC `UNIONS (simplicial_link A (w:real^N)) SUBSET
                   UNIONS (simplicial_link K w)` THEN
      SET_TAC[];
      UNDISCH_TAC `UNIONS (simplicial_link L (w:real^N)) = {p,q}` THEN
      UNDISCH_TAC `UNIONS (simplicial_link L (w:real^N)) SUBSET
                   UNIONS (simplicial_link A w)` THEN
      UNDISCH_TAC `UNIONS (simplicial_link L (w:real^N)) SUBSET
                   UNIONS (simplicial_link B w)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 (UNIONS (simplicial_link A (w:real^N))) {p,q}`
  MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[]] THEN
  MATCH_MP_TAC MOI_S4O_CIRCLE_ARC THEN
  MAP_EVERY EXISTS_TAC [`UNIONS (simplicial_link K (w:real^N))`;
                        `UNIONS (simplicial_link B (w:real^N))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[UNION_SUBSET] THEN
    UNDISCH_TAC `UNIONS (simplicial_link K (w:real^N)) SUBSET
                 UNIONS (simplicial_link A w) UNION UNIONS (simplicial_link B w)` THEN
    SET_TAC[];
    DISCH_TAC THEN UNDISCH_TAC `~(e2 SUBSET UNIONS (L:(real^N->bool)->bool))` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `UNIONS (simplicial_link B (w:real^N)) SUBSET {p,q}` THEN
    UNDISCH_TAC `(e2:real^N->bool) SUBSET UNIONS (simplicial_link B (w:real^N))` THEN
    UNDISCH_TAC `UNIONS (simplicial_link L (w:real^N)) = {p,q}` THEN
    UNDISCH_TAC `UNIONS (simplicial_link L (w:real^N)) SUBSET UNIONS L` THEN
    SET_TAC[];
    DISCH_TAC THEN UNDISCH_TAC `~(e1 SUBSET UNIONS (L:(real^N->bool)->bool))` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `UNIONS (simplicial_link A (w:real^N)) SUBSET {p,q}` THEN
    UNDISCH_TAC `(e1:real^N->bool) SUBSET UNIONS (simplicial_link A (w:real^N))` THEN
    UNDISCH_TAC `UNIONS (simplicial_link L (w:real^N)) = {p,q}` THEN
    UNDISCH_TAC `UNIONS (simplicial_link L (w:real^N)) SUBSET UNIONS L` THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* As in pc_moi_fnd_bcollar.ml: edges in L, edges off L, the side manifold.  *)
(* ========================================================================= *)

(* Edges of K inside L have a triangle strictly on each side.                *)

let MOI_FCS_SIDE_EDGE_IN = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 e.
     moi_fcs_split K L K1 K2 /\ e IN K /\ aff_dim e = &1 /\ e SUBSET UNIONS L
     ==> ?r. r IN K /\ aff_dim r = &2 /\ e SUBSET r /\ r SUBSET closure K1 /\
             ~(r SUBSET closure K2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcs_split]) THEN
  SUBGOAL_THEN `closure K2 DIFF UNIONS L = (K2:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K2:real^N->bool`; `K1:real^N->bool`] MOI_FCS_SIDE_UNIONS) THEN
    ASM_SIMP_TAC[MOI_FCS_SPLIT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior e:real^N->bool = {})` MP_TAC THENL
   [SUBGOAL_THEN `convex (e:real^N->bool)` (fun th -> SIMP_TAC[th; RELATIVE_INTERIOR_EQ_EMPTY])
    THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim ({}:real^N->bool) = &1` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  SUBGOAL_THEN `(x:real^N) IN e` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?r:real^N->bool. r IN K /\ aff_dim r = &2 /\
                                 r DIFF UNIONS L SUBSET K1 /\ x IN r`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^N) IN closure K1` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`] MOI_FCS_SIDE_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `r:real^N->bool`]
    MOI_FCS_TRI_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `r:real^N->bool`]
    MOI_FCS_TRI_CLOSURE_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`e:real^N->bool`; `r INTER e:real^N->bool`; `e:real^N->bool`]
      SUBSET_OF_FACE_OF) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_FM3_LF_INTER];
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]];
      SET_TAC[]];
    DISCH_TAC THEN
    UNDISCH_TAC `~(relative_interior r:real^N->bool = {})` THEN REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`relative_interior r SUBSET r DIFF UNIONS (L:(real^N->bool)->bool)`;
      `r DIFF UNIONS L SUBSET (K1:real^N->bool)`;
      `(r:real^N->bool) SUBSET closure K2`;
      `closure K2 DIFF UNIONS L = (K2:real^N->bool)`;
      `K1 INTER K2:real^N->bool = {}`] THEN
    SET_TAC[]]);;

(* Edges of a side off L: all their triangles in K lie on that side.         *)

let MOI_FCS_SIDE_EDGE_OFF = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 e r.
     moi_fcs_split K L K1 K2 /\ e SUBSET closure K1 /\ ~(e SUBSET UNIONS L) /\
     r IN K /\ aff_dim r = &2 /\ e SUBSET r
     ==> r SUBSET closure K1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  SUBGOAL_THEN `closure K1 DIFF UNIONS L = (K1:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`] MOI_FCS_SIDE_UNIONS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `r:real^N->bool`]
    MOI_FCS_TRI_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `r:real^N->bool`]
    MOI_FCS_TRI_CLOSURE_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `?x:real^N. x IN e /\ ~(x IN UNIONS L)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN K1` ASSUME_TAC THENL
   [UNDISCH_TAC `closure K1 DIFF UNIONS L = (K1:real^N->bool)` THEN
    UNDISCH_TAC `(e:real^N->bool) SUBSET closure K1` THEN
    UNDISCH_TAC `(x:real^N) IN e` THEN UNDISCH_TAC `~((x:real^N) IN UNIONS L)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`r DIFF UNIONS L SUBSET (K2:real^N->bool)`; `K1 INTER K2:real^N->bool = {}`;
    `(x:real^N) IN K1`; `(x:real^N) IN e`; `~((x:real^N) IN UNIONS L)`;
    `(e:real^N->bool) SUBSET r`] THEN
  SET_TAC[]);;

(* An edge of K inside L has exactly one triangle on each side.              *)

let MOI_FCS_SIDE_EDGE_L = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 e.
     moi_fcs_split K L K1 K2 /\ e IN K /\ aff_dim e = &1 /\ e SUBSET UNIONS L
     ==> CARD {r | r IN {q | q IN K /\ q SUBSET closure K1} /\ aff_dim r = &2 /\
                   e SUBSET r} = 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcs_split]) THEN
  SUBGOAL_THEN `CARD {r | r IN K /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FGB_CMB2_EDGE_INT THEN
    SUBGOAL_THEN `?x:real^N. x IN e` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim ({}:real^N->bool) = &1` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (UNIONS L) (surface_boundary (K:(real^N->bool)->bool))` THEN
    UNDISCH_TAC `(e:real^N->bool) SUBSET UNIONS L` THEN
    UNDISCH_TAC `(x:real^N) IN e` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `e:real^N->bool`]
    MOI_FCS_SIDE_EDGE_IN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K2:real^N->bool`; `K1:real^N->bool`; `e:real^N->bool`]
    MOI_FCS_SIDE_EDGE_IN) THEN
  ASM_SIMP_TAC[MOI_FCS_SPLIT_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(r1:real^N->bool = r2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{r | r IN K /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = {r1,r2}`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];

      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{r | r IN {q | q IN K /\ q SUBSET closure K1} /\ aff_dim r = &2 /\
         (e:real^N->bool) SUBSET r} = {r1}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool` o GEN_REWRITE_RULE I [EXTENSION] o
      check (fun th -> is_eq(concl th) && rand(concl th) = `{r1:real^N->bool,r2}`)) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `r:real^N->bool = r1 \/ r = r2` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(r2 SUBSET closure (K1:real^N->bool))` THEN
      UNDISCH_TAC `(r:real^N->bool) SUBSET closure K1` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[CARD_SING]]);;

(* The side complex is a combinatorial surface with boundary L plus the      *)
(* part of the boundary of K on that side.                                    *)

let MOI_FCS_SIDE_MANIFOLD = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcs_split K L K1 K2
     ==> FINITE {q | q IN K /\ q SUBSET closure K1} /\
         combinatorial_manifold_with_boundary 2 {q | q IN K /\ q SUBSET closure K1} /\
         UNIONS {q | q IN K /\ q SUBSET closure K1} = closure K1 /\
         surface_boundary {q | q IN K /\ q SUBSET closure K1} =
         UNIONS L UNION (surface_boundary K INTER closure K1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCS_SIDE_COMPLEX) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcs_split]) THEN
  SUBGOAL_THEN `closure K1 DIFF UNIONS L = (K1:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`] MOI_FCS_SIDE_UNIONS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 2
                  {q:real^N->bool | q IN K /\ q SUBSET closure K1}`
  ASSUME_TAC THENL
   [REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `{w:real^N} IN K /\ w IN closure K1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{w:real^N} IN {q | q IN K /\ q SUBSET closure K1}` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(w:real^N) IN UNIONS L` THENL
     [DISJ2_TAC THEN MATCH_MP_TAC MOI_FCS_SIDE_LINK_ON THEN
      MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `K2:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                     `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`]
        MOI_FCS_SIDE_LINK_OFF) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `combinatorial_manifold_with_boundary 2 (K:(real^N->bool)->bool)` THEN
      REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S = {q:real^N->bool | q IN K /\ q SUBSET closure K1}` THEN
  SUBGOAL_THEN `!q:real^N->bool. q IN S <=> q IN K /\ q SUBSET closure K1`
  ASSUME_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN S /\ ~(e SUBSET UNIONS L)
        ==> {r | r IN S /\ aff_dim r = &2 /\ e SUBSET r} =
            {r | r IN K /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r}`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FCS_SIDE_EDGE_OFF THEN
    MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                          `K2:real^N->bool`; `e:real^N->bool`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [surface_boundary] THEN
    REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(e:real^N->bool) SUBSET UNIONS L` THENL
     [UNDISCH_TAC `(e:real^N->bool) SUBSET UNIONS L` THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^N->bool) IN K /\ e SUBSET closure K1` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^N->bool) SUBSET surface_boundary K` MP_TAC THENL
     [REWRITE_TAC[surface_boundary] THEN
      MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `CARD {r | r IN S /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = 1` THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `CARD:((real^N->bool)->bool)->num`)) (concl th) = false &&
        can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(e:real^N->bool) SUBSET closure K1` THEN SET_TAC[]];
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `?e:real^N->bool. e IN L /\ aff_dim e = &1 /\ x IN e`
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `~(aff_dim (s:real^N->bool) = -- &1)` ASSUME_TAC THENL
         [REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `aff_dim (s:real^N->bool) = &0 \/ aff_dim s = &1` MP_TAC THENL
         [MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN
          SUBGOAL_THEN `aff_dim (s:real^N->bool) <= &1` MP_TAC THENL
           [ASM_SIMP_TAC[]; ALL_TAC] THEN
          UNDISCH_TAC `~(aff_dim (s:real^N->bool) = -- &1)` THEN INT_ARITH_TAC;
          ALL_TAC] THEN
        STRIP_TAC THENL [ALL_TAC; EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]] THEN
        UNDISCH_TAC `aff_dim (s:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
        DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
        SUBGOAL_THEN `a:real^N = x` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `~({e | e IN L /\ aff_dim e = &1 /\ (x:real^N) IN e} = {})` MP_TAC THENL
         [DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
            is_forall(concl th) &&
            can (find_term ((=) `CARD:((real^N->bool)->bool)->num`)) (concl th))) THEN
          ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(e:real^N->bool) IN K /\ e SUBSET UNIONS L /\ e IN S` STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "S" THEN ASM SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[surface_boundary; IN_UNIONS] THEN EXISTS_TAC `e:real^N->bool` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                     `K1:real^N->bool`; `K2:real^N->bool`; `e:real^N->bool`]
        MOI_FCS_SIDE_EDGE_L) THEN
      ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      UNDISCH_TAC `(x:real^N) IN surface_boundary K` THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [surface_boundary] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~((x:real^N) IN UNIONS L)` ASSUME_TAC THENL
       [UNDISCH_TAC `DISJOINT (UNIONS L) (surface_boundary (K:(real^N->bool)->bool))` THEN
        REWRITE_TAC[surface_boundary] THEN
        UNDISCH_TAC `(x:real^N) IN e` THEN
        UNDISCH_TAC `CARD {r | r IN K /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = 1` THEN
        UNDISCH_TAC `aff_dim (e:real^N->bool) = &1` THEN
        UNDISCH_TAC `(e:real^N->bool) IN K` THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `?r:real^N->bool. r IN K /\ aff_dim r = &2 /\ e SUBSET r`
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `~({r | r IN K /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = {})`
        MP_TAC THENL
         [DISCH_TAC THEN
          UNDISCH_TAC `CARD {r | r IN K /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = 1` THEN
          ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM]];
        ALL_TAC] THEN

      SUBGOAL_THEN `(r:real^N->bool) SUBSET closure K1` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_FCS_SIDE_EDGE_OFF THEN
        MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                              `K2:real^N->bool`; `{x:real^N}`] THEN
        ASM_REWRITE_TAC[SING_SUBSET] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(e:real^N->bool) IN S /\ ~(e SUBSET UNIONS L)` STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `CARD {r | r IN S /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = 1`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
          (CONJ (ASSUME `(e:real^N->bool) IN S`)
                (ASSUME `~((e:real^N->bool) SUBSET UNIONS L)`))]) THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[surface_boundary; IN_UNIONS] THEN EXISTS_TAC `e:real^N->bool` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);;

(* ========================================================================= *)
(* MOI_FCS_CLOPEN_SIDES, and the bridge MOI_FCS_SPLIT_FCB from bcollar's     *)
(* two-component splits (components of the complement are relatively closed, *)
(* so with two of them each is also relatively open).                        *)
(* ========================================================================= *)

let MOI_FCS_CLOPEN_SIDES = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     FINITE K /\ combinatorial_manifold_with_boundary 2 K /\
     simplicial_subcomplex L K /\ (!s. s IN L ==> aff_dim s <= &1) /\
     (!v. {v} IN L ==> CARD {e | e IN L /\ aff_dim e = &1 /\ v IN e} = 2) /\
     (!q. q IN K ==> q INTER UNIONS L IN L /\ (q INTER UNIONS L) face_of q) /\
     DISJOINT (UNIONS L) (surface_boundary K) /\
     K1 UNION K2 = UNIONS K DIFF UNIONS L /\ DISJOINT K1 K2 /\
     open_in (subtopology euclidean (UNIONS K DIFF UNIONS L)) K1 /\
     open_in (subtopology euclidean (UNIONS K DIFF UNIONS L)) K2 /\
     UNIONS L SUBSET closure K1 /\ UNIONS L SUBSET closure K2
     ==> FINITE {q | q IN K /\ q SUBSET closure K1} /\
         combinatorial_manifold_with_boundary 2 {q | q IN K /\ q SUBSET closure K1} /\
         UNIONS {q | q IN K /\ q SUBSET closure K1} = closure K1 /\
         surface_boundary {q | q IN K /\ q SUBSET closure K1} =
         UNIONS L UNION (surface_boundary K INTER closure K1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_FCS_SIDE_MANIFOLD THEN
  EXISTS_TAC `K2:real^N->bool` THEN ASM_REWRITE_TAC[moi_fcs_split]);;

let MOI_FCS_SPLIT_FCB = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcb_split K L K1 K2 ==> moi_fcs_split K L K1 K2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
  SUBGOAL_THEN
   `closed_in (subtopology euclidean (UNIONS K DIFF UNIONS L)) (K1:real^N->bool) /\
    closed_in (subtopology euclidean (UNIONS K DIFF UNIONS L)) (K2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_COMPONENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_fcs_split] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    SUBGOAL_THEN `K1 = (UNIONS K DIFF UNIONS L) DIFF (K2:real^N->bool)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    SUBGOAL_THEN `K2 = (UNIONS K DIFF UNIONS L) DIFF (K1:real^N->bool)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV]]);;

