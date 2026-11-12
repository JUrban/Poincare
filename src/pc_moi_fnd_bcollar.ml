(* ========================================================================= *)
(* pc_moi_fnd_bcollar: collars of the boundary of combinatorial surfaces.    *)
(* Main theorem:                                                             *)
(*   MOI_FCB_BOUNDARY_COLLAR_2 : for FINITE c, combinatorial 2-manifold with *)
(*   boundary, and v open in |c| around the boundary, a PL collar            *)
(*   p : surface_boundary c x [0,1] -> w, w inside v, the boundary in the    *)
(*   interior of w (relative to |c|), p(x,0) = x.                            *)
(* Route: cap the surface (pc_moi_fnd_cap), split the derived neighbourhood  *)
(* of each lifted boundary component (pc_moi_fnd_nb2) into the lifted side   *)
(* and the cone side, analyse the sides (two-sided splits), show by the      *)
(* Euler count and the planar-surface theorem (SURFACE_EULER_PLANAR of       *)
(* pc_moi_fnd_surfb, at the type of the cap) that the lifted side is an      *)
(* annulus with ends, take the end collar (psi of pc_moi_fnd_plst), carry    *)
(* it back by fstcart and glue over the components.                          *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_cap.ml";;
needs "src/pc_moi_fnd_nb2.ml";;
needs "src/pc_moi_fnd_plst.ml";;
needs "src/pc_moi_fnd_surfb.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Two-sided splits of a combinatorial surface with boundary K along a full  *)
(* subcomplex L of dimension at most 1 with all vertex degrees 2, disjoint   *)
(* from the boundary, whose complement has exactly two components K1, K2,    *)
(* each accumulating on L (moi_fcb_split; the 2D analogue of moi_fbc_split   *)
(* in pc_moi_fnd_bicol).  The closure of each side carries a combinatorial   *)
(* surface with boundary, whose boundary is L together with the part of the  *)
(* boundary of K on that side.                                               *)
(* ========================================================================= *)

let moi_fcb_split = new_definition
 `moi_fcb_split (K:(real^N->bool)->bool) L K1 K2 <=>
    FINITE K /\ combinatorial_manifold_with_boundary 2 K /\
    simplicial_subcomplex L K /\ (!s. s IN L ==> aff_dim s <= &1) /\
    (!v. {v} IN L ==> CARD {e | e IN L /\ aff_dim e = &1 /\ v IN e} = 2) /\
    (!q. q IN K ==> q INTER UNIONS L IN L /\ (q INTER UNIONS L) face_of q) /\
    DISJOINT (UNIONS L) (surface_boundary K) /\
    components (UNIONS K DIFF UNIONS L) = {K1,K2} /\ ~(K1 = K2) /\
    UNIONS L SUBSET closure K1 /\ UNIONS L SUBSET closure K2`;;

let MOI_FCB_SPLIT_SYM = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcb_split K L K1 K2 ==> moi_fcb_split K L K2 K1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fcb_split] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_FCB_SPLIT_FACTS = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcb_split K L K1 K2
     ==> lf_simplicial_complex K /\ simplicial_complex K /\
         FINITE L /\ simplicial_complex L /\ lf_simplicial_complex L /\
         L SUBSET K /\ UNIONS L SUBSET UNIONS K /\
         (!s. s IN L ==> aff_dim s <= &1) /\
         (!s. s IN K ==> compact s /\ convex s) /\
         (!s. s IN K ==> aff_dim s <= &2) /\
         K1 IN components (UNIONS K DIFF UNIONS L) /\
         K2 IN components (UNIONS K DIFF UNIONS L) /\
         K1 INTER K2 = {} /\
         K1 UNION K2 = UNIONS K DIFF UNIONS L /\
         compact (UNIONS K) /\ compact (UNIONS L)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fcb_split] THEN STRIP_TAC THEN
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
  ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF; IN_INSERT] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[COMPONENTS_NONOVERLAP; IN_INSERT];
    FIRST_X_ASSUM(MP_TAC o AP_TERM `UNIONS:((real^N->bool)->bool)->real^N->bool` o
      check (fun th -> is_eq(concl th) &&
        (try fst(dest_const(rator(lhs(concl th)))) = "components"
         with Failure _ -> false))) THEN
    REWRITE_TAC[GSYM UNIONS_COMPONENTS; UNIONS_2] THEN MESON_TAC[];
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]]);;

(* A triangle minus L is connected (star-shaped from a relative interior    *)
(* point) and contains the relative interior, so it lies on exactly one    *)
(* side.                                                                     *)

let MOI_FCB_TRI_SIDE = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 R.
     moi_fcb_split K L K1 K2 /\ R IN K /\ aff_dim R = &2
     ==> ~(relative_interior R = {}) /\
         relative_interior R SUBSET R DIFF UNIONS L /\
         (R DIFF UNIONS L SUBSET K1 \/ R DIFF UNIONS L SUBSET K2) /\
         ~(R DIFF UNIONS L SUBSET K1 /\ R DIFF UNIONS L SUBSET K2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
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
  SUBGOAL_THEN `R DIFF UNIONS L SUBSET
                connected_component (UNIONS K DIFF UNIONS L) (c:real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC STARLIKE_IMP_CONNECTED THEN REWRITE_TAC[starlike] THEN
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
      SUBGOAL_THEN `(R:real^N->bool) SUBSET UNIONS K` MP_TAC THENL
       [ASM SET_TAC[]; SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_component (UNIONS K DIFF UNIONS L) (c:real^N) = K1 \/
                connected_component (UNIONS K DIFF UNIONS L) c = K2` MP_TAC THENL
   [SUBGOAL_THEN `connected_component (UNIONS K DIFF UNIONS L) (c:real^N) IN
                  components (UNIONS K DIFF UNIONS (L:(real^N->bool)->bool))` MP_TAC THENL
     [REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `c:real^N` THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `(R:real^N->bool) SUBSET UNIONS K` MP_TAC THENL
       [ASM SET_TAC[]; UNDISCH_TAC `(c:real^N) IN R DIFF UNIONS L` THEN SET_TAC[]];
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN
  UNDISCH_TAC `(c:real^N) IN R DIFF UNIONS L` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "SUBSET" &&
        lhand(concl th) = `R DIFF UNIONS (L:(real^N->bool)->bool)`
    with Failure _ -> false)) THEN
  SET_TAC[]);;

(* Every point of K lies in a triangle.                                      *)

let MOI_FCB_TRI_COVER = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 x.
     moi_fcb_split K L K1 K2 /\ x IN UNIONS K
     ==> ?R. R IN K /\ aff_dim R = &2 /\ x IN R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS K` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `q:real^N->bool`] MOI_FSB_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `R:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The closure of a side is the union of its triangles.                      *)


let MOI_FCB_SIDE_UNIONS = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcb_split K L K1 K2
     ==> closure K1 =
         UNIONS {R | R IN K /\ aff_dim R = &2 /\ R DIFF UNIONS L SUBSET K1} /\
         closure K1 DIFF UNIONS L = K1 /\
         closure K1 SUBSET UNIONS K`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  ABBREV_TAC `T1 = {R:real^N->bool | R IN K /\ aff_dim R = &2 /\
                                      R DIFF UNIONS L SUBSET K1}` THEN
  SUBGOAL_THEN `UNIONS (T1:(real^N->bool)->bool) SUBSET UNIONS K` ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS (T1:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[moi_fcb_split]; EXPAND_TAC "T1" THEN SET_TAC[]];
      EXPAND_TAC "T1" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K1:real^N->bool) SUBSET UNIONS T1` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS K DIFF UNIONS L` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `x:real^N`]
      MOI_FCB_TRI_COVER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
      MOI_FCB_TRI_SIDE) THEN
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
      MOI_FCB_TRI_SIDE) THEN
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

let MOI_FCB_SIDES_MEET = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcb_split K L K1 K2
     ==> closure K1 INTER closure K2 = UNIONS L /\
         closure K1 UNION closure K2 = UNIONS K /\
         closure K1 INTER K2 = {} /\ K1 INTER closure K2 = {}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SIDE_UNIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SIDE_UNIONS o
    MATCH_MP MOI_FCB_SPLIT_SYM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
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
      MOI_FCB_TRI_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
      MOI_FCB_TRI_SIDE) THEN
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

let MOI_FCB_LOCAL_TRIS = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 x.
     moi_fcb_split K L K1 K2 /\ x IN UNIONS K
     ==> ?e. &0 < e /\
             !y. y IN UNIONS K /\ dist(x,y) < e
                 ==> ?R. R IN K /\ aff_dim R = &2 /\ x IN R /\ y IN R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  SUBGOAL_THEN
   `closed (UNIONS {R:real^N->bool | R IN K /\ aff_dim R = &2 /\ ~(x IN R)})`
  MP_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[moi_fcb_split]; SET_TAC[]];
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
    MOI_FCB_TRI_COVER) THEN
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

let MOI_FCB_SIDE_OPEN = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcb_split K L K1 K2 ==> open_in (subtopology euclidean (UNIONS K)) K1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS K DIFF UNIONS L` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `x:real^N`]
    MOI_FCB_LOCAL_TRIS) THEN
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
    MOI_FCB_TRI_SIDE) THEN
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

let MOI_FCB_TRI_CLOSURE_SIDE = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 R.
     moi_fcb_split K L K1 K2 /\ R IN K /\ aff_dim R = &2
     ==> (R DIFF UNIONS L SUBSET K1 ==> R SUBSET closure K1) /\
         (R SUBSET closure K1 \/ R SUBSET closure K2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!K1' K2'. moi_fcb_split K L K1' K2' /\ R DIFF UNIONS L SUBSET K1'
              ==> R SUBSET closure (K1':real^N->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SIDE_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `R:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
    MOI_FCB_TRI_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `R SUBSET closure (K1:real^N->bool)` (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `K2:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `R SUBSET closure (K2:real^N->bool)` (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `K1:real^N->bool` THEN
      ASM_SIMP_TAC[MOI_FCB_SPLIT_SYM];
      DISCH_TAC THEN
      UNDISCH_TAC `~(R DIFF UNIONS L SUBSET K1 /\
                     R DIFF UNIONS L SUBSET (K2:real^N->bool))` THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_FCB_SIDE_TRI_AT = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fcb_split K L K1 K2 /\ w IN closure K1
     ==> ?R. R IN K /\ aff_dim R = &2 /\ w IN R /\ R SUBSET closure K1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SIDE_UNIONS) THEN
  UNDISCH_TAC `(w:real^N) IN closure K1` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `R:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
    MOI_FCB_TRI_CLOSURE_SIDE) THEN
  ASM_SIMP_TAC[]);;

(* The side complex.                                                         *)

let MOI_FCB_SIDE_COMPLEX = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcb_split K L K1 K2
     ==> simplicial_subcomplex {q | q IN K /\ q SUBSET closure K1} K /\
         FINITE {q | q IN K /\ q SUBSET closure K1} /\
         lf_simplicial_complex {q | q IN K /\ q SUBSET closure K1} /\
         UNIONS {q | q IN K /\ q SUBSET closure K1} = closure K1 /\
         L SUBSET {q | q IN K /\ q SUBSET closure K1}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
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
      MOI_FCB_SIDE_TRI_AT) THEN
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

let MOI_FCB_SIDE_LINK_OFF = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fcb_split K L K1 K2 /\ w IN closure K1 /\ ~(w IN UNIONS L)
     ==> simplicial_link {q | q IN K /\ q SUBSET closure K1} w =
         simplicial_link K w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
  SUBGOAL_THEN `(w:real^N) IN K1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`] MOI_FCB_SIDE_UNIONS) THEN
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
    MOI_FCB_TRI_SIDE) THEN
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
      MOI_FCB_TRI_CLOSURE_SIDE) THEN
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

let MOI_FCB_LINK_COVER = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fcb_split K L K1 K2 /\ {w} IN K
     ==> simplicial_link K w SUBSET
         simplicial_link {q | q IN K /\ q SUBSET closure K1} w UNION
         simplicial_link {q | q IN K /\ q SUBSET closure K2} w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
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
    MOI_FCB_TRI_CLOSURE_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_TAC o CONJUNCT2) THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL
    [ASM SET_TAC[];
     EXISTS_TAC `R:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]));;

(* Points of L in the link of K lie in the link of L (fullness).             *)

let MOI_FCB_LINK_FULL = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fcb_split K L K1 K2 /\ {w} IN K /\ w IN UNIONS L
     ==> UNIONS L INTER UNIONS (simplicial_link K w) SUBSET
         UNIONS (simplicial_link L w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
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


let MOI_FCB_LINK_TRI = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w R.
     moi_fcb_split K L K1 K2 /\ {w} IN K /\ w IN UNIONS L /\
     R IN K /\ aff_dim R = &2 /\ w IN R /\ R SUBSET closure K1
     ==> ?e. e IN simplicial_link {q | q IN K /\ q SUBSET closure K1} w /\
             ~(e SUBSET UNIONS L) /\ e SUBSET R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
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



(* A vertex of degree 2 in a complex of dimension at most 1 has a link of   *)
(* two points.                                                               *)

let MOI_FCB_HULL_PAIR_OFF = prove
 (`!d w a (y:real^N). ~(w IN d) /\ d SUBSET {w,a} /\ y IN convex hull d ==> y = a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `d SUBSET {a:real^N}` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `convex:(real^N->bool)->bool` HULL_MONO)) THEN
  REWRITE_TAC[CONVEX_HULL_SING] THEN ASM SET_TAC[]);;

let MOI_FCB_DEG2_LINK = prove
 (`!(L:(real^N->bool)->bool) w.
     simplicial_complex L /\ (!s. s IN L ==> aff_dim s <= &1) /\ {w} IN L /\
     CARD {e | e IN L /\ aff_dim e = &1 /\ w IN e} = 2
     ==> ?p q. ~(p = q) /\ UNIONS (simplicial_link L w) = {p,q}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{e | e IN L /\ aff_dim e = &1 /\ (w:real^N) IN e} HAS_SIZE 2` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE] THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^N->bool` (X_CHOOSE_THEN `e2:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o GEN_REWRITE_RULE I [EXTENSION])))) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(e1:real^N->bool) IN L /\ aff_dim e1 = &1 /\ (w:real^N) IN e1 /\
                (e2:real^N->bool) IN L /\ aff_dim e2 = &1 /\ w IN e2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e1:real^N->bool`; `w:real^N`]
    MOI_FSB_EDGE_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e2:real^N->bool`; `w:real^N`]
    MOI_FSB_EDGE_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`] THEN CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_UNIONS; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `~(aff_dim (t:real^N->bool) = -- &1)` ASSUME_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim (t:real^N->bool) = &0 \/ aff_dim t = &1` MP_TAC THENL
     [MP_TAC(ISPEC `t:real^N->bool` AFF_DIM_GE) THEN
      SUBGOAL_THEN `aff_dim (t:real^N->bool) <= &1` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(aff_dim (t:real^N->bool) = -- &1)` THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `aff_dim (t:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `(s:real^N->bool) face_of {a:real^N}` THEN
      DISCH_THEN(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
      UNDISCH_TAC `(w:real^N) IN {a}` THEN UNDISCH_TAC `~((w:real^N) IN s)` THEN
      UNDISCH_TAC `(y:real^N) IN s` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `t = convex hull {w:real^N,p} \/ t = convex hull {w,q}` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "face_of" (concl th) &&
      lhand(concl th) = `s:real^N->bool`)) THEN
    SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    SUBGOAL_THEN `~((w:real^N) IN d)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((w:real^N) IN convex hull d)` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FCB_HULL_PAIR_OFF THEN
    MAP_EVERY EXISTS_TAC [`d:real^N->bool`; `w:real^N`] THEN ASM_REWRITE_TAC[]);
    STRIP_TAC THENL

     [EXISTS_TAC `{p:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
      EXISTS_TAC `{q:real^N}` THEN ASM_REWRITE_TAC[IN_SING]]]);;

(* Links on L: the link of a side at a vertex of L is one of the two arcs   *)
(* into which the two points of link_L cut the circle link_K.                *)

let MOI_FCB_SIDE_LINK_ON = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fcb_split K L K1 K2 /\ {w} IN K /\ w IN UNIONS L
     ==> pl_ball 1 (UNIONS (simplicial_link {q | q IN K /\ q SUBSET closure K1} w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SIDES_MEET) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
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
    MOI_FCB_LINK_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`]
    MOI_FCB_LINK_FULL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`]
    MOI_FCB_SIDE_TRI_AT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K2:real^N->bool`; `K1:real^N->bool`; `w:real^N`]
    MOI_FCB_SIDE_TRI_AT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_FCB_SPLIT_SYM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R2:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`; `R1:real^N->bool`]
    MOI_FCB_LINK_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K2:real^N->bool`; `K1:real^N->bool`; `w:real^N`; `R2:real^N->bool`]
    MOI_FCB_LINK_TRI) THEN
  ASM_SIMP_TAC[MOI_FCB_SPLIT_SYM] THEN
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


(* Edges of K inside L have a triangle strictly on each side.                *)

let MOI_FCB_SIDE_EDGE_IN = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 e.
     moi_fcb_split K L K1 K2 /\ e IN K /\ aff_dim e = &1 /\ e SUBSET UNIONS L
     ==> ?r. r IN K /\ aff_dim r = &2 /\ e SUBSET r /\ r SUBSET closure K1 /\
             ~(r SUBSET closure K2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
  SUBGOAL_THEN `closure K2 DIFF UNIONS L = (K2:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K2:real^N->bool`; `K1:real^N->bool`] MOI_FCB_SIDE_UNIONS) THEN
    ASM_SIMP_TAC[MOI_FCB_SPLIT_SYM];
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
                   `K1:real^N->bool`; `K2:real^N->bool`] MOI_FCB_SIDE_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `r:real^N->bool`]
    MOI_FCB_TRI_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `r:real^N->bool`]
    MOI_FCB_TRI_CLOSURE_SIDE) THEN
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

let MOI_FCB_SIDE_EDGE_OFF = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 e r.
     moi_fcb_split K L K1 K2 /\ e SUBSET closure K1 /\ ~(e SUBSET UNIONS L) /\
     r IN K /\ aff_dim r = &2 /\ e SUBSET r
     ==> r SUBSET closure K1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  SUBGOAL_THEN `closure K1 DIFF UNIONS L = (K1:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`] MOI_FCB_SIDE_UNIONS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `r:real^N->bool`]
    MOI_FCB_TRI_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `r:real^N->bool`]
    MOI_FCB_TRI_CLOSURE_SIDE) THEN
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

let MOI_FCB_SIDE_EDGE_L = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 e.
     moi_fcb_split K L K1 K2 /\ e IN K /\ aff_dim e = &1 /\ e SUBSET UNIONS L
     ==> CARD {r | r IN {q | q IN K /\ q SUBSET closure K1} /\ aff_dim r = &2 /\
                   e SUBSET r} = 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
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
    MOI_FCB_SIDE_EDGE_IN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K2:real^N->bool`; `K1:real^N->bool`; `e:real^N->bool`]
    MOI_FCB_SIDE_EDGE_IN) THEN
  ASM_SIMP_TAC[MOI_FCB_SPLIT_SYM] THEN
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

let MOI_FCB_SIDE_MANIFOLD = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcb_split K L K1 K2
     ==> FINITE {q | q IN K /\ q SUBSET closure K1} /\
         combinatorial_manifold_with_boundary 2 {q | q IN K /\ q SUBSET closure K1} /\
         UNIONS {q | q IN K /\ q SUBSET closure K1} = closure K1 /\
         surface_boundary {q | q IN K /\ q SUBSET closure K1} =
         UNIONS L UNION (surface_boundary K INTER closure K1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SIDE_COMPLEX) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
  SUBGOAL_THEN `closure K1 DIFF UNIONS L = (K1:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`] MOI_FCB_SIDE_UNIONS) THEN
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
     [DISJ2_TAC THEN MATCH_MP_TAC MOI_FCB_SIDE_LINK_ON THEN
      MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `K2:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                     `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`]
        MOI_FCB_SIDE_LINK_OFF) THEN
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
    MATCH_MP_TAC MOI_FCB_SIDE_EDGE_OFF THEN
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
        MOI_FCB_SIDE_EDGE_L) THEN
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
       [MATCH_MP_TAC MOI_FCB_SIDE_EDGE_OFF THEN
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
(* Collars of the ends of a PL annulus with ends (via the map psi of         *)
(* pc_moi_fnd_plst, a PL product structure of the square annulus), and the   *)
(* planar-surface theorem in the form needed here: a planar surface with chi *)
(* = 0 and two boundary components is an annulus whose ends are its boundary *)
(* components, so each boundary component has a PL collar.                   *)
(* ========================================================================= *)

(* The map psi of plst on the two boundary squares of the square annulus.   *)

let MOI_FCB_PSI_SQ = prove
 (`!u:real^2.
     u IN moi_fps_sq
     ==> moi_fps_psi u = pastecart u (lift(&1)) /\
         moi_fps_psi (&2 % u) = pastecart u (lift(&2))`,
  GEN_TAC THEN REWRITE_TAC[MOI_FPS_SQ] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_fps_psi; moi_fps_pr; moi_fps_pt; moi_fps_pl; moi_fps_pb; moi_fps_w;
              VECTOR_MUL_COMPONENT] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[PASTECART_INJ; LIFT_EQ] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  ASM_REAL_ARITH_TAC);;

(* The outer boundary square.                                                 *)

let MOI_FCB_RF2 = prove
 (`!x:real^2.
     x IN relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]) <=>
     max (abs(x$1)) (abs(x$2)) = &2`,
  GEN_TAC THEN
  MP_TAC(SPEC `&2` MOI_FN2_RF_SQUARE) THEN REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* Affine bijections are PL homeomorphisms onto the image.                    *)

let MOI_FCB_AFFINE_PLH = prove
 (`!(s:real^M->bool) (l:real^M->real^M) l' y.
     locally_polyhedral s /\ linear l /\ linear l' /\
     (!x. l'(l x) = x) /\ (!x. l(l' x) = x)
     ==> pl_homeomorphism (s,IMAGE (\x. l x + y) s)
                          ((\x. l x + y),(\z. l' z + --(l' y)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  ASM_SIMP_TAC[PL_MAP_ON_AFFINE] THEN
  REWRITE_TAC[homeomorphism] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST;
               FORALL_IN_IMAGE] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_NEG;
               VECTOR_ARITH `(a + b) + --b:real^N = a`;
               VECTOR_ARITH `(a + --b) + b:real^N = a`] THEN
  REWRITE_TAC[IMAGE_ID]);;

(* End collars of a PL annulus with ends: both ends have PL collars whose    *)
(* image is the whole annulus.                                                *)

let MOI_FCB_ANN_SETUP = prove
 (`!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> ?f g phi.
           pl_homeomorphism (moi_fps_ann,a) (f,g) /\
           j0 = IMAGE f moi_fps_sq /\
           j1 = IMAGE f (relative_frontier
                           (interval[--vector[&2;&2]:real^2,vector[&2;&2]])) /\
           pl_homeomorphism (moi_fps_sq PCROSS interval[lift(&1),lift(&2)],moi_fps_ann)
                            (phi,moi_fps_psi) /\
           (!u. u IN moi_fps_ann ==> phi(moi_fps_psi u) = u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends] THEN
  REWRITE_TAC[GSYM moi_fps_ann] THEN
  REWRITE_TAC[GSYM MOI_FPS_VEC1_2] THEN REWRITE_TAC[GSYM moi_fps_sq] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  X_CHOOSE_TAC `phi:real^(2,1)finite_sum->real^2` MOI_FPS_PSI_PLH THEN
  MAP_EVERY EXISTS_TAC [`f:real^2->real^N`; `g:real^N->real^2`;
                        `phi:real^(2,1)finite_sum->real^2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
    ASM_MESON_TAC[]]);;

let MOI_FCB_SQ_ANN = prove
 (`moi_fps_sq SUBSET moi_fps_ann /\
   relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]) SUBSET
   moi_fps_ann /\
   locally_polyhedral moi_fps_sq /\
   locally_polyhedral (moi_fps_sq PCROSS interval[vec 0:real^1,vec 1])`,
  REWRITE_TAC[SUBSET; MOI_FPS_SQ; MOI_FPS_ANN; MOI_FCB_RF2] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THENL
   [REWRITE_TAC[MOI_FPS_SQ_PL_POLYHEDRON];
    MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN
    REWRITE_TAC[MOI_FPS_SQ_PL_POLYHEDRON] THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_INTERVAL]]);;

let MOI_FCB_SQ_SHIFT = prove
 (`IMAGE (\x:real^(2,1)finite_sum. x + pastecart (vec 0) (lift(&1)))
         (moi_fps_sq PCROSS interval[vec 0:real^1,vec 1]) =
   moi_fps_sq PCROSS interval[lift(&1),lift(&2)]`,
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[FORALL_PASTECART; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              PASTECART_ADD; PASTECART_INJ; VECTOR_ADD_RID] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `t:real^1`] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^1` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(b:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; LIFT_DROP; DROP_VEC] THEN REAL_ARITH_TAC;
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`u:real^2`; `t - lift(&1)`] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `t:real^1 = (t - a) + a`] THEN
    UNDISCH_TAC `(t:real^1) IN interval[lift(&1),lift(&2)]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; LIFT_DROP; DROP_VEC] THEN REAL_ARITH_TAC]);;

let MOI_FCB_ANN_COLLAR0 = prove
 (`!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> ?p q. pl_homeomorphism (j0 PCROSS interval[vec 0:real^1,vec 1],a) (p,q) /\
               !x. x IN j0 ==> p(pastecart x (vec 0)) = x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_FCB_ANN_SETUP) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    (X_CHOOSE_THEN `phi:real^(2,1)finite_sum->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_homeomorphism (j0,moi_fps_sq) (g:real^N->real^2,f)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FPS_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`moi_fps_ann`; `a:real^N->bool`] THEN
    ASM_REWRITE_TAC[MOI_FCB_SQ_ANN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j0:real^N->bool`; `moi_fps_sq`; `g:real^N->real^2`;
                 `f:real^2->real^N`; `interval[vec 0:real^1,vec 1]`]
    MOI_FCL_PLH_PCROSS_ID) THEN
  ASM_REWRITE_TAC[POLYTOPE_INTERVAL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_fps_sq PCROSS interval[vec 0:real^1,vec 1]`;
                 `\x:real^(2,1)finite_sum. x`; `\x:real^(2,1)finite_sum. x`;
                 `pastecart (vec 0:real^2) (lift(&1))`] MOI_FCB_AFFINE_PLH) THEN
  REWRITE_TAC[LINEAR_ID; MOI_FCB_SQ_ANN; MOI_FCB_SQ_SHIFT] THEN DISCH_TAC THEN
  EXISTS_TAC `(f:real^2->real^N) o (phi:real^(2,1)finite_sum->real^2) o
              (\x:real^(2,1)finite_sum. x + pastecart (vec 0) (lift(&1))) o
              (\z:real^(N,1)finite_sum. pastecart ((g:real^N->real^2) (fstcart z))
                                                  (sndcart z))` THEN
  EXISTS_TAC `(((\z:real^(2,1)finite_sum. pastecart ((f:real^2->real^N) (fstcart z))
                                                     (sndcart z)) o
                (\x:real^(2,1)finite_sum. x + --(pastecart (vec 0) (lift(&1))))) o
               moi_fps_psi) o (g:real^N->real^2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_fps_ann` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `moi_fps_sq PCROSS interval[lift(&1),lift(&2)]` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `moi_fps_sq PCROSS interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_ADD;
              VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
  SUBGOAL_THEN `(g:real^N->real^2) x IN moi_fps_sq /\ (f:real^2->real^N)(g x) = x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (j0,moi_fps_sq) (g:real^N->real^2,f)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(CONJUNCT1(MATCH_MP MOI_FCB_PSI_SQ th))]) THEN
  SUBGOAL_THEN `(g:real^N->real^2) x IN moi_fps_ann` (fun th -> ASM_SIMP_TAC[th]) THEN
  ASM_MESON_TAC[MOI_FCB_SQ_ANN; SUBSET]);;

let MOI_FCB_RF2_SHIFT = prove
 (`IMAGE (\x:real^(2,1)finite_sum.
            pastecart (inv(&2) % fstcart x) (--(sndcart x)) + pastecart (vec 0) (lift(&2)))
         (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]) PCROSS
          interval[vec 0:real^1,vec 1]) =
   moi_fps_sq PCROSS interval[lift(&1),lift(&2)]`,
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[FORALL_PASTECART; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART;
              PASTECART_ADD; PASTECART_INJ; VECTOR_ADD_RID] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `t:real^1`] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^1` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(a:real^2) IN relative_frontier
                     (interval[--vector[&2;&2],vector[&2;&2]])` THEN
      REWRITE_TAC[MOI_FCB_RF2; MOI_FPS_SQ; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(b:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_NEG; LIFT_DROP; DROP_VEC] THEN
      REAL_ARITH_TAC];
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`&2 % u:real^2`; `lift(&2) - t`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH `t:real^1 = --(a - t) + a`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(u:real^2) IN moi_fps_sq` THEN
      REWRITE_TAC[MOI_FCB_RF2; MOI_FPS_SQ; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(t:real^1) IN interval[lift(&1),lift(&2)]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; LIFT_DROP; DROP_VEC] THEN REAL_ARITH_TAC]]);;

let MOI_FCB_ANN_COLLAR1 = prove
 (`!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> ?p q. pl_homeomorphism (j1 PCROSS interval[vec 0:real^1,vec 1],a) (p,q) /\
               !x. x IN j1 ==> p(pastecart x (vec 0)) = x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_FCB_ANN_SETUP) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    (X_CHOOSE_THEN `phi:real^(2,1)finite_sum->real^2` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `Q2 = relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]])` THEN
  SUBGOAL_THEN `Q2 SUBSET moi_fps_ann /\ pl_polyhedron (Q2:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q2" THEN REWRITE_TAC[MOI_FCB_SQ_ANN] THEN
    MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
    REWRITE_TAC[POLYTOPE_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (j1,Q2) (g:real^N->real^2,f)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FPS_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`moi_fps_ann`; `a:real^N->bool`] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j1:real^N->bool`; `Q2:real^2->bool`; `g:real^N->real^2`;
                 `f:real^2->real^N`; `interval[vec 0:real^1,vec 1]`]
    MOI_FCL_PLH_PCROSS_ID) THEN
  ASM_REWRITE_TAC[POLYTOPE_INTERVAL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(Q2:real^2->bool) PCROSS interval[vec 0:real^1,vec 1]`;
                 `\z:real^(2,1)finite_sum. pastecart (inv(&2) % fstcart z) (--(sndcart z))`;
                 `\z:real^(2,1)finite_sum. pastecart (&2 % fstcart z) (--(sndcart z))`;
                 `pastecart (vec 0:real^2) (lift(&2))`] MOI_FCB_AFFINE_PLH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_INTERVAL];
      REWRITE_TAC[LINEAR_PASTECART_EQ] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LINEAR_FSTCART];
        MATCH_MP_TAC LINEAR_COMPOSE_NEG THEN REWRITE_TAC[LINEAR_SNDCART]];
      REWRITE_TAC[LINEAR_PASTECART_EQ] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LINEAR_FSTCART];
        MATCH_MP_TAC LINEAR_COMPOSE_NEG THEN REWRITE_TAC[LINEAR_SNDCART]];
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_MUL_ASSOC;
                  VECTOR_NEG_NEG] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID; PASTECART_FST_SND];
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_MUL_ASSOC;
                  VECTOR_NEG_NEG] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID; PASTECART_FST_SND]];
    ALL_TAC] THEN
  EXPAND_TAC "Q2" THEN REWRITE_TAC[MOI_FCB_RF2_SHIFT] THEN
  REWRITE_TAC[ASSUME `relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]) =
                      Q2`] THEN
  DISCH_TAC THEN
  EXISTS_TAC `(f:real^2->real^N) o (phi:real^(2,1)finite_sum->real^2) o
              (\x:real^(2,1)finite_sum.
                 pastecart (inv(&2) % fstcart x) (--(sndcart x)) +
                 pastecart (vec 0) (lift(&2))) o
              (\z:real^(N,1)finite_sum. pastecart ((g:real^N->real^2) (fstcart z))
                                                  (sndcart z))` THEN
  EXISTS_TAC `(((\z:real^(2,1)finite_sum. pastecart ((f:real^2->real^N) (fstcart z))
                                                     (sndcart z)) o
                (\z:real^(2,1)finite_sum.
                   pastecart (&2 % fstcart z) (--(sndcart z)) +
                   --(pastecart (&2 % fstcart (pastecart (vec 0:real^2) (lift(&2))))
                                (--(sndcart (pastecart (vec 0:real^2) (lift(&2)))))))) o
               moi_fps_psi) o (g:real^N->real^2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_fps_ann` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `moi_fps_sq PCROSS interval[lift(&1),lift(&2)]` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `(Q2:real^2->bool) PCROSS interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_ADD;
              VECTOR_NEG_0; VECTOR_ADD_LID; VECTOR_ADD_RID; VECTOR_MUL_RZERO] THEN
  SUBGOAL_THEN `(g:real^N->real^2) x IN Q2 /\ (f:real^2->real^N)(g x) = x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (j1,Q2) (g:real^N->real^2,f)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2) % (g:real^N->real^2) x IN moi_fps_sq` ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^N->real^2) x IN Q2` THEN EXPAND_TAC "Q2" THEN
    REWRITE_TAC[MOI_FCB_RF2; MOI_FPS_SQ; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(CONJUNCT2(MATCH_MP MOI_FCB_PSI_SQ th))]) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN
  SUBGOAL_THEN `(g:real^N->real^2) x IN moi_fps_ann` (fun th -> ASM_SIMP_TAC[th]) THEN
  ASM SET_TAC[]);;

(* The planar-surface theorem for chi = 0 and two boundary components: the  *)
(* surface is a PL annulus with ends, the ends forming its boundary.        *)

let MOI_FCB_PLANAR_ANNULUS = prove
 (mk_imp(MOI_FND_SURFACE_PLANAR,
  `!(S:(real^N->bool)->bool).
     FINITE S /\ combinatorial_manifold_with_boundary 2 S /\
     connected (UNIONS S) /\ ~(UNIONS S = {}) /\
     complex_euler S = &0 /\ CARD (components (surface_boundary S)) = 2
     ==> ?j1 j2. pl_annulus_with_ends (UNIONS S) j1 j2 /\
                 surface_boundary S = j1 UNION j2`),
  DISCH_THEN(LABEL_TAC "PLANAR") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "PLANAR" (MP_TAC o SPEC `S:(real^N->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `1` o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  X_CHOOSE_TAC `h:real^2->real^2` MOI_FEU_HD1_PL_HOMEOMORPHISM THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE ((f:real^2->real^N) o (h:real^2->real^2))
           (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`;
    `IMAGE ((f:real^2->real^N) o (h:real^2->real^2))
           (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pl_annulus_with_ends] THEN
    MAP_EVERY EXISTS_TAC [`(f:real^2->real^N) o (h:real^2->real^2)`;
                          `moi_feu_hd1_map o (g:real^N->real^2)`] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `holed_disk_model 1` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM IMAGE_UNION; GSYM MOI_FN2_HD1_FRONTIER; IMAGE_o] THEN
  SUBGOAL_THEN `IMAGE (h:real^2->real^2) (IMAGE moi_feu_hd1_map
                  (frontier (holed_disk_model 1))) = frontier (holed_disk_model 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> (k:real^2->real^2) x = x) ==> IMAGE k s = s`) THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    UNDISCH_TAC `pl_homeomorphism
                   (holed_disk_model 1,
                    interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                    interval(--vector[&1;&1]:real^2,vector[&1;&1]))
                   (moi_feu_hd1_map,h:real^2->real^2)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT1) THEN
    MP_TAC(ISPEC `holed_disk_model 1` FRONTIER_SUBSET_CLOSED) THEN
    REWRITE_TAC[MOI_FEU_EULER_HOLED_DISK_MODEL; COMPACT_IMP_CLOSED] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; MOI_FEU_EULER_HOLED_DISK_MODEL] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The ends of a PL annulus.                                                  *)

let MOI_FCB_ANN_ENDS_FACTS = prove
 (`!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> connected j0 /\ connected j1 /\ compact j0 /\ compact j1 /\
         j0 INTER j1 = {} /\ ~(j0 = {}) /\ ~(j1 = {})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_FCB_ANN_SETUP) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    (X_CHOOSE_THEN `phi:real^(2,1)finite_sum->real^2` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `Q2 = relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]])` THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on moi_fps_ann /\
                (!x y. x IN moi_fps_ann /\ y IN moi_fps_ann /\ f x = f y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (moi_fps_ann,a) (f:real^2->real^N,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fps_sq SUBSET moi_fps_ann /\ (Q2:real^2->bool) SUBSET moi_fps_ann`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "Q2" THEN REWRITE_TAC[MOI_FCB_SQ_ANN]; ALL_TAC] THEN
  SUBGOAL_THEN `connected moi_fps_sq /\ compact moi_fps_sq /\
                connected (Q2:real^2->bool) /\ compact Q2 /\
                ~(moi_fps_sq = {}) /\ ~(Q2 = {}) /\ moi_fps_sq INTER Q2 = {}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `Q2 = IMAGE (\x:real^2. &2 % x) moi_fps_sq` SUBST1_TAC THENL
     [EXPAND_TAC "Q2" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      X_GEN_TAC `y:real^2` THEN REWRITE_TAC[MOI_FCB_RF2; IN_IMAGE; MOI_FPS_SQ] THEN
      EQ_TAC THENL
       [DISCH_TAC THEN EXISTS_TAC `inv(&2) % y:real^2` THEN
        REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_COMPONENT] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID] THEN
        ASM_REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `connected moi_fps_sq /\ compact moi_fps_sq /\ ~(moi_fps_sq = {})`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S4O_SPHERE1_CONNECTED THEN REWRITE_TAC[MOI_FPS_SQ_PL_SPHERE];
        MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN REWRITE_TAC[MOI_FPS_SQ_PL_POLYHEDRON];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; MOI_FPS_SQ] THEN
        EXISTS_TAC `vector[&1; &0]:real^2` THEN REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_LINEAR_IMAGE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY; MOI_FPS_SQ] THEN

      GEN_TAC THEN
      MATCH_MP_TAC(TAUT `(p ==> ~q) ==> ~(p /\ q)`) THEN DISCH_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `max (abs((x:real^2)$1)) (abs(x$2)) = &1` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MAP_EVERY UNDISCH_TAC
     [`!x y. x IN moi_fps_ann /\ y IN moi_fps_ann /\ (f:real^2->real^N) x = f y
             ==> x = y`;
      `moi_fps_sq INTER Q2:real^2->bool = {}`;
      `moi_fps_sq SUBSET moi_fps_ann`; `(Q2:real^2->bool) SUBSET moi_fps_ann`] THEN
    SET_TAC[]]);;

(* A connected closed part of the union of the two ends, separated from the *)
(* rest, is one of the ends.                                                  *)

let MOI_FCB_END_CHOICE = prove
 (`!(a:real^N->bool) j0 j1 J R.
     pl_annulus_with_ends a j0 j1 /\ j0 UNION j1 = J UNION R /\
     connected J /\ ~(J = {}) /\ closed J /\ closed R /\ J INTER R = {}
     ==> J = j0 \/ J = j1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_ANN_ENDS_FACTS) THEN
  SUBGOAL_THEN `!j:real^N->bool. connected j /\ closed j /\ J SUBSET j /\
                                 j SUBSET J UNION R ==> j = J`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:real^N->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `connected (j:real^N->bool)` THEN REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`J:real^N->bool`; `R:real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `connected (J:real^N->bool)` THEN REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`j0:real^N->bool`; `j1:real^N->bool`]) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THENL
   [ASM SET_TAC[];
    ASM SET_TAC[];
    DISJ2_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
    DISJ1_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[]]);;

(* A collar of a boundary component J of a planar surface with chi = 0 and   *)
(* two boundary components (via the annulus with ends).                      *)

let MOI_FCB_SIDE_ANN_COLLAR = prove
 (mk_imp(MOI_FND_SURFACE_PLANAR,
  `!(S:(real^N->bool)->bool) J R.
     FINITE S /\ combinatorial_manifold_with_boundary 2 S /\
     connected (UNIONS S) /\ ~(UNIONS S = {}) /\
     complex_euler S = &0 /\ CARD (components (surface_boundary S)) = 2 /\
     surface_boundary S = J UNION R /\ connected J /\ ~(J = {}) /\
     closed J /\ closed R /\ J INTER R = {}
     ==> ?p q. pl_homeomorphism (J PCROSS interval[vec 0:real^1,vec 1],UNIONS S) (p,q) /\
               !x. x IN J ==> p(pastecart x (vec 0)) = x`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_FCB_PLANAR_ANNULUS (ASSUME MOI_FND_SURFACE_PLANAR)) THEN
  DISCH_THEN(MP_TAC o SPEC `S:(real^N->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j0:real^N->bool` (X_CHOOSE_THEN `j1:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`UNIONS S:real^N->bool`; `j0:real^N->bool`; `j1:real^N->bool`;
                 `J:real^N->bool`; `R:real^N->bool`] MOI_FCB_END_CHOICE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THENL
   [MATCH_MP_TAC MOI_FCB_ANN_COLLAR0 THEN EXISTS_TAC `j1:real^N->bool`;
    MATCH_MP_TAC MOI_FCB_ANN_COLLAR1 THEN EXISTS_TAC `j0:real^N->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Gluing collars over finitely many disjoint pieces.                        *)
(* ========================================================================= *)

(* Gluing collars over disjoint pieces (the [0,1] versions of             *)
(* MOI_FBC_DISJOINT_GLUE and MOI_FBC_FAMILY_GLUE of pc_moi_fnd_bicol).      *)

let MOI_FCB_DISJOINT_GLUE01 = prove
 (`!(s1:real^N->bool) s2 w1 w2 (p1:real^(N,1)finite_sum->real^N) q1 p2 q2.
     compact s1 /\ compact s2 /\ DISJOINT s1 s2 /\ DISJOINT w1 w2 /\
     pl_homeomorphism (s1 PCROSS interval[vec 0:real^1,vec 1],w1) (p1,q1) /\
     pl_homeomorphism (s2 PCROSS interval[vec 0:real^1,vec 1],w2) (p2,q2)
     ==> ?p q. pl_homeomorphism ((s1 UNION s2) PCROSS interval[vec 0:real^1,vec 1],
                                 w1 UNION w2) (p,q) /\
               (!z. z IN s1 PCROSS interval[vec 0,vec 1] ==> p z = p1 z) /\
               (!z. z IN s2 PCROSS interval[vec 0,vec 1] ==> p z = p2 z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (MP_TAC o GEN_REWRITE_RULE I [pl_homeomorphism])
                     (MP_TAC o GEN_REWRITE_RULE I [pl_homeomorphism])))))) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `h1 = (s1:real^N->bool) PCROSS interval[vec 0:real^1,vec 1]` THEN
  ABBREV_TAC `h2 = (s2:real^N->bool) PCROSS interval[vec 0:real^1,vec 1]` THEN
  ABBREV_TAC `p = \z:real^(N,1)finite_sum.
                    if fstcart z IN s1 then (p1:real^(N,1)finite_sum->real^N) z
                    else p2 z` THEN
  SUBGOAL_THEN
   `(!z. z IN h1 ==> (p:real^(N,1)finite_sum->real^N) z = p1 z) /\
    (!z. z IN h2 ==> p z = p2 z) /\
    compact (h1:real^(N,1)finite_sum->bool) /\ compact (h2:real^(N,1)finite_sum->bool) /\
    (s1 UNION s2) PCROSS interval[vec 0:real^1,vec 1] = h1 UNION h2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "h1"; "h2"] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                PCROSS_UNION] THEN
    SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; ASSUME `compact (s1:real^N->bool)`;
             ASSUME `compact (s2:real^N->bool)`] THEN
    UNDISCH_TAC `DISJOINT (s1:real^N->bool) s2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (h1 UNION h2:real^(N,1)finite_sum->bool)
                          (p:real^(N,1)finite_sum->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_UNION THEN
    ASM_SIMP_TAC[CLOSED_SUBSET; SUBSET_UNION; COMPACT_IMP_CLOSED] THEN
    CONJ_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THENL
     [EXISTS_TAC `p1:real^(N,1)finite_sum->real^N`;
      EXISTS_TAC `p2:real^(N,1)finite_sum->real^N`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h1 UNION h2:real^(N,1)finite_sum->bool`;
                 `p:real^(N,1)finite_sum->real^N`] MOI_FCL_PLH_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_UNION] THEN
    MAP_EVERY X_GEN_TAC [`z1:real^(N,1)finite_sum`; `z2:real^(N,1)finite_sum`] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN
    UNDISCH_TAC `(p:real^(N,1)finite_sum->real^N) z1 = p z2` THEN
    ASM_SIMP_TAC[] THENL
     [DISCH_THEN(MP_TAC o AP_TERM `q1:real^N->real^(N,1)finite_sum`) THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `(p1:real^(N,1)finite_sum->real^N) z1 IN w1 /\
                    (p2:real^(N,1)finite_sum->real^N) z2 IN w2` MP_TAC THENL
       [ASM SET_TAC[];
        UNDISCH_TAC `DISJOINT (w1:real^N->bool) w2` THEN SET_TAC[]];
      SUBGOAL_THEN `(p2:real^(N,1)finite_sum->real^N) z1 IN w2 /\
                    (p1:real^(N,1)finite_sum->real^N) z2 IN w1` MP_TAC THENL
       [ASM SET_TAC[];
        UNDISCH_TAC `DISJOINT (w1:real^N->bool) w2` THEN SET_TAC[]];
      DISCH_THEN(MP_TAC o AP_TERM `q2:real^N->real^(N,1)finite_sum`) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:real^N->real^(N,1)finite_sum`) THEN
  MAP_EVERY EXISTS_TAC [`p:real^(N,1)finite_sum->real^N`;
                        `q:real^N->real^(N,1)finite_sum`] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `IMAGE (p:real^(N,1)finite_sum->real^N) (h1 UNION h2) = w1 UNION w2`
  (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[IMAGE_UNION] THEN BINOP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (p1:real^(N,1)finite_sum->real^N) h1` THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (p2:real^(N,1)finite_sum->real^N) h2` THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]]]);;

(* Finitely many collars with pairwise disjoint images.                     *)

let MOI_FCB_FAMILY_GLUE01 = prove
 (`!(W:(real^N->bool)->real^N->bool)
    (P:(real^N->bool)->real^(N,1)finite_sum->real^N)
    (Q:(real^N->bool)->real^N->real^(N,1)finite_sum) ff.
     FINITE ff /\
     (!C. C IN ff ==> compact C /\
                     pl_homeomorphism (C PCROSS interval[vec 0:real^1,vec 1],W C)
                                      (P C,Q C)) /\
     (!C D. C IN ff /\ D IN ff /\ ~(C = D) ==> DISJOINT C D /\ DISJOINT (W C) (W D))
     ==> ?p q. pl_homeomorphism (UNIONS ff PCROSS interval[vec 0:real^1,vec 1],
                                 UNIONS (IMAGE W ff)) (p,q) /\
               !C z. C IN ff /\ z IN C PCROSS interval[vec 0,vec 1] ==> p z = P C z`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a ==> b /\ c ==> d`] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY; UNIONS_0; IMAGE_CLAUSES; PCROSS_EMPTY] THEN
    MAP_EVERY EXISTS_TAC [`\z:real^(N,1)finite_sum. vec 0:real^N`;
                          `\y:real^N. vec 0:real^(N,1)finite_sum`] THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism; pl_map_on; NOT_IN_EMPTY;
                IMAGE_CLAUSES; CONTINUOUS_ON_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real^N->bool`; `ff:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)
    (LABEL_TAC "disj")) THEN
  REMOVE_THEN "ih" MP_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "disj" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p':real^(N,1)finite_sum->real^N`
    (X_CHOOSE_THEN `q':real^N->real^(N,1)finite_sum`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agree")))) THEN
  MP_TAC(ISPECL [`C:real^N->bool`; `UNIONS ff:real^N->bool`;
                 `(W:(real^N->bool)->real^N->bool) C`;
                 `UNIONS (IMAGE (W:(real^N->bool)->real^N->bool) ff)`;
                 `(P:(real^N->bool)->real^(N,1)finite_sum->real^N) C`;
                 `(Q:(real^N->bool)->real^N->real^(N,1)finite_sum) C`;
                 `p':real^(N,1)finite_sum->real^N`; `q':real^N->real^(N,1)finite_sum`]
    MOI_FCB_DISJOINT_GLUE01) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_FBC_DISJOINT_UNIONS; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[];
      X_GEN_TAC `D:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "disj" (MP_TAC o SPECL [`C:real^N->bool`; `D:real^N->bool`]) THEN
      REWRITE_TAC[IN_INSERT] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `D:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "disj" (MP_TAC o SPECL [`C:real^N->bool`; `D:real^N->bool`]) THEN
      REWRITE_TAC[IN_INSERT] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^(N,1)finite_sum->real^N`
    (X_CHOOSE_THEN `q:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`p:real^(N,1)finite_sum->real^N`;
                        `q:real^N->real^(N,1)finite_sum`] THEN
  ASM_REWRITE_TAC[UNIONS_INSERT; IMAGE_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`D:real^N->bool`; `z:real^(N,1)finite_sum`] THEN
  REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
   [ASM_SIMP_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(p':real^(N,1)finite_sum->real^N) z` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `p':real^(N,1)finite_sum->real^N`)) (concl th) &&
        can (find_term ((=) `p:real^(N,1)finite_sum->real^N`)) (concl th))) THEN
      SUBGOAL_THEN `(D:real^N->bool) PCROSS interval[vec 0:real^1,vec 1] SUBSET
                    UNIONS ff PCROSS interval[vec 0,vec 1]` MP_TAC THENL
       [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[];
        UNDISCH_TAC `(z:real^(N,1)finite_sum) IN D PCROSS interval[vec 0,vec 1]` THEN
        SET_TAC[]];
      USE_THEN "agree" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* Collars of L on the sides of a split, from the Euler count                *)
(* chi K = chi S1 + chi S2 - chi L and the planar-surface theorem.          *)
(* ========================================================================= *)

(* A closed connected piece separated from a nonempty closed rest is a       *)
(* component, and there are at least two components.                         *)

let MOI_FCB_TWO_COMPS = prove
 (`!(J:real^N->bool) R.
     connected J /\ ~(J = {}) /\ closed J /\ ~(R = {}) /\ closed R /\
     J INTER R = {} /\ FINITE (components (J UNION R))
     ==> J IN components (J UNION R) /\ 2 <= CARD (components (J UNION R))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(J:real^N->bool) IN components (J UNION R)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_COMPONENTS_MAXIMAL] THEN ASM_REWRITE_TAC[SUBSET_UNION] THEN
    X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `connected (d:real^N->bool)` THEN
    REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`J:real^N->bool`; `R:real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `y:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(R:real^N->bool = {})`)) THEN
  SUBGOAL_THEN `connected_component (J UNION R) (y:real^N) IN components (J UNION R) /\
                ~(connected_component (J UNION R) (y:real^N) = J)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS; IN_UNION] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN connected_component (J UNION R) y` MP_TAC THENL
     [REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
      ASM_REWRITE_TAC[IN_UNION];
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD {J:real^N->bool, connected_component (J UNION R) y}` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ARITH_TAC;
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* Surface boundaries of finite complexes are closed.                         *)

let MOI_FCB_SB_CLOSED = prove
 (`!(K:(real^N->bool)->bool).
     FINITE K /\ (!s. s IN K ==> compact s) ==> closed (surface_boundary K)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[surface_boundary] THEN
  MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[COMPACT_IMP_CLOSED]]);;

(* Collars of L on each side of a split, when chi K = 0 and both sides meet *)
(* the boundary of K (Euler count and the planar-surface theorem).           *)

let MOI_FCB_SPLIT_COLLAR = prove
 (mk_imp(MOI_FND_SURFACE_PLANAR,
  `!(K:(real^N->bool)->bool) L K1 K2.
     moi_fcb_split K L K1 K2 /\ complex_euler K = &0 /\ pl_sphere 1 (UNIONS L) /\
     ~(surface_boundary K INTER K1 = {}) /\ ~(surface_boundary K INTER K2 = {})
     ==> ?p q. pl_homeomorphism (UNIONS L PCROSS interval[vec 0:real^1,vec 1],closure K1)
                                (p,q) /\
               !x. x IN UNIONS L ==> p(pastecart x (vec 0)) = x`),
  DISCH_THEN(LABEL_TAC "PLANAR") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCB_SIDES_MEET) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fcb_split]) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`] MOI_FCB_SIDE_MANIFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K2:real^N->bool`; `K1:real^N->bool`] MOI_FCB_SIDE_MANIFOLD) THEN
  ASM_SIMP_TAC[MOI_FCB_SPLIT_SYM] THEN STRIP_TAC THEN
  ABBREV_TAC `S1 = {q:real^N->bool | q IN K /\ q SUBSET closure K1}` THEN
  ABBREV_TAC `S2 = {q:real^N->bool | q IN K /\ q SUBSET closure K2}` THEN
  SUBGOAL_THEN `(S1:(real^N->bool)->bool) UNION S2 = K` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S1"; "S2"] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `q:real^N->bool` THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(q:real^N->bool) IN K` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `q:real^N->bool = {}` THEN ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `q:real^N->bool`] MOI_FSB_PURE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `r:real^N->bool`]
      MOI_FCB_TRI_CLOSURE_SIDE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S1:(real^N->bool)->bool) INTER S2 = L` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S1"; "S2"] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `q:real^N->bool` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `q INTER UNIONS L = q:real^N->bool` (fun th ->
        FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o C MATCH_MP (ASSUME `(q:real^N->bool) IN K`) o
          check (fun th' -> is_forall(concl th') &&
            can (find_term ((=) `(face_of):(real^N->bool)->(real^N->bool)->bool`))
                (concl th'))) THEN REWRITE_TAC[th]) THEN
      UNDISCH_TAC `closure K1 INTER closure K2 = UNIONS (L:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(q:real^N->bool) SUBSET closure K1` THEN
      UNDISCH_TAC `(q:real^N->bool) SUBSET closure K2` THEN SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(q:real^N->bool) IN K /\ q SUBSET UNIONS L` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `complex_euler (L:(real^N->bool)->bool) = &0` ASSUME_TAC THENL
   [MP_TAC(ISPEC `L:(real^N->bool)->bool` COMPLEX_EULER_VALUES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INT_ARITH `x <= &1 ==> x <= &2:int`];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `complex_euler (S1:(real^N->bool)->bool) + complex_euler (S2:(real^N->bool)->bool) = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S1:(real^N->bool)->bool`; `S2:(real^N->bool)->bool`]
      COMPLEX_EULER_UNION) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;

    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected (UNIONS L:real^N->bool) /\ ~(UNIONS L:real^N->bool = {}) /\
    closed (UNIONS L:real^N->bool) /\ closed (surface_boundary K:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S4O_SPHERE1_CONNECTED; COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FTA_PL_SPHERE_NONEMPTY];
      MATCH_MP_TAC MOI_FCB_SB_CLOSED THEN ASM_SIMP_TAC[]];

    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Ka Kb Sa:(real^N->bool)->bool.
      moi_fcb_split K L Ka Kb /\ ~(surface_boundary K INTER Ka = {}) /\
      Sa = {q | q IN K /\ q SUBSET closure Ka}
      ==> FINITE (components (surface_boundary Sa)) /\
          complex_euler Sa + &(CARD (components (surface_boundary Sa))) <= &2 /\
          2 <= CARD (components (surface_boundary Sa))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`Ka:real^N->bool`; `Kb:real^N->bool`;
                         `Sa:(real^N->bool)->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `Ka:real^N->bool`; `Kb:real^N->bool`] MOI_FCB_SIDE_MANIFOLD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    SUBGOAL_THEN `connected (closure Ka:real^N->bool) /\ ~(closure Ka:real^N->bool = {})`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CLOSURE THEN
        MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN
        EXISTS_TAC `UNIONS K DIFF UNIONS L:real^N->bool` THEN
        MP_TAC(MATCH_MP MOI_FCB_SPLIT_FACTS (ASSUME
          `moi_fcb_split (K:(real^N->bool)->bool) L (Ka:real^N->bool) Kb`)) THEN
        SIMP_TAC[];

        MP_TAC(ISPEC `Ka:real^N->bool` CLOSURE_SUBSET) THEN
        UNDISCH_TAC `~(surface_boundary K INTER Ka:real^N->bool = {})` THEN SET_TAC[]];
      ALL_TAC] THEN
    USE_THEN "PLANAR" (MP_TAC o SPEC `{q:real^N->bool | q IN K /\ q SUBSET closure Ka}`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`UNIONS L:real^N->bool`;
                   `surface_boundary K INTER closure Ka:real^N->bool`]
      MOI_FCB_TWO_COMPS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CLOSED_INTER; CLOSED_CLOSURE] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPEC `Ka:real^N->bool` CLOSURE_SUBSET) THEN
        UNDISCH_TAC `~(surface_boundary K INTER Ka:real^N->bool = {})` THEN SET_TAC[];
        UNDISCH_TAC `DISJOINT (UNIONS L) (surface_boundary (K:(real^N->bool)->bool))` THEN
        SET_TAC[];
        UNDISCH_TAC `FINITE (components (surface_boundary
                       {q:real^N->bool | q IN K /\ q SUBSET closure Ka}))` THEN
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`K1:real^N->bool`; `K2:real^N->bool`;
                              `S1:(real^N->bool)->bool`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`K2:real^N->bool`; `K1:real^N->bool`;
                                `S2:(real^N->bool)->bool`]) THEN
  ASM_SIMP_TAC[MOI_FCB_SPLIT_SYM] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `complex_euler (S1:(real^N->bool)->bool) = &0 /\
                CARD (components (surface_boundary (S1:(real^N->bool)->bool))) = 2`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_FCB_SIDE_ANN_COLLAR (ASSUME MOI_FND_SURFACE_PLANAR)) THEN
  DISCH_THEN(MP_TAC o SPECL [`S1:(real^N->bool)->bool`; `UNIONS L:real^N->bool`;
                             `surface_boundary K INTER closure K1:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CLOSURE THEN
      MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN
      EXISTS_TAC `UNIONS K DIFF UNIONS L:real^N->bool` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `K1:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
      ASM_SIMP_TAC[CLOSED_INTER; CLOSED_CLOSURE];
      UNDISCH_TAC `DISJOINT (UNIONS L) (surface_boundary (K:(real^N->bool)->bool))` THEN
      SET_TAC[]];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* Geometric splits of the derived neighbourhood of a polygon in a closed    *)
(* surface (two closed sets meeting in the polygon), with the lemmas:        *)
(* interiors in subtopologies, two closed pieces as components, components   *)
(* meeting the derived frontier (nb2 classes), the second derived            *)
(* subdivision of the polygon as a full subcomplex.                          *)
(* ========================================================================= *)

(* Interiors in subtopologies.                                                 *)

let MOI_FCB_INTERIOR_OPEN = prove
 (`!X S J:real^N->bool.
     J SUBSET (subtopology euclidean X) interior_of S
     ==> ?O. open O /\ J SUBSET O /\ X INTER O SUBSET S`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`; `S:real^N->bool`]
    OPEN_IN_INTERIOR_OF) THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `O:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`; `S:real^N->bool`]
    INTERIOR_OF_SUBSET) THEN
  ASM SET_TAC[]);;

(* Two closed pieces of a set with at most two components are its           *)
(* components.                                                                *)


let MOI_FCB_TWO_PIECES = prove
 (`!(X:real^N->bool) A B.
     closed A /\ closed B /\ X SUBSET A UNION B /\ A INTER B INTER X = {} /\
     ~(X INTER A = {}) /\ ~(X INTER B = {}) /\
     FINITE (components X) /\ CARD (components X) <= 2
     ==> components X = {X INTER A, X INTER B}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!C:real^N->bool. C IN components X ==> C SUBSET A \/ C SUBSET B`
  ASSUME_TAC THENL
   [X_GEN_TAC `C:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `connected (C:real^N->bool) /\ C SUBSET X` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED; IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `connected (C:real^N->bool)` THEN
    REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`A:real^N->bool`; `B:real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a b:real^N. a IN X INTER A /\ b IN X INTER B`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Ca = connected_component (X:real^N->bool) a` THEN
  ABBREV_TAC `Cb = connected_component (X:real^N->bool) b` THEN
  SUBGOAL_THEN `(Ca:real^N->bool) IN components X /\ (Cb:real^N->bool) IN components X /\
                (a:real^N) IN Ca /\ (b:real^N) IN Cb`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Ca"; "Cb"] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN
    REWRITE_TAC[IN] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONNECTED_COMPONENT_REFL) THEN
    UNDISCH_TAC `(a:real^N) IN X INTER A` THEN UNDISCH_TAC `(b:real^N) IN X INTER B` THEN
    REWRITE_TAC[IN_INTER] THEN REWRITE_TAC[IN] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Ca:real^N->bool) SUBSET A /\ (Cb:real^N->bool) SUBSET B` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `Ca:real^N->bool` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `A INTER B INTER X:real^N->bool = {}` THEN
      UNDISCH_TAC `(a:real^N) IN X INTER A` THEN UNDISCH_TAC `(a:real^N) IN Ca` THEN
      UNDISCH_TAC `(Ca:real^N->bool) SUBSET B` THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `Cb:real^N->bool` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `A INTER B INTER X:real^N->bool = {}` THEN
      UNDISCH_TAC `(b:real^N) IN X INTER B` THEN UNDISCH_TAC `(b:real^N) IN Cb` THEN
      UNDISCH_TAC `(Cb:real^N->bool) SUBSET A` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Ca:real^N->bool = Cb)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `A INTER B INTER X:real^N->bool = {}` THEN
    UNDISCH_TAC `(a:real^N) IN X INTER A` THEN UNDISCH_TAC `(a:real^N) IN Ca` THEN
    UNDISCH_TAC `(Cb:real^N->bool) SUBSET B` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `components (X:real^N->bool) = {Ca,Cb}` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_LE THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `X:real^N->bool = Ca UNION Cb` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `X:real^N->bool` UNIONS_COMPONENTS) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[UNIONS_2] THEN SET_TAC[];
      ASM_MESON_TAC[IN_COMPONENTS_SUBSET; UNION_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Ca = X INTER (A:real^N->bool) /\ Cb = X INTER B`
  (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `A INTER B INTER X:real^N->bool = {}` THEN
  UNDISCH_TAC `X:real^N->bool = Ca UNION Cb` THEN
  UNDISCH_TAC `(Ca:real^N->bool) SUBSET A` THEN
  UNDISCH_TAC `(Cb:real^N->bool) SUBSET B` THEN SET_TAC[]);;



(* Every component of the derived neighbourhood minus the polygon meets the  *)
(* derived frontier (the classes of pc_moi_fnd_nb2).                         *)


let MOI_FCB_COMP_MEETS_FR = prove
 (`!(m:(real^N->bool)->bool) l U.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ U IN components (derived_nbhd m l DIFF UNIONS l)
     ==> ~(derived_frontier m l INTER U = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(U:real^N->bool) IN components (derived_nbhd m l DIFF UNIONS l)` THEN
  ASM_SIMP_TAC[MOI_FN2_COMPONENTS_NL] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[MOI_FN2_UX_COMPONENT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `simplex_barycentre (f:real^N->bool)` THEN
  SUBGOAL_THEN `simplex_barycentre (f:real^N->bool) IN derived_frontier m l` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FN2_BARY_IN_FR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `simplex_barycentre (f:real^N->bool) IN derived_frontier m l` THEN
  REWRITE_TAC[derived_frontier; frontier_of; IN_DIFF] THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS m:real^N->bool)`;
                 `derived_nbhd m (l:(real^N->bool)->bool)`] CLOSURE_OF_CLOSED_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `UNIONS l SUBSET
               subtopology euclidean (UNIONS m) interior_of
               derived_nbhd m (l:(real^N->bool)->bool)` THEN
  SET_TAC[]);;


(* The second derived subdivision of a subcomplex is a full subcomplex of   *)
(* the derived neighbourhood complex.                                        *)

let MOI_FCB_L_SUBCOMPLEX = prove
 (`!(m:(real^N->bool)->bool) l.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\ ~(UNIONS l = {})
     ==> simplicial_subcomplex (barycentric_subdivision (barycentric_subdivision l))
                               (derived_nbhd_complex m l) /\
         UNIONS (barycentric_subdivision (barycentric_subdivision l)) = UNIONS l /\
         lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision l)) /\
         (!q. q IN derived_nbhd_complex m l
              ==> q INTER UNIONS l IN barycentric_subdivision (barycentric_subdivision l) /\
                  (q INTER UNIONS l) face_of q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                 `barycentric_subdivision (l:(real^N->bool)->bool)`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `L = barycentric_subdivision (barycentric_subdivision
                    (l:(real^N->bool)->bool))` THEN
  SUBGOAL_THEN `UNIONS (L:(real^N->bool)->bool) = UNIONS l` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
      REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
      SUBGOAL_THEN `!r:real^N->bool. r IN L ==> r IN barycentric_subdivision
                                     (barycentric_subdivision m)` ASSUME_TAC THENL
       [UNDISCH_TAC `simplicial_subcomplex (L:(real^N->bool)->bool)
                       (barycentric_subdivision (barycentric_subdivision m))` THEN
        SIMP_TAC[simplicial_subcomplex; SUBSET];
        ALL_TAC] THEN
      ASM_CASES_TAC `q:real^N->bool = {}` THENL
       [SUBGOAL_THEN `?r:real^N->bool. r IN L /\ ~(r = {})` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `~(UNIONS l:real^N->bool = {})` THEN
          REWRITE_TAC[GSYM(ASSUME `UNIONS (L:(real^N->bool)->bool) = UNIONS l`)] THEN
          SET_TAC[];
          ALL_TAC] THEN
        EXISTS_TAC `r:real^N->bool` THEN ASM_SIMP_TAC[EMPTY_FACE_OF] THEN
        SUBGOAL_THEN `(r:real^N->bool) SUBSET UNIONS l` MP_TAC THENL
         [REWRITE_TAC[GSYM(ASSUME `UNIONS (L:(real^N->bool)->bool) = UNIONS l`)] THEN
          UNDISCH_TAC `(r:real^N->bool) IN L` THEN SET_TAC[];
          UNDISCH_TAC `~(r:real^N->bool = {})` THEN SET_TAC[]];
        EXISTS_TAC `q:real^N->bool` THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `(q:real^N->bool) SUBSET UNIONS l` MP_TAC THENL
           [REWRITE_TAC[GSYM(ASSUME `UNIONS (L:(real^N->bool)->bool) = UNIONS l`)] THEN
            UNDISCH_TAC `(q:real^N->bool) IN L` THEN SET_TAC[];
            UNDISCH_TAC `~(q:real^N->bool = {})` THEN SET_TAC[]];
          MATCH_MP_TAC FACE_OF_REFL THEN MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
          EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]];
      MAP_EVERY X_GEN_TAC [`r:real^N->bool`; `f:real^N->bool`] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `UNIONS (l:(real^N->bool)->bool) = UNIONS (barycentric_subdivision l)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "L" THEN MATCH_MP_TAC MOI_FRN_FULL THEN
    EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `simplicial_subcomplex (derived_nbhd_complex m (l:(real^N->bool)->bool))
                   (barycentric_subdivision (barycentric_subdivision m))` THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]]);;

(* A geometric split of the derived neighbourhood of a polygon in a closed   *)
(* surface: two closed sets A, B covering it and meeting in the polygon,     *)
(* each accumulating on it, give a split along the polygon (with chi = 0 and *)
(* both sides meeting the derived frontier).                                  *)

let MOI_FCB_GEOM_SPLIT = prove
 (mk_imp(MOI_FND_SURFACE_PLANAR,
  `!(m:(real^N->bool)->bool) l A B.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\
     closed A /\ closed B /\ A SUBSET UNIONS m /\ B SUBSET UNIONS m /\
     derived_nbhd m l SUBSET A UNION B /\ A INTER B = UNIONS l /\
     UNIONS l SUBSET closure (A DIFF UNIONS l) /\ UNIONS l SUBSET closure (B DIFF UNIONS l)
     ==> moi_fcb_split (derived_nbhd_complex m l)
                       (barycentric_subdivision (barycentric_subdivision l))
                       (derived_nbhd m l INTER A DIFF UNIONS l)
                       (derived_nbhd m l INTER B DIFF UNIONS l) /\
         complex_euler (derived_nbhd_complex m l) = &0 /\
         ~(surface_boundary (derived_nbhd_complex m l) INTER
           (derived_nbhd m l INTER A DIFF UNIONS l) = {}) /\
         ~(surface_boundary (derived_nbhd_complex m l) INTER
           (derived_nbhd m l INTER B DIFF UNIONS l) = {}) /\
         UNIONS (barycentric_subdivision (barycentric_subdivision l)) = UNIONS l /\
         UNIONS l SUBSET (subtopology euclidean (UNIONS m)) interior_of derived_nbhd m l`),
  DISCH_THEN(LABEL_TAC "PLANAR") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `~(UNIONS l:real^N->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_PL_SPHERE_NONEMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_NC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FN2_COMPONENT_COUNT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FCB_L_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* at most two components *)
  SUBGOAL_THEN `CARD (components (derived_frontier m (l:(real^N->bool)->bool))) <= 2`
  ASSUME_TAC THENL
   [USE_THEN "PLANAR" (MP_TAC o SPEC `derived_nbhd_complex (m:(real^N->bool)->bool) l`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (components (derived_nbhd m l DIFF UNIONS (l:(real^N->bool)->bool)))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FN2_COMPONENTS_NL] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[moi_frn_vp];
    ALL_TAC] THEN
  (* the polygon in the closures of both pieces *)
  MP_TAC(ISPECL [`UNIONS m:real^N->bool`; `derived_nbhd m (l:(real^N->bool)->bool)`;
                 `UNIONS l:real^N->bool`] MOI_FCB_INTERIOR_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!X:real^N->bool. closed X /\ X SUBSET UNIONS m /\ UNIONS l SUBSET closure (X DIFF UNIONS l)
                     ==> UNIONS l SUBSET closure (derived_nbhd m l INTER X DIFF UNIONS l)`
  ASSUME_TAC THENL
   [X_GEN_TAC `X:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `O INTER closure (X DIFF UNIONS l):real^N->bool` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_INTER]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure (O INTER (X DIFF UNIONS l)):real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_INTER_CLOSURE_SUBSET] THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
    UNDISCH_TAC `UNIONS m INTER O SUBSET derived_nbhd m (l:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(X:real^N->bool) SUBSET UNIONS m` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS l SUBSET closure (derived_nbhd m l INTER A DIFF UNIONS (l:(real^N->bool)->bool)) /\
    UNIONS l SUBSET closure (derived_nbhd m l INTER B DIFF UNIONS (l:(real^N->bool)->bool))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(derived_nbhd m l INTER A DIFF UNIONS (l:(real^N->bool)->bool) = {}) /\
    ~(derived_nbhd m l INTER B DIFF UNIONS (l:(real^N->bool)->bool) = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `UNIONS l SUBSET
                   closure (derived_nbhd m l INTER A DIFF UNIONS (l:(real^N->bool)->bool))`;
      UNDISCH_TAC `UNIONS l SUBSET
                   closure (derived_nbhd m l INTER B DIFF UNIONS (l:(real^N->bool)->bool))`] THEN
    ASM_REWRITE_TAC[CLOSURE_EMPTY; SUBSET_EMPTY];
    ALL_TAC] THEN

  (* the components *)
  SUBGOAL_THEN
   `components (derived_nbhd m l DIFF UNIONS (l:(real^N->bool)->bool)) =
    {derived_nbhd m l INTER A DIFF UNIONS l, derived_nbhd m l INTER B DIFF UNIONS l}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`derived_nbhd m l DIFF UNIONS (l:(real^N->bool)->bool)`;
                   `A:real^N->bool`; `B:real^N->bool`] MOI_FCB_TWO_PIECES) THEN
    REWRITE_TAC[SET_RULE `(n DIFF j) INTER (a:real^N->bool) = n INTER a DIFF j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `derived_nbhd m (l:(real^N->bool)->bool) SUBSET A UNION B` THEN
      SET_TAC[];
      UNDISCH_TAC `A INTER B = UNIONS (l:(real^N->bool)->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `DISJOINT (UNIONS l) (surface_boundary (derived_nbhd_complex m (l:(real^N->bool)->bool)))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[derived_frontier; frontier_of] THEN
    UNDISCH_TAC `UNIONS l SUBSET
                 subtopology euclidean (UNIONS m) interior_of
                 derived_nbhd m (l:(real^N->bool)->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_fcb_split] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                     `barycentric_subdivision (l:(real^N->bool)->bool)`] MOI_FN2_CONTEXT) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                     `barycentric_subdivision (l:(real^N->bool)->bool)`] MOI_FN2_CONTEXT) THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `DISJOINT (UNIONS l) (surface_boundary (derived_nbhd_complex m
                     (l:(real^N->bool)->bool)))` THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `~(derived_nbhd m l INTER A DIFF UNIONS (l:(real^N->bool)->bool) = {})` THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!s t:A->bool. s = t /\ s INTER t = {} ==> s = {}`) THEN
      EXISTS_TAC `derived_nbhd m l INTER B DIFF UNIONS (l:(real^N->bool)->bool)` THEN
      CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `A INTER B = UNIONS (l:(real^N->bool)->bool)` THEN SET_TAC[]]];

    MATCH_MP_TAC MOI_FCB_COMP_MEETS_FR THEN ASM_REWRITE_TAC[IN_INSERT];
    MATCH_MP_TAC MOI_FCB_COMP_MEETS_FR THEN ASM_REWRITE_TAC[IN_INSERT]]);;

(* ========================================================================= *)
(* The boundary collar.  For one boundary component P: cap the surface,      *)
(* subdivide finely around the lifted P inside an open set that misses the   *)
(* other cones, split the derived neighbourhood by the lifted surface and    *)
(* the cone of P, take the collar on the lifted side, and transport it back  *)
(* by fstcart; then glue the collars of the components.  The planar-surface  *)
(* theorem enters at the type of the cap.                                    *)
(* ========================================================================= *)

(* The collar of one lifted boundary component inside the cap.               *)

let MOI_FCB_CAP_COLLAR = prove
 (mk_imp(inst [`:(N,2)finite_sum`,`:N`] MOI_FND_SURFACE_PLANAR,
  `!(c:(real^N->bool)->bool) ix P U.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     (!P Q. P IN components (surface_boundary c) /\
            Q IN components (surface_boundary c) /\ ix P = ix Q ==> P = Q) /\
     P IN components (surface_boundary c) /\
     open_in (subtopology euclidean (UNIONS (moi_fcb_cap c ix))) U /\
     IMAGE moi_fcb_lift P SUBSET U /\
     U SUBSET IMAGE moi_fcb_lift (UNIONS c) UNION moi_fcb_cone c ix P
     ==> ?W (p:real^((N,2)finite_sum,1)finite_sum->real^(N,2)finite_sum) q.
           pl_homeomorphism (IMAGE moi_fcb_lift P PCROSS interval[vec 0:real^1,vec 1],W)
                            (p,q) /\
           (!x. x IN IMAGE moi_fcb_lift P ==> p(pastecart x (vec 0)) = x) /\
           W SUBSET U INTER IMAGE moi_fcb_lift (UNIONS c) /\
           pl_polyhedron W /\
           (?O. open O /\ IMAGE moi_fcb_lift P SUBSET O /\
                O INTER IMAGE moi_fcb_lift (UNIONS c) SUBSET W)`),
  DISCH_THEN(LABEL_TAC "PLANAR") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`]
    MOI_FCB_CAP_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`] MOI_FCB_CAP_CM2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `P:real^N->bool`] MOI_FCB_LIFT_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`; `P:real^N->bool`]
    MOI_FCB_CONE_LIFT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `lP = {IMAGE moi_fcb_lift s:real^(N,2)finite_sum->bool |
                    s | s IN c /\ s SUBSET (P:real^N->bool)}` THEN
  SUBGOAL_THEN `simplicial_subcomplex lP (moi_fcb_cap (c:(real^N->bool)->bool) ix) /\
                UNIONS lP = IMAGE moi_fcb_lift (P:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lP" THEN CONJ_TAC THENL
     [REWRITE_TAC[simplicial_subcomplex] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; MOI_FCB_CAP_IN] THEN MESON_TAC[];
        REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
        X_GEN_TAC `s:real^N->bool` THEN REPEAT DISCH_TAC THEN
        X_GEN_TAC `f:real^(N,2)finite_sum->bool` THEN
        DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC o
          MATCH_MP MOI_FCB_LIFT_FACES) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `g:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[MOI_FCB_SC_FACES];
          ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]]];
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^(N,2)finite_sum` THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `t:real^(N,2)finite_sum->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) MP_TAC)) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(s:real^N->bool) SUBSET P` THEN SET_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `P:real^N->bool`; `x:real^N`]
          MOI_FCB_BD_COVER) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `IMAGE moi_fcb_lift (e:real^N->bool):real^(N,2)finite_sum->bool` THEN
        CONJ_TAC THENL [EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fcb_cap (c:(real^N->bool)->bool) ix`;
                 `lP:(real^(N,2)finite_sum->bool)->bool`;
                 `U:real^(N,2)finite_sum->bool`] DERIVED_NBHD_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `n:num`)] THEN
  MP_TAC(ISPECL [`moi_fcb_cap (c:(real^N->bool)->bool) ix`;
                 `lP:(real^(N,2)finite_sum->bool)->bool`; `n:num`]
    MOI_FDN_ITER_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_fcb_cap (c:(real^N->bool)->bool) ix`; `n:num`] MOI_FBC_ITER_CM2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `m = ITER n barycentric_subdivision (moi_fcb_cap (c:(real^N->bool)->bool) ix)` THEN
  ABBREV_TAC `l = ITER n barycentric_subdivision (lP:(real^(N,2)finite_sum->bool)->bool)` THEN
  SUBGOAL_THEN
   `compact (IMAGE moi_fcb_lift (UNIONS c):real^(N,2)finite_sum->bool) /\
    compact (moi_fcb_cone (c:(real^N->bool)->bool) ix P) /\
    IMAGE moi_fcb_lift (UNIONS c) SUBSET UNIONS (m:(real^(N,2)finite_sum->bool)->bool) /\
    moi_fcb_cone (c:(real^N->bool)->bool) ix P SUBSET UNIONS m`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FCB_CONE_COMPACT] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`]
      MOI_FCB_CAP_UNIONS) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN REWRITE_TAC[MOI_FCB_LIFT] THEN
      MATCH_MP_TAC COMPACT_UNIONS THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
      ASM_MESON_TAC[MOI_FCB_SC_CONVEX; SIMPLEX_IMP_COMPACT];
      SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!a b c:A->bool. b SUBSET c ==> b SUBSET a UNION c`) THEN
      MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `P:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (INST_TYPE [`:(N,2)finite_sum`,`:N`] MOI_FCB_GEOM_SPLIT)
    (ASSUME (inst [`:(N,2)finite_sum`,`:N`] MOI_FND_SURFACE_PLANAR))) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`m:(real^(N,2)finite_sum->bool)->bool`; `l:(real^(N,2)finite_sum->bool)->bool`;
    `IMAGE moi_fcb_lift (UNIONS c):real^(N,2)finite_sum->bool`;
    `moi_fcb_cone (c:(real^N->bool)->bool) ix P`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U:real^(N,2)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `U SUBSET IMAGE moi_fcb_lift (UNIONS c) UNION
                   moi_fcb_cone (c:(real^N->bool)->bool) ix P` THEN SET_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FCB_LIFT_CLOSURE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FCB_CONE_CLOSURE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Z1 = derived_nbhd m l INTER IMAGE moi_fcb_lift (UNIONS c) DIFF
                   UNIONS (l:(real^(N,2)finite_sum->bool)->bool)` THEN
  ABBREV_TAC `Z2 = derived_nbhd m l INTER moi_fcb_cone (c:(real^N->bool)->bool) ix P DIFF
                   UNIONS (l:(real^(N,2)finite_sum->bool)->bool)` THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP (INST_TYPE [`:(N,2)finite_sum`,`:N`] MOI_FCB_SPLIT_COLLAR)
    (ASSUME (inst [`:(N,2)finite_sum`,`:N`] MOI_FND_SURFACE_PLANAR))) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`derived_nbhd_complex m (l:(real^(N,2)finite_sum->bool)->bool)`;
    `barycentric_subdivision (barycentric_subdivision
       (l:(real^(N,2)finite_sum->bool)->bool))`;
    `Z1:real^(N,2)finite_sum->bool`; `Z2:real^(N,2)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^((N,2)finite_sum,1)finite_sum->real^(N,2)finite_sum`
    (X_CHOOSE_THEN `q:real^(N,2)finite_sum->real^((N,2)finite_sum,1)finite_sum`
      STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `UNIONS l SUBSET closure (Z1:real^(N,2)finite_sum->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fcb_split (derived_nbhd_complex m l)
                   (barycentric_subdivision (barycentric_subdivision l)) Z1
                   (Z2:real^(N,2)finite_sum->bool)` THEN
    REWRITE_TAC[moi_fcb_split] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (l:(real^(N,2)finite_sum->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; FINITE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^(N,2)finite_sum->bool)->bool`;
                 `l:(real^(N,2)finite_sum->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`closure Z1:real^(N,2)finite_sum->bool`;
                        `p:real^((N,2)finite_sum,1)finite_sum->real^(N,2)finite_sum`;
                        `q:real^(N,2)finite_sum->real^((N,2)finite_sum,1)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN

  SUBGOAL_THEN `closure Z1 SUBSET
                derived_nbhd m l INTER IMAGE moi_fcb_lift (UNIONS (c:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [EXPAND_TAC "Z1" THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];

    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `derived_nbhd m l SUBSET (U:real^(N,2)finite_sum->bool)` THEN
    UNDISCH_TAC `closure Z1 SUBSET
                 derived_nbhd m l INTER IMAGE moi_fcb_lift (UNIONS (c:(real^N->bool)->bool))` THEN
    SET_TAC[];
    SUBGOAL_THEN `closure Z1 = IMAGE (p:real^((N,2)finite_sum,1)finite_sum->real^(N,2)finite_sum)
                     (IMAGE moi_fcb_lift (P:real^N->bool) PCROSS interval[vec 0:real^1,vec 1])`
    SUBST1_TAC THENL
     [UNDISCH_TAC `pl_homeomorphism
                     (IMAGE moi_fcb_lift (P:real^N->bool) PCROSS interval[vec 0:real^1,vec 1],
                      closure Z1)
                     (p:real^((N,2)finite_sum,1)finite_sum->real^(N,2)finite_sum,q)` THEN
      SIMP_TAC[pl_homeomorphism; homeomorphism];
      ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN CONJ_TAC THENL
       [MATCH_MP_TAC PL_POLYHEDRON_LINEAR_IMAGE THEN ASM_REWRITE_TAC[MOI_FCB_LIFT];
        MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_INTERVAL]];
      UNDISCH_TAC `pl_homeomorphism
                     (IMAGE moi_fcb_lift (P:real^N->bool) PCROSS interval[vec 0:real^1,vec 1],
                      closure Z1)
                     (p:real^((N,2)finite_sum,1)finite_sum->real^(N,2)finite_sum,q)` THEN
      SIMP_TAC[pl_homeomorphism]];
    MP_TAC(ISPECL [`UNIONS (m:(real^(N,2)finite_sum->bool)->bool)`;
                   `derived_nbhd m (l:(real^(N,2)finite_sum->bool)->bool)`;
                   `UNIONS (l:(real^(N,2)finite_sum->bool)->bool)`] MOI_FCB_INTERIOR_OPEN) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:real^(N,2)finite_sum->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `O:real^(N,2)finite_sum->bool` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS l SUBSET (O:real^(N,2)finite_sum->bool)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `Z1:real^(N,2)finite_sum->bool` CLOSURE_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`UNIONS m INTER O SUBSET derived_nbhd m (l:(real^(N,2)finite_sum->bool)->bool)`;
      `IMAGE moi_fcb_lift (UNIONS c) SUBSET UNIONS (m:(real^(N,2)finite_sum->bool)->bool)`;
      `UNIONS l SUBSET closure (Z1:real^(N,2)finite_sum->bool)`;
      `derived_nbhd m l INTER IMAGE moi_fcb_lift (UNIONS c) DIFF
       UNIONS (l:(real^(N,2)finite_sum->bool)->bool) = Z1`] THEN
    SET_TAC[]]);;

(* The collar of one boundary component, transported back from the cap.     *)

let MOI_FCB_COLLAR_ONE = prove
 (mk_imp(inst [`:(N,2)finite_sum`,`:N`] MOI_FND_SURFACE_PLANAR,
  `!(c:(real^N->bool)->bool) P u.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     P IN components (surface_boundary c) /\
     open_in (subtopology euclidean (UNIONS c)) u /\ P SUBSET u
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           pl_homeomorphism (P PCROSS interval[vec 0:real^1,vec 1],w) (p,q) /\
           w SUBSET u /\ P SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
           !x. x IN P ==> p(pastecart x (vec 0)) = x`),
  DISCH_THEN(LABEL_TAC "PLANAR") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(\P. 0):(real^N->bool)->num`]
    MOI_FCB_CAP_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `components (surface_boundary (c:(real^N->bool)->bool))`
    MOI_FCB_INDEX_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `ix:(real^N->bool)->num`) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`; `P:real^N->bool`;
                 `u:real^N->bool`] MOI_FCB_UPRIME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^(N,2)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(MATCH_MP MOI_FCB_CAP_COLLAR
    (ASSUME (inst [`:(N,2)finite_sum`,`:N`] MOI_FND_SURFACE_PLANAR))) THEN
  DISCH_THEN(MP_TAC o SPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`;
                             `P:real^N->bool`; `U:real^(N,2)finite_sum->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^(N,2)finite_sum->bool`
   (X_CHOOSE_THEN `p':real^((N,2)finite_sum,1)finite_sum->real^(N,2)finite_sum`
    (X_CHOOSE_THEN `q':real^(N,2)finite_sum->real^((N,2)finite_sum,1)finite_sum`
      STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `P:real^N->bool`] MOI_FCB_LIFT_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the lift as a PL homeomorphism onto its image *)
  SUBGOAL_THEN
   `pl_homeomorphism (P,IMAGE moi_fcb_lift P)
                     (moi_fcb_lift:real^N->real^(N,2)finite_sum,fstcart)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism] THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; MOI_FCB_LIFT; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF; MOI_FCB_LIFT; IMAGE_ID];
      MP_TAC(ISPECL [`P:real^N->bool`; `moi_fcb_lift:real^N->real^(N,2)finite_sum`;
                     `vec 0:real^(N,2)finite_sum`] PL_MAP_ON_AFFINE) THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; MOI_FCB_LIFT; VECTOR_ADD_RID; ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:real^N->bool`; `IMAGE moi_fcb_lift P:real^(N,2)finite_sum->bool`;
                 `moi_fcb_lift:real^N->real^(N,2)finite_sum`;
                 `fstcart:real^(N,2)finite_sum->real^N`; `interval[vec 0:real^1,vec 1]`]
    MOI_FCL_PLH_PCROSS_ID) THEN
  ASM_REWRITE_TAC[POLYTOPE_INTERVAL] THEN DISCH_TAC THEN
  (* fstcart on the collar *)
  SUBGOAL_THEN `W SUBSET IMAGE moi_fcb_lift (UNIONS (c:(real^N->bool)->bool))`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (W,IMAGE fstcart W)
                     (fstcart:real^(N,2)finite_sum->real^N,moi_fcb_lift)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism] THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; MOI_FCB_LIFT; FORALL_IN_IMAGE] THEN
      SUBGOAL_THEN `!z:real^(N,2)finite_sum. z IN W ==> moi_fcb_lift(fstcart z) = z`
      ASSUME_TAC THENL
       [X_GEN_TAC `z:real^(N,2)finite_sum` THEN DISCH_TAC THEN
        SUBGOAL_THEN `?y:real^N. z = moi_fcb_lift y` STRIP_ASSUME_TAC THENL
         [ASM SET_TAC[]; ASM_REWRITE_TAC[MOI_FCB_LIFT]];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> (k:A->A) x = x) ==> IMAGE k s = s`) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`W:real^(N,2)finite_sum->bool`; `fstcart:real^(N,2)finite_sum->real^N`;
                     `vec 0:real^N`] PL_MAP_ON_AFFINE) THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; LINEAR_FSTCART; VECTOR_ADD_RID;
                   ETA_AX]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE fstcart (W:real^(N,2)finite_sum->bool)` THEN
  EXISTS_TAC `fstcart o ((p':real^((N,2)finite_sum,1)finite_sum->real^(N,2)finite_sum) o
              (\z:real^(N,1)finite_sum. pastecart (moi_fcb_lift (fstcart z)) (sndcart z)))` THEN
  EXISTS_TAC `((\z:real^((N,2)finite_sum,1)finite_sum. pastecart (fstcart (fstcart z)) (sndcart z)) o
               (q':real^(N,2)finite_sum->real^((N,2)finite_sum,1)finite_sum)) o moi_fcb_lift` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `W:real^(N,2)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE moi_fcb_lift (P:real^N->bool) PCROSS interval[vec 0:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE fstcart (IMAGE moi_fcb_lift (u:real^N->bool))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[];
      REWRITE_TAC[GSYM IMAGE_o; o_DEF; MOI_FCB_LIFT; IMAGE_ID; SUBSET_REFL]];
    REWRITE_TAC[SUBSET; interior_of; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN
    EXISTS_TAC `UNIONS c INTER {y:real^N | moi_fcb_lift y IN O}` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `{y:real^N | moi_fcb_lift y IN O}` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; MOI_FCB_LIFT];
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ix:(real^N->bool)->num`; `P:real^N->bool`]
          MOI_FCB_CONE_LIFT) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        UNDISCH_TAC `IMAGE moi_fcb_lift P SUBSET
                     IMAGE moi_fcb_lift (UNIONS (c:(real^N->bool)->bool))` THEN
        UNDISCH_TAC `(x:real^N) IN P` THEN
        REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[MOI_FCB_LIFT];
        UNDISCH_TAC `IMAGE moi_fcb_lift P SUBSET (O:real^(N,2)finite_sum->bool)` THEN
        UNDISCH_TAC `(x:real^N) IN P` THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        MESON_TAC[]];
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      EXISTS_TAC `moi_fcb_lift (y:real^N)` THEN REWRITE_TAC[MOI_FCB_LIFT] THEN
      UNDISCH_TAC `O INTER IMAGE moi_fcb_lift (UNIONS (c:(real^N->bool)->bool)) SUBSET W` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    SUBGOAL_THEN `moi_fcb_lift (x:real^N) IN IMAGE moi_fcb_lift P` ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_FCB_LIFT]]);;

(* The boundary collar (with the planar-surface theorem at the cap's type    *)
(* as a hypothesis): collars of the components glued.                        *)

let MOI_FCB_BOUNDARY_COLLAR_COND = prove
 (mk_imp(inst [`:(N,2)finite_sum`,`:N`] MOI_FND_SURFACE_PLANAR,
  `!(c:(real^N->bool)->bool) v.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     open_in (subtopology euclidean (UNIONS c)) v /\ surface_boundary c SUBSET v
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           pl_homeomorphism
             (surface_boundary c PCROSS interval[vec 0:real^1,vec 1],w) (p,q) /\
           w SUBSET v /\
           surface_boundary c SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
           !x. x IN surface_boundary c ==> p(pastecart x (vec 0)) = x`),
  DISCH_THEN(LABEL_TAC "PLANAR") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSB_BD_CIRCLES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!C. C IN components (surface_boundary c) ==> compact (C:real^N->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `C:real^N->bool`] MOI_FCB_LIFT_SPHERE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!C D. C IN components (surface_boundary c) /\ D IN components (surface_boundary c) /\
          ~(C = D) ==> DISJOINT (C:real^N->bool) D`
  ASSUME_TAC THENL [REWRITE_TAC[DISJOINT] THEN MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
  MP_TAC(ISPEC `components (surface_boundary (c:(real^N->bool)->bool))` MOI_FBC_SEPARATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:(real^N->bool)->real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!C. C IN components (surface_boundary c)
        ==> ?w (p:real^(N,1)finite_sum->real^N) q.
              pl_homeomorphism (C PCROSS interval[vec 0:real^1,vec 1],w) (p,q) /\
              w SUBSET v INTER O C /\
              C SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
              !x. x IN C ==> p(pastecart x (vec 0)) = x`
  MP_TAC THENL
   [X_GEN_TAC `C:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(MATCH_MP MOI_FCB_COLLAR_ONE
      (ASSUME (inst [`:(N,2)finite_sum`,`:N`] MOI_FND_SURFACE_PLANAR))) THEN
    DISCH_THEN(MP_TAC o SPECL [`c:(real^N->bool)->bool`; `C:real^N->bool`;
                               `v INTER (O:(real^N->bool)->real^N->bool) C`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN ASM_SIMP_TAC[];
        REWRITE_TAC[SUBSET_INTER] THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `surface_boundary c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[IN_COMPONENTS_SUBSET]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:(real^N->bool)->real^N->bool`

   (X_CHOOSE_THEN `Pm:(real^N->bool)->real^(N,1)finite_sum->real^N`
    (X_CHOOSE_TAC `Qm:(real^N->bool)->real^N->real^(N,1)finite_sum`))) THEN
  MP_TAC(ISPECL [`W:(real^N->bool)->real^N->bool`;
                 `Pm:(real^N->bool)->real^(N,1)finite_sum->real^N`;
                 `Qm:(real^N->bool)->real^N->real^(N,1)finite_sum`;
                 `components (surface_boundary (c:(real^N->bool)->bool))`]
    MOI_FCB_FAMILY_GLUE01) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`C:real^N->bool`; `D:real^N->bool`] THEN STRIP_TAC THEN
    TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN

    SUBGOAL_THEN `(W:(real^N->bool)->real^N->bool) C SUBSET O C /\ W D SUBSET O D /\
                  DISJOINT ((O:(real^N->bool)->real^N->bool) C) (O D)`
    MP_TAC THENL [ASM_MESON_TAC[SUBSET_INTER]; SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^(N,1)finite_sum->real^N`
   (X_CHOOSE_THEN `q:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `UNIONS (components (surface_boundary c)) =
                surface_boundary (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM UNIONS_COMPONENTS]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS (IMAGE (W:(real^N->bool)->real^N->bool)
                   (components (surface_boundary c)))`;
    `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`] THEN
  UNDISCH_TAC
   `pl_homeomorphism
     (UNIONS (components (surface_boundary c)) PCROSS interval[vec 0:real^1,vec 1],
      UNIONS (IMAGE (W:(real^N->bool)->real^N->bool) (components (surface_boundary c))))
     (p:real^(N,1)finite_sum->real^N,q)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `C:real^N->bool` THEN
    DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `v INTER (O:(real^N->bool)->real^N->bool) C` THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?C:real^N->bool. C IN components (surface_boundary c) /\ x IN C`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN surface_boundary c` THEN
      UNDISCH_TAC `UNIONS (components (surface_boundary c)) =
                   surface_boundary (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!s t x:A. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `subtopology euclidean (UNIONS c) interior_of
                (W:(real^N->bool)->real^N->bool) C` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INTERIOR_OF_MONO THEN
    MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?C:real^N->bool. C IN components (surface_boundary c) /\ x IN C`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN surface_boundary c` THEN
      UNDISCH_TAC `UNIONS (components (surface_boundary c)) =
                   surface_boundary (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(Pm:(real^N->bool)->real^(N,1)finite_sum->real^N) C (pastecart x (vec 0))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `p:real^(N,1)finite_sum->real^N`)) (concl th) &&
        can (find_term ((=) `Pm:(real^N->bool)->real^(N,1)finite_sum->real^N`)) (concl th))) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL];
      ASM_SIMP_TAC[]]]);;

(* The boundary collar MOI_FCB_BOUNDARY_COLLAR_2, with SURFACE_EULER_PLANAR  *)
(* of pc_moi_fnd_surfb at the type of the cap.                               *)

let MOI_FCB_BOUNDARY_COLLAR_2 = prove
 (`!(c:(real^N->bool)->bool) v.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     open_in (subtopology euclidean (UNIONS c)) v /\ surface_boundary c SUBSET v
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           pl_homeomorphism
             (surface_boundary c PCROSS interval[vec 0:real^1,vec 1],w) (p,q) /\
           w SUBSET v /\
           surface_boundary c SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
           !x. x IN surface_boundary c ==> p(pastecart x (vec 0)) = x`,
  MATCH_ACCEPT_TAC(MP MOI_FCB_BOUNDARY_COLLAR_COND
    (INST_TYPE [`:(N,2)finite_sum`,`:N`] SURFACE_EULER_PLANAR)));;

