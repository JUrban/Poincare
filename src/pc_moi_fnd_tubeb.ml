(* ========================================================================= *)
(* pc_moi_fnd_tubeb: foundations of the Moise PL core, the tube             *)
(* N = derived_nbhd t l of a graph l (Moise GTM 47, p.223).  Main theorem   *)
(* (the statement term of pc_moi_fnd_stmt.ml):                               *)
(*   GRAPH_TUBE_FRONTIER_3 = MOI_FND_GRAPH_TUBE_FRONTIER_3: for a finite    *)
(*   graph in a complex in real^3, N lies in the open part of UNIONS t, so  *)
(*   its interior and frontier in real^3 are the relative ones and UNIONS l *)
(*   lies in its interior.                                                   *)
(* Route: a point of a simplex of the first derived through a vertex v of t  *)
(* is off the link of v in t; so each dual cell lies in the open star of its *)
(* vertex, which is open in real^3 by invariance of domain                   *)
(* (MOI_FM3_INTERIOR_VIA_STAR).                                              *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_tubea.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The dual cells lie in the open part of UNIONS t (real^3).                *)
(* ------------------------------------------------------------------------- *)

let moi_ftb_head_is s th =
  try fst(dest_const(fst(strip_comb(concl th)))) = s with Failure _ -> false;;

(* A point of the hull of the barycentres of a chain through {v} is off the *)
(* link of v: the hull lies in the top simplex minus the face cut out by a  *)
(* link simplex, a convex set containing every barycentre.                  *)
let MOI_FTB_CHAIN_OFF_LINK = prove
 (`!(t:(real^N->bool)->bool) h v x.
     moi_bar_complex t /\ moi_bar_chain t h /\ {v} IN h /\
     x IN convex hull (IMAGE simplex_barycentre h)
     ==> ~(x IN UNIONS (simplicial_link t v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_UNIONS; simplicial_link; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((h:(real^N->bool)->bool) = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `h:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS (h:(real^N->bool)->bool) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  (* every member of the chain contains v *)
  SUBGOAL_THEN `!r:real^N->bool. r IN h ==> v IN r` ASSUME_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(r:real^N->bool = {})` MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
    UNDISCH_TAC `moi_bar_chain t (h:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN
    DISCH_THEN(MP_TAC o SPECL [`r:real^N->bool`; `{v:real^N}`] o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(UNIONS h INTER s':real^N->bool) face_of UNIONS h` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_complex (t:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`UNIONS (h:(real^N->bool)->bool)`; `s':real^N->bool`] o
               last o CONJUNCTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (UNIONS (h:(real^N->bool)->bool))` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (UNIONS h DIFF (UNIONS h INTER s':real^N->bool))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_STILLCONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE simplex_barycentre (h:(real^N->bool)->bool) SUBSET
                UNIONS h DIFF (UNIONS h INTER s')` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `r face_of UNIONS (h:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_FACE_OF_MAX]; ALL_TAC] THEN
    SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]; ALL_TAC] THEN
    SUBGOAL_THEN `~(r:real^N->bool = {})` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]; ALL_TAC] THEN
    SUBGOAL_THEN `simplex_barycentre (r:real^N->bool) IN relative_interior r` ASSUME_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR]; ALL_TAC] THEN
    SUBGOAL_THEN `(r INTER (UNIONS h INTER s':real^N->bool)) face_of r` ASSUME_TAC THENL
     [MATCH_MP_TAC FACE_OF_SUBSET THEN EXISTS_TAC `UNIONS (h:(real^N->bool)->bool)` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FACE_OF_INTER THEN ASM_REWRITE_TAC[];
        SET_TAC[];
        ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(r INTER (UNIONS h INTER s':real^N->bool) = r)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(v:real^N) IN r` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `r INTER (UNIONS h INTER s':real^N->bool) = r` THEN
      UNDISCH_TAC `~((v:real^N) IN s')` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`r INTER (UNIONS h INTER s':real^N->bool)`; `r:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    SUBGOAL_THEN `(r:real^N->bool) SUBSET UNIONS h` MP_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `simplex_barycentre (r:real^N->bool) IN relative_interior r` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (IMAGE simplex_barycentre (h:(real^N->bool)->bool)) SUBSET
                UNIONS h DIFF (UNIONS h INTER s')` MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN s'` THEN
  UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre h)` THEN
  SET_TAC[]);;

(* In real^3 a dual cell lies in the interior of UNIONS t: it is in the    *)
(* cone over the link of v in t and off the link, so the star chart sends  *)
(* it into the interior of the 3-simplex (invariance of domain).            *)
let MOI_FTB_CELL_INTERIOR = prove
 (`!(t:(real^3->bool)->bool) l v.
     graph_in_complex t l /\ {v} IN l
     ==> derived_dual_cell t l v SUBSET interior (UNIONS t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  SUBGOAL_THEN `{v:real^3} IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (UNIONS (simplicial_link t (v:real^3)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `v:real^3`] MOI_FM3_STAR_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^3`
    (X_CHOOSE_THEN `q:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?s:real^3->bool. s IN t /\ v IN s /\ x IN s` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `v:real^3`]
      MOI_FTA_CELL_IN_STAR) THEN
    ASM_REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link t v)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_IN_STAR THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^3) IN UNIONS (simplicial_link t v))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `v:real^3`; `x:real^3`]
      MOI_FTA_IN_DUAL_CELL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(CONJUNCT2(EQ_MP th (ASSUME
      `(x:real^3) IN derived_dual_cell t l v`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `h:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FTB_CHAIN_OFF_LINK THEN EXISTS_TAC `h:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FM3_INTERIOR_VIA_STAR THEN
  MAP_EVERY EXISTS_TAC [`v:real^3`; `S:real^3->bool`; `p:real^3->real^3`;
                        `q:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `interior (S:real^3->bool) = S DIFF relative_frontier S` SUBST1_TAC THENL
   [SUBGOAL_THEN `affine hull (S:real^3->bool) = (:real^3)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN ASM_MESON_TAC[AFF_DIM_SIMPLEX];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM RELATIVE_INTERIOR_INTERIOR; relative_frontier] THEN
    SUBGOAL_THEN `closure (S:real^3->bool) = S` SUBST1_TAC THENL
     [ASM_MESON_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
    MP_TAC(ISPEC `S:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (moi_ftb_head_is "pl_homeomorphism")) THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `S:real^3->bool`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `relative_frontier (S:real^3->bool)`)) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link t v)}`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[v:real^3,y]` THEN
    REWRITE_TAC[ENDS_IN_SEGMENT; IN_ELIM_THM] THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `x:real^3 = y` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* The tube lies in the interior of UNIONS t. *)
let MOI_FTB_NBHD_INTERIOR = prove
 (`!(t:(real^3->bool)->bool) l.
     graph_in_complex t l
     ==> derived_nbhd t l SUBSET interior (UNIONS t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP GRAPH_TUBE_DUAL_CELLS) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_FTB_CELL_INTERIOR THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Point-set topology: relative interior and frontier of a set inside an    *)
(* open subset of the ambient set.                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_FTB_INTERIOR_OF_OPEN_PART = prove
 (`!(X:real^N->bool) U N.
     open U /\ U SUBSET X /\ N SUBSET U
     ==> (subtopology euclidean X) interior_of N = interior N`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[MOI_FTA_IN_INTERIOR_SUB; interior; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `W INTER U:real^N->bool` THEN ASM_SIMP_TAC[OPEN_INTER] THEN
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MOI_FTB_FRONTIER_OF_OPEN_PART = prove
 (`!(X:real^N->bool) U N.
     open U /\ U SUBSET X /\ N SUBSET U /\ closed N
     ==> (subtopology euclidean X) frontier_of N = frontier N`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier_of; frontier] THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `U:real^N->bool`; `N:real^N->bool`]
    MOI_FTB_INTERIOR_OF_OPEN_PART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
  SUBGOAL_THEN `(X:real^N->bool) INTER N = N` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let GRAPH_TUBE_FRONTIER_3 = prove
 (MOI_FND_GRAPH_TUBE_FRONTIER_3,
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `compact (derived_nbhd t (l:(real^3->bool)->bool))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `derived_nbhd t (l:(real^3->bool)->bool) SUBSET interior (UNIONS t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTB_NBHD_INTERIOR THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(subtopology euclidean (UNIONS t)) interior_of
                derived_nbhd t (l:(real^3->bool)->bool) = interior (derived_nbhd t l)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTB_INTERIOR_OF_OPEN_PART THEN
    EXISTS_TAC `interior (UNIONS (t:(real^3->bool)->bool))` THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR; INTERIOR_SUBSET];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[derived_frontier] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_FTB_FRONTIER_OF_OPEN_PART THEN
    EXISTS_TAC `interior (UNIONS (t:(real^3->bool)->bool))` THEN
    ASM_SIMP_TAC[OPEN_INTERIOR; INTERIOR_SUBSET; COMPACT_IMP_CLOSED];
    CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `interior (derived_nbhd t (l:(real^3->bool)->bool))`)) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

