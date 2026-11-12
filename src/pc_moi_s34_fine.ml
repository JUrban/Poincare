(* ========================================================================= *)
(* pc_moi_s34_fine: subdivisions of locally finite complexes finer than a   *)
(* relatively open cover, in the second-star form of MOI_S34_LF_FINE        *)
(* (Moise GTM 47, Sec 34, printed p.239, and Sec 35.1, p.251), with the     *)
(* induced subdivision of a subcomplex.  Route: the layer technique of      *)
(* pc_moi_lfopen (Moise Theorem 8.2), here over an exhaustion of t by       *)
(* finite subcomplexes, with iterated barycentric subdivisions of depth set *)
(* by gap and Lebesgue radii of the layers (HEINE_BOREL_LEMMA), glued by    *)
(* MOI_LFO_LAYER_EXT (SIMPLICIAL_SUBDIVISION_EXTEND) and MOI_LFO_CHAIN_LF.  *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_lfopen.ml";;
needs "src/pc_moi_fnd_dn.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part A: subdivisions from refinements, and induced subdivisions.         *)
(* ------------------------------------------------------------------------- *)

(* A point of a simplex t of c that lies in the polyhedron of a complex c'  *)
(* refining c lies in a simplex of c' inside t: take the face of a simplex   *)
(* of c' through the point in its relative interior.                         *)

let MOI_S4F_POINT_IN_SUBSIMPLEX = prove
 (`!(c:(real^N->bool)->bool) (c':(real^N->bool)->bool) (t:real^N->bool)
    (x:real^N).
     moi_bar_complex c /\ moi_bar_complex c' /\
     (!s. s IN c' /\ ~(s = {}) ==> ?u. u IN c /\ s SUBSET u) /\
     t IN c /\ x IN t /\ x IN UNIONS c'
     ==> ?s. s IN c' /\ x IN s /\ s SUBSET t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_bar_complex] THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS c'` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `convex(s0:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s0:real^N->bool`; `x:real^N`]
    IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^N->bool) IN c'` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN f` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?u:real^N->bool. u IN c /\ f SUBSET u` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  EXISTS_TAC `f:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t INTER u:real^N->bool` THEN
  REWRITE_TAC[INTER_SUBSET] THEN
  MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `u:real^N->bool` THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* A complex c' refining a complex c with the same polyhedron subdivides c. *)

let MOI_S4F_SUBDIVIDES = prove
 (`!(c:(real^N->bool)->bool) (c':(real^N->bool)->bool).
     moi_bar_complex c /\ moi_bar_complex c' /\ UNIONS c' = UNIONS c /\
     (!s. s IN c' ==> ?u. u IN c /\ s SUBSET u)
     ==> subdivides c' c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[subdivides] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
  EXISTS_TAC `{s:real^N->bool | s IN c' /\ s SUBSET t}` THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `c':(real^N->bool)->bool`;
                 `t:real^N->bool`; `x:real^N`] MOI_S4F_POINT_IN_SUBSIMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `UNIONS c' = UNIONS (c:(real^N->bool)->bool)` THEN
      DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[]];
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* The subdivision of a subcomplex k induced by a subdivision t' of t: the  *)
(* simplices of t' inside a simplex of k.                                    *)

let MOI_S4F_INDUCED_SUBDIVISION = prove
 (`!(t:(real^N->bool)->bool) (k:(real^N->bool)->bool)
    (t':(real^N->bool)->bool).
     simplicial_subcomplex k t /\ moi_bar_complex t' /\ subdivides t' t
     ==> simplicial_subcomplex {s | s IN t' /\ ?u. u IN k /\ s SUBSET u} t' /\
         subdivides {s | s IN t' /\ ?u. u IN k /\ s SUBSET u} k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[simplicial_subcomplex; subdivides; moi_bar_complex] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!u:real^N->bool. u IN k
       ==> ?d. d SUBSET {s | s IN t' /\ ?u. u IN k /\ s SUBSET u} /\
               UNIONS d = u`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(u:real^N->bool) IN t` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC
     `!v:real^N->bool. v IN t ==> ?d. d SUBSET t' /\ UNIONS d = v` THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `UNIONS d = (u:real^N->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[SUBSET];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(x:real^N) IN UNIONS d` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN ASM SET_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part B: a locally finite complex is countable, and it is exhausted by    *)
(* finite subcomplexes tt r, each polyhedron inside the relative interior   *)
(* of the next (tt (SUC r) = the closed star of tt r plus one more simplex). *)
(* ------------------------------------------------------------------------- *)

let MOI_S4F_LF_COUNTABLE = prove
 (`!t:(real^N->bool)->bool. lf_simplicial_complex t ==> COUNTABLE t`,
  GEN_TAC THEN REWRITE_TAC[lf_simplicial_complex] THEN STRIP_TAC THEN
  MP_TAC(ISPEC
   `{u:real^N->bool | open u /\
                      FINITE {s:real^N->bool | s IN t /\ ~(s INTER u = {})}}`
   LINDELOF) THEN
  ANTS_TAC THENL [SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN
  EXISTS_TAC
   `({}:real^N->bool) INSERT
    UNIONS (IMAGE (\u:real^N->bool.
                     {s:real^N->bool | s IN t /\ ~(s INTER u = {})}) f)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COUNTABLE_INSERT] THEN MATCH_MP_TAC COUNTABLE_UNIONS THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
    UNDISCH_TAC
     `f SUBSET {u:real^N->bool | open u /\
                 FINITE {s:real^N->bool | s IN t /\ ~(s INTER u = {})}}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INSERT; IN_UNIONS; EXISTS_IN_IMAGE] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^N` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS f` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  ASM SET_TAC[]);;

let MOI_S4F_EXHAUST = prove
 (`!t:(real^N->bool)->bool.
     lf_simplicial_complex t /\ ~(t = {})
     ==> ?tt:num->(real^N->bool)->bool.
           tt 0 = {} /\
           (!r. simplicial_subcomplex (tt r) t) /\
           (!r. FINITE (tt r)) /\
           (!r. tt r SUBSET tt (SUC r)) /\
           (!s. s IN t ==> ?r. s IN tt r) /\
           (!r x. x IN UNIONS (tt r)
                  ==> ?v. open v /\ x IN v /\
                          v INTER UNIONS t SUBSET UNIONS (tt (SUC r)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_SIMP_TAC[MOI_S4F_LF_COUNTABLE] THEN
  DISCH_THEN(X_CHOOSE_TAC `f:num->real^N->bool`) THEN
  SUBGOAL_THEN
   `(!r:num. (f:num->real^N->bool) r IN t) /\
    (!s:real^N->bool. s IN t ==> ?r. s = f r)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `t = IMAGE (f:num->real^N->bool) (:num)` THEN
  DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPECL
   [`{}:(real^N->bool)->bool`;
    `\(c:(real^N->bool)->bool) (r:num).
       {s:real^N->bool | ?q. q IN t /\
                             (~(q INTER UNIONS c = {}) \/
                              q = (f:num->real^N->bool) r) /\
                             s face_of q}`]
    num_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:num->(real^N->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "rec" o REWRITE_RULE[IN_ELIM_THM] o
       GEN_REWRITE_RULE BINDER_CONV [EXTENSION]))) THEN
  EXISTS_TAC `tt:num->(real^N->bool)->bool` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^N->bool. q IN t ==> FINITE {s | s face_of q}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_POLYTOPE_FACES THEN
    ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. simplicial_subcomplex ((tt:num->(real^N->bool)->bool) r) t /\
        FINITE (tt r)`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[simplicial_subcomplex; EMPTY_SUBSET; NOT_IN_EMPTY;
                      FINITE_EMPTY];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
      USE_THEN "rec" (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[lf_simplicial_complex];
        ASM_MESON_TAC[FACE_OF_TRANS]];
      ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `UNIONS (IMAGE (\q:real^N->bool. {s:real^N->bool | s face_of q})
       ((f:num->real^N->bool) r INSERT
        {q:real^N->bool | q IN t /\
           ~(q INTER UNIONS ((tt:num->(real^N->bool)->bool) r) = {})}))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE; FORALL_IN_INSERT] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_INSERT] THEN
        MATCH_MP_TAC MOI_FDN_LF_COMPACT_MEETS_FINITE THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
          X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
          MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `q:real^N->bool`]
            MOI_FDN_LF_SIMPLEX) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[] THEN
            ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
            SIMP_TAC[]];
          MATCH_MP_TAC SUBSET_UNIONS THEN
          ASM_MESON_TAC[simplicial_subcomplex]];
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_INSERT] THEN
      USE_THEN "rec" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:num` THEN REWRITE_TAC[SUBSET] THEN
    USE_THEN "rec" (fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) IN t` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THENL
     [EXISTS_TAC `(f:num->real^N->bool) r` THEN
      ASM_REWRITE_TAC[EMPTY_FACE_OF];
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISJ1_TAC THEN ASM SET_TAC[];
        MATCH_MP_TAC FACE_OF_REFL THEN
        ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?r:num. s = (f:num->real^N->bool) r` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `SUC r` THEN USE_THEN "rec" (fun th -> REWRITE_TAC[th]) THEN
    EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_REFL THEN
    ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `x:real^N`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`;
                 `UNIONS ((tt:num->(real^N->bool)->bool) r)`;
                 `UNIONS (t:(real^N->bool)->bool)`]
    MOI_FDN_LF_MEETS_INTERIOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ASM_REWRITE_TAC[interior_of; IN_ELIM_THM; OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(y:real^N) IN UNIONS {s:real^N->bool | s IN t /\
       ~(s INTER UNIONS ((tt:num->(real^N->bool)->bool) r) = {})}`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN CONJ_TAC THENL
   [USE_THEN "rec" (fun th -> REWRITE_TAC[th]) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FACE_OF_REFL THEN
    ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part C: metric margins from compactness (HEINE_BOREL_LEMMA): the gap     *)
(* between a compact set and the complement of a relative neighbourhood,    *)
(* and Lebesgue radii of a compact set for a relatively open cover.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4F_GAP = prove
 (`!(a:real^N->bool) (b:real^N->bool) (x0:real^N->bool).
     compact a /\
     (!x. x IN a ==> ?v. open v /\ x IN v /\ v INTER x0 SUBSET b)
     ==> ?e. &0 < e /\
             !y z. y IN a /\ z IN x0 /\ dist(y,z) < e ==> z IN b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `a:real^N->bool` HEINE_BOREL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC
    `{v:real^N->bool | open v /\ v INTER x0 SUBSET b}`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^N`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^N) IN ball(y,e)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL]; ALL_TAC] THEN
  ASM SET_TAC[]);;

let MOI_S4F_LEBESGUE = prove
 (`!(a:real^N->bool) (x0:real^N->bool) (cv:(real^N->bool)->bool).
     compact a /\ a SUBSET x0 /\ x0 SUBSET UNIONS cv /\
     (!w. w IN cv ==> open_in (subtopology euclidean x0) w)
     ==> ?e. &0 < e /\
             !y. y IN a ==> ?w. w IN cv /\ ball(y,e) INTER x0 SUBSET w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `a:real^N->bool` HEINE_BOREL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC
    `{v:real^N->bool | open v /\ ?w. w IN cv /\ v INTER x0 SUBSET w}`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?w:real^N->bool. w IN cv /\ y IN w` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC
       `!w:real^N->bool. w IN cv ==> open_in (subtopology euclidean x0) w` THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^N->bool`) THEN
      ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `v:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `w:real^N->bool` THEN ASM SET_TAC[]; ASM SET_TAC[]];
      SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  EXISTS_TAC `w:real^N->bool` THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part D: the parameters of the layers: a positive decreasing radius       *)
(* sequence below given positive sequences, and monotone depths for the     *)
(* iterated barycentric subdivisions of the finite complexes tt r.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4F_RHO = prove
 (`!(e:num->real) (ep:num->real).
     (!r. &0 < e r) /\ (!r. &0 < ep r)
     ==> ?rho:num->real.
           (!r. &0 < rho r) /\ (!r. rho r <= e r) /\
           (!r. rho r <= e (SUC r)) /\ (!r. rho r <= ep r) /\
           (!i j. i <= j ==> rho j <= rho i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`min (min ((e:num->real) 0) (e (SUC 0))) ((ep:num->real) 0)`;
    `\(x:real) (r:num).
       min x (min (min ((e:num->real) (SUC r)) (e (SUC (SUC r))))
                  ((ep:num->real) (SUC r)))`]
    num_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `rho:num->real` THEN
  SUBGOAL_THEN
   `!r. &0 < (rho:num->real) r /\ rho r <= (e:num->real) r /\
        rho r <= e (SUC r) /\ rho r <= (ep:num->real) r`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `\i j. (rho:num->real) j <= rho i` TRANSITIVE_STEPWISE_LE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_MIN_LE] THEN REAL_ARITH_TAC);;

let MOI_S4F_DEPTHS = prove
 (`!(tt:num->(real^N->bool)->bool) (eta:num->real).
     (!r. simplicial_complex (tt r)) /\ (!r. &0 < eta r)
     ==> ?nn:num->num.
           (!i j. i <= j ==> nn i <= nn j) /\
           (!r m s. nn r <= m /\ s IN ITER m barycentric_subdivision (tt r)
                    ==> diameter s < eta r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!r. ?n. !m s. n <= m /\
                  s IN ITER m barycentric_subdivision
                         ((tt:num->(real^N->bool)->bool) r)
                  ==> diameter s < (eta:num->real) r`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_LFO_ITER_FINE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `n0:num->num`) THEN
  MP_TAC(ISPECL [`(n0:num->num) 0`;
                 `\(x:num) (r:num). MAX x ((n0:num->num) (SUC r))`]
    num_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `nn:num->num` THEN
  SUBGOAL_THEN `!r. (n0:num->num) r <= nn r` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `\i j. (nn:num->num) i <= nn j` TRANSITIVE_STEPWISE_LE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LE_REFL] THEN ARITH_TAC;
    ASM_MESON_TAC[LE_TRANS]]);;

(* ------------------------------------------------------------------------- *)
(* Part E: the layers.  For the finite complexes t0 = tt r SUBSET t1 =       *)
(* tt (SUC r) the layer r is a subdivision of the simplices of               *)
(* ITER n0 barycentric_subdivision t0 not inside b = UNIONS (tt (r - 1)),     *)
(* refined to ITER n1 barycentric_subdivision t0 away from b; layer SUC r is *)
(* built in the same way from t1, n1 and UNIONS t0.                           *)
(* ------------------------------------------------------------------------- *)

(* The layer of an iterated barycentric subdivision of c over b covers the  *)
(* rest of the polyhedron of c.                                              *)

let MOI_S4F_LAYER_UNION = prove
 (`!(c:(real^N->bool)->bool) n (b:real^N->bool).
     simplicial_complex c /\ b SUBSET UNIONS c
     ==> b UNION UNIONS (moi_lfo_layer (ITER n barycentric_subdivision c)
                                       (UNIONS c) b) = UNIONS c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_lfo_poly (ITER n barycentric_subdivision c) (UNIONS c) =
    UNIONS (c:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_lfo_poly] THEN
    SUBGOAL_THEN
     `{s | s IN ITER n barycentric_subdivision c /\ s SUBSET UNIONS c} =
      ITER n barycentric_subdivision (c:(real^N->bool)->bool)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      ASM_MESON_TAC[MOI_LFO_ITER_SIMPLEX];
      ASM_SIMP_TAC[MOI_LFO_ITER_UNIONS]];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  MATCH_MP_TAC MOI_LFO_UNIONS_LAYER THEN
  ASM_SIMP_TAC[MOI_LFO_ITER_SC]);;

(* The interface: points of UNIONS t0 on the next layer lie in simplices    *)
(* common to the two subdivided layers nc0 and nc1, by the gap ep between b *)
(* and the complement of UNIONS t0 and the mesh bounds eta0, eta1.           *)

let MOI_S4F_INTERFACE = prove
 (`!(t0:(real^N->bool)->bool) (t1:(real^N->bool)->bool) n0 n1
    (b:real^N->bool) ep eta0 eta1
    (nc0:(real^N->bool)->bool) (nc1:(real^N->bool)->bool).
     simplicial_complex t1 /\ simplicial_subcomplex t0 t1 /\ n0 <= n1 /\
     (!s. s IN ITER n0 barycentric_subdivision t0 ==> diameter s < eta0) /\
     (!s. s IN ITER n1 barycentric_subdivision t1 ==> diameter s < eta1) /\
     eta0 + eta1 <= ep /\
     (!y z. y IN b /\ z IN UNIONS t1 /\ dist(y,z) < ep ==> z IN UNIONS t0) /\
     (!s. s IN moi_lfo_restrict (ITER n1 barycentric_subdivision t0)
                 (moi_lfo_outer (ITER n0 barycentric_subdivision t0)
                                (UNIONS t0) b) /\
          ~(s = {})
          ==> s IN nc0) /\
     (!s. s IN moi_lfo_layer (ITER n1 barycentric_subdivision t1)
                 (UNIONS t1) (UNIONS t0) /\
          DISJOINT s
            (UNIONS (moi_lfo_outer (ITER n1 barycentric_subdivision t1)
                                   (UNIONS t1) (UNIONS t0)))
          ==> s IN nc1)
     ==> UNIONS t0 INTER
         UNIONS (moi_lfo_layer (ITER n1 barycentric_subdivision t1)
                               (UNIONS t1) (UNIONS t0))
         SUBSET UNIONS (nc0 INTER nc1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "d0")
   (CONJUNCTS_THEN2 (LABEL_TAC "d1") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "gap")
   (CONJUNCTS_THEN2 (LABEL_TAC "nc0") (LABEL_TAC "nc1"))))))))) THEN
  SUBGOAL_THEN `simplicial_complex (t0:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LFO_SUBCOMPLEX THEN
    EXISTS_TAC `t1:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t1:(real^N->bool)->bool`; `t0:(real^N->bool)->bool`;
                 `n1:num`] MOI_FDN_ITER_SUBCOMPLEX) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  STRIP_TAC THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `(x:real^N) IN UNIONS (moi_lfo_layer (ITER n1 barycentric_subdivision t1)
                               (UNIONS t1) (UNIONS t0))` THEN
  GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN REWRITE_TAC[MOI_LFO_IN_LAYER] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool`
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
                    ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^N->bool) face_of s` THEN
    DISCH_THEN(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
    UNDISCH_TAC `(x:real^N) IN g` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^N. z IN s /\ ~(z IN UNIONS t0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~((s:real^N->bool) SUBSET UNIONS t0)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?f:real^N->bool. f IN ITER n1 barycentric_subdivision t0 /\ x IN f`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN UNIONS t0` THEN
    UNDISCH_TAC
     `UNIONS (ITER n1 barycentric_subdivision t0) =
      UNIONS (t0:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->bool) IN ITER n1 barycentric_subdivision t1`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(f:real^N->bool) IN ITER n1 barycentric_subdivision t0` THEN
    UNDISCH_TAC
     `simplicial_subcomplex (ITER n1 barycentric_subdivision t0)
        (ITER n1 barycentric_subdivision (t1:(real^N->bool)->bool))` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(s INTER f:real^N->bool) face_of s /\ (s INTER f) face_of f`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t1:(real^N->bool)->bool`; `n1:num`] MOI_LFO_ITER_SC) THEN
    ASM_REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `f:real^N->bool`] o
      last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(s INTER f:real^N->bool) IN ITER n1 barycentric_subdivision t0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t0:(real^N->bool)->bool`; `n1:num`] MOI_LFO_ITER_SC) THEN
    ASM_REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`s INTER f:real^N->bool`; `f:real^N->bool`] o
      el 2 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->bool) SUBSET UNIONS t0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t0:(real^N->bool)->bool`; `n1:num`; `f:real^N->bool`]
      MOI_LFO_ITER_SIMPLEX) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN s INTER f` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `~(s INTER f:real^N->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN s INTER f` THEN SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [IN_UNIONS] THEN
  EXISTS_TAC `s INTER f:real^N->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    USE_THEN "nc1" MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[MOI_LFO_IN_LAYER] THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SET_RULE
       `DISJOINT (a:real^N->bool) (UNIONS u) <=>
        !v. v IN u ==> DISJOINT a v`] THEN
      REWRITE_TAC[MOI_LFO_IN_OUTER] THEN
      UNDISCH_TAC `(f:real^N->bool) SUBSET UNIONS t0` THEN SET_TAC[]]] THEN
  USE_THEN "nc0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_LFO_IN_RESTRICT] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t0:(real^N->bool)->bool`; `n1:num`; `n0:num`]
    MOI_LFO_ITER_REFINES) THEN
  ASM_REWRITE_TAC[moi_lfo_refines] THEN
  DISCH_THEN(MP_TAC o SPEC `s INTER f:real^N->bool` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bounded(h:real^N->bool) /\ h SUBSET UNIONS t0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t0:(real^N->bool)->bool`; `n0:num`; `h:real^N->bool`]
      MOI_LFO_ITER_SIMPLEX) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bounded(s:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t1:(real^N->bool)->bool`; `n1:num`; `s:real^N->bool`]
      MOI_LFO_ITER_SIMPLEX) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN h` ASSUME_TAC THENL
   [UNDISCH_TAC `(s INTER f:real^N->bool) SUBSET h` THEN
    UNDISCH_TAC `(x:real^N) IN s INTER f` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `h INTER (b:real^N->bool) = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `dist(y:real^N,x) <= diameter(h:real^N->bool) /\
                  dist(x:real^N,z) <= diameter(s:real^N->bool)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[dist] THEN CONJ_TAC THEN
      MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `diameter(h:real^N->bool) < eta0 /\
                  diameter(s:real^N->bool) < eta1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "d0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "d1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(y:real^N,z) < ep` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`y:real^N`; `x:real^N`; `z:real^N`] DIST_TRIANGLE) THEN
      UNDISCH_TAC `eta0 + eta1 <= ep` THEN
      UNDISCH_TAC `dist(y:real^N,x) <= diameter(h:real^N->bool)` THEN
      UNDISCH_TAC `dist(x:real^N,z) <= diameter(s:real^N->bool)` THEN
      UNDISCH_TAC `diameter(h:real^N->bool) < eta0` THEN
      UNDISCH_TAC `diameter(s:real^N->bool) < eta1` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN UNIONS t1` ASSUME_TAC THENL
     [UNDISCH_TAC `(s:real^N->bool) SUBSET UNIONS t1` THEN
      UNDISCH_TAC `(z:real^N) IN s` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~((z:real^N) IN UNIONS t0)` THEN REWRITE_TAC[] THEN
    USE_THEN "gap" MATCH_MP_TAC THEN EXISTS_TAC `y:real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_LFO_IN_OUTER; MOI_LFO_IN_LAYER] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `h:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `h INTER (b:real^N->bool) = {}` THEN
    UNDISCH_TAC `(x:real^N) IN h` THEN SET_TAC[];
    MATCH_MP_TAC FACE_OF_REFL THEN
    MP_TAC(ISPECL [`t0:(real^N->bool)->bool`; `n0:num`] MOI_LFO_ITER_SC) THEN
    ASM_REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `h:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX]]);;

(* The layer after next misses UNIONS t0 (Moise's condition that the union  *)
(* of the first layers is a neighbourhood of the earlier ones), by the gap   *)
(* ep between UNIONS t0 and the complement of UNIONS t1.                      *)

let MOI_S4F_MISS = prove
 (`!(t0:(real^N->bool)->bool) (t1:(real^N->bool)->bool)
    (t2:(real^N->bool)->bool) n2 ep eta2.
     simplicial_complex t2 /\
     (!s. s IN ITER n2 barycentric_subdivision t2 ==> diameter s < eta2) /\
     eta2 <= ep /\
     (!y z. y IN UNIONS t0 /\ z IN UNIONS t2 /\ dist(y,z) < ep
            ==> z IN UNIONS t1)
     ==> UNIONS t0 INTER
         UNIONS (moi_lfo_layer (ITER n2 barycentric_subdivision t2)
                               (UNIONS t2) (UNIONS t1)) = {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  UNDISCH_TAC
   `(x:real^N) IN UNIONS (moi_lfo_layer (ITER n2 barycentric_subdivision t2)
                               (UNIONS t2) (UNIONS t1))` THEN
  REWRITE_TAC[IN_UNIONS; MOI_LFO_IN_LAYER] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool`
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
                    ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^N->bool) face_of s` THEN
    DISCH_THEN(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^N. z IN s /\ ~(z IN UNIONS t1)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bounded(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LFO_ITER_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `dist(x:real^N,z) < ep` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `diameter(s:real^N->bool)` THEN CONJ_TAC THENL
     [REWRITE_TAC[dist] THEN ASM_MESON_TAC[DIAMETER_BOUNDED_BOUND];
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `eta2:real` THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN UNIONS t1` (fun th -> ASM_MESON_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:real^N` THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part F: the family of subdivided layers nc r (Moise's L'_r, here for the  *)
(* exhaustion tt) and the conditions of MOI_LFO_CHAIN_LF for it.             *)
(* ------------------------------------------------------------------------- *)

let MOI_S4F_LAYER_FAMILY = prove
 (`!(tt:num->(real^N->bool)->bool) (nn:num->num).
     (!r. simplicial_complex (tt r)) /\ (!i j. i <= j ==> nn i <= nn j)
     ==> ?nc:num->(real^N->bool)->bool.
           !r. simplicial_complex (nc r) /\
               UNIONS (nc r) =
               UNIONS (moi_lfo_layer
                        (ITER (nn r) barycentric_subdivision (tt r))
                        (UNIONS (tt r)) (UNIONS (tt (r - 1)))) /\
               (!s. s IN nc r
                    ==> ?u. u IN moi_lfo_layer
                                   (ITER (nn r) barycentric_subdivision (tt r))
                                   (UNIONS (tt r)) (UNIONS (tt (r - 1))) /\
                            s SUBSET u) /\
               (!s. s IN moi_lfo_restrict
                          (ITER (nn (SUC r)) barycentric_subdivision (tt r))
                          (moi_lfo_outer
                             (ITER (nn r) barycentric_subdivision (tt r))
                             (UNIONS (tt r)) (UNIONS (tt (r - 1)))) /\
                    ~(s = {})
                    ==> s IN nc r) /\
               (!s. s IN moi_lfo_layer
                          (ITER (nn r) barycentric_subdivision (tt r))
                          (UNIONS (tt r)) (UNIONS (tt (r - 1))) /\
                    DISJOINT s
                      (UNIONS (moi_lfo_outer
                                 (ITER (nn r) barycentric_subdivision (tt r))
                                 (UNIONS (tt r)) (UNIONS (tt (r - 1)))))
                    ==> s IN nc r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN
  X_GEN_TAC `r:num` THEN MATCH_MP_TAC MOI_LFO_LAYER_EXT THEN
  REWRITE_TAC[SIMPLICIAL_SUBDIVISION_EXTEND] THEN
  ASM_SIMP_TAC[MOI_LFO_ITER_SC] THEN
  MATCH_MP_TAC MOI_LFO_ITER_REFINES THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

let MOI_S4F_LAYERS = prove
 (`!(t:(real^N->bool)->bool) (tt:num->(real^N->bool)->bool) (nn:num->num)
    (rho:num->real) (ep:num->real).
     lf_simplicial_complex t /\ tt 0 = {} /\
     (!r. simplicial_subcomplex (tt r) t) /\ (!r. FINITE (tt r)) /\
     (!r. tt r SUBSET tt (SUC r)) /\
     (!i j. i <= j ==> nn i <= nn j) /\
     (!r m s. nn r <= m /\ s IN ITER m barycentric_subdivision (tt r)
              ==> diameter s < rho r / &4) /\
     (!r. &0 < rho r) /\ (!i j. i <= j ==> rho j <= rho i) /\
     (!r. rho r <= ep r) /\
     (!r y z. y IN UNIONS (tt r) /\ z IN UNIONS t /\ dist(y,z) < ep r
              ==> z IN UNIONS (tt (SUC r)))
     ==> ?nc:num->(real^N->bool)->bool.
           (!r. simplicial_complex (nc r)) /\
           UNIONS (nc 0) = UNIONS (tt 0) /\
           (!r. UNIONS (tt r) UNION UNIONS (nc (SUC r)) =
                UNIONS (tt (SUC r))) /\
           (!r. UNIONS (tt r) INTER UNIONS (nc (SUC r))
                SUBSET UNIONS (nc r INTER nc (SUC r))) /\
           (!r. UNIONS (tt r) INTER UNIONS (nc (SUC (SUC r))) = {}) /\
           (!r s. s IN nc r ==> diameter s < rho r / &4) /\
           (!r s. s IN nc r /\ ~(s = {}) ==> ?u. u IN t /\ s SUBSET u)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "t0")
   (CONJUNCTS_THEN2 (LABEL_TAC "sub") (CONJUNCTS_THEN2 (LABEL_TAC "fin")
   (CONJUNCTS_THEN2 (LABEL_TAC "inc") (CONJUNCTS_THEN2 (LABEL_TAC "nnm")
   (CONJUNCTS_THEN2 (LABEL_TAC "dep") (CONJUNCTS_THEN2 (LABEL_TAC "rpos")
   (CONJUNCTS_THEN2 (LABEL_TAC "rdec") (CONJUNCTS_THEN2 (LABEL_TAC "rep")
   (LABEL_TAC "gap"))))))))))) THEN
  SUBGOAL_THEN `!r. simplicial_complex ((tt:num->(real^N->bool)->bool) r)`
  (LABEL_TAC "sc") THENL
   [GEN_TAC THEN REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    ASM_MESON_TAC[MOI_FDN_LF_SUBCOMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. i <= j ==> (tt:num->(real^N->bool)->bool) i SUBSET tt j`
  (LABEL_TAC "mono") THENL
   [MP_TAC(ISPEC `\i j. (tt:num->(real^N->bool)->bool) i SUBSET tt j`
      TRANSITIVE_STEPWISE_LE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "inc" (fun th -> REWRITE_TAC[th; SUBSET_REFL]) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r s. s IN ITER ((nn:num->num) r) barycentric_subdivision
                    ((tt:num->(real^N->bool)->bool) r)
          ==> diameter s < (rho:num->real) r / &4`
  (LABEL_TAC "dep0") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "dep" MATCH_MP_TAC THEN
    EXISTS_TAC `(nn:num->num) r` THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:num->(real^N->bool)->bool`; `nn:num->num`]
    MOI_S4F_LAYER_FAMILY) THEN
  ANTS_TAC THENL
   [USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "nnm" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nc:num->(real^N->bool)->bool` (LABEL_TAC "nc")) THEN
  EXISTS_TAC `nc:num->(real^N->bool)->bool` THEN
  SUBGOAL_THEN
   `!r. UNIONS ((tt:num->(real^N->bool)->bool) (r - 1)) UNION
        UNIONS ((nc:num->(real^N->bool)->bool) r) = UNIONS (tt r)`
  (LABEL_TAC "un") THENL
   [GEN_TAC THEN
    USE_THEN "nc" (fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(SPEC `r:num` th))]) THEN
    MATCH_MP_TAC MOI_S4F_LAYER_UNION THEN
    USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SUBSET_UNIONS THEN USE_THEN "mono" MATCH_MP_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "nc" (fun th -> REWRITE_TAC[th]);
    USE_THEN "un" (MP_TAC o SPEC `0`) THEN
    USE_THEN "t0" (fun th -> REWRITE_TAC[th; ARITH_RULE `0 - 1 = 0`;
                                         UNIONS_0; UNION_EMPTY]);
    X_GEN_TAC `r:num` THEN USE_THEN "un" (MP_TAC o SPEC `SUC r`) THEN
    REWRITE_TAC[SUC_SUB1];
    X_GEN_TAC `r:num` THEN
    USE_THEN "nc" (MP_TAC o SPEC `SUC r`) THEN REWRITE_TAC[SUC_SUB1] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 SUBST1_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
        (LABEL_TAC "nc1"))))) THEN
    USE_THEN "nc" (MP_TAC o SPEC `r:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "nc0")
        (K ALL_TAC))))) THEN
    MATCH_MP_TAC MOI_S4F_INTERFACE THEN
    MAP_EVERY EXISTS_TAC
     [`(nn:num->num) r`; `UNIONS ((tt:num->(real^N->bool)->bool) (r - 1))`;
      `(ep:num->real) (r - 1)`; `(rho:num->real) r / &4`;
      `(rho:num->real) (SUC r) / &4`] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "sc" (fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[simplicial_subcomplex] THEN CONJ_TAC THENL
       [USE_THEN "inc" (fun th -> REWRITE_TAC[th]);
        USE_THEN "sub" (MP_TAC o SPEC `r:num`) THEN
        REWRITE_TAC[simplicial_subcomplex] THEN MESON_TAC[]];
      USE_THEN "nnm" MATCH_MP_TAC THEN ARITH_TAC;
      USE_THEN "dep0" (fun th -> REWRITE_TAC[th]);
      USE_THEN "dep0" (fun th -> REWRITE_TAC[th]);
      USE_THEN "rdec" (MP_TAC o SPECL [`r - 1`; `r:num`]) THEN
      USE_THEN "rdec" (MP_TAC o SPECL [`r - 1`; `SUC r`]) THEN
      USE_THEN "rep" (MP_TAC o SPEC `r - 1`) THEN
      USE_THEN "rpos" (MP_TAC o SPEC `r - 1`) THEN
      REWRITE_TAC[ARITH_RULE `r - 1 <= r /\ r - 1 <= SUC r`] THEN
      REAL_ARITH_TAC;
      STRUCT_CASES_TAC(SPEC `r:num` num_CASES) THENL
       [USE_THEN "t0" (fun th -> REWRITE_TAC[th; ARITH_RULE `0 - 1 = 0`;
                                             UNIONS_0; NOT_IN_EMPTY]);
        REWRITE_TAC[SUC_SUB1] THEN
        MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^N`] THEN STRIP_TAC THEN
        USE_THEN "gap" MATCH_MP_TAC THEN EXISTS_TAC `y:real^N` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC
         `(z:real^N) IN UNIONS ((tt:num->(real^N->bool)->bool) (SUC (SUC n)))` THEN
        USE_THEN "sub" (MP_TAC o SPEC `SUC (SUC n)`) THEN
        REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[]];
      USE_THEN "nc0" ACCEPT_TAC;
      USE_THEN "nc1" ACCEPT_TAC];
    X_GEN_TAC `r:num` THEN
    USE_THEN "nc" (MP_TAC o SPEC `SUC (SUC r)`) THEN REWRITE_TAC[SUC_SUB1] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))) THEN
    MATCH_MP_TAC MOI_S4F_MISS THEN
    MAP_EVERY EXISTS_TAC
     [`(ep:num->real) r`; `(rho:num->real) (SUC (SUC r)) / &4`] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "sc" (fun th -> REWRITE_TAC[th]);
      USE_THEN "dep0" (fun th -> REWRITE_TAC[th]);
      USE_THEN "rdec" (MP_TAC o SPECL [`r:num`; `SUC (SUC r)`]) THEN
      USE_THEN "rep" (MP_TAC o SPEC `r:num`) THEN
      USE_THEN "rpos" (MP_TAC o SPEC `SUC (SUC r)`) THEN
      REWRITE_TAC[ARITH_RULE `r <= SUC (SUC r)`] THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^N`] THEN STRIP_TAC THEN
      USE_THEN "gap" MATCH_MP_TAC THEN EXISTS_TAC `y:real^N` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `(z:real^N) IN UNIONS ((tt:num->(real^N->bool)->bool) (SUC (SUC r)))` THEN
      USE_THEN "sub" (MP_TAC o SPEC `SUC (SUC r)`) THEN
      REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`r:num`; `s:real^N->bool`] THEN DISCH_TAC THEN
    USE_THEN "nc" (fun th -> MP_TAC(MATCH_MP
      (CONJUNCT1(CONJUNCT2(CONJUNCT2(SPEC `r:num` th))))
      (ASSUME `(s:real^N->bool) IN nc (r:num)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(u:real^N->bool) IN ITER ((nn:num->num) r) barycentric_subdivision
                             ((tt:num->(real^N->bool)->bool) r)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`ITER ((nn:num->num) r) barycentric_subdivision
              ((tt:num->(real^N->bool)->bool) r)`;
        `UNIONS ((tt:num->(real^N->bool)->bool) r)`;
        `UNIONS ((tt:num->(real^N->bool)->bool) (r - 1))`]
       MOI_LFO_LAYER_SUBSET) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC MOI_LFO_ITER_SC THEN
        USE_THEN "sc" (fun th -> REWRITE_TAC[th]);
        DISCH_THEN(MP_TAC o SPEC `u:real^N->bool` o REWRITE_RULE[SUBSET]) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `diameter(u:real^N->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIAMETER_SUBSET THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(tt:num->(real^N->bool)->bool) r`; `(nn:num->num) r`;
                     `u:real^N->bool`] MOI_LFO_ITER_SIMPLEX) THEN
      USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[];
      USE_THEN "dep0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`r:num`; `s:real^N->bool`] THEN STRIP_TAC THEN
    USE_THEN "nc" (fun th -> MP_TAC(MATCH_MP
      (CONJUNCT1(CONJUNCT2(CONJUNCT2(SPEC `r:num` th))))
      (ASSUME `(s:real^N->bool) IN nc (r:num)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(u:real^N->bool) IN ITER ((nn:num->num) r) barycentric_subdivision
                             ((tt:num->(real^N->bool)->bool) r)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`ITER ((nn:num->num) r) barycentric_subdivision
              ((tt:num->(real^N->bool)->bool) r)`;
        `UNIONS ((tt:num->(real^N->bool)->bool) r)`;
        `UNIONS ((tt:num->(real^N->bool)->bool) (r - 1))`]
       MOI_LFO_LAYER_SUBSET) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC MOI_LFO_ITER_SC THEN
        USE_THEN "sc" (fun th -> REWRITE_TAC[th]);
        DISCH_THEN(MP_TAC o SPEC `u:real^N->bool` o REWRITE_RULE[SUBSET]) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(tt:num->(real^N->bool)->bool) r`; `(nn:num->num) r`;
                   `0`] MOI_LFO_ITER_REFINES) THEN
    USE_THEN "sc" (fun th -> REWRITE_TAC[th; LE_0; ITER; moi_lfo_refines]) THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^N->bool` o CONJUNCT1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(s:real^N->bool) SUBSET u` THEN
      UNDISCH_TAC `~(s:real^N->bool = {})` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^N->bool` THEN CONJ_TAC THENL
     [USE_THEN "sub" (MP_TAC o SPEC `r:num`) THEN
      REWRITE_TAC[simplicial_subcomplex] THEN
      UNDISCH_TAC `(v:real^N->bool) IN tt (r:num)` THEN SET_TAC[];
      UNDISCH_TAC `(s:real^N->bool) SUBSET u` THEN
      UNDISCH_TAC `(u:real^N->bool) SUBSET v` THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part G: the union t' of a chain of layers nc r over polyhedra a r         *)
(* (the hypotheses of MOI_LFO_CHAIN_LF) is a locally finite subdivision of t *)
(* and, with mesh eta r on layer r and Lebesgue radii e r of a r with        *)
(* 2 eta i <= e r for r <= SUC i, it is fine in the second-star sense.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S4F_CHAIN_POLY = prove
 (`!(nc:num->(real^N->bool)->bool) (a:num->real^N->bool).
     UNIONS (nc 0) = a 0 /\
     (!r. a r UNION UNIONS (nc (SUC r)) = a (SUC r))
     ==> (!r. UNIONS (nc r) SUBSET a r) /\
         (!i j. i <= j ==> a i SUBSET a j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [INDUCT_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN SET_TAC[];
    MP_TAC(ISPEC `\i j. (a:num->real^N->bool) i SUBSET a j`
      TRANSITIVE_STEPWISE_LE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
     [MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    SET_TAC[]]);;

(* Two meeting simplices of the chain lie in layers at most one apart in    *)
(* the direction that matters here.                                          *)

let MOI_S4F_CHAIN_MEET = prove
 (`!(nc:num->(real^N->bool)->bool) (a:num->real^N->bool) i j q q1.
     UNIONS (nc 0) = a 0 /\
     (!r. a r UNION UNIONS (nc (SUC r)) = a (SUC r)) /\
     (!r. a r INTER UNIONS (nc (SUC (SUC r))) = {}) /\
     q IN nc i /\ q1 IN nc j /\ ~(q INTER q1 = {})
     ==> j <= SUC i`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "miss") STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`nc:num->(real^N->bool)->bool`; `a:num->real^N->bool`]
    MOI_S4F_CHAIN_POLY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "poly") (LABEL_TAC "mono")) THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `m = j - 2` THEN
  SUBGOAL_THEN `SUC (SUC m) = j /\ i <= m` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`j - 2 = m`; `SUC i < j`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^N->bool) SUBSET a (m:num)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(a:num->real^N->bool) i` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS ((nc:num->(real^N->bool)->bool) i)` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(q:real^N->bool) IN nc (i:num)` THEN SET_TAC[];
        USE_THEN "poly" (fun th -> REWRITE_TAC[th])];
      USE_THEN "mono" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q1:real^N->bool) SUBSET UNIONS (nc (SUC (SUC m)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `SUC (SUC m) = j` THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `(q1:real^N->bool) IN nc (j:num)` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "miss" (MP_TAC o SPEC `m:num`) THEN
  UNDISCH_TAC `~((q:real^N->bool) INTER q1 = {})` THEN
  UNDISCH_TAC `(q:real^N->bool) SUBSET a (m:num)` THEN
  UNDISCH_TAC `(q1:real^N->bool) SUBSET UNIONS (nc (SUC (SUC m)))` THEN
  SET_TAC[]);;

(* A simplex through a point v of a r, r minimal, is in a layer j >= r.     *)

let MOI_S4F_CHAIN_FIRST = prove
 (`!(nc:num->(real^N->bool)->bool) (a:num->real^N->bool) r j (v:real^N) q1.
     UNIONS (nc 0) = a 0 /\
     (!r. a r UNION UNIONS (nc (SUC r)) = a (SUC r)) /\
     (!m. m < r ==> ~(v IN a m)) /\ q1 IN nc j /\ v IN q1
     ==> r <= j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`nc:num->(real^N->bool)->bool`; `a:num->real^N->bool`]
    MOI_S4F_CHAIN_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `!m:num. m < r ==> ~((v:real^N) IN (a:num->real^N->bool) m)` THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `!r. UNIONS ((nc:num->(real^N->bool)->bool) r) SUBSET a r` THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
  UNDISCH_TAC `(q1:real^N->bool) IN nc (j:num)` THEN
  UNDISCH_TAC `(v:real^N) IN q1` THEN SET_TAC[]);;

(* The union of the chain is a locally finite subdivision of t.             *)

let MOI_S4F_CHAIN_SUBDIVIDES = prove
 (`!(t:(real^N->bool)->bool) (nc:num->(real^N->bool)->bool)
    (a:num->real^N->bool).
     lf_simplicial_complex t /\ ~(t = {}) /\
     (!r. simplicial_complex (nc r)) /\
     UNIONS (nc 0) = a 0 /\
     (!r. a r UNION UNIONS (nc (SUC r)) = a (SUC r)) /\
     (!r. a r INTER UNIONS (nc (SUC r)) SUBSET UNIONS (nc r INTER nc (SUC r))) /\
     (!r. a r INTER UNIONS (nc (SUC (SUC r))) = {}) /\
     (!r. a r SUBSET UNIONS t) /\
     (!r x. x IN a r
            ==> ?v. open v /\ x IN v /\ v INTER UNIONS t SUBSET a (SUC r)) /\
     UNIONS t SUBSET UNIONS (IMAGE a (:num)) /\
     (!r s. s IN nc r /\ ~(s = {}) ==> ?u. u IN t /\ s SUBSET u)
     ==> lf_simplicial_complex (UNIONS (IMAGE nc (:num))) /\
         UNIONS (UNIONS (IMAGE nc (:num))) = UNIONS t /\
         subdivides (UNIONS (IMAGE nc (:num))) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`nc:num->(real^N->bool)->bool`; `a:num->real^N->bool`;
                 `UNIONS (t:(real^N->bool)->bool)`] MOI_LFO_CHAIN_LF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `UNIONS (IMAGE (a:num->real^N->bool) (:num)) = UNIONS t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; IN_UNIV];
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4F_SUBDIVIDES THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX];
    ASM_MESON_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX];
    REWRITE_TAC[MOI_LFO_IN_UNIONS_IMAGE] THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_TAC `r:num`) THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THENL
     [ASM_REWRITE_TAC[EMPTY_SUBSET; MEMBER_NOT_EMPTY];
      ASM_MESON_TAC[]]]);;

(* The second-star condition of MOI_S34_LF_FINE for the union of a chain.   *)

let MOI_S4F_CHAIN_STAR = prove
 (`!(t:(real^N->bool)->bool) (cv:(real^N->bool)->bool)
    (nc:num->(real^N->bool)->bool) (a:num->real^N->bool)
    (eta:num->real) (e:num->real).
     UNIONS (nc 0) = a 0 /\
     (!r. a r UNION UNIONS (nc (SUC r)) = a (SUC r)) /\
     (!r. a r INTER UNIONS (nc (SUC (SUC r))) = {}) /\
     UNIONS t SUBSET UNIONS (IMAGE a (:num)) /\
     UNIONS (UNIONS (IMAGE nc (:num))) = UNIONS t /\
     (!r s. s IN nc r ==> bounded s /\ diameter s < eta r) /\
     (!r y. y IN a r ==> ?w. w IN cv /\ ball(y,e r) INTER UNIONS t SUBSET w) /\
     (!r i. r <= SUC i ==> &2 * eta i <= e r)
     ==> !v. {v} IN UNIONS (IMAGE nc (:num))
             ==> ?w. w IN cv /\
                     UNIONS {q | q IN UNIONS (IMAGE nc (:num)) /\
                                 ~(q INTER
                                   moi_s34_cstar (UNIONS (IMAGE nc (:num))) {v}
                                   = {})}
                     SUBSET w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cov")
   (CONJUNCTS_THEN2 (LABEL_TAC "un") (CONJUNCTS_THEN2 (LABEL_TAC "diam")
   (CONJUNCTS_THEN2 (LABEL_TAC "leb") (LABEL_TAC "eta")))))))) THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN UNIONS t` ASSUME_TAC THENL
   [USE_THEN "un" (fun th -> REWRITE_TAC[SYM th]) THEN
    GEN_REWRITE_TAC I [IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r:num. (v:real^N) IN (a:num->real^N->bool) r /\
            !m:num. m < r ==> ~(v IN a m)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `\r:num. (v:real^N) IN (a:num->real^N->bool) r` num_WOP) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "cov" (MP_TAC o SPEC `v:real^N` o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "leb" (fun th -> MP_TAC(MATCH_MP (SPECL [`r:num`; `v:real^N`] th)
    (ASSUME `(v:real^N) IN (a:num->real^N->bool) r`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM; moi_s34_cstar] THEN
  X_GEN_TAC `q:real^N->bool` THEN
  REWRITE_TAC[MOI_LFO_IN_UNIONS_IMAGE] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNIONS; IN_ELIM_THM;
              IN_SING] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `i:num`)
   (X_CHOOSE_THEN `p:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `q1:real^N->bool` MP_TAC)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `j:num`)
     (X_CHOOSE_THEN `v':real^N` STRIP_ASSUME_TAC))
   ASSUME_TAC) THEN
  UNDISCH_TAC `(v':real^N) = v` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `r <= j /\ j <= SUC i` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4F_CHAIN_FIRST THEN
      MAP_EVERY EXISTS_TAC [`nc:num->(real^N->bool)->bool`;
        `a:num->real^N->bool`; `v:real^N`; `q1:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S4F_CHAIN_MEET THEN
      MAP_EVERY EXISTS_TAC [`nc:num->(real^N->bool)->bool`;
        `a:num->real^N->bool`; `q:real^N->bool`; `q1:real^N->bool`] THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "diam" (fun th -> MP_TAC(MATCH_MP
    (SPECL [`i:num`; `q:real^N->bool`] th)
    (ASSUME `(q:real^N->bool) IN nc (i:num)`))) THEN
  USE_THEN "diam" (fun th -> MP_TAC(MATCH_MP
    (SPECL [`j:num`; `q1:real^N->bool`] th)
    (ASSUME `(q1:real^N->bool) IN nc (j:num)`))) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 * (eta:num->real) i <= e(r:num) /\
                &2 * (eta:num->real) j <= e(r:num)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "eta" MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`r:num <= j`; `j:num <= SUC i`] THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN ball(v,e(r:num)) INTER UNIONS t`
    (fun th -> ASM SET_TAC[th]) THEN
  REWRITE_TAC[IN_INTER; IN_BALL] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `dist(v:real^N,p) <= diameter(q1:real^N->bool) /\
                  dist(p:real^N,y) <= diameter(q:real^N->bool)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[dist] THEN CONJ_TAC THEN
      MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`v:real^N`; `p:real^N`; `y:real^N`] DIST_TRIANGLE) THEN
    MAP_EVERY UNDISCH_TAC
     [`dist(v:real^N,p) <= diameter(q1:real^N->bool)`;
      `dist(p:real^N,y) <= diameter(q:real^N->bool)`;
      `diameter(q1:real^N->bool) < (eta:num->real) j`;
      `diameter(q:real^N->bool) < (eta:num->real) i`;
      `&2 * (eta:num->real) i <= e(r:num)`;
      `&2 * (eta:num->real) j <= e(r:num)`] THEN
    REAL_ARITH_TAC;
    USE_THEN "un" (fun th -> REWRITE_TAC[SYM th]) THEN
    GEN_REWRITE_TAC I [IN_UNIONS] THEN
    EXISTS_TAC `q:real^N->bool` THEN
    ASM_REWRITE_TAC[MOI_LFO_IN_UNIONS_IMAGE] THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part H: the theorem LF_FINE (the statement MOI_S34_LF_FINE of             *)
(* pc_moi_s34_stmt.ml).  t = {} is MOI_S4D_SAN_LF_FINE_EMPTY; otherwise the  *)
(* exhaustion tt, gaps ep, Lebesgue radii e, radii rho and depths nn give    *)
(* the layers nc, whose union t' is the subdivision; k' is induced.          *)
(* ------------------------------------------------------------------------- *)

let LF_FINE = prove
 (`!(t:(real^N->bool)->bool) (k:(real^N->bool)->bool)
    (cv:(real^N->bool)->bool).
     lf_simplicial_complex t /\ simplicial_subcomplex k t /\
     (!w. w IN cv ==> open_in (subtopology euclidean (UNIONS t)) w) /\
     UNIONS t SUBSET UNIONS cv
     ==> ?t' k'. lf_simplicial_complex t' /\ subdivides t' t /\
                 simplicial_subcomplex k' t' /\ subdivides k' k /\
                 !v. {v} IN t'
                     ==> ?w. w IN cv /\
                             UNIONS {q | q IN t' /\
                                         ~(q INTER moi_s34_cstar t' {v} = {})}
                             SUBSET w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:(real^N->bool)->bool = {}` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC MOI_S4D_SAN_LF_FINE_EMPTY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_S4F_EXHAUST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:num->(real^N->bool)->bool`
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!r. simplicial_complex ((tt:num->(real^N->bool)->bool) r)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    ASM_MESON_TAC[MOI_FDN_LF_SUBCOMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. compact (UNIONS ((tt:num->(real^N->bool)->bool) r)) /\
        UNIONS (tt r) SUBSET UNIONS t`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_LFO_SIMPLEX_COMPACT];
      MATCH_MP_TAC SUBSET_UNIONS THEN ASM_MESON_TAC[simplicial_subcomplex]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS t SUBSET
    UNIONS (IMAGE (\r:num. UNIONS ((tt:num->(real^N->bool)->bool) r)) (:num))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?r:num. (s:real^N->bool) IN
                          (tt:num->(real^N->bool)->bool) r`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `r:num` THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?ep:num->real.
      (!r. &0 < ep r) /\
      (!r y z. y IN UNIONS ((tt:num->(real^N->bool)->bool) r) /\
               z IN UNIONS t /\ dist(y,z) < ep r
               ==> z IN UNIONS (tt (SUC r)))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!r. ?e. &0 < e /\
              !y z. y IN UNIONS ((tt:num->(real^N->bool)->bool) r) /\
                    z IN UNIONS t /\ dist(y,z) < e
                    ==> z IN UNIONS (tt (SUC r))`
    MP_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MOI_S4F_GAP THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SKOLEM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e:num->real.
      (!r. &0 < e r) /\
      (!r y. y IN UNIONS ((tt:num->(real^N->bool)->bool) r)
             ==> ?w. w IN cv /\ ball(y,e r) INTER UNIONS t SUBSET w)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!r. ?e. &0 < e /\
              !y. y IN UNIONS ((tt:num->(real^N->bool)->bool) r)
                  ==> ?w. w IN cv /\ ball(y,e) INTER UNIONS t SUBSET w`
    MP_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MOI_S4F_LEBESGUE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SKOLEM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:num->real`; `ep:num->real`] MOI_S4F_RHO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:num->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:num->(real^N->bool)->bool`;
                 `\r:num. (rho:num->real) r / &4`] MOI_S4F_DEPTHS) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:num->num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `tt:num->(real^N->bool)->bool`;
                 `nn:num->num`; `rho:num->real`; `ep:num->real`]
    MOI_S4F_LAYERS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nc:num->(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `nc:num->(real^N->bool)->bool`;
                 `\r:num. UNIONS ((tt:num->(real^N->bool)->bool) r)`]
    MOI_S4F_CHAIN_SUBDIVIDES) THEN
  BETA_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `cv:(real^N->bool)->bool`;
                 `nc:num->(real^N->bool)->bool`;
                 `\r:num. UNIONS ((tt:num->(real^N->bool)->bool) r)`;
                 `\r:num. (rho:num->real) r / &4`; `e:num->real`]
    MOI_S4F_CHAIN_STAR) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_LFO_SIMPLEX_COMPACT]; ASM_MESON_TAC[]];
      MAP_EVERY X_GEN_TAC [`r:num`; `i:num`] THEN
      STRUCT_CASES_TAC(SPEC `r:num` num_CASES) THENL
       [DISCH_TAC THEN
        MP_TAC(SPECL [`0`; `i:num`]
          (ASSUME `!i j. i <= j ==> (rho:num->real) j <= rho i`)) THEN
        MP_TAC(SPEC `0` (ASSUME `!r. (rho:num->real) r <= e r`)) THEN
        MP_TAC(SPEC `i:num` (ASSUME `!r. &0 < (rho:num->real) r`)) THEN
        REWRITE_TAC[LE_0] THEN REAL_ARITH_TAC;
        REWRITE_TAC[LE_SUC] THEN DISCH_TAC THEN
        MP_TAC(MATCH_MP (SPECL [`n:num`; `i:num`]
          (ASSUME `!i j. i <= j ==> (rho:num->real) j <= rho i`))
          (ASSUME `n:num <= i`)) THEN
        MP_TAC(SPEC `n:num` (ASSUME `!r. (rho:num->real) r <= e (SUC r)`)) THEN
        MP_TAC(SPEC `i:num` (ASSUME `!r. &0 < (rho:num->real) r`)) THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  EXISTS_TAC `UNIONS (IMAGE (nc:num->(real^N->bool)->bool) (:num))` THEN
  EXISTS_TAC
   `{s | s IN UNIONS (IMAGE (nc:num->(real^N->bool)->bool) (:num)) /\
         ?u. u IN k /\ s SUBSET u}` THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
                 `UNIONS (IMAGE (nc:num->(real^N->bool)->bool) (:num))`]
    MOI_S4F_INDUCED_SUBDIVISION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

