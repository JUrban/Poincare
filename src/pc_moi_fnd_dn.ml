(* ========================================================================= *)
(* pc_moi_fnd_dn: basic facts about second-derived neighbourhoods (Moise     *)
(* GTM 47, p.155 and p.223), subcomplexes under barycentric subdivision,     *)
(* and smallness of derived neighbourhoods under iterated subdivision, for   *)
(* the foundations of the Moise PL core.  Main theorems:                     *)
(* BARYCENTRIC_SUBDIVISION_SUBCOMPLEX, DERIVED_NBHD_BASIC,                   *)
(* DERIVED_NBHD_SMALL (the terms MOI_FND_BARYCENTRIC_SUBCOMPLEX,             *)
(* MOI_FND_DERIVED_NBHD_BASIC, MOI_FND_DERIVED_NBHD_SMALL of                 *)
(* pc_moi_fnd_stmt.ml).                                                      *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_star.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Simplices of locally finite complexes; subcomplexes.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_FDN_LF_SIMPLEX = prove
 (`!(c:(real^N->bool)->bool) s.
     lf_simplicial_complex c /\ s IN c
     ==> (?n. n simplex s) /\ compact s /\ convex s /\ bounded s /\ closed s`,
  REWRITE_TAC[lf_simplicial_complex] THEN
  MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX; COMPACT_IMP_BOUNDED;
            COMPACT_IMP_CLOSED]);;

(* A face-closed subset of a complex satisfies the three complex axioms.     *)

let MOI_FDN_SUBCOMPLEX_BAR_COMPLEX = prove
 (`!(k:(real^N->bool)->bool) c.
     moi_bar_complex c /\ simplicial_subcomplex k c ==> moi_bar_complex k`,
  REWRITE_TAC[moi_bar_complex; simplicial_subcomplex; SUBSET] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* A subcomplex of a locally finite complex is locally finite.               *)

let MOI_FDN_LF_SUBCOMPLEX = prove
 (`!(k:(real^N->bool)->bool) c.
     lf_simplicial_complex c /\ simplicial_subcomplex k c
     ==> lf_simplicial_complex k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_SUBCOMPLEX_BAR_COMPLEX]; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN UNIONS k` THEN
    UNDISCH_TAC `simplicial_subcomplex (k:(real^N->bool)->bool) c` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
  UNDISCH_TAC `simplicial_subcomplex (k:(real^N->bool)->bool) c` THEN
  REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. Barycentric subdivision of a subcomplex                                *)
(* (BARYCENTRIC_SUBDIVISION_SUBCOMPLEX).                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_FDN_BAR_SUBDIVISION_MONO = prove
 (`!(k:(real^N->bool)->bool) c.
     k SUBSET c
     ==> barycentric_subdivision k SUBSET barycentric_subdivision c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; MOI_BAR_IN_SUBDIVISION] THEN
  X_GEN_TAC `s:real^N->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_bar_chain (k:(real^N->bool)->bool) f` THEN
  REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let BARYCENTRIC_SUBDIVISION_SUBCOMPLEX = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> simplicial_subcomplex (barycentric_subdivision l)
                               (barycentric_subdivision t) /\
         UNIONS (barycentric_subdivision l) = UNIONS l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FDN_SUBCOMPLEX_BAR_COMPLEX THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_BAR_UNIONS_SUBDIVISION] THEN
  REWRITE_TAC[simplicial_subcomplex] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FDN_BAR_SUBDIVISION_MONO THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_BAR_SUBDIVISION_COMPLEX) THEN
    REWRITE_TAC[moi_bar_complex] THEN MESON_TAC[]]);;

(* Iterated subdivisions of a complex and of a subcomplex.                   *)

let MOI_FDN_ITER_SUBCOMPLEX = prove
 (`!(t:(real^N->bool)->bool) l n.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> lf_simplicial_complex (ITER n barycentric_subdivision t) /\
         UNIONS (ITER n barycentric_subdivision t) = UNIONS t /\
         simplicial_subcomplex (ITER n barycentric_subdivision l)
                               (ITER n barycentric_subdivision t) /\
         UNIONS (ITER n barycentric_subdivision l) = UNIONS l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ITER n barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `ITER n barycentric_subdivision (l:(real^N->bool)->bool)`]
    BARYCENTRIC_SUBDIVISION_SUBCOMPLEX) THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF; UNIONS_BARYCENTRIC_SUBDIVISION]);;

(* ------------------------------------------------------------------------- *)
(* 3. Locally finite families of simplices: closed unions, finitely many    *)
(* simplices meeting a compact set, open stars.                              *)
(* ------------------------------------------------------------------------- *)

let MOI_FDN_LF_LOCALLY_FINITE_IN = prove
 (`!c:(real^N->bool)->bool.
     lf_simplicial_complex c
     ==> locally_finite_in (subtopology euclidean (UNIONS c)) c`,
  GEN_TAC THEN REWRITE_TAC[lf_simplicial_complex] THEN STRIP_TAC THEN
  REWRITE_TAC[locally_finite_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `UNIONS c INTER (u:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
  SET_TAC[]);;

(* Adapted from MOI_FN1_LF_CLOSED_IN_UNIONS (pc_moi_fnd1.ml, which this     *)
(* file does not load).                                                     *)

let MOI_FDN_LF_CLOSED_IN_UNIONS = prove
 (`!c d:(real^N->bool)->bool.
     lf_simplicial_complex c /\ d SUBSET c
     ==> closed_in (subtopology euclidean (UNIONS c)) (UNIONS d)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CLOSED_IN_LOCALLY_FINITE_UNIONS THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX; SUBSET];
    MATCH_MP_TAC LOCALLY_FINITE_IN_SUBSET THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_FDN_LF_LOCALLY_FINITE_IN]]);;

let MOI_FDN_LF_COMPACT_MEETS_FINITE = prove
 (`!(c:(real^N->bool)->bool) k.
     lf_simplicial_complex c /\ compact k /\ k SUBSET UNIONS c
     ==> FINITE {s | s IN c /\ ~(s INTER k = {})}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS c):(real^N)topology`;
                 `k:real^N->bool`; `c:(real^N->bool)->bool`]
    COMPACT_LF_OPEN_NEIGHBORHOOD) THEN
  ASM_SIMP_TAC[MOI_FDN_LF_LOCALLY_FINITE_IN; COMPACT_IN_SUBTOPOLOGY;
               COMPACT_IN_EUCLIDEAN] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
  ASM SET_TAC[]);;

(* The simplices of a complex meeting a set a, with their faces: a          *)
(* subcomplex, with the same polyhedron as the meeting simplices, open in   *)
(* the polyhedron around a, finite when a is compact.                        *)

let MOI_FDN_MEETS_FACES_SUBCOMPLEX = prove
 (`!(b:(real^N->bool)->bool) a.
     lf_simplicial_complex b
     ==> simplicial_subcomplex
           {s | ?r. r IN b /\ ~(r INTER a = {}) /\ s face_of r} b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lf_simplicial_complex] THEN STRIP_TAC THEN
  REWRITE_TAC[simplicial_subcomplex; SUBSET; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[FACE_OF_TRANS]]);;

let MOI_FDN_MEETS_FACES_UNIONS = prove
 (`!(b:(real^N->bool)->bool) a.
     lf_simplicial_complex b
     ==> UNIONS {s | ?r. r IN b /\ ~(r INTER a = {}) /\ s face_of r} =
         UNIONS {s | s IN b /\ ~(s INTER a = {})}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THENL
   [MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
    ASM_MESON_TAC[FACE_OF_REFL; MOI_FDN_LF_SIMPLEX]]);;

let MOI_FDN_MEETS_FACES_FINITE = prove
 (`!(b:(real^N->bool)->bool) a.
     lf_simplicial_complex b /\ FINITE {s | s IN b /\ ~(s INTER a = {})}
     ==> FINITE {s | ?r. r IN b /\ ~(r INTER a = {}) /\ s face_of r}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `UNIONS (IMAGE (\r:real^N->bool. {f:real^N->bool | f face_of r})
                            {s | s IN b /\ ~(s INTER a = {})})` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
     [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]; ALL_TAC] THEN
    MATCH_MP_TAC FINITE_FACES_OF_SIMPLEX THEN
    EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[]]);;

let MOI_FDN_LF_MEETS_INTERIOR = prove
 (`!(b:(real^N->bool)->bool) a u.
     lf_simplicial_complex b /\ UNIONS b = u /\ a SUBSET u
     ==> a SUBSET (subtopology euclidean u) interior_of
                  UNIONS {s | s IN b /\ ~(s INTER a = {})}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[SUBSET; interior_of; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  EXISTS_TAC `moi_sta_open_star (b:(real^N->bool)->bool) x` THEN
  ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN] THEN
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN UNIONS b` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `x:real^N` THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 4. The second-derived neighbourhood: complex, polyhedron, closedness,     *)
(* neighbourhood of UNIONS l, finiteness (DERIVED_NBHD_BASIC, Moise p.155).  *)
(* ------------------------------------------------------------------------- *)

let MOI_FDN_BAR2_LF = prove
 (`!t:(real^N->bool)->bool.
     lf_simplicial_complex t
     ==> lf_simplicial_complex
           (barycentric_subdivision (barycentric_subdivision t)) /\
         UNIONS (barycentric_subdivision (barycentric_subdivision t)) =
         UNIONS t`,
  SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF; UNIONS_BARYCENTRIC_SUBDIVISION]);;

let MOI_FDN_DERIVED_NBHD_COMPLEX_SUBCOMPLEX = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t
     ==> simplicial_subcomplex (derived_nbhd_complex t l)
           (barycentric_subdivision (barycentric_subdivision t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[derived_nbhd_complex] THEN
  MATCH_MP_TAC MOI_FDN_MEETS_FACES_SUBCOMPLEX THEN
  ASM_SIMP_TAC[MOI_FDN_BAR2_LF]);;

let MOI_FDN_DERIVED_NBHD_COMPLEX_LF = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t
     ==> lf_simplicial_complex (derived_nbhd_complex t l)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
  EXISTS_TAC
   `barycentric_subdivision
      (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
  ASM_SIMP_TAC[MOI_FDN_BAR2_LF; MOI_FDN_DERIVED_NBHD_COMPLEX_SUBCOMPLEX]);;

let MOI_FDN_UNIONS_DERIVED_NBHD_COMPLEX = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t
     ==> UNIONS (derived_nbhd_complex t l) = derived_nbhd t l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[derived_nbhd_complex; derived_nbhd] THEN
  MATCH_MP_TAC MOI_FDN_MEETS_FACES_UNIONS THEN
  ASM_SIMP_TAC[MOI_FDN_BAR2_LF]);;

let MOI_FDN_DERIVED_NBHD_SUBSET = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t ==> derived_nbhd t l SUBSET UNIONS t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
    [SYM(CONJUNCT2(MATCH_MP MOI_FDN_BAR2_LF th))]) THEN
  REWRITE_TAC[derived_nbhd] THEN SET_TAC[]);;

let MOI_FDN_DERIVED_NBHD_CLOSED_IN = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t
     ==> closed_in (subtopology euclidean (UNIONS t)) (derived_nbhd t l)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o RAND_CONV)
    [SYM(CONJUNCT2(MATCH_MP MOI_FDN_BAR2_LF th))]) THEN
  REWRITE_TAC[derived_nbhd] THEN
  MATCH_MP_TAC MOI_FDN_LF_CLOSED_IN_UNIONS THEN
  ASM_SIMP_TAC[MOI_FDN_BAR2_LF] THEN SET_TAC[]);;

let MOI_FDN_DERIVED_NBHD_INTERIOR = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ UNIONS l SUBSET UNIONS t
     ==> UNIONS l SUBSET
           (subtopology euclidean (UNIONS t)) interior_of (derived_nbhd t l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[derived_nbhd] THEN
  MATCH_MP_TAC MOI_FDN_LF_MEETS_INTERIOR THEN
  ASM_SIMP_TAC[MOI_FDN_BAR2_LF]);;

let MOI_FDN_DERIVED_NBHD_FINITE = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ FINITE l
     ==> FINITE (derived_nbhd_complex t l) /\ compact (derived_nbhd t l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `compact (UNIONS (l:(real^N->bool)->bool)) /\ UNIONS l SUBSET UNIONS t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[simplicial_subcomplex; SUBSET; MOI_FDN_LF_SIMPLEX];
      ASM_MESON_TAC[simplicial_subcomplex; SUBSET_UNIONS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (derived_nbhd_complex (t:(real^N->bool)->bool) l)`
  ASSUME_TAC THENL
   [REWRITE_TAC[derived_nbhd_complex] THEN
    MATCH_MP_TAC MOI_FDN_MEETS_FACES_FINITE THEN
    ASM_SIMP_TAC[MOI_FDN_BAR2_LF] THEN
    MATCH_MP_TAC MOI_FDN_LF_COMPACT_MEETS_FINITE THEN
    ASM_SIMP_TAC[MOI_FDN_BAR2_LF];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC
    [GSYM(MATCH_MP MOI_FDN_UNIONS_DERIVED_NBHD_COMPLEX th)]) THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `l:(real^N->bool)->bool` o
    MATCH_MP MOI_FDN_DERIVED_NBHD_COMPLEX_SUBCOMPLEX) THEN
  REWRITE_TAC[simplicial_subcomplex] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o REWRITE_RULE[SUBSET] o
    CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`barycentric_subdivision
       (barycentric_subdivision (t:(real^N->bool)->bool))`;
    `s:real^N->bool`] MOI_FDN_LF_SIMPLEX) THEN
  ASM_SIMP_TAC[MOI_FDN_BAR2_LF]);;

let DERIVED_NBHD_BASIC = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> lf_simplicial_complex (derived_nbhd_complex t l) /\
         simplicial_subcomplex (derived_nbhd_complex t l)
           (barycentric_subdivision (barycentric_subdivision t)) /\
         UNIONS (derived_nbhd_complex t l) = derived_nbhd t l /\
         derived_nbhd t l SUBSET UNIONS t /\
         closed_in (subtopology euclidean (UNIONS t)) (derived_nbhd t l) /\
         UNIONS l SUBSET
           (subtopology euclidean (UNIONS t)) interior_of (derived_nbhd t l) /\
         (FINITE l ==> FINITE (derived_nbhd_complex t l) /\
                       compact (derived_nbhd t l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FDN_DERIVED_NBHD_COMPLEX_LF;
               MOI_FDN_DERIVED_NBHD_COMPLEX_SUBCOMPLEX;
               MOI_FDN_UNIONS_DERIVED_NBHD_COMPLEX;
               MOI_FDN_DERIVED_NBHD_SUBSET; MOI_FDN_DERIVED_NBHD_CLOSED_IN;
               MOI_FDN_DERIVED_NBHD_FINITE] THEN
  MATCH_MP_TAC MOI_FDN_DERIVED_NBHD_INTERIOR THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[simplicial_subcomplex; SUBSET_UNIONS]);;

(* ------------------------------------------------------------------------- *)
(* 5. Small derived neighbourhoods (DERIVED_NBHD_SMALL, Moise p.223, p.230,  *)
(* p.239).  Every simplex of the second subdivision meeting UNIONS l lies in *)
(* a simplex of t, so the derived neighbourhood stays within the mesh of t   *)
(* of UNIONS l.                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_FDN_DERIVED_NBHD_FINE = prove
 (`!(t:(real^N->bool)->bool) l e.
     lf_simplicial_complex t /\ (!s. s IN t ==> diameter s < e)
     ==> !x. x IN derived_nbhd t l
             ==> x IN UNIONS t /\ ?y. y IN UNIONS l /\ dist(y,x) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?s:real^N->bool.
      s IN barycentric_subdivision (barycentric_subdivision t) /\
      ~(s INTER UNIONS l = {}) /\ x IN s`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN derived_nbhd t l` THEN
    REWRITE_TAC[derived_nbhd; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?s1:real^N->bool. s1 IN barycentric_subdivision t /\ s SUBSET s1`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o
      MATCH_MP BARYCENTRIC_SUBDIVISION_REFINES o
      MATCH_MP BARYCENTRIC_SUBDIVISION_LF) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?s0:real^N->bool. s0 IN t /\ s1 SUBSET s0`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o
      MATCH_MP BARYCENTRIC_SUBDIVISION_REFINES) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(s INTER UNIONS l:real^N->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `bounded(s0:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s0:real^N->bool` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[dist] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `diameter(s0:real^N->bool)` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let DERIVED_NBHD_SMALL = prove
 (`!(t:(real^N->bool)->bool) l v.
     simplicial_complex t /\ simplicial_subcomplex l t /\
     open_in (subtopology euclidean (UNIONS t)) v /\ UNIONS l SUBSET v
     ==> ?n. derived_nbhd (ITER n barycentric_subdivision t)
                          (ITER n barycentric_subdivision l) SUBSET v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool) /\ FINITE t`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(UNIONS (l:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; FINITE_SUBSET];
      ASM_MESON_TAC[simplicial_subcomplex; SUBSET; MOI_FDN_LF_SIMPLEX]];
    ALL_TAC] THEN
  UNDISCH_TAC
   `open_in (subtopology euclidean (UNIONS t)) (v:real^N->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`UNIONS (l:(real^N->bool)->bool)`; `(:real^N) DIFF w`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `d:real`]
    ITERATED_BARYCENTRIC_SUBDIVISION_FINE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `n:num`]
    MOI_FDN_ITER_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ITER n barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `ITER n barycentric_subdivision (l:(real^N->bool)->bool)`;
                 `d:real`] MOI_FDN_DERIVED_NBHD_FINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `x:real^N`]) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  ASM_CASES_TAC `(x:real^N) IN w` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `dist(y:real^N,x) < d` THEN REAL_ARITH_TAC);;

