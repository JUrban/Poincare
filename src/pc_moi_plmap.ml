(* ========================================================================= *)
(* pc_moi_plmap: the calculus of PL maps in real^N.                         *)
(* Locally polyhedral sets, PL maps on them: identity, affine maps,        *)
(* restriction, locality, gluing along closed pieces, composition,         *)
(* pairing, sums, scalar multiples, inverses of PL homeomorphisms, PL       *)
(* images of compact polyhedra, PL balls and spheres.                       *)
(* Moise, Geometric Topology in Dimensions 2 and 3, Sec 5; Rourke and       *)
(* Sanderson, Introduction to PL topology, Ch 1-2.                          *)
(* ========================================================================= *)

needs "src/pc_moi_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* The sets on which the identity map is PL: near each point, finitely many *)
(* polytopes inside the set cover a neighbourhood of the point in the set.  *)

let locally_polyhedral = new_definition
 `locally_polyhedral (s:real^N->bool) <=>
    !x. x IN s
        ==> ?c u. FINITE c /\ open u /\ x IN u /\ s INTER u SUBSET UNIONS c /\
                  !k. k IN c ==> polytope k /\ k SUBSET s`;;

(* ------------------------------------------------------------------------- *)
(* Elementary facts.                                                         *)
(* ------------------------------------------------------------------------- *)

let LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID = prove
 (`!s:real^N->bool. locally_polyhedral s <=> pl_map_on s (\x. x)`,
  GEN_TAC THEN REWRITE_TAC[locally_polyhedral; pl_map_on] THEN
  SUBGOAL_THEN
   `!k:real^N->bool. ?l:real^N->real^N y. linear l /\ !z. z IN k ==> z = l z + y`
   (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN MAP_EVERY EXISTS_TAC [`\x:real^N. x`; `vec 0:real^N`] THEN
  REWRITE_TAC[LINEAR_ID; VECTOR_ADD_RID]);;

let PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL = prove
 (`!(s:real^M->bool) (f:real^M->real^N). pl_map_on s f ==> locally_polyhedral s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_map_on; locally_polyhedral] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:(real^M->bool)->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^M->bool` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let PL_MAP_ON_EQ = prove
 (`!(s:real^M->bool) (f:real^M->real^N) g.
     (!x. x IN s ==> f x = g x) /\ pl_map_on s f ==> pl_map_on s g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_map_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pl")) THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  REMOVE_THEN "pl" (MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:(real^M->bool)->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
     STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
  ASM_MESON_TAC[SUBSET]);;

let PL_MAP_ON_AFFINE = prove
 (`!(s:real^M->bool) (l:real^M->real^N) y.
     locally_polyhedral s /\ linear l ==> pl_map_on s (\x. l x + y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_polyhedral; pl_map_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lp") ASSUME_TAC) THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  REMOVE_THEN "lp" (MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:(real^M->bool)->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
  ASM_REWRITE_TAC[]);;

let PL_MAP_ON_CONST = prove
 (`!(s:real^M->bool) (y:real^N). locally_polyhedral s ==> pl_map_on s (\x. y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `(\x. vec 0):real^M->real^N`; `y:real^N`]
    PL_MAP_ON_AFFINE) THEN
  ASM_REWRITE_TAC[LINEAR_ZERO; VECTOR_ADD_LID]);;

let LOCALLY_POLYHEDRAL_POLYTOPE = prove
 (`!s:real^N->bool. polytope s ==> locally_polyhedral s`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[locally_polyhedral] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`{s:real^N->bool}`; `(:real^N)`] THEN
  ASM_REWRITE_TAC[FINITE_SING; OPEN_UNIV; IN_UNIV; INTER_UNIV; UNIONS_1;
                  SUBSET_REFL; FORALL_IN_INSERT; NOT_IN_EMPTY]);;

let LOCALLY_POLYHEDRAL_PL_POLYHEDRON = prove
 (`!s:real^N->bool. pl_polyhedron s ==> locally_polyhedral s`,
  GEN_TAC THEN REWRITE_TAC[pl_polyhedron; locally_polyhedral] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `(:real^N)`] THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; INTER_UNIV; SUBSET_REFL] THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]);;

let LOCALLY_POLYHEDRAL_LF_COMPLEX = prove
 (`!c:(real^N->bool)->bool.
        lf_simplicial_complex c ==> locally_polyhedral (UNIONS c)`,
  GEN_TAC THEN REWRITE_TAC[lf_simplicial_complex; locally_polyhedral] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sx") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lf")))) THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REMOVE_THEN "lf" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`{s:real^N->bool | s IN c /\ ~(s INTER u = {})}`; `u:real^N->bool`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN SET_TAC[];
    X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]]]);;

let LOCALLY_POLYHEDRAL_OPEN = prove
 (`!s:real^N->bool. open s ==> locally_polyhedral s`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[locally_polyhedral] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real^N` (GEN_REWRITE_RULE I [OPEN_CONTAINS_INTERVAL]
    (ASSUME `open(s:real^N->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`{interval[a:real^N,b]}`; `interval(a:real^N,b)`] THEN
  ASM_REWRITE_TAC[FINITE_SING; OPEN_INTERVAL; FORALL_IN_INSERT; NOT_IN_EMPTY;
                  POLYTOPE_INTERVAL; UNIONS_1] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
  SET_TAC[]);;

let LOCALLY_POLYHEDRAL_INTER_OPEN = prove
 (`!(s:real^N->bool) u.
        locally_polyhedral s /\ open u ==> locally_polyhedral (s INTER u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_polyhedral] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lp") ASSUME_TAC) THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  REMOVE_THEN "lp" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool`
    (X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC `x:real^N` (GEN_REWRITE_RULE I [OPEN_CONTAINS_INTERVAL]
    (ASSUME `open(u:real^N->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `IMAGE (\k:real^N->bool. k INTER interval[a,b]) c` THEN
  EXISTS_TAC `v INTER interval(a:real^N,b)` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; OPEN_INTER; OPEN_INTERVAL; IN_INTER;
               FORALL_IN_IMAGE] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; UNIONS_IMAGE; IN_ELIM_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_INTER; IN_UNIONS]) THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[POLYTOPE_INTER; POLYTOPE_INTERVAL] THEN ASM SET_TAC[]]);;

let PL_MAP_ON_LOCAL = prove
 (`!(s:real^M->bool) (f:real^M->real^N).
     pl_map_on s f <=>
     !x. x IN s ==> ?u. open u /\ x IN u /\ pl_map_on (s INTER u) f`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; INTER_UNIV];
    DISCH_TAC THEN REWRITE_TAC[pl_map_on] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o GEN_REWRITE_RULE I [pl_map_on]) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool`
      (X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`c:(real^M->bool)->bool`; `u INTER v:real^M->bool`] THEN
    ASM_SIMP_TAC[OPEN_INTER; IN_INTER; INTER_ASSOC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET_INTER]) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM INTER_ASSOC]; ASM_MESON_TAC[]]]);;

let PL_MAP_ON_SUBSET = prove
 (`!(s:real^M->bool) t (f:real^M->real^N).
     pl_map_on s f /\ t SUBSET s /\ locally_polyhedral t ==> pl_map_on t f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_map_on; locally_polyhedral] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "t"))) THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  REMOVE_THEN "t" (MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^M->bool)->bool`
    (X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "f" (MP_TAC o SPEC `x:real^M`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool`
    (X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `{k INTER k' | (k:real^M->bool) IN c /\ (k':real^M->bool) IN d}` THEN
  EXISTS_TAC `u INTER v:real^M->bool` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^M` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?k:real^M->bool. k IN c /\ z IN k` STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `s INTER u SUBSET UNIONS (c:(real^M->bool)->bool)`) THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `?k':real^M->bool. k' IN d /\ z IN k'` STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `t INTER v SUBSET UNIONS (d:(real^M->bool)->bool)`) THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `k INTER k':real^M->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `k':real^M->bool`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `m:real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `k':real^M->bool`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k':real^M->bool`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[POLYTOPE_INTER] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
      ASM_SIMP_TAC[IN_INTER]]]);;

(* ------------------------------------------------------------------------- *)
(* Skolemized form, continuity, affine (pre)images, composition.            *)
(* ------------------------------------------------------------------------- *)

let MOI_PLM_PL_MAP_ON_ALT = prove
 (`!(s:real^M->bool) (f:real^M->real^N).
        pl_map_on s f <=>
        !x. x IN s
            ==> ?c u (L:(real^M->bool)->real^M->real^N) Y.
                  FINITE c /\ open u /\ x IN u /\ s INTER u SUBSET UNIONS c /\
                  !k. k IN c
                      ==> polytope k /\ k SUBSET s /\ linear (L k) /\
                          !z. z IN k ==> f z = L k z + Y k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_map_on] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; RIGHT_IMP_EXISTS_THM; SKOLEM_THM]);;

let MOI_PLM_CONTINUOUS_ON_UNIONS_CLOSED = prove
 (`!(f:real^M->real^N) c.
        FINITE c /\ (!k. k IN c ==> closed k /\ f continuous_on k)
        ==> f continuous_on (UNIONS c)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; CONTINUOUS_ON_EMPTY; UNIONS_INSERT; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `c:(real^M->bool)->bool`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_UNION THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[]);;

let MOI_PLM_AFFINE_CONTINUOUS_ON = prove
 (`!(f:real^M->real^N) l y k.
        linear l /\ (!z. z IN k ==> f z = l z + y) ==> f continuous_on k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\z:real^M. (l:real^M->real^N) z + y` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON;
               ETA_AX]);;

let PL_MAP_ON_IMP_CONTINUOUS_ON = prove
 (`!(s:real^M->bool) (f:real^M->real^N). pl_map_on s f ==> f continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_PLM_PL_MAP_ON_ALT] THEN DISCH_TAC THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:(real^M->bool)->bool`; `u:real^M->bool`;
    `L:(real^M->bool)->real^M->real^N`; `Y:(real^M->bool)->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) continuous_on (s INTER u)` MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `UNIONS c:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_PLM_CONTINUOUS_ON_UNIONS_CLOSED THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED] THEN
    MATCH_MP_TAC MOI_PLM_AFFINE_CONTINUOUS_ON THEN
    MAP_EVERY EXISTS_TAC [`(L:(real^M->bool)->real^M->real^N) k`;
                          `(Y:(real^M->bool)->real^N) k`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[IN_INTER] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CONTINUOUS_WITHIN_OPEN_IN THEN
  ASM_SIMP_TAC[IN_INTER; OPEN_IN_OPEN_INTER]);;

let MOI_PLM_POLYHEDRON_AFFINE_PREIMAGE = prove
 (`!(l:real^M->real^N) y m.
        linear l /\ polyhedron m ==> polyhedron {z | l z + y IN m}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{z:real^M | (l:real^M->real^N) z + y IN m} =
                {z | l z IN IMAGE (\w. --y + w) m}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `z:real^M` THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `(l:real^M->real^N) z + y` THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(--y + w) + y:real^N = w`]];
    MATCH_MP_TAC POLYHEDRON_LINEAR_PREIMAGE THEN
    ASM_REWRITE_TAC[POLYHEDRON_TRANSLATION_EQ]]);;

let MOI_PLM_POLYTOPE_AFFINE_IMAGE = prove
 (`!(l:real^M->real^N) y k.
        linear l /\ polytope k ==> polytope (IMAGE (\z. l z + y) k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\z. (l:real^M->real^N) z + y) k =
                IMAGE (\x. y + x) (IMAGE l k)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC;
    ASM_SIMP_TAC[POLYTOPE_TRANSLATION_EQ; POLYTOPE_LINEAR_IMAGE]]);;

let PL_MAP_ON_COMPOSE = prove
 (`!(s:real^M->bool) (t:real^N->bool) (f:real^M->real^N) (g:real^N->real^P).
     pl_map_on s f /\ pl_map_on t g /\ IMAGE f s SUBSET t
     ==> pl_map_on s (g o f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) continuous_on s` ASSUME_TAC THENL
   [ASM_MESON_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON]; ALL_TAC] THEN
  REWRITE_TAC[pl_map_on] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real^M` (GEN_REWRITE_RULE I [MOI_PLM_PL_MAP_ON_ALT]
    (ASSUME `pl_map_on (s:real^M->bool) (f:real^M->real^N)`))) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:(real^M->bool)->bool`; `u:real^M->bool`;
    `L:(real^M->bool)->real^M->real^N`; `Y:(real^M->bool)->real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `(f:real^M->real^N) x` (GEN_REWRITE_RULE I [MOI_PLM_PL_MAP_ON_ALT]
    (ASSUME `pl_map_on (t:real^N->bool) (g:real^N->real^P)`))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`d:(real^N->bool)->bool`; `v:real^N->bool`;
    `L':(real^N->bool)->real^N->real^P`; `Y':(real^N->bool)->real^P`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?w:real^M->bool. open w /\ x IN w /\
                  !z. z IN w /\ z IN s ==> (f:real^M->real^N) z IN v`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real^N`; `x:real^M`; `s:real^M->bool`]
      CONTINUOUS_WITHIN_OPEN) THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN];
      DISCH_THEN(MP_TAC o SPEC `v:real^N->bool`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `{k INTER {z | (L:(real^M->bool)->real^M->real^N) k z + Y k IN m} |
               k IN c /\ (m:real^N->bool) IN d}` THEN
  EXISTS_TAC `u INTER w:real^M->bool` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^M` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?k:real^M->bool. k IN c /\ z IN k` STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `s INTER u SUBSET UNIONS (c:(real^M->bool)->bool)`) THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?m:real^N->bool. m IN d /\ (f:real^M->real^N) z IN m`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `t INTER v SUBSET UNIONS (d:(real^N->bool)->bool)`) THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC
     `k INTER {z | (L:(real^M->bool)->real^M->real^N) k z + Y k IN m}` THEN
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `m:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `q:real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `m:real^N->bool`
      (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC))) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC MOI_PLM_POLYHEDRON_AFFINE_PREIMAGE THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON; ETA_AX];
      ASM SET_TAC[];
      EXISTS_TAC `(L':(real^N->bool)->real^N->real^P) m o
                  (L:(real^M->bool)->real^M->real^N) k` THEN
      EXISTS_TAC `(L':(real^N->bool)->real^N->real^P) m
                  ((Y:(real^M->bool)->real^N) k) +
                  (Y':(real^N->bool)->real^P) m` THEN
      ASM_SIMP_TAC[LINEAR_COMPOSE; IN_INTER; IN_ELIM_THM; o_THM] THEN
      X_GEN_TAC `z:real^M` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `(g:real^N->real^P) ((L:(real^M->bool)->real^M->real^N) k z + Y k) =
        (L':(real^N->bool)->real^N->real^P) m (L k z + Y k) + Y' m`
      SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[LINEAR_ADD] THEN REWRITE_TAC[VECTOR_ADD_ASSOC]]]);;

(* ------------------------------------------------------------------------- *)
(* Gluing along relatively closed pieces.                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_PLM_PIECE_MONO = prove
 (`!(k:real^M->bool) s s' (f:real^M->real^N).
        s SUBSET s' /\ polytope k /\ k SUBSET s /\
        (?l y. linear l /\ !z. z IN k ==> f z = l z + y)
        ==> polytope k /\ k SUBSET s' /\
            (?l y. linear l /\ !z. z IN k ==> f z = l z + y)`,
  MESON_TAC[SUBSET_TRANS]);;

let MOI_PLM_PL_MAP_ON_UNION_LEMMA = prove
 (`!(s:real^M->bool) t (f:real^M->real^N) x.
     pl_map_on s f /\ pl_map_on t f /\
     closed_in (subtopology euclidean (s UNION t)) t /\ x IN s
     ==> ?c u. FINITE c /\ open u /\ x IN u /\
               (s UNION t) INTER u SUBSET UNIONS c /\
               !k. k IN c
                   ==> polytope k /\ k SUBSET s UNION t /\
                       ?l y. linear l /\ !z. z IN k ==> f z = l z + y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real^M` (GEN_REWRITE_RULE I [pl_map_on]
    (ASSUME `pl_map_on (s:real^M->bool) (f:real^M->real^N)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool`
    (X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `(x:real^M) IN t` THENL
   [MP_TAC(SPEC `x:real^M` (GEN_REWRITE_RULE I [pl_map_on]
      (ASSUME `pl_map_on (t:real^M->bool) (f:real^M->real^N)`))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:(real^M->bool)->bool`
      (X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC
     [`c UNION d:(real^M->bool)->bool`; `u INTER v:real^M->bool`] THEN
    ASM_SIMP_TAC[FINITE_UNION; OPEN_INTER; IN_INTER] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      X_GEN_TAC `k:real^M->bool` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_PLM_PIECE_MONO THENL
       [EXISTS_TAC `s:real^M->bool`; EXISTS_TAC `t:real^M->bool`] THEN
      ASM_SIMP_TAC[SUBSET_UNION]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CLOSED_IN_CLOSED]) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^M->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`c:(real^M->bool)->bool`; `u DIFF e:real^M->bool`] THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[OPEN_DIFF];
      ASM SET_TAC[];
      ASM SET_TAC[];
      X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_PLM_PIECE_MONO THEN EXISTS_TAC `s:real^M->bool` THEN
      ASM_SIMP_TAC[SUBSET_UNION]]]);;

let PL_MAP_ON_UNION = prove
 (`!(s:real^M->bool) t (f:real^M->real^N).
     pl_map_on s f /\ pl_map_on t f /\
     closed_in (subtopology euclidean (s UNION t)) s /\
     closed_in (subtopology euclidean (s UNION t)) t
     ==> pl_map_on (s UNION t) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [pl_map_on] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [MATCH_MP_TAC MOI_PLM_PL_MAP_ON_UNION_LEMMA THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`t:real^M->bool`; `s:real^M->bool`; `f:real^M->real^N`;
                   `x:real^M`] MOI_PLM_PL_MAP_ON_UNION_LEMMA) THEN
    SUBST1_TAC(ISPECL [`t:real^M->bool`; `s:real^M->bool`] UNION_COMM) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Common refinement of two PL maps; pairing, sums and scalar multiples.     *)
(* ------------------------------------------------------------------------- *)

let MOI_PLM_PL_MAP_ON_PAIR = prove
 (`!(s:real^M->bool) (f:real^M->real^N) (g:real^M->real^P).
     pl_map_on s f /\ pl_map_on s g
     ==> !x. x IN s
             ==> ?c u. FINITE c /\ open u /\ x IN u /\
                       s INTER u SUBSET UNIONS c /\
                       !k. k IN c
                           ==> polytope k /\ k SUBSET s /\
                               (?l y. linear l /\
                                      !z. z IN k ==> f z = l z + y) /\
                               (?l y. linear l /\
                                      !z. z IN k ==> g z = l z + y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_map_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f") (LABEL_TAC "g")) THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  REMOVE_THEN "g" (MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^M->bool)->bool`
    (X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "f" (MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool`
    (X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `{k INTER k' | (k:real^M->bool) IN c /\ (k':real^M->bool) IN d}` THEN
  EXISTS_TAC `u INTER v:real^M->bool` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^M` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?k:real^M->bool. k IN c /\ z IN k` STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `s INTER u SUBSET UNIONS (c:(real^M->bool)->bool)`) THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?k':real^M->bool. k' IN d /\ z IN k'` STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `s INTER v SUBSET UNIONS (d:(real^M->bool)->bool)`) THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `k INTER k':real^M->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `k':real^M->bool`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `m:real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `k':real^M->bool`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k':real^M->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `l2:real^M->real^P` (X_CHOOSE_THEN `y2:real^P`
       STRIP_ASSUME_TAC)))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `l1:real^M->real^N` (X_CHOOSE_THEN `y1:real^N`
       STRIP_ASSUME_TAC)))) THEN
    ASM_SIMP_TAC[POLYTOPE_INTER] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`l1:real^M->real^N`; `y1:real^N`] THEN
      ASM_SIMP_TAC[IN_INTER];
      MAP_EVERY EXISTS_TAC [`l2:real^M->real^P`; `y2:real^P`] THEN
      ASM_SIMP_TAC[IN_INTER]]]);;

let PL_MAP_ON_PASTECART = prove
 (`!(s:real^M->bool) (f:real^M->real^N) (g:real^M->real^P).
     pl_map_on s f /\ pl_map_on s g
     ==> pl_map_on s (\x. pastecart (f x) (g x))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_PLM_PL_MAP_ON_PAIR) THEN
  DISCH_TAC THEN REWRITE_TAC[pl_map_on] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:(real^M->bool)->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `l1:real^M->real^N` (X_CHOOSE_THEN `y1:real^N`
        STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `l2:real^M->real^P` (X_CHOOSE_THEN `y2:real^P`
        STRIP_ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `\z:real^M. pastecart ((l1:real^M->real^N) z)
                                   ((l2:real^M->real^P) z)` THEN
  EXISTS_TAC `pastecart (y1:real^N) (y2:real^P)` THEN
  ASM_SIMP_TAC[LINEAR_PASTECART; PASTECART_ADD]);;

let PL_MAP_ON_ADD = prove
 (`!(s:real^M->bool) (f:real^M->real^N) g.
     pl_map_on s f /\ pl_map_on s g ==> pl_map_on s (\x. f x + g x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_PLM_PL_MAP_ON_PAIR) THEN
  DISCH_TAC THEN REWRITE_TAC[pl_map_on] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:(real^M->bool)->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `l1:real^M->real^N` (X_CHOOSE_THEN `y1:real^N`
        STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `l2:real^M->real^N` (X_CHOOSE_THEN `y2:real^N`
        STRIP_ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `\z:real^M. (l1:real^M->real^N) z + (l2:real^M->real^N) z` THEN
  EXISTS_TAC `y1 + y2:real^N` THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE_ADD] THEN REPEAT STRIP_TAC THEN
  VECTOR_ARITH_TAC);;

let PL_MAP_ON_CMUL = prove
 (`!(s:real^M->bool) (f:real^M->real^N) c.
     pl_map_on s f ==> pl_map_on s (\x. c % f x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_map_on] THEN DISCH_TAC THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:(real^M->bool)->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
     STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `\z:real^M. c % (l:real^M->real^N) z` THEN
  EXISTS_TAC `c % y:real^N` THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE_CMUL; VECTOR_ADD_LDISTRIB]);;

(* ------------------------------------------------------------------------- *)
(* Inverses of PL homeomorphisms: linear algebra of injective affine maps.   *)
(* ------------------------------------------------------------------------- *)

let MOI_PLM_LINEAR_LEFT_INVERSE_ON_SUBSPACE = prove
 (`!(f:real^M->real^N) s.
        linear f /\ subspace s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ?g. linear g /\ !x. x IN s ==> g (f x) = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^M->bool` BASIS_SUBSPACE_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\y:real^N. @x:real^M. x IN b /\ (f:real^M->real^N) x = y`;
                 `IMAGE (f:real^M->real^N) b`] LINEAR_INDEPENDENT_EXTEND) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE_GEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:real^N->real^M` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:real^M. x IN b ==> (g:real^N->real^M) (f x) = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^M->real^N) x`) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(g:real^N->real^M) o (f:real^M->real^N)`; `\x:real^M. x`;
                 `b:real^M->bool`; `s:real^M->bool`] LINEAR_EQ) THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE; LINEAR_ID; SUBSET_REFL; o_THM]);;

let MOI_PLM_AFFINE_INJECTIVE_KERNEL = prove
 (`!(l:real^M->real^N) y k z0 d.
        linear l /\ z0 IN relative_interior k /\
        (!x x'. x IN k /\ x' IN k /\ l x + y = l x' + y ==> x = x') /\
        d IN span {x - z0 | x IN k} /\ l d = vec 0
        ==> d = vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)))) THEN
  MP_TAC(GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR]
    (ASSUME `(z0:real^M) IN relative_interior k`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real`
    STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[GSYM DIFFS_AFFINE_HULL_SPAN; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^M` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST_ALL_TAC)) THEN
  ASM_CASES_TAC `p - z0:real^M = vec 0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?t. &0 < t /\ t * norm(p - z0:real^M) < e` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `e / (&2 * norm(p - z0:real^M))` THEN
    SUBGOAL_THEN `&0 < norm(p - z0:real^M)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> e / (&2 * n) * n = e / &2`] THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `z0 + t % (p - z0):real^M IN k` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_INTER; IN_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[NORM_ARITH `dist(a:real^M,a + b) = norm b`; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`];
      SUBGOAL_THEN `z0 + t % (p - z0):real^M = (&1 - t) % z0 + t % p`
      SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
      ASM_SIMP_TAC[HULL_INC] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `z0 + t % (p - z0):real^M = z0` MP_TAC THENL
   [USE_THEN "inj" MATCH_MP_TAC THEN ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    REWRITE_TAC[VECTOR_ARITH `(z0:real^M) + t % d = z0 <=> t % d = vec 0`;
                VECTOR_MUL_EQ_0] THEN
    ASM_MESON_TAC[REAL_LT_IMP_NZ]]);;

let MOI_PLM_AFFINE_INJECTIVE_LEFT_INVERSE = prove
 (`!(l:real^M->real^N) y k.
        linear l /\ convex k /\
        (!x x'. x IN k /\ x' IN k /\ l x + y = l x' + y ==> x = x')
        ==> ?l':real^N->real^M y'.
                linear l' /\ !x. x IN k ==> l' (l x + y) + y' = x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "inj"))) THEN
  ASM_CASES_TAC `k:real^M->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`(\x. vec 0):real^N->real^M`; `vec 0:real^M`] THEN
    ASM_REWRITE_TAC[LINEAR_ZERO; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z0:real^M. z0 IN relative_interior k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(z0:real^M) IN k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:real^M->real^N`; `span {x - z0 | x IN k}:real^M->bool`]
    MOI_PLM_LINEAR_LEFT_INVERSE_ON_SUBSPACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSPACE_SPAN] THEN
    MAP_EVERY X_GEN_TAC [`v:real^M`; `w:real^M`] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC MOI_PLM_AFFINE_INJECTIVE_KERNEL THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`; `k:real^M->bool`;
                          `z0:real^M`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SPAN_SUB THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MATCH_MP LINEAR_SUB (ASSUME `linear(l:real^M->real^N)`)] THEN
      ASM_REWRITE_TAC[VECTOR_SUB_EQ]];
    ALL_TAC] THEN
  REMOVE_THEN "inj" (K ALL_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`g:real^N->real^M`;
                        `z0 - (g:real^N->real^M) ((l:real^M->real^N) z0 + y)`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(l:real^M->real^N) x + y = l (x - z0) + (l z0 + y)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[LINEAR_SUB] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_ADD] THEN
  SUBGOAL_THEN `(g:real^N->real^M) ((l:real^M->real^N) (x - z0)) = x - z0`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC SPAN_SUPERSET THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[];
    VECTOR_ARITH_TAC]);;

let PL_MAP_ON_HOMEOMORPHISM_INVERSE = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g.
     homeomorphism (s,t) (f,g) /\ pl_map_on s f ==> pl_map_on t g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  REWRITE_TAC[pl_map_on] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(SPEC `(g:real^N->real^M) y` (GEN_REWRITE_RULE I [MOI_PLM_PL_MAP_ON_ALT]
    (ASSUME `pl_map_on (s:real^M->bool) (f:real^M->real^N)`))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c:(real^M->bool)->bool`; `u:real^M->bool`;
    `L:(real^M->bool)->real^M->real^N`; `Y:(real^M->bool)->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?v:real^N->bool. open v /\ y IN v /\
                  !w. w IN t /\ w IN v ==> (g:real^N->real^M) w IN u`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^N->real^M`; `y:real^N`; `t:real^N->bool`]
      CONTINUOUS_WITHIN_OPEN) THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN];
      DISCH_THEN(MP_TAC o SPEC `u:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (IMAGE (f:real^M->real^N)) c` THEN
  EXISTS_TAC `v:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; ASSUME `FINITE (c:(real^M->bool)->bool)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?k:real^M->bool. k IN c /\ (g:real^N->real^M) w IN k`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `s INTER u SUBSET UNIONS (c:(real^M->bool)->bool)`) THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(g:real^N->real^M) w` THEN ASM_MESON_TAC[];
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE (f:real^M->real^N) k =
                    IMAGE (\z. (L:(real^M->bool)->real^M->real^N) k z + Y k) k`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `(!x:A. x IN s ==> (f:A->B) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC MOI_PLM_POLYTOPE_AFFINE_IMAGE THEN
        ASM_REWRITE_TAC[ETA_AX]];
      EXPAND_TAC "t" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`(L:(real^M->bool)->real^M->real^N) k`;
                     `(Y:(real^M->bool)->real^N) k`; `k:real^M->bool`]
        MOI_PLM_AFFINE_INJECTIVE_LEFT_INVERSE) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN
        MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN STRIP_TAC THEN
        SUBGOAL_THEN `(f:real^M->real^N) a = f b` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o AP_TERM `g:real^N->real^M`) THEN
        ASM_MESON_TAC[SUBSET];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l':real^N->real^M` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y':real^M` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(g:real^N->real^M) (f x) = x` SUBST1_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `(f:real^M->real^N) x =
                    (L:(real^M->bool)->real^M->real^N) k x +
                    (Y:(real^M->bool)->real^N) k` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* PL homeomorphisms, PL images of compact polyhedra, PL balls and spheres.  *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g.
     homeomorphism (s,t) (f,g) /\ pl_map_on s f
     ==> pl_homeomorphism (s,t) (f,g)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[pl_homeomorphism] THEN
  MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
  MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `f:real^M->real^N`] THEN
  ASM_REWRITE_TAC[]);;

let PL_HOMEOMORPHISM_COMPOSE = prove
 (`!(s:real^M->bool) (t:real^N->bool) (u:real^P->bool) f g f' g'.
     pl_homeomorphism (s,t) (f,g) /\ pl_homeomorphism (t,u) (f',g')
     ==> pl_homeomorphism (s,u) (f' o f,g o g')`,
  REWRITE_TAC[pl_homeomorphism] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

let PL_HOMEOMORPHISM_SYM = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g.
     pl_homeomorphism (s,t) (f,g) <=> pl_homeomorphism (t,s) (g,f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN
  MESON_TAC[HOMEOMORPHISM_SYM]);;

let MOI_PLM_PL_MAP_ON_COMPACT_FINITE = prove
 (`!(s:real^M->bool) (f:real^M->real^N).
        compact s /\ pl_map_on s f
        ==> ?c. FINITE c /\ s = UNIONS c /\
                !k. k IN c
                    ==> polytope k /\ k SUBSET s /\
                        ?l y. linear l /\ !z. z IN k ==> f z = l z + y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_map_on] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`C:real^M->(real^M->bool)->bool`;
                       `U:real^M->real^M->bool`] THEN
  DISCH_THEN(LABEL_TAC "cov") THEN
  MP_TAC(ISPEC `s:real^M->bool` COMPACT_IMP_HEINE_BOREL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (U:real^M->real^M->bool) s`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[EXISTS_FINITE_SUBSET_IMAGE] o
    ONCE_REWRITE_RULE[TAUT `a /\ b /\ c <=> b /\ a /\ c`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `UNIONS (IMAGE (C:real^M->(real^M->bool)->bool) p)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN ASM_MESON_TAC[SUBSET];
    REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `z:real^M` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `?x:real^M. x IN p /\ z IN (U:real^M->real^M->bool) x`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `s SUBSET UNIONS (IMAGE (U:real^M->real^M->bool) p)` THEN
        REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^M) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "cov" (MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       `?k:real^M->bool. k IN (C:real^M->(real^M->bool)->bool) x /\ z IN k`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `s INTER (U:real^M->real^M->bool) x SUBSET
                     UNIONS ((C:real^M->(real^M->bool)->bool) x)` THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      SUBGOAL_THEN `(x:real^M) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "cov" (MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(k:real^M->bool) SUBSET s` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM SET_TAC[]]];
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `k:real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^M) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "cov" (MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let PL_POLYHEDRON_PL_IMAGE = prove
 (`!(s:real^M->bool) (f:real^M->real^N).
     pl_polyhedron s /\ pl_map_on s f ==> pl_polyhedron (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact (s:real^M->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_polyhedron]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real^N`]
    MOI_PLM_PL_MAP_ON_COMPACT_FINITE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `IMAGE (IMAGE (f:real^M->real^N)) c` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `k:real^M->bool` THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
        STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `IMAGE (f:real^M->real^N) k = IMAGE (\z. l z + y) k`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x:A. x IN s ==> (f:A->B) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC MOI_PLM_POLYTOPE_AFFINE_IMAGE THEN
      ASM_REWRITE_TAC[ETA_AX]];
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [ASSUME `s:real^M->bool = UNIONS c`] THEN
    REWRITE_TAC[IMAGE_UNIONS]]);;

let PL_BALL_PL_HOMEOMORPHIC = prove
 (`!n (s:real^N->bool) (t:real^N->bool) f g.
     pl_ball n s /\ pl_homeomorphism (s,t) (f,g) ==> pl_ball n t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool`
    (X_CHOOSE_THEN `f0:real^N->real^N` (X_CHOOSE_THEN `g0:real^N->real^N`
      STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`;
                        `(f:real^N->real^N) o (f0:real^N->real^N)`;
                        `(g0:real^N->real^N) o (g:real^N->real^N)`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let PL_SPHERE_PL_HOMEOMORPHIC = prove
 (`!n (s:real^N->bool) (t:real^N->bool) f g.
     pl_sphere n s /\ pl_homeomorphism (s,t) (f,g) ==> pl_sphere n t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool`
    (X_CHOOSE_THEN `f0:real^N->real^N` (X_CHOOSE_THEN `g0:real^N->real^N`
      STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`;
                        `(f:real^N->real^N) o (f0:real^N->real^N)`;
                        `(g0:real^N->real^N) o (g:real^N->real^N)`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let PL_BALL_SIMPLEX = prove
 (`!n k:real^N->bool. &n simplex k ==> pl_ball n k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_ball] THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `\x:real^N. x`; `\x:real^N. x`] THEN
  ASM_REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID;
                  GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN
  ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]);;

let PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX = prove
 (`!n k:real^N->bool.
        &(n + 1) simplex k ==> pl_sphere n (relative_frontier k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_sphere] THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `\x:real^N. x`; `\x:real^N. x`] THEN
  ASM_REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID;
                  GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
  SUBGOAL_THEN `polytope (k:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{f:real^N->bool | f facet_of k}` THEN
  ASM_SIMP_TAC[FINITE_POLYTOPE_FACETS; IN_ELIM_THM;
               RELATIVE_FRONTIER_OF_POLYHEDRON; POLYTOPE_IMP_POLYHEDRON] THEN
  ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; facet_of]);;

