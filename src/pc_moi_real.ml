(* ========================================================================= *)
(* pc_moi_real: abstract simplicial complexes, their rectilinear            *)
(* realizations in a fixed real^N, existence of realizations in general     *)
(* position (2d+1 <= dimindex(:N)), the simplexwise affine PL homeomorphism *)
(* between two realizations of one complex, and re-realization of          *)
(* geometric simplicial complexes in another space.                         *)
(* Rourke-Sanderson, Introduction to PL topology, Ch 2.                      *)
(* ========================================================================= *)

needs "src/pc_moi_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

let abstract_complex = new_definition
 `abstract_complex (k:(V->bool)->bool) <=>
    (!s. s IN k ==> FINITE s /\ ~(s = {})) /\
    (!s t. s IN k /\ ~(t = {}) /\ t SUBSET s ==> t IN k)`;;

let abstract_realization = new_definition
 `abstract_realization (f:V->real^N) (k:(V->bool)->bool) =
    {} INSERT {convex hull (IMAGE f s) | s IN k}`;;

let abstract_realizes = new_definition
 `abstract_realizes (f:V->real^N) (k:(V->bool)->bool) <=>
    (!s. s IN k ==> ~affine_dependent (IMAGE f s)) /\
    (!x y. x IN UNIONS k /\ y IN UNIONS k /\ f x = f y ==> x = y) /\
    (!s t. s IN k /\ t IN k
           ==> convex hull (IMAGE f s) INTER convex hull (IMAGE f t) =
               convex hull (IMAGE f (s INTER t)))`;;

(* ------------------------------------------------------------------------- *)
(* Affine maps x |-> l x + y with l linear: extension from an affinely      *)
(* independent set, agreement on affine hulls, images of convex hulls.      *)
(* ------------------------------------------------------------------------- *)

let MOI_REAL_AFFINE_EXTEND_POINTS = prove
 (`!(c:real^M->bool) (g:real^M->real^N).
        ~affine_dependent c
        ==> ?l y. linear l /\ !x. x IN c ==> l x + y = g x`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c:real^M->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`\x:real^M. vec 0:real^N`; `vec 0:real^N`] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; LINEAR_ZERO];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:real^M` o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `independent {x - a | x | x IN (c:real^M->bool) DELETE a}`
  MP_TAC THENL
   [REWRITE_TAC[independent] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^M`; `(c:real^M->bool) DELETE a`]
      DEPENDENT_IMP_AFFINE_DEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_DELETE] THEN
    ASM_SIMP_TAC[SET_RULE `(a:real^M) IN c ==> a INSERT (c DELETE a) = c`];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LINEAR_INDEPENDENT_EXTEND) THEN
  DISCH_THEN(MP_TAC o SPEC `\z:real^M. (g:real^M->real^N)(z + a) - g a`) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_DELETE] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`l:real^M->real^N`;
                        `(g:real^M->real^N) a - (l:real^M->real^N) a`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:real^M = a` THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
  ASM_SIMP_TAC[LINEAR_SUB; VECTOR_ARITH `(x - a) + a:real^M = x`] THEN
  VECTOR_ARITH_TAC);;

let MOI_REAL_AFFINE_EXTEND = prove
 (`!(f:V->real^M) (g:V->real^N) s.
        ~affine_dependent (IMAGE f s) /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ?l y. linear l /\ !v. v IN s ==> l (f v) + y = g v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (f:V->real^M) s`;
                 `\x:real^M. (g:V->real^N) (@v. v IN s /\ f v = x)`]
    MOI_REAL_AFFINE_EXTEND_POINTS) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N`
   (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:V` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:V`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  SELECT_ELIM_TAC THEN ASM_MESON_TAC[]);;

let MOI_REAL_AFFINE_EQ_ON_AFFINE_HULL = prove
 (`!(l1:real^M->real^N) l2 y1 y2 s.
        linear l1 /\ linear l2 /\ (!x. x IN s ==> l1 x + y1 = l2 x + y2)
        ==> !x. x IN affine hull s ==> l1 x + y1 = l2 x + y2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `affine hull s SUBSET {x:real^M | (l1:real^M->real^N) x + y1 = l2 x + y2}`
  MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[affine; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `u:real`; `v:real`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `v = &1 - u` SUBST_ALL_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
    MAP_EVERY UNDISCH_TAC
     [`(l1:real^M->real^N) a + y1 = l2 a + y2`;
      `(l1:real^M->real^N) b + y1 = l2 b + y2`] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(p:real^N) + y1 = q + y2 <=> p = q + y2 - y1`] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN VECTOR_ARITH_TAC;
    SET_TAC[]]);;

let MOI_REAL_AFFINE_EQ_ON_CONVEX_HULL = prove
 (`!(l1:real^M->real^N) l2 y1 y2 s.
        linear l1 /\ linear l2 /\ (!x. x IN s ==> l1 x + y1 = l2 x + y2)
        ==> !x. x IN convex hull s ==> l1 x + y1 = l2 x + y2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_REAL_AFFINE_EQ_ON_AFFINE_HULL) THEN
  MP_TAC(ISPEC `s:real^M->bool` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
  SET_TAC[]);;

let MOI_REAL_AFFINE_IMAGE_CONVEX_HULL = prove
 (`!(l:real^M->real^N) y s.
        linear l
        ==> IMAGE (\x. l x + y) (convex hull s) =
            convex hull (IMAGE (\x. l x + y) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^M. (l:real^M->real^N) x + y) = (\x. y + x) o l`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o; CONVEX_HULL_TRANSLATION] THEN
  ASM_SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Result 1: the realization of a finite abstract complex is a simplicial   *)
(* complex (injectivity on vertices is not needed here).                    *)
(* ------------------------------------------------------------------------- *)

let ABSTRACT_REALIZATION_SIMPLICIAL_COMPLEX = prove
 (`!(f:V->real^N) k.
     FINITE k /\ abstract_complex k /\ abstract_realizes f k
     ==> simplicial_complex (abstract_realization f k)`,
  REWRITE_TAC[abstract_complex; abstract_realizes; abstract_realization] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_complex] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FINITE_INSERT; SIMPLE_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE];
    REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [EXISTS_TAC `-- &1:int` THEN REWRITE_TAC[SIMPLEX_EMPTY];
      X_GEN_TAC `s:V->bool` THEN DISCH_TAC THEN
      EXISTS_TAC `&(CARD(IMAGE (f:V->real^N) s)) - &1:int` THEN
      MATCH_MP_TAC SIMPLEX_CONVEX_HULL THEN ASM_SIMP_TAC[] THEN
      INT_ARITH_TAC];
    REWRITE_TAC[IMP_CONJ] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL [SIMP_TAC[FACE_OF_EMPTY; IN_INSERT]; ALL_TAC] THEN
    X_GEN_TAC `s:V->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `c:real^N->bool` THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `c':real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_IMAGE]) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:V->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `t:V->bool = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; IN_INSERT];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN DISJ2_TAC THEN
    EXISTS_TAC `t:V->bool` THEN ASM_MESON_TAC[];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT;
                FORALL_IN_GSPEC; INTER_EMPTY; EMPTY_FACE_OF] THEN
    X_GEN_TAC `s:V->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `t:V->bool` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    CONJ_TAC THEN EXISTS_TAC `IMAGE (f:V->real^N) (s INTER t)` THEN
    REWRITE_TAC[] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* General position.  A point avoiding the affine hulls of the images of    *)
(* all subsets of at most n <= dimindex(:N) points (finitely many proper     *)
(* affine subspaces, a negligible set); then induction on the finite vertex *)
(* set gives an injective map whose images of all subsets of at most n+1     *)
(* points are affinely independent.                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_REAL_AVOID_AFFINE_HULLS = prove
 (`!(f:V->real^N) w n.
        FINITE w /\ n <= dimindex(:N)
        ==> ?p. !u. u SUBSET w /\ CARD u <= n
                    ==> ~(p IN affine hull (IMAGE f u))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `negligible (UNIONS {affine hull (IMAGE (f:V->real^N) u) |
                        u | u SUBSET w /\ CARD u <= n})`
  MP_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{u:V->bool | u SUBSET w}` THEN
      ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `u:V->bool` THEN
      STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_AFFINE_HULL THEN
      SUBGOAL_THEN `FINITE (u:V->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD (u:V->bool)` THEN
      ASM_SIMP_TAC[CARD_IMAGE_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[NOT_NEGLIGIBLE_UNIV]
   `negligible s ==> ~(s = (:real^N))`)) THEN
  REWRITE_TAC[EXTENSION; IN_UNIV; NOT_FORALL_THM; IN_UNIONS; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]);;

let MOI_REAL_GENERAL_POSITION = prove
 (`!n (w:V->bool).
        FINITE w /\ 1 <= n /\ n <= dimindex(:N)
        ==> ?f:V->real^N.
              (!x y. x IN w /\ y IN w /\ f x = f y ==> x = y) /\
              (!u. u SUBSET w /\ CARD u <= n + 1
                   ==> ~affine_dependent (IMAGE f u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `FINITE (w:V->bool)` THEN
  SPEC_TAC(`w:V->bool`,`w:V->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [EXISTS_TAC `(\x. vec 0):V->real^N` THEN
    REWRITE_TAC[NOT_IN_EMPTY; SUBSET_EMPTY] THEN
    SIMP_TAC[IMAGE_CLAUSES; AFFINE_INDEPENDENT_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:V`; `w:V->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `f:V->real^N`
     (CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "ind")))
   STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:V->real^N`; `w:V->bool`; `n:num`]
    MOI_REAL_AVOID_AFFINE_HULLS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (LABEL_TAC "avoid")) THEN
  SUBGOAL_THEN `!y:V. y IN w ==> ~(p:real^N = f y)` (LABEL_TAC "new") THENL
   [X_GEN_TAC `y:V` THEN DISCH_TAC THEN
    USE_THEN "avoid" (MP_TAC o SPEC `{y:V}`) THEN
    REWRITE_TAC[SING_SUBSET; CARD_SING; IMAGE_CLAUSES; AFFINE_HULL_SING;
                IN_SING] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\x:V. if x = a then p else (f:V->real^N) x` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_INSERT] THEN MAP_EVERY X_GEN_TAC [`x:V`; `y:V`] THEN
    ASM_CASES_TAC `x:V = a` THEN ASM_CASES_TAC `y:V = a` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `u:V->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (u:V->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_INSERT]; ALL_TAC] THEN
  ASM_CASES_TAC `(a:V) IN u` THENL
   [SUBGOAL_THEN
     `IMAGE (\x:V. if x = a then p else (f:V->real^N) x) u =
      p INSERT IMAGE f (u DELETE a)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INSERT; IN_DELETE] THEN
      X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `x:V` STRIP_ASSUME_TAC) THEN
        ASM_CASES_TAC `x:V = a` THEN ASM_MESON_TAC[];
        STRIP_TAC THENL
         [EXISTS_TAC `a:V` THEN ASM_REWRITE_TAC[];
          EXISTS_TAC `x:V` THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(u:V->bool) DELETE a SUBSET w /\ CARD (u DELETE a) <= n`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[CARD_DELETE] THEN CONJ_TAC THENL
       [ASM SET_TAC[]; ASM_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN CONJ_TAC THENL
     [USE_THEN "ind" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      USE_THEN "avoid" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN
     `IMAGE (\x:V. if x = a then p else (f:V->real^N) x) u = IMAGE f u`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x:V. x IN u ==> (g:V->real^N) x = f x)
        ==> IMAGE g u = IMAGE f u`) THEN
      X_GEN_TAC `x:V` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(x:V = a)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "ind" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Result 2: existence of a realization in real^N, 2d+1 <= dimindex(:N).    *)
(* ------------------------------------------------------------------------- *)

let ABSTRACT_REALIZES_EXISTS = prove
 (`!(k:(V->bool)->bool) d.
     FINITE k /\ abstract_complex k /\ (!s. s IN k ==> CARD s <= d + 1) /\
     2 * d + 1 <= dimindex(:N)
     ==> ?f:V->real^N. abstract_realizes f k`,
  REWRITE_TAC[abstract_complex; abstract_realizes] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2 * d + 1`; `UNIONS k:V->bool`]
    MOI_REAL_GENERAL_POSITION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNIONS] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:V->real^N`
   (CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "ind"))) THEN
  EXISTS_TAC `f:V->real^N` THEN
  SUBGOAL_THEN `!s:V->bool. s IN k ==> s SUBSET UNIONS k` ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:V->bool` THEN DISCH_TAC THEN
    USE_THEN "ind" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `d + 1` THEN
    ASM_SIMP_TAC[] THEN ARITH_TAC;
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:V->bool`; `t:V->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (f:V->real^N) (s INTER t) = IMAGE f s INTER IMAGE f t`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!w. (!x y. x IN w /\ y IN w /\ (f:V->real^N) x = f y ==> x = y) /\
        s SUBSET w /\ t SUBSET w
        ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t`) THEN
      EXISTS_TAC `UNIONS k:V->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONVEX_HULL_INTER THEN REWRITE_TAC[GSYM IMAGE_UNION] THEN
    USE_THEN "ind" MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[UNION_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(s:V->bool) + CARD(t:V->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_UNION_LE THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE
     `a <= d + 1 /\ b <= d + 1 ==> a + b <= (2 * d + 1) + 1`) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Piecewise affine maps on finite unions of polytopes: continuity by        *)
(* pasting closed pieces, and the PL property (one global chart).           *)
(* ------------------------------------------------------------------------- *)

let MOI_REAL_CONTINUOUS_ON_CLOSED_UNIONS = prove
 (`!(h:real^M->real^N) c.
        FINITE c /\ (!s. s IN c ==> closed s /\ h continuous_on s)
        ==> h continuous_on (UNIONS c)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; CONTINUOUS_ON_EMPTY; UNIONS_INSERT;
              FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_UNION THEN
  ASM_MESON_TAC[CLOSED_UNIONS]);;

let MOI_REAL_PIECEWISE_AFFINE_UNIONS = prove
 (`!(h:real^M->real^N) c.
        FINITE c /\
        (!t. t IN c ==> polytope t /\
                        ?l y. linear l /\ !z. z IN t ==> h z = l z + y)
        ==> h continuous_on (UNIONS c) /\ pl_map_on (UNIONS c) h`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MOI_REAL_CONTINUOUS_ON_CLOSED_UNIONS THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N`
     (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\z:real^M. (l:real^M->real^N) z + y` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST];
    REWRITE_TAC[pl_map_on] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`c:(real^M->bool)->bool`; `(:real^M)`] THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; INTER_UNIV; SUBSET_REFL] THEN
    X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(t:real^M->bool) SUBSET UNIONS c` (fun th -> REWRITE_TAC[th])
    THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^M->bool`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Gluing maps given on the pieces of a family when they agree on overlaps. *)
(* ------------------------------------------------------------------------- *)

let MOI_REAL_GLUE = prove
 (`!(t:A->real^M->bool) (a:A->real^M->real^N) k.
        (!i j x. i IN k /\ j IN k /\ x IN t i /\ x IN t j ==> a i x = a j x)
        ==> ?h. !i x. i IN k /\ x IN t i ==> h x = a i x`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x:real^M. (a:A->real^M->real^N) (@i. i IN k /\ x IN t i) x` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  SELECT_ELIM_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The simplexwise affine map of a realization f onto vertex images g.      *)
(* ------------------------------------------------------------------------- *)

let MOI_REAL_SIMPLEXWISE_AFFINE = prove
 (`!(f:V->real^M) (g:V->real^N) k.
        abstract_realizes f k
        ==> ?h. !s. s IN k
                    ==> ?l y. linear l /\
                              (!v. v IN s ==> l (f v) + y = g v) /\
                              (!x. x IN convex hull (IMAGE f s)
                                   ==> h x = l x + y)`,
  REWRITE_TAC[abstract_realizes] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. s IN k
        ==> ?l y. linear l /\
                  !v. v IN s ==> (l:real^M->real^N) ((f:V->real^M) v) + y =
                                 (g:V->real^N) v`
  MP_TAC THENL
   [X_GEN_TAC `s:V->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_REAL_AFFINE_EXTEND THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(V->bool)->real^M->real^N`
   (X_CHOOSE_THEN `Y:(V->bool)->real^N` (LABEL_TAC "LY"))) THEN
  MP_TAC(ISPECL
   [`\s:V->bool. convex hull (IMAGE (f:V->real^M) s)`;
    `\s:V->bool. \x:real^M. (L:(V->bool)->real^M->real^N) s x + Y s`;
    `k:(V->bool)->bool`] MOI_REAL_GLUE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:V->bool`; `t:V->bool`; `x:real^M`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`(L:(V->bool)->real^M->real^N) s`;
                   `(L:(V->bool)->real^M->real^N) t`;
                   `(Y:(V->bool)->real^N) s`; `(Y:(V->bool)->real^N) t`;
                   `IMAGE (f:V->real^M) (s INTER t)`]
      MOI_REAL_AFFINE_EQ_ON_CONVEX_HULL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FORALL_IN_IMAGE; IN_INTER]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `x IN convex hull (IMAGE (f:V->real^M) s) INTER convex hull (IMAGE f t)`
    MP_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N` (LABEL_TAC "h")) THEN
  EXISTS_TAC `h:real^M->real^N` THEN X_GEN_TAC `s:V->bool` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`(L:(V->bool)->real^M->real^N) s`;
                        `(Y:(V->bool)->real^N) s`] THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  USE_THEN "h" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_REAL_IMAGE_SIMPLEX = prove
 (`!(f:V->real^M) (g:V->real^N) h l y s.
        linear l /\ (!v. v IN s ==> l (f v) + y = g v) /\
        (!x. x IN convex hull (IMAGE f s) ==> h x = l x + y)
        ==> IMAGE h (convex hull (IMAGE f s)) = convex hull (IMAGE g s)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `IMAGE (\x. (l:real^M->real^N) x + y)
          (convex hull (IMAGE (f:V->real^M) s))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_REAL_AFFINE_IMAGE_CONVEX_HULL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN MATCH_MP_TAC IMAGE_EQ THEN
  ASM_SIMP_TAC[]);;

let MOI_REAL_AFFINE_INVERSE_ON_SIMPLEX = prove
 (`!(f:V->real^M) (g:V->real^N) h h' l y l' y' s.
        linear l /\ linear l' /\
        (!v. v IN s ==> l (f v) + y = g v) /\
        (!v. v IN s ==> l' (g v) + y' = f v) /\
        (!x. x IN convex hull (IMAGE f s) ==> h x = l x + y) /\
        (!x. x IN convex hull (IMAGE g s) ==> h' x = l' x + y')
        ==> !x. x IN convex hull (IMAGE f s) ==> h' (h x) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^M->real^N) x = l x + y` SUBST1_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(l:real^M->real^N) x + y IN convex hull (IMAGE (g:V->real^N) s)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:V->real^M`; `g:V->real^N`; `h:real^M->real^N`;
                   `l:real^M->real^N`; `y:real^N`; `s:V->bool`]
      MOI_REAL_IMAGE_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `x:real^M` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `!z. z IN convex hull (IMAGE (f:V->real^M) s)
        ==> ((l':real^N->real^M) o (l:real^M->real^N)) z + (l' y + y') =
            (\z:real^M. z) z + vec 0`
  MP_TAC THENL
   [MATCH_MP_TAC MOI_REAL_AFFINE_EQ_ON_CONVEX_HULL THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[LINEAR_COMPOSE; LINEAR_ID] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN
    X_GEN_TAC `v:V` THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ADD_RID; VECTOR_ADD_ASSOC] THEN
    SUBGOAL_THEN
     `(l':real^N->real^M) ((l:real^M->real^N) ((f:V->real^M) v)) + l' y =
      l' (g v)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM LINEAR_ADD]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ASM_SIMP_TAC[o_THM; VECTOR_ADD_RID; LINEAR_ADD] THEN
  VECTOR_ARITH_TAC);;

let MOI_REAL_IMAGE_UNIONS_GSPEC = prove
 (`!(h:A->B) (a:C->A->bool) b k.
        (!s. s IN k ==> IMAGE h (a s) = b s)
        ==> IMAGE h (UNIONS {a s | s IN k}) = UNIONS {b s | s IN k}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
  REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o; o_DEF] THEN
  MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Result 3: two realizations of one finite complex are PL homeomorphic by  *)
(* the simplexwise affine map extending the vertex correspondence.          *)
(* ------------------------------------------------------------------------- *)

let ABSTRACT_REALIZATIONS_PL_HOMEOMORPHIC = prove
 (`!(f:V->real^M) (g:V->real^N) k.
     FINITE k /\ abstract_complex k /\ abstract_realizes f k /\ abstract_realizes g k
     ==> ?h h'. pl_homeomorphism (UNIONS (abstract_realization f k),
                                  UNIONS (abstract_realization g k)) (h,h') /\
                (!v. v IN UNIONS k ==> h(f v) = g v) /\
                (!s. s IN k
                     ==> IMAGE h (convex hull (IMAGE f s)) =
                         convex hull (IMAGE g s) /\
                         ?l y. linear l /\
                               !x. x IN convex hull (IMAGE f s) ==> h x = l x + y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!s:V->bool. s IN k ==> FINITE s` ASSUME_TAC THENL
   [ASM_MESON_TAC[abstract_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:V->real^M`; `g:V->real^N`; `k:(V->bool)->bool`]
    MOI_REAL_SIMPLEXWISE_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N` (LABEL_TAC "h")) THEN
  MP_TAC(ISPECL [`g:V->real^N`; `f:V->real^M`; `k:(V->bool)->bool`]
    MOI_REAL_SIMPLEXWISE_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h':real^N->real^M` (LABEL_TAC "h'")) THEN
  MAP_EVERY EXISTS_TAC [`h:real^M->real^N`; `h':real^N->real^M`] THEN
  SUBGOAL_THEN
   `!s. s IN k
        ==> IMAGE (h:real^M->real^N) (convex hull (IMAGE (f:V->real^M) s)) =
            convex hull (IMAGE (g:V->real^N) s) /\
            IMAGE (h':real^N->real^M) (convex hull (IMAGE g s)) =
            convex hull (IMAGE f s) /\
            (!x. x IN convex hull (IMAGE f s) ==> h' (h x) = x) /\
            (!x. x IN convex hull (IMAGE g s) ==> h (h' x) = x) /\
            (?l y. linear l /\
                   !x. x IN convex hull (IMAGE f s) ==> h x = l x + y) /\
            (?l y. linear l /\
                   !x. x IN convex hull (IMAGE g s) ==> h' x = l x + y)`
  (LABEL_TAC "S") THENL
   [X_GEN_TAC `s:V->bool` THEN DISCH_TAC THEN
    USE_THEN "h" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:V->bool) IN k`))) THEN
    USE_THEN "h'" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:V->bool) IN k`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M`
     (X_CHOOSE_THEN `y':real^M` STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N`
     (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_REAL_IMAGE_SIMPLEX THEN
      MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_REAL_IMAGE_SIMPLEX THEN
      MAP_EVERY EXISTS_TAC [`l':real^N->real^M`; `y':real^M`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_REAL_AFFINE_INVERSE_ON_SIMPLEX THEN
      MAP_EVERY EXISTS_TAC [`g:V->real^N`; `l:real^M->real^N`; `y:real^N`;
                            `l':real^N->real^M`; `y':real^M`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_REAL_AFFINE_INVERSE_ON_SIMPLEX THEN
      MAP_EVERY EXISTS_TAC [`f:V->real^M`; `l':real^N->real^M`; `y':real^M`;
                            `l:real^M->real^N`; `y:real^N`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`l':real^N->real^M`; `y':real^M`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h:real^M->real^N) continuous_on
      UNIONS {convex hull (IMAGE (f:V->real^M) s) | s IN k} /\
    pl_map_on (UNIONS {convex hull (IMAGE f s) | s IN k}) h`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_REAL_PIECEWISE_AFFINE_UNIONS THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `s:V->bool` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_SIMP_TAC[];
      USE_THEN "S" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:V->bool) IN k`))) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h':real^N->real^M) continuous_on
      UNIONS {convex hull (IMAGE (g:V->real^N) s) | s IN k} /\
    pl_map_on (UNIONS {convex hull (IMAGE g s) | s IN k}) h'`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_REAL_PIECEWISE_AFFINE_UNIONS THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `s:V->bool` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_SIMP_TAC[];
      USE_THEN "S" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:V->bool) IN k`))) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism; abstract_realization;
              UNIONS_INSERT; UNION_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                FORALL_IN_GSPEC] THEN
    X_GEN_TAC `s:V->bool` THEN DISCH_TAC THEN
    USE_THEN "S" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:V->bool) IN k`))) THEN
    SIMP_TAC[];
    MP_TAC(ISPECL [`h:real^M->real^N`;
                   `\s:V->bool. convex hull (IMAGE (f:V->real^M) s)`;
                   `\s:V->bool. convex hull (IMAGE (g:V->real^N) s)`;
                   `k:(V->bool)->bool`] MOI_REAL_IMAGE_UNIONS_GSPEC) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `s:V->bool` THEN DISCH_TAC THEN
    USE_THEN "S" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:V->bool) IN k`))) THEN
    SIMP_TAC[];
    REWRITE_TAC[FORALL_IN_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                FORALL_IN_GSPEC] THEN
    X_GEN_TAC `s:V->bool` THEN DISCH_TAC THEN
    USE_THEN "S" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:V->bool) IN k`))) THEN
    SIMP_TAC[];
    MP_TAC(ISPECL [`h':real^N->real^M`;
                   `\s:V->bool. convex hull (IMAGE (g:V->real^N) s)`;
                   `\s:V->bool. convex hull (IMAGE (f:V->real^M) s)`;
                   `k:(V->bool)->bool`] MOI_REAL_IMAGE_UNIONS_GSPEC) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `s:V->bool` THEN DISCH_TAC THEN
    USE_THEN "S" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:V->bool) IN k`))) THEN
    SIMP_TAC[];
    REWRITE_TAC[FORALL_IN_UNIONS] THEN
    MAP_EVERY X_GEN_TAC [`s:V->bool`; `v:V`] THEN STRIP_TAC THEN
    USE_THEN "h" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:V->bool) IN k`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N`
     (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(f:V->real^M) v IN convex hull (IMAGE f s)` ASSUME_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `s:V->bool` THEN DISCH_TAC THEN
    USE_THEN "S" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:V->bool) IN k`))) THEN
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The abstract complex of vertex sets of a geometric simplicial complex:   *)
(* the affinely independent nonempty sets whose hulls are simplices of c.   *)
(* It is realized by the identity map, with polyhedron UNIONS c.            *)
(* ------------------------------------------------------------------------- *)

let moi_real_vertex_sets = new_definition
 `moi_real_vertex_sets (c:(real^M->bool)->bool) =
    {t | ~(t = {}) /\ ~affine_dependent t /\ convex hull t IN c}`;;

let MOI_REAL_IN_VERTEX_SETS = prove
 (`!(c:(real^M->bool)->bool) t.
        t IN moi_real_vertex_sets c <=>
        ~(t = {}) /\ ~affine_dependent t /\ convex hull t IN c`,
  REWRITE_TAC[moi_real_vertex_sets; IN_ELIM_THM]);;

let MOI_REAL_SIMPLEX_VERTICES = prove
 (`!(c:(real^M->bool)->bool) s.
        simplicial_complex c /\ s IN c /\ ~(s = {})
        ==> ?t. t IN moi_real_vertex_sets c /\ s = convex hull t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^M->bool)` MP_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  REWRITE_TAC[SIMPLEX; MOI_REAL_IN_VERTEX_SETS] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `t:real^M->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `t:real^M->bool` THEN
  ASM_MESON_TAC[CONVEX_HULL_EQ_EMPTY]);;

let MOI_REAL_VERTEX_SETS_FINITE = prove
 (`!c:(real^M->bool)->bool.
        FINITE c ==> FINITE (moi_real_vertex_sets c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\s:real^M->bool. {v:real^M | v extreme_point_of s}) c` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; MOI_REAL_IN_VERTEX_SETS; IN_IMAGE] THEN
  X_GEN_TAC `t:real^M->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `convex hull t:real^M->bool` THEN
  ASM_SIMP_TAC[EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT]);;

let MOI_REAL_VERTEX_SETS_ABSTRACT_COMPLEX = prove
 (`!c:(real^M->bool)->bool.
        simplicial_complex c ==> abstract_complex (moi_real_vertex_sets c)`,
  REWRITE_TAC[abstract_complex; MOI_REAL_IN_VERTEX_SETS] THEN
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^M->bool`; `t:real^M->bool`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[AFFINE_DEPENDENT_MONO]; ALL_TAC] THEN
  UNDISCH_TAC `simplicial_complex (c:(real^M->bool)->bool)` THEN
  REWRITE_TAC[simplicial_complex] THEN
  DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
  EXISTS_TAC `convex hull s:real^M->bool` THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  EXISTS_TAC `t:real^M->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL = prove
 (`!(c:(real^M->bool)->bool) s t.
        simplicial_complex c /\
        ~affine_dependent s /\ ~affine_dependent t /\
        convex hull s IN c /\ convex hull t IN c
        ==> convex hull s INTER convex hull t = convex hull (s INTER t)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `simplicial_complex (c:(real^M->bool)->bool)` THEN
  REWRITE_TAC[simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPECL [`convex hull s:real^M->bool`;
                             `convex hull t:real^M->bool`] o
             last o CONJUNCTS) THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s':real^M->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `t':real^M->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `~affine_dependent (s':real^M->bool) /\ ~affine_dependent (t':real^M->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_DEPENDENT_MONO]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull s' = convex hull (t':real^M->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s':real^M->bool = t'` ASSUME_TAC THENL
   [MP_TAC(ISPEC `s':real^M->bool`
      EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    MP_TAC(ISPEC `t':real^M->bool`
      EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
    SIMP_TAC[SUBSET_INTER; HULL_MONO; INTER_SUBSET]]);;

let MOI_REAL_VERTEX_SETS_REALIZES = prove
 (`!c:(real^M->bool)->bool.
        simplicial_complex c
        ==> abstract_realizes (\x:real^M. x) (moi_real_vertex_sets c)`,
  REWRITE_TAC[abstract_realizes; MOI_REAL_IN_VERTEX_SETS; IMAGE_ID] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL THEN
  EXISTS_TAC `c:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_REAL_VERTEX_SETS_CARD = prove
 (`!(c:(real^M->bool)->bool) d.
        (!s. s IN c ==> aff_dim s <= &d)
        ==> !t. t IN moi_real_vertex_sets c ==> CARD t <= d + 1`,
  REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `convex hull t:real^M->bool`) THEN
  ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
  REWRITE_TAC[INT_ARITH `a - &1:int <= b <=> a <= b + &1`;
              INT_OF_NUM_ADD; INT_OF_NUM_LE]);;

let MOI_REAL_VERTEX_SETS_UNIONS = prove
 (`!c:(real^M->bool)->bool.
        simplicial_complex c
        ==> UNIONS (abstract_realization (\x:real^M. x)
                                         (moi_real_vertex_sets c)) =
            UNIONS c`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[abstract_realization; UNIONS_INSERT; UNION_EMPTY; IMAGE_ID] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^M` THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM; MOI_REAL_IN_VERTEX_SETS] THEN
    X_GEN_TAC `u:real^M->bool` THEN STRIP_TAC THEN
    EXISTS_TAC `u:real^M->bool` THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `s:real^M->bool`]
      MOI_REAL_SIMPLEX_VERTICES) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `t:real^M->bool` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Result 4: re-realization of a geometric simplicial complex of dimension  *)
(* at most d in real^N, 2d+1 <= dimindex(:N), by a simplexwise affine PL     *)
(* homeomorphism carrying simplices onto simplices.                          *)
(* ------------------------------------------------------------------------- *)

let SIMPLICIAL_COMPLEX_REREALIZATION = prove
 (`!(c:(real^M->bool)->bool) d.
     simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &d) /\
     2 * d + 1 <= dimindex(:N)
     ==> ?(c':(real^N->bool)->bool) h h'.
           simplicial_complex c' /\
           pl_homeomorphism (UNIONS c,UNIONS c') (h,h') /\
           (!s. s IN c ==> IMAGE h s IN c') /\
           (!s'. s' IN c' ==> ?s. s IN c /\ s' = IMAGE h s) /\
           (!s. s IN c ==> ?l y. linear l /\ !x. x IN s ==> h x = l x + y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `FINITE (moi_real_vertex_sets (c:(real^M->bool)->bool)) /\
    abstract_complex (moi_real_vertex_sets c) /\
    abstract_realizes (\x:real^M. x) (moi_real_vertex_sets c)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_REAL_VERTEX_SETS_ABSTRACT_COMPLEX;
                 MOI_REAL_VERTEX_SETS_REALIZES] THEN
    MATCH_MP_TAC MOI_REAL_VERTEX_SETS_FINITE THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_real_vertex_sets (c:(real^M->bool)->bool)`; `d:num`]
    ABSTRACT_REALIZES_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_REAL_VERTEX_SETS_CARD THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^M->real^N`) THEN
  MP_TAC(ISPECL [`\x:real^M. x`; `g:real^M->real^N`;
                 `moi_real_vertex_sets (c:(real^M->bool)->bool)`]
    ABSTRACT_REALIZATIONS_PL_HOMEOMORPHIC) THEN
  ASM_REWRITE_TAC[IMAGE_ID] THEN
  ASM_SIMP_TAC[MOI_REAL_VERTEX_SETS_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N`
   (X_CHOOSE_THEN `h':real^N->real^M`
     (CONJUNCTS_THEN2 (LABEL_TAC "plh")
        (CONJUNCTS_THEN2 (LABEL_TAC "vert") (LABEL_TAC "simp"))))) THEN
  EXISTS_TAC `IMAGE (IMAGE (h:real^M->real^N)) c` THEN
  MAP_EVERY EXISTS_TAC [`h:real^M->real^N`; `h':real^N->real^M`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `c:(real^M->bool)->bool = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; simplicial_complex; FINITE_EMPTY;
                      NOT_IN_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `({}:real^M->bool) IN c` ASSUME_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_TAC `s:real^M->bool` o
        REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
      UNDISCH_TAC `simplicial_complex (c:(real^M->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[EMPTY_FACE_OF];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (IMAGE (h:real^M->real^N)) c =
      abstract_realization g (moi_real_vertex_sets c)`
    SUBST1_TAC THENL
     [REWRITE_TAC[abstract_realization] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_INSERT; FORALL_IN_GSPEC]
      THENL
       [X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
        ASM_CASES_TAC `s:real^M->bool = {}` THENL
         [ASM_REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT]; ALL_TAC] THEN
        MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `s:real^M->bool`]
          MOI_REAL_SIMPLEX_VERTICES) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
        REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN DISJ2_TAC THEN
        EXISTS_TAC `t:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "simp" (fun th ->
          MP_TAC(MATCH_MP th (ASSUME
            `(t:real^M->bool) IN moi_real_vertex_sets c`))) THEN
        SIMP_TAC[];
        CONJ_TAC THENL
         [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `{}:real^M->bool` THEN
          ASM_REWRITE_TAC[IMAGE_CLAUSES];
          ALL_TAC] THEN
        X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `convex hull t:real^M->bool` THEN
        CONJ_TAC THENL
         [USE_THEN "simp" (fun th ->
            MP_TAC(MATCH_MP th (ASSUME
              `(t:real^M->bool) IN moi_real_vertex_sets c`))) THEN
          SIMP_TAC[];
          ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS]]];
      ALL_TAC] THEN
    MATCH_MP_TAC ABSTRACT_REALIZATION_SIMPLICIAL_COMPLEX THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `UNIONS (IMAGE (IMAGE (h:real^M->real^N)) c) =
      UNIONS (abstract_realization g (moi_real_vertex_sets c))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_UNIONS] THEN
      USE_THEN "plh" (MP_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
      SIMP_TAC[];
      USE_THEN "plh" ACCEPT_TAC];
    SIMP_TAC[FUN_IN_IMAGE];
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^M->bool = {}` THENL
     [MAP_EVERY EXISTS_TAC [`\x:real^M. vec 0:real^N`; `vec 0:real^N`] THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY; LINEAR_ZERO];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `s:real^M->bool`]
      MOI_REAL_SIMPLEX_VERTICES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "simp" (fun th ->
      MP_TAC(MATCH_MP th (ASSUME
        `(t:real^M->bool) IN moi_real_vertex_sets c`))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

