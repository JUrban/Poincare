(* ========================================================================= *)
(* pc_sch_level: regular levels of the height x$3 on a collared sphere in    *)
(* R^3, a step of the proof of the smooth Schoenflies theorem.               *)
(*                                                                           *)
(* Main result: SCH_LEVEL_FINITE |- SCH_LEVEL_FINITE_STATEMENT: a level of  *)
(* the height containing no critical point is compact and locally           *)
(* connected (an inverse-function chart in parameter space straightens it    *)
(* into a segment), hence has finitely many components (FINITE_COMPONENTS). *)
(* The local machinery (inverse-function charts at points of the sphere,     *)
(* adapted to the height) is reused by pc_sch_generic.                       *)
(* ========================================================================= *)

needs "src/pc_sch_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Linear algebra in R^3 (with the cross product written out, since the      *)
(* library cross product is not loaded) and restriction of diffeomorphisms.  *)
(* ------------------------------------------------------------------------- *)

(* Cramer's rule for the matrix with rows t, u and t x u (written out).      *)

let SCH4_CRAMER3 = prove
 (`!t1 t2 t3 u1 u2 u3 h1 h2 h3:real.
     t1 * h1 + t2 * h2 + t3 * h3 = &0 /\
     u1 * h1 + u2 * h2 + u3 * h3 = &0 /\
     (t2 * u3 - t3 * u2) * h1 + (t3 * u1 - t1 * u3) * h2 +
     (t1 * u2 - t2 * u1) * h3 = &0
     ==> ((t2 * u3 - t3 * u2) pow 2 + (t3 * u1 - t1 * u3) pow 2 +
          (t1 * u2 - t2 * u1) pow 2) * h1 = &0 /\
         ((t2 * u3 - t3 * u2) pow 2 + (t3 * u1 - t1 * u3) pow 2 +
          (t1 * u2 - t2 * u1) pow 2) * h2 = &0 /\
         ((t2 * u3 - t3 * u2) pow 2 + (t3 * u1 - t1 * u3) pow 2 +
          (t1 * u2 - t2 * u1) pow 2) * h3 = &0`,
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

(* If t is a unit vector and u is not a multiple of t, then t, u and their   *)
(* cross product (written out) have no common orthogonal vector but 0.       *)

let SCH4_CROSS3_INJ = prove
 (`!t u h:real^3.
     norm t = &1 /\ ~(u = (t dot u) % t) /\
     t dot h = &0 /\ u dot h = &0 /\
     (vector[t$2 * u$3 - t$3 * u$2; t$3 * u$1 - t$1 * u$3;
             t$1 * u$2 - t$2 * u$1]:real^3) dot h = &0
     ==> h = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(norm(u - (t dot u) % t:real^3) pow 2 = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0; VECTOR_SUB_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3) dot t = &1` MP_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(t:real^3) dot h = &0`; `(u:real^3) dot h = &0`;
    `(vector[(t:real^3)$2 * (u:real^3)$3 - t$3 * u$2; t$3 * u$1 - t$1 * u$3;
             t$1 * u$2 - t$2 * u$1]:real^3) dot h = &0`] THEN
  REWRITE_TAC[NORM_POW_2; DOT_3; VECTOR_3; CART_EQ; DIMINDEX_3; FORALL_3;
              VEC_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  MAP_EVERY (fun (a,b) -> SPEC_TAC(a,b))
   [`(h:real^3)$3`,`h3:real`; `(h:real^3)$2`,`h2:real`; `(h:real^3)$1`,`h1:real`;
    `(u:real^3)$3`,`u3:real`; `(u:real^3)$2`,`u2:real`; `(u:real^3)$1`,`u1:real`;
    `(t:real^3)$3`,`t3:real`; `(t:real^3)$2`,`t2:real`; `(t:real^3)$1`,`t1:real`] THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`t1:real`; `t2:real`; `t3:real`; `u1:real`; `u2:real`; `u3:real`;
                `h1:real`; `h2:real`; `h3:real`] SCH4_CRAMER3) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  SUBGOAL_THEN
   `(u1 - (t1 * u1 + t2 * u2 + t3 * u3) * t1) *
    (u1 - (t1 * u1 + t2 * u2 + t3 * u3) * t1) +
    (u2 - (t1 * u1 + t2 * u2 + t3 * u3) * t2) *
    (u2 - (t1 * u1 + t2 * u2 + t3 * u3) * t2) +
    (u3 - (t1 * u1 + t2 * u2 + t3 * u3) * t3) *
    (u3 - (t1 * u1 + t2 * u2 + t3 * u3) * t3) =
    (t2 * u3 - t3 * u2) pow 2 + (t3 * u1 - t1 * u3) pow 2 +
    (t1 * u2 - t2 * u1) pow 2`
  SUBST1_TAC THENL
   [UNDISCH_TAC `t1 * t1 + t2 * t2 + t3 * t3 = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN MESON_TAC[]);;

(* The third row of the matrix of a linear map computes the third           *)
(* component.                                                                *)

let SCH4_ROW3_DOT = prove
 (`!L:real^3->real^3 h. linear L ==> (matrix L)$3 dot h = (L h)$3`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)
    [GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH]);;

(* The derivative in a has_derivative statement is linear.                  *)

let SCH4_HAS_DERIVATIVE_IMP_LINEAR = prove
 (`!(f:real^M->real^N) f' net. (f has_derivative f') net ==> linear f'`,
  SIMP_TAC[has_derivative]);;

(* Restriction of a diffeomorphism to an open subset of its domain.          *)

let SCH4_DIFFEO_RESTRICT = prove
 (`!s t (f:real^M->real^N) f' w.
        diffeomorphism_on s t f f' /\ open w /\ w SUBSET s
        ==> diffeomorphism_on w (IMAGE f w) f f'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) w = {y | y IN t /\ f' y IN w}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN ASM SET_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN ASM SET_TAC[]]);;

(* Images of open subsets under a diffeomorphism are open.                    *)

let SCH4_DIFFEO_IMAGE_OPEN = prove
 (`!s t (f:real^M->real^N) f' w.
        diffeomorphism_on s t f f' /\ open w /\ w SUBSET s
        ==> open(IMAGE f w)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SCH4_DIFFEO_RESTRICT) THEN
  SIMP_TAC[diffeomorphism_on]);;

(* ------------------------------------------------------------------------- *)
(* Basic facts about necks, and the height chart map                         *)
(*   x |-> (|x|^2, (g x)$3, c dot x)                                         *)
(* (its derivative and smoothness).                                          *)
(* ------------------------------------------------------------------------- *)

let SCH4_SPHERE_SUBSET_ANNULUS = prove
 (`sphere(vec 0:real^N,&1) SUBSET annulus (&1 / &2) (&2)`,
  REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
  REAL_ARITH_TAC);;

let SCH4_NECK_FACTS = prove
 (`!g g':real^N->real^N.
        sch_neck g g'
        ==> open(annulus (&1 / &2) (&2):real^N->bool) /\
            smooth_map_on (annulus (&1 / &2) (&2)) g /\
            g continuous_on annulus (&1 / &2) (&2) /\
            open(IMAGE g (annulus (&1 / &2) (&2))) /\
            smooth_map_on (IMAGE g (annulus (&1 / &2) (&2))) g' /\
            g' continuous_on IMAGE g (annulus (&1 / &2) (&2)) /\
            (!x. x IN annulus (&1 / &2) (&2) ==> g'(g x) = x) /\
            (!y. y IN IMAGE g (annulus (&1 / &2) (&2)) ==> g(g' y) = y /\
                 g' y IN annulus (&1 / &2) (&2)) /\
            (!x. x IN annulus (&1 / &2) (&2)
                 ==> (g has_derivative frechet_derivative g (at x)) (at x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_neck; diffeomorphism_on] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_HAS_DERIVATIVE THEN ASM_REWRITE_TAC[]);;

(* The derivative of the height chart map.                                   *)

let SCH4_HMAP_DERIV = prove
 (`!(g:real^3->real^3) g' (c:real^3) s.
        (g has_derivative g') (at s)
        ==> ((\x. vector[norm x pow 2; (g x)$3; c dot x]:real^3) has_derivative
             (\h. vector[&2 * (s dot h); (g' h)$3; c dot h])) (at s)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [HAS_DERIVATIVE_COMPONENTWISE_AT] THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_3] THENL
   [REWRITE_TAC[LIFT_CMUL; HAS_DERIVATIVE_SQNORM_AT];
    SUBGOAL_THEN `!y:real^3. y$3 = basis 3 dot y`
     (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LIFT_DOT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_DOT]]);;

(* Its smoothness.                                                           *)

let SCH4_HMAP_SMOOTH = prove
 (`!(g:real^3->real^3) (c:real^3) s.
        open s /\ smooth_map_on s g
        ==> smooth_map_on s (\x. vector[norm x pow 2; (g x)$3; c dot x]:real^3)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE th]) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_3] THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `\x:real^3. x`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`s:real^3->bool`; `\x:real^3. c:real^3`; `\x:real^3. x`]
      SMOOTH_MAP_ON_DOT_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]]);;

(* ------------------------------------------------------------------------- *)
(* An inverse-function chart at a regular point of the height.               *)
(* At a parameter t on the unit sphere that is not critical for g, the map   *)
(*   x |-> (|x|^2, (g x)$3, c dot x)                                         *)
(* (c = t x u, u the third row of the derivative of g at t) is a local       *)
(* diffeomorphism; in these coordinates the level of the height through g t  *)
(* is a straight segment.                                                    *)
(* ------------------------------------------------------------------------- *)

(* Non-critical means: the third row of the derivative is not a multiple of  *)
(* the normal t.                                                             *)

let SCH4_NONCRIT_ROW = prove
 (`!g:real^3->real^3 t.
        t IN sphere(vec 0,&1) /\ ~sch_crit g t /\
        linear(frechet_derivative g (at t))
        ==> ~((matrix(frechet_derivative g (at t)))$3 =
              (t dot (matrix(frechet_derivative g (at t)))$3) % t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_crit] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?v:real^3. orthogonal t v /\
                           ~((frechet_derivative (g:real^3->real^3) (at t) v)$3 = &0)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\w:real^3. w dot v`) THEN
  ASM_SIMP_TAC[SCH4_ROW3_DOT; DOT_LMUL] THEN
  UNDISCH_TAC `orthogonal (t:real^3) v` THEN REWRITE_TAC[orthogonal] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

(* The chart.                                                                *)

let SCH4_REGULAR_CHART = prove
 (`!g g':real^3->real^3 t.
        sch_neck g g' /\ t IN sphere(vec 0,&1) /\ ~sch_crit g t
        ==> ?c Td U Psi.
              open Td /\ t IN Td /\ Td SUBSET annulus (&1 / &2) (&2) /\ open U /\
              diffeomorphism_on Td U
                (\x. vector[norm x pow 2; (g x)$3; c dot x]:real^3) Psi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  SUBGOAL_THEN `(t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `((g:real^3->real^3) has_derivative frechet_derivative g (at t)) (at t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (g:real^3->real^3) (at t))` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `t:real^3`] SCH4_NONCRIT_ROW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `L = frechet_derivative (g:real^3->real^3) (at t)` THEN
  ABBREV_TAC `u:real^3 = (matrix(L:real^3->real^3))$3` THEN
  ABBREV_TAC `c:real^3 = vector[(t:real^3)$2 * (u:real^3)$3 - t$3 * u$2;
                                t$3 * u$1 - t$1 * u$3; t$1 * u$2 - t$2 * u$1]` THEN
  EXISTS_TAC `c:real^3` THEN
  MP_TAC(ISPECL [`\x. vector[norm x pow 2; (g:real^3->real^3) x$3; c dot x]:real^3`;
                 `annulus (&1 / &2) (&2):real^3->bool`; `t:real^3`]
         SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SCH4_HMAP_SMOOTH] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `L:real^3->real^3`; `c:real^3`; `t:real^3`]
      SCH4_HMAP_DERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET; NOT_EXISTS_THM] THEN
    X_GEN_TAC `h:real^3` THEN
    SUBGOAL_THEN `linear(\h. vector[&2 * ((t:real^3) dot h);
                                    ((L:real^3->real^3) h)$3; (c:real^3) dot h]:real^3)`
    ASSUME_TAC THENL [ASM_MESON_TAC[SCH4_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN
    REWRITE_TAC[TAUT `~(~p /\ q) <=> q ==> p`] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                                      VEC_COMPONENT]) THEN
    STRIP_TAC THEN MATCH_MP_TAC SCH4_CROSS3_INJ THEN
    MAP_EVERY EXISTS_TAC [`t:real^3`; `u:real^3`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IN_SPHERE_0];
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "u" THEN ASM_SIMP_TAC[SCH4_ROW3_DOT];
      ASM_REWRITE_TAC[]];
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Regular levels are compact and locally connected, hence have              *)
(* finitely many components: SCH_LEVEL_FINITE.                               *)
(* ------------------------------------------------------------------------- *)

let SCH4_LEVEL_EQ = prove
 (`!g:real^3->real^3 a.
        sch_level g a = IMAGE g (sphere(vec 0,&1)) INTER {x:real^3 | x$3 = a}`,
  REWRITE_TAC[sch_level; EXTENSION; IN_INTER; IN_ELIM_THM]);;

let SCH4_LEVEL_COMPACT = prove
 (`!g g':real^3->real^3 a. sch_neck g g' ==> compact(sch_level g a)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  REWRITE_TAC[SCH4_LEVEL_EQ] THEN
  MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
  REWRITE_TAC[CLOSED_STANDARD_HYPERPLANE] THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_SPHERE] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
  ASM_REWRITE_TAC[SCH4_SPHERE_SUBSET_ANNULUS]);;

(* In the chart of SCH4_REGULAR_CHART, the level near g t0 is the image of a *)
(* straight segment.                                                         *)

let SCH4_LEVEL_IN_CHART = prove
 (`!g g':real^3->real^3 a c Td U Psi B.
        sch_neck g g' /\ Td SUBSET annulus (&1 / &2) (&2) /\
        diffeomorphism_on Td U
          (\x. vector[norm x pow 2; (g x)$3; c dot x]:real^3) Psi /\
        B SUBSET U
        ==> sch_level g a INTER IMAGE (g o Psi) B =
            IMAGE (g o Psi) {z | z IN B /\ z$1 = &1 /\ z$2 = a}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  SUBGOAL_THEN
   `!z:real^3. z IN U
               ==> (Psi:real^3->real^3) z IN Td /\
                   norm(Psi z) pow 2 = z$1 /\ ((g:real^3->real^3)(Psi z))$3 = z$2`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `diffeomorphism_on Td U
          (\x. vector[norm x pow 2; (g:real^3->real^3) x$3; (c:real^3) dot x]:real^3)
          Psi` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(vector[norm((Psi:real^3->real^3) z) pow 2; (g:real^3->real^3)(Psi z)$3;
                          (c:real^3) dot Psi z]:real^3) = z` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(AP_TERM `\v:real^3. v$1` th) THEN
                         MP_TAC(AP_TERM `\v:real^3. v$2` th)) THEN
    REWRITE_TAC[VECTOR_3] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; o_THM; sch_level; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)
      (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^3) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Psi:real^3->real^3) z = s` ASSUME_TAC THENL
     [SUBGOAL_THEN `(Psi:real^3->real^3) z IN annulus (&1 / &2) (&2) /\
                    (s:real^3) IN annulus (&1 / &2) (&2)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET];
        ALL_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(s:real^3) = &1` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `norm((Psi:real^3->real^3) z) pow 2 = (z:real^3)$1`)) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `((g:real^3->real^3)((Psi:real^3->real^3) z))$3 = (z:real^3)$2`)) THEN
      ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [CONJ_TAC THENL
       [EXISTS_TAC `(Psi:real^3->real^3) z` THEN ASM_REWRITE_TAC[IN_SPHERE_0] THEN
        MP_TAC(ISPECL [`norm((Psi:real^3->real^3) z)`; `2`] REAL_POW_EQ_1) THEN
        ASM_REWRITE_TAC[REAL_ABS_NORM] THEN ARITH_TAC;
        ASM_REWRITE_TAC[]];
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]]]);;

let SCH4_LEVEL_LOCALLY_CONNECTED = prove
 (`!g g':real^3->real^3 a.
        sch_neck g g' /\ (!t. sch_crit g t ==> ~((g t)$3 = a))
        ==> locally connected (sch_level g a)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  REWRITE_TAC[LOCALLY_CONNECTED] THEN
  MAP_EVERY X_GEN_TAC [`v:real^3->bool`; `x:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `O:real^3->bool` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  SUBGOAL_THEN `?t0:real^3. t0 IN sphere(vec 0,&1) /\ (g:real^3->real^3) t0 = x /\
                            (x:real^3)$3 = a /\ x IN O`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN v` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    REWRITE_TAC[sch_level; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t0:real^3`]
    SCH4_REGULAR_CHART) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:real^3`; `Td:real^3->bool`; `U:real^3->bool`;
                       `Psi:real^3->real^3`] THEN STRIP_TAC THEN
  ABBREV_TAC `Phi = \x. vector[norm x pow 2; (g:real^3->real^3) x$3; c dot x]:real^3` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `((g:real^3->real^3) o (Psi:real^3->real^3)) continuous_on U`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Phi:real^3->real^3) t0 IN U /\
                ((g:real^3->real^3) o (Psi:real^3->real^3)) (Phi t0) = x /\
                (Phi t0)$1 = &1 /\ (Phi t0)$2 = a`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[];
      EXPAND_TAC "Phi" THEN REWRITE_TAC[VECTOR_3] THEN
      UNDISCH_TAC `(t0:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      EXPAND_TAC "Phi" THEN ASM_REWRITE_TAC[VECTOR_3]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(g:real^3->real^3) o (Psi:real^3->real^3)`; `U:real^3->bool`;
                 `O:real^3->bool`] CONTINUOUS_OPEN_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `(Phi:real^3->real^3) t0`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball((Phi:real^3->real^3) t0,e) SUBSET U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE ((g:real^3->real^3) o (Psi:real^3->real^3))
                {z | z IN ball((Phi:real^3->real^3) t0,e) /\ z$1 = &1 /\ z$2 = a}` THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `c:real^3`;
                 `Td:real^3->bool`; `U:real^3->bool`; `Psi:real^3->real^3`;
                 `ball((Phi:real^3->real^3) t0,e)`] SCH4_LEVEL_IN_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "eq") THEN
  REPEAT CONJ_TAC THENL
   [REMOVE_THEN "eq" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    REWRITE_TAC[IMAGE_o] THEN
    MATCH_MP_TAC SCH4_DIFFEO_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`annulus (&1 / &2) (&2):real^3->bool`;
                          `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                          `g':real^3->real^3`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[sch_neck]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SCH4_DIFFEO_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `Td:real^3->bool`;
                            `Phi:real^3->real^3`] THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN
      MATCH_MP_TAC DIFFEOMORPHISM_ON_SYM THEN ASM_MESON_TAC[];
      ASM SET_TAC[]];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONVEX_CONNECTED THEN
      SUBGOAL_THEN `{z | z IN ball((Phi:real^3->real^3) t0,e) /\ z$1 = &1 /\ z$2 = a} =
                    ball(Phi t0,e) INTER {z:real^3 | z$1 = &1} INTER
                    {z:real^3 | z$2 = a}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
      REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[CONVEX_BALL; CONVEX_STANDARD_HYPERPLANE]];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(Phi:real^3->real^3) t0` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; IN_ELIM_THM];
    REMOVE_THEN "eq" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE `(t:real^3->bool) SUBSET o' ==> l INTER t SUBSET l INTER o'`) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[]]);;

(* The statement SCH_LEVEL_FINITE_STATEMENT.                                 *)

let SCH_LEVEL_FINITE = prove
 (`SCH_LEVEL_FINITE_STATEMENT`,
  REWRITE_TAC[SCH_LEVEL_FINITE_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_COMPONENTS THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SCH4_LEVEL_COMPACT];
    MATCH_MP_TAC SCH4_LEVEL_LOCALLY_CONNECTED THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The companion chart at a critical point (used by                         *)
(* pc_sch_generic): at a critical parameter t the map                        *)
(*   x |-> ((g x)$1, (g x)$2, |x|^2)                                         *)
(* is a local diffeomorphism, so near g t the sphere is a graph over the     *)
(* horizontal coordinates.                                                   *)
(* ------------------------------------------------------------------------- *)

(* The derivative of a diffeomorphism is inverted by the derivative of its   *)
(* inverse (the proof of ODE_DIFFEO_DERIVATIVE_INVERSE in pc_ode_vf.ml,      *)
(* repeated here because this file does not load that one).                  *)

let SCH4_DIFFEO_DERIV_INV = prove
 (`!U V (psi:real^M->real^N) phi x k.
        diffeomorphism_on U V psi phi /\ x IN U
        ==> frechet_derivative phi (at (psi x)) (frechet_derivative psi (at x) k) = k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(psi:real^M->real^N) x IN V` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^M->bool`; `psi:real^M->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `phi:real^N->real^M`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(psi:real^M->real^N) x`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`psi:real^M->real^N`; `phi:real^N->real^M`;
                 `frechet_derivative (psi:real^M->real^N) (at x)`;
                 `frechet_derivative (phi:real^N->real^M) (at ((psi:real^M->real^N) x))`;
                 `x:real^M`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((phi:real^N->real^M) o (psi:real^M->real^N) has_derivative (\h. h)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`\y:real^M. y`; `U:real^M->bool`] THEN
    ASM_SIMP_TAC[o_THM; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(phi:real^N->real^M) o (psi:real^M->real^N)`;
                 `frechet_derivative (phi:real^N->real^M) (at ((psi:real^M->real^N) x)) o
                  frechet_derivative psi (at x)`;
                 `\h:real^M. h`; `x:real^M`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `k:real^M`) THEN
  REWRITE_TAC[o_THM]);;

(* The derivative and smoothness of the critical chart map.                  *)

let SCH4_CMAP_DERIV = prove
 (`!(g:real^3->real^3) g' s.
        (g has_derivative g') (at s)
        ==> ((\x. vector[(g x)$1; (g x)$2; norm x pow 2]:real^3) has_derivative
             (\h. vector[(g' h)$1; (g' h)$2; &2 * (s dot h)])) (at s)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [HAS_DERIVATIVE_COMPONENTWISE_AT] THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_3] THENL
   [SUBGOAL_THEN `!y:real^3. y$1 = basis 1 dot y`
     (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LIFT_DOT THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `!y:real^3. y$2 = basis 2 dot y`
     (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LIFT_DOT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_CMUL; HAS_DERIVATIVE_SQNORM_AT]]);;

let SCH4_CMAP_SMOOTH = prove
 (`!(g:real^3->real^3) s.
        open s /\ smooth_map_on s g
        ==> smooth_map_on s (\x. vector[(g x)$1; (g x)$2; norm x pow 2]:real^3)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE th]) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_3] THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`s:real^3->bool`; `\x:real^3. x`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]]);;

(* The chart at a critical point.                                            *)

let SCH4_CRITICAL_CHART = prove
 (`!g g':real^3->real^3 t.
        sch_neck g g' /\ sch_crit g t
        ==> ?Td U Psi.
              open Td /\ t IN Td /\ Td SUBSET annulus (&1 / &2) (&2) /\ open U /\
              diffeomorphism_on Td U
                (\x. vector[(g x)$1; (g x)$2; norm x pow 2]:real^3) Psi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [sch_crit]) THEN
  SUBGOAL_THEN `(t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `((g:real^3->real^3) has_derivative frechet_derivative g (at t)) (at t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (g:real^3->real^3) (at t))` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:real^3. frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) t))
                             (frechet_derivative g (at t) k) = k`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SCH4_DIFFEO_DERIV_INV THEN
    MAP_EVERY EXISTS_TAC [`annulus (&1 / &2) (&2):real^3->bool`;
                          `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`] THEN
    ASM_MESON_TAC[sch_neck];
    ALL_TAC] THEN
  ABBREV_TAC `L = frechet_derivative (g:real^3->real^3) (at t)` THEN
  MP_TAC(ISPECL [`\x. vector[(g:real^3->real^3) x$1; g x$2; norm x pow 2]:real^3`;
                 `annulus (&1 / &2) (&2):real^3->bool`; `t:real^3`]
         SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SCH4_CMAP_SMOOTH] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `L:real^3->real^3`; `t:real^3`]
      SCH4_CMAP_DERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET; NOT_EXISTS_THM] THEN
    X_GEN_TAC `h:real^3` THEN
    SUBGOAL_THEN `linear(\h. vector[((L:real^3->real^3) h)$1; (L h)$2;
                                    &2 * ((t:real^3) dot h)]:real^3)`
    ASSUME_TAC THENL [ASM_MESON_TAC[SCH4_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN
    REWRITE_TAC[TAUT `~(~p /\ q) <=> q ==> p`] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                                      VEC_COMPONENT]) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `((L:real^3->real^3) h)$3 = &0` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[orthogonal] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(L:real^3->real^3) h = vec 0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `linear(frechet_derivative (g':real^3->real^3)
                           (at ((g:real^3->real^3) t)))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(ACCEPT_TAC o MATCH_MP LINEAR_0)];
    MESON_TAC[]]);;

(* In the critical chart the sphere is a graph over the horizontal           *)
(* coordinates: points of g(sphere) in g(Psi B) are the g(Psi z) with z in B *)
(* and z$3 = 1, and g(Psi z) has horizontal coordinates z$1, z$2.            *)

let SCH4_GRAPH_IN_CHART = prove
 (`!g g':real^3->real^3 Td U Psi B.
        sch_neck g g' /\ Td SUBSET annulus (&1 / &2) (&2) /\
        diffeomorphism_on Td U
          (\x. vector[(g x)$1; (g x)$2; norm x pow 2]:real^3) Psi /\
        B SUBSET U
        ==> IMAGE g (sphere(vec 0,&1)) INTER IMAGE (g o Psi) B =
            IMAGE (g o Psi) {z | z IN B /\ z$3 = &1} /\
            (!z. z IN U ==> Psi z IN Td /\
                            (g(Psi z))$1 = z$1 /\ (g(Psi z))$2 = z$2 /\
                            norm(Psi z) pow 2 = z$3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  SUBGOAL_THEN
   `!z:real^3. z IN U
               ==> (Psi:real^3->real^3) z IN Td /\
                   ((g:real^3->real^3)(Psi z))$1 = z$1 /\ (g(Psi z))$2 = z$2 /\
                   norm(Psi z) pow 2 = z$3`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `diffeomorphism_on Td U
          (\x. vector[(g:real^3->real^3) x$1; g x$2; norm x pow 2]:real^3) Psi` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(vector[(g:real^3->real^3)((Psi:real^3->real^3) z)$1;
                          g(Psi z)$2; norm(Psi z) pow 2]:real^3) = z` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(AP_TERM `\v:real^3. v$1` th) THEN
                         MP_TAC(AP_TERM `\v:real^3. v$2` th) THEN
                         MP_TAC(AP_TERM `\v:real^3. v$3` th)) THEN
    REWRITE_TAC[VECTOR_3] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; o_THM; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^3) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Psi:real^3->real^3) z = s` ASSUME_TAC THENL
     [SUBGOAL_THEN `(Psi:real^3->real^3) z IN annulus (&1 / &2) (&2) /\
                    (s:real^3) IN annulus (&1 / &2) (&2)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET];
        ALL_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(s:real^3) = &1` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `norm((Psi:real^3->real^3) z) pow 2 = (z:real^3)$3`)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `(Psi:real^3->real^3) z` THEN ASM_REWRITE_TAC[IN_SPHERE_0] THEN
      MP_TAC(ISPECL [`norm((Psi:real^3->real^3) z)`; `2`] REAL_POW_EQ_1) THEN
      ASM_REWRITE_TAC[REAL_ABS_NORM] THEN ARITH_TAC;
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]]]);;

