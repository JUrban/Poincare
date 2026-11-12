(* ========================================================================= *)
(* pc_sch_generic: Morse position of a collared sphere in R^3, a step of the *)
(* proof of the smooth Schoenflies theorem.                                  *)
(*                                                                           *)
(* Main result: SCH_GENERIC |- SCH_GENERIC_STATEMENT.  Route:                 *)
(*  1. Sard (BABY_SARD) for the cone x |-> |x| nu(x/|x|) over the unit       *)
(*     normal nu of the sphere in collar coordinates gives a direction v     *)
(*     such that every critical point of the height <v,.> is nondegenerate  *)
(*     in the sense that the cone map has invertible derivative there; a     *)
(*     rotation takes v to basis 3.                                          *)
(*  2. Critical points are then isolated, hence finitely many, and at each   *)
(*     the sphere is a graph z = phi(y) over the horizontal plane with       *)
(*     invertible Hessian (sch3_nondeg).                                     *)
(*  3. One critical point at a time, a compactly supported vertical shear    *)
(*     y |-> y + chi(y) w(y) e3 (a diffeomorphism by SMT_PERTURB_ID) replaces *)
(*     phi by its quadratic Taylor polynomial near the point (plus a small   *)
(*     shift of the critical value), without creating critical points; a    *)
(*     linear change of the horizontal coordinates gives sch_hchart.  No     *)
(*     Morse lemma is used.                                                  *)
(* ========================================================================= *)

needs "src/pc_sch_level.ml";;
needs "src/pc_smt_rn.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Smoothness of lifted real expressions and of vector expressions on open   *)
(* sets (a rule set modelled on that of the Navier_Stokes development,       *)
(* github.com/hol-light-family/Navier_Stokes), and a tactic that decomposes  *)
(* such goals.                                                               *)
(* ------------------------------------------------------------------------- *)

let SCH3_SL_ADD = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x + g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`; `\x:real^M. lift(g x)`]
                SMOOTH_MAP_ON_LIFT_ADD) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCH3_SL_SUB = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x - g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`; `\x:real^M. lift(g x)`]
                SMOOTH_MAP_ON_LIFT_SUB) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCH3_SL_MUL = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x * g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`; `\x:real^M. lift(g x)`]
                SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCH3_SL_NEG = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x))
     ==> smooth_map_on s (\x. lift(--(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`] SMOOTH_MAP_ON_LIFT_NEG) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCH3_SL_POW = prove
 (`!s (f:real^M->real) n.
     open s /\ smooth_map_on s (\x. lift(f x))
     ==> smooth_map_on s (\x. lift(f x pow n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`; `n:num`]
    SMOOTH_MAP_ON_LIFT_POW) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCH3_SL_INV = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x)) /\ (!x. x IN s ==> ~(f x = &0))
     ==> smooth_map_on s (\x. lift(inv(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`] SMOOTH_MAP_ON_LIFT_INV) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let SCH3_SL_DIV = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x)) /\
     (!x. x IN s ==> ~(g x = &0))
     ==> smooth_map_on s (\x. lift(f x / g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`; `\x:real^M. lift(g x)`]
                SMOOTH_MAP_ON_LIFT_DIV) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let SCH3_SL_SQRT = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x)) /\ (!x. x IN s ==> &0 < f x)
     ==> smooth_map_on s (\x. lift(sqrt(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`] SMOOTH_MAP_ON_LIFT_SQRT) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let SCH3_SL_CONST = prove
 (`!s c. smooth_map_on s (\x:real^M. lift c)`,
  REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let SCH3_SL_COMPONENT = prove
 (`!s (f:real^M->real^N) k.
     open s /\ smooth_map_on s f ==> smooth_map_on s (\x. lift(f x$k))`,
  REWRITE_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT]);;

let SCH3_SL_COORD = prove
 (`!s k. open s ==> smooth_map_on s (\x:real^M. lift(x$k))`,
  REWRITE_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE]);;

let SCH3_SL_DOT = prove
 (`!s (f:real^M->real^N) g.
     open s /\ smooth_map_on s f /\ smooth_map_on s g
     ==> smooth_map_on s (\x. lift(f x dot g x))`,
  REWRITE_TAC[SMOOTH_MAP_ON_DOT_OPEN]);;

let SCH3_SL_NORM = prove
 (`!s (f:real^M->real^N).
     open s /\ smooth_map_on s f /\ (!x. x IN s ==> ~(f x = vec 0))
     ==> smooth_map_on s (\x. lift(norm(f x)))`,
  REWRITE_TAC[SMOOTH_MAP_ON_LIFT_NORM]);;

let SCH3_SL_NORM_POW2 = prove
 (`!s (f:real^M->real^N).
     open s /\ smooth_map_on s f ==> smooth_map_on s (\x. lift(norm(f x) pow 2))`,
  REWRITE_TAC[SMOOTH_MAP_ON_NORM_POW2_OPEN]);;

let SCH3_SL_DROP = prove
 (`!s (f:real^M->real^1). smooth_map_on s f ==> smooth_map_on s (\x. lift(drop(f x)))`,
  REWRITE_TAC[LIFT_DROP; ETA_AX]);;

let SCH3_SV_CMUL = prove
 (`!s (a:real^M->real) (f:real^M->real^N).
     open s /\ smooth_map_on s (\x. lift(a x)) /\ smooth_map_on s f
     ==> smooth_map_on s (\x. a x % f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(a x)`; `f:real^M->real^N`]
    SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCH3_SV_ADD = prove
 (`!s (f:real^M->real^N) g.
     open s /\ smooth_map_on s f /\ smooth_map_on s g
     ==> smooth_map_on s (\x. f x + g x)`,
  REWRITE_TAC[SMOOTH_MAP_ON_ADD_OPEN]);;

let SCH3_SV_SUB = prove
 (`!s (f:real^M->real^N) g.
     open s /\ smooth_map_on s f /\ smooth_map_on s g
     ==> smooth_map_on s (\x. f x - g x)`,
  REWRITE_TAC[SMOOTH_MAP_ON_SUB_OPEN]);;

let SCH3_SV_NEG = prove
 (`!s (f:real^M->real^N).
     open s /\ smooth_map_on s f ==> smooth_map_on s (\x. --(f x))`,
  REWRITE_TAC[SMOOTH_MAP_ON_NEG_OPEN]);;

let SCH3_SV_CONST = prove
 (`!s (c:real^N). smooth_map_on s (\x:real^M. c)`,
  REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let SCH3_SV_ID = prove
 (`!s. smooth_map_on s (\x:real^M. x)`,
  REWRITE_TAC[SMOOTH_MAP_ON_ID]);;

let SCH3_SV_VECTOR3 = prove
 (`!s (a:real^M->real) b c.
     open s /\ smooth_map_on s (\x. lift(a x)) /\ smooth_map_on s (\x. lift(b x)) /\
     smooth_map_on s (\x. lift(c x))
     ==> smooth_map_on s (\x. vector[a x; b x; c x]:real^3)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE th]) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_3]);;

let SCH3_SV_VECTOR2 = prove
 (`!s (a:real^M->real) b.
     open s /\ smooth_map_on s (\x. lift(a x)) /\ smooth_map_on s (\x. lift(b x))
     ==> smooth_map_on s (\x. vector[a x; b x]:real^2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE th]) THEN
  REWRITE_TAC[DIMINDEX_2; ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_2]);;

(* Composition with a smooth map on an open set containing the image.       *)

let SCH3_SV_COMPOSE = prove
 (`!s t (f:real^N->real^P) (g:real^M->real^N).
     open s /\ open t /\ smooth_map_on s g /\ smooth_map_on t f /\
     (!x. x IN s ==> g x IN t)
     ==> smooth_map_on s (\x. f(g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `t:real^N->bool`; `g:real^M->real^N`;
                 `f:real^N->real^P`] SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* The decomposition tactic: leaves the atoms (assumptions close them when  *)
(* they are literally present) and the side conditions as goals.            *)

let SCH3_SMOOTH_TAC =
  let rules = [SCH3_SL_NORM_POW2; SCH3_SL_ADD; SCH3_SL_SUB; SCH3_SL_MUL; SCH3_SL_NEG; SCH3_SL_POW;
               SCH3_SL_DIV; SCH3_SL_INV; SCH3_SL_SQRT; SCH3_SL_DOT; SCH3_SL_NORM;
               SCH3_SV_CMUL; SCH3_SV_ADD; SCH3_SV_SUB; SCH3_SV_NEG;
               SCH3_SV_VECTOR3; SCH3_SV_VECTOR2] in
  let leaves = [SCH3_SL_CONST; SCH3_SV_CONST; SCH3_SV_ID; SCH3_SL_COORD;
                SMOOTH_MAP_ON_LIFT_COMPONENT; ETA_AX] in
  let step = FIRST (map MATCH_MP_TAC rules) THEN REPEAT CONJ_TAC in
  REPEAT CONJ_TAC THEN
  REPEAT (FIRST [ASM_SIMP_TAC leaves THEN NO_TAC; ASM_REWRITE_TAC[] THEN NO_TAC;
                 step]);;

(* ------------------------------------------------------------------------- *)
(* The conormal of a neck.  For x in the annulus,                            *)
(* sch3_conormal g x is the vector n with n . (Dg(x) h) = x . h for all h    *)
(* (the normal of the surface g(sphere |x|) at g x, scaled).                 *)
(* ------------------------------------------------------------------------- *)

let sch3_conormal = new_definition
 `sch3_conormal (g:real^3->real^3) (x:real^3) =
    @n:real^3. !h. n dot (frechet_derivative g (at x) h) = x dot h`;;

let SCH3_LAMBDA3 = prove
 (`!f:num->real. (lambda i. f i):real^3 = vector[f 1; f 2; f 3]`,
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; LAMBDA_BETA; ARITH]);;

let SCH3_LINEAR_ROWS_DOT = prove
 (`!L:real^3->real^3 x v.
        linear L ==> (lambda i. L(basis i) dot x):real^3 dot v = x dot L v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v:real^3 = v$1 % basis 1 + v$2 % basis 2 + v$3 % basis 3`
  SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; DOT_RADD; DOT_RMUL; SCH3_LAMBDA3] THEN
  SIMP_TAC[DOT_3; VECTOR_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

(* Existence, the formula through g', and uniqueness.                        *)

let SCH3_CONORMAL = prove
 (`!g g':real^3->real^3 x.
        sch_neck g g' /\ x IN annulus (&1 / &2) (&2)
        ==> sch3_conormal g x =
              (lambda i. frechet_derivative g' (at (g x)) (basis i) dot x) /\
            (!h. sch3_conormal g x dot frechet_derivative g (at x) h = x dot h) /\
            (!n. (!h. n dot frechet_derivative g (at x) h = x dot h)
                 ==> n = sch3_conormal g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  SUBGOAL_THEN `(g:real^3->real^3) x IN IMAGE g (annulus (&1 / &2) (&2))`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^3. frechet_derivative g' (at ((g:real^3->real^3) x))
                 (frechet_derivative g (at x) h) = h`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SCH4_DIFFEO_DERIV_INV THEN
    MAP_EVERY EXISTS_TAC [`annulus (&1 / &2) (&2):real^3->bool`;
                          `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`] THEN
    ASM_MESON_TAC[sch_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k:real^3. frechet_derivative g (at x)
                 (frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) x)) k) = k`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                   `annulus (&1 / &2) (&2):real^3->bool`;
                   `g':real^3->real^3`; `g:real^3->real^3`;
                   `(g:real^3->real^3) x`; `k:real^3`] SCH4_DIFFEO_DERIV_INV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFFEOMORPHISM_ON_SYM THEN
      ASM_MESON_TAC[sch_neck];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) x)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `n0 = (lambda i. frechet_derivative (g':real^3->real^3)
                                 (at ((g:real^3->real^3) x)) (basis i) dot x):real^3` THEN
  SUBGOAL_THEN `!v:real^3. n0 dot v = x dot frechet_derivative (g':real^3->real^3)
                                        (at ((g:real^3->real^3) x)) v`
  ASSUME_TAC THENL
   [EXPAND_TAC "n0" THEN GEN_TAC THEN MATCH_MP_TAC SCH3_LINEAR_ROWS_DOT THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h:real^3. n0 dot frechet_derivative (g:real^3->real^3) (at x) h = x dot h`
  (LABEL_TAC "ex") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n:real^3. (!h. n dot frechet_derivative (g:real^3->real^3) (at x) h = x dot h)
               ==> n = n0`
  (LABEL_TAC "uniq") THENL
   [X_GEN_TAC `n:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM VECTOR_EQ_RDOT] THEN X_GEN_TAC `k:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) x)) k`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch3_conormal (g:real^3->real^3) x = n0` ASSUME_TAC THENL
   [REWRITE_TAC[sch3_conormal] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC `y:real^3` THEN BETA_TAC THEN EQ_TAC THENL
     [USE_THEN "uniq" (MATCH_ACCEPT_TAC o SPEC `y:real^3`);
      DISCH_THEN SUBST1_TAC THEN USE_THEN "ex" ACCEPT_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* The conormal is not zero.                                                 *)

let SCH3_CONORMAL_NZ = prove
 (`!g g':real^3->real^3 x.
        sch_neck g g' /\ x IN annulus (&1 / &2) (&2)
        ==> ~(sch3_conormal g x = vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `x:real^3`] SCH3_CONORMAL) THEN
  ASM_REWRITE_TAC[DOT_LZERO] THEN
  DISCH_THEN(MP_TAC o SYM o SPEC `x:real^3` o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[DOT_EQ_0] THEN DISCH_TAC THEN
  UNDISCH_TAC `(x:real^3) IN annulus (&1 / &2) (&2)` THEN
  ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_0] THEN REAL_ARITH_TAC);;

(* Smoothness on the annulus.                                                *)

let SCH3_CONORMAL_SMOOTH = prove
 (`!g g':real^3->real^3.
        sch_neck g g'
        ==> smooth_map_on (annulus (&1 / &2) (&2)) (sch3_conormal g)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\x:real^3. vector[frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) x)) (basis 1) dot x;
                                frechet_derivative g' (at (g x)) (basis 2) dot x;
                                frechet_derivative g' (at (g x)) (basis 3) dot x]:real^3` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `x:real^3`] SCH3_CONORMAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[SCH3_LAMBDA3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. smooth_map_on (annulus (&1 / &2) (&2))
          (\x. frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) x)) (basis k))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`annulus (&1 / &2) (&2):real^3->bool`;
                   `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                   `\y. frechet_derivative (g':real^3->real^3) (at y) (basis k)`;
                   `g:real^3->real^3`] SCH3_SV_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SCH3_SMOOTH_TAC);;

(* Behaviour under an orthogonal transformation of the target.               *)

let SCH3_NECK_ORTHO = prove
 (`!f f':real^3->real^3 Q.
        sch_neck f f' /\ orthogonal_transformation Q
        ==> ?Q'. orthogonal_transformation Q' /\ (!x. Q'(Q x) = x) /\ (!y. Q(Q' y) = y) /\
                 diffeomorphism_on (:real^3) (:real^3) Q Q' /\
                 sch_neck (Q o f) (f' o Q')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Q':real^3->real^3` STRIP_ASSUME_TAC o
    MATCH_MP SMT_ORTHOGONAL_DIFFEO) THEN
  EXISTS_TAC `Q':real^3->real^3` THEN ASM_REWRITE_TAC[sch_neck] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
  EXISTS_TAC `IMAGE (f:real^3->real^3) (annulus (&1 / &2) (&2))` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[sch_neck]; ALL_TAC] THEN
  MATCH_MP_TAC SCH4_DIFFEO_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`] THEN
  ASM_REWRITE_TAC[SUBSET_UNIV]);;

let SCH3_FRECHET_ORTHO = prove
 (`!f:real^3->real^3 Q x.
        f differentiable at x /\ orthogonal_transformation Q
        ==> frechet_derivative (Q o f) (at x) = Q o frechet_derivative f (at x)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN MATCH_MP_TAC DIFF_CHAIN_AT THEN
  ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR]);;

let SCH3_CONORMAL_ORTHO = prove
 (`!f f':real^3->real^3 Q x.
        sch_neck f f' /\ orthogonal_transformation Q /\ x IN annulus (&1 / &2) (&2)
        ==> sch3_conormal (Q o f) x = Q(sch3_conormal f x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `Q:real^3->real^3`]
    SCH3_NECK_ORTHO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q':real^3->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(Q:real^3->real^3) o (f:real^3->real^3)`;
                 `(f':real^3->real^3) o (Q':real^3->real^3)`; `x:real^3`] SCH3_CONORMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> CONV_TAC SYM_CONV THEN MATCH_MP_TAC(last(CONJUNCTS th))) THEN
  X_GEN_TAC `h:real^3` THEN
  SUBGOAL_THEN `(f:real^3->real^3) differentiable at x` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SCH3_FRECHET_ORTHO; o_THM] THEN
  UNDISCH_TAC `orthogonal_transformation (Q:real^3->real^3)` THEN
  REWRITE_TAC[orthogonal_transformation] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `x:real^3`] SCH3_CONORMAL) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Critical points through the conormal, and through a local                 *)
(* graph parametrization of the sphere.                                      *)
(* ------------------------------------------------------------------------- *)

(* The gradient of a real function on the plane.                             *)

let sch3_grad = new_definition
 `sch3_grad (psi:real^2->real) (y:real^2) =
    vector[drop(frechet_derivative (\z. lift(psi z)) (at y) (basis 1));
           drop(frechet_derivative (\z. lift(psi z)) (at y) (basis 2))]:real^2`;;

let SCH3_GRAD_EQ_0 = prove
 (`!psi:real^2->real y.
        sch3_grad psi y = vec 0 <=>
        drop(frechet_derivative (\z. lift(psi z)) (at y) (basis 1)) = &0 /\
        drop(frechet_derivative (\z. lift(psi z)) (at y) (basis 2)) = &0`,
  REWRITE_TAC[sch3_grad; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT]);;

(* The two diffeomorphisms of a neck.                                       *)

let SCH3_NECK_DIFFEO = prove
 (`!g g':real^3->real^3.
        sch_neck g g'
        ==> diffeomorphism_on (annulus (&1 / &2) (&2))
                              (IMAGE g (annulus (&1 / &2) (&2))) g g' /\
            diffeomorphism_on (IMAGE g (annulus (&1 / &2) (&2)))
                              (annulus (&1 / &2) (&2)) g' g`,
  REWRITE_TAC[sch_neck] THEN MESON_TAC[DIFFEOMORPHISM_ON_SYM]);;

(* Critical points: the conormal is vertical.                                *)

let SCH3_CRIT_CONORMAL = prove
 (`!g g':real^3->real^3 t.
        sch_neck g g' /\ t IN sphere(vec 0,&1)
        ==> (sch_crit g t <=>
             (sch3_conormal g t)$1 = &0 /\ (sch3_conormal g t)$2 = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  SUBGOAL_THEN `(t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH3_NECK_DIFFEO) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH3_CONORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH3_CONORMAL_NZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `N = sch3_conormal (g:real^3->real^3) t` THEN
  ABBREV_TAC `M = frechet_derivative (g:real^3->real^3) (at t)` THEN
  ABBREV_TAC `L = frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) t))` THEN
  SUBGOAL_THEN `(g:real^3->real^3) t IN IMAGE g (annulus (&1 / &2) (&2))`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:real^3. (M:real^3->real^3) ((L:real^3->real^3) k) = k` ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["M"; "L"] THEN
    MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                   `annulus (&1 / &2) (&2):real^3->bool`;
                   `g':real^3->real^3`; `g:real^3->real^3`;
                   `(g:real^3->real^3) t`; `k:real^3`] SCH4_DIFFEO_DERIV_INV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(M:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k:real^3. (N:real^3) dot k = t dot (L:real^3->real^3) k` ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(SPEC `k:real^3` th)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[sch_crit] THEN ASM_REWRITE_TAC[orthogonal] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `~((t:real^3) dot (L:real^3->real^3)(basis 3) = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(L:real^3->real^3)(basis 3)`) THEN
      ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!j. 1 <= j /\ j <= 2 ==> (t:real^3) dot (L:real^3->real^3)(basis j) = &0`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC
       `(t dot (L:real^3->real^3)(basis 3)) % L(basis j) - (t dot L(basis j)) % L(basis 3)`) THEN
      REWRITE_TAC[DOT_RSUB; DOT_RMUL] THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `linear(L:real^3->real^3)` ASSUME_TAC THENL
       [EXPAND_TAC "L" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[LINEAR_SUB; LINEAR_CMUL; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
                   BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
      SUBGOAL_THEN `~(j = 3)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(N:real^3)$1 = N dot basis 1 /\ (N:real^3)$2 = N dot basis 2`
      (fun th -> REWRITE_TAC[th]) THENL
     [SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH];
    STRIP_TAC THEN X_GEN_TAC `h:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:real^3` o check (fun th ->
      is_forall(concl th) && is_eq(snd(strip_forall(concl th))) &&
      can (find_term ((=) `M:real^3->real^3`)) (concl th) &&
      can (find_term ((=) `N:real^3`)) (concl th))) THEN
    REWRITE_TAC[DOT_3; ASSUME `(N:real^3)$1 = &0`; ASSUME `(N:real^3)$2 = &0`;
                ASSUME `(t:real^3) dot h = &0`; REAL_MUL_LZERO; REAL_ADD_LID] THEN
    SUBGOAL_THEN `~((N:real^3)$3 = &0)` MP_TAC THENL
     [UNDISCH_TAC `~(N:real^3 = vec 0)` THEN
      ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN MESON_TAC[]]);;

(* Curves (maps from the plane) into the unit sphere have derivatives        *)
(* orthogonal to the position.                                               *)

let SCH3_SPHERE_MAP_ORTHO = prove
 (`!(sigma:real^2->real^3) s' D y.
        open D /\ y IN D /\ (!z. z IN D ==> sigma z IN sphere(vec 0,&1)) /\
        (sigma has_derivative s') (at y)
        ==> !h. sigma y dot s' h = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\z. lift(norm((sigma:real^2->real^3) z) pow 2)) has_derivative
     ((\x. &2 % lift(sigma y dot x)) o s')) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sigma:real^2->real^3`; `\x:real^3. lift(norm x pow 2)`;
                   `s':real^2->real^3`; `\x:real^3. &2 % lift(sigma (y:real^2) dot x)`;
                   `y:real^2`] DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT; o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. lift(norm((sigma:real^2->real^3) z) pow 2)) has_derivative (\h. vec 0)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`\z:real^2. lift(&1)`; `D:real^2->bool`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN ASM_SIMP_TAC[IN_SPHERE_0] THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. lift(norm((sigma:real^2->real^3) z) pow 2)`;
                 `(\x. &2 % lift(sigma (y:real^2) dot x)) o (s':real^2->real^3)`;
                 `\h:real^2. vec 0:real^1`; `y:real^2`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> X_GEN_TAC `h:real^2` THEN
    MP_TAC(AP_THM th `h:real^2`)) THEN
  REWRITE_TAC[o_THM; VECTOR_MUL_EQ_0; GSYM DROP_EQ_0; LIFT_DROP] THEN REAL_ARITH_TAC);;

(* The derivative of the graph map y |-> (y$1, y$2, psi y).                  *)

let SCH3_HAS_DERIVATIVE_GRAPH = prove
 (`!(psi:real^2->real) y.
        (\z. lift(psi z)) differentiable at y
        ==> ((\z. vector[z$1; z$2; psi z]:real^3) has_derivative
             (\h. vector[h$1; h$2;
                         drop(frechet_derivative (\z. lift(psi z)) (at y) h)]))
            (at y)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [HAS_DERIVATIVE_COMPONENTWISE_AT] THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_3] THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT];
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT];
    ASM_REWRITE_TAC[LIFT_DROP; ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS]]);;

(* If g o sigma is the graph map, the derivative of g on the image of the    *)
(* derivative of sigma is that of the graph map.                             *)

let SCH3_GRAPH_CHAIN = prove
 (`!(g:real^3->real^3) (sigma:real^2->real^3) (psi:real^2->real) D y h.
        open D /\ y IN D /\
        g differentiable at (sigma y) /\ sigma differentiable at y /\
        (\z. lift(psi z)) differentiable at y /\
        (!z. z IN D ==> g(sigma z) = vector[z$1; z$2; psi z])
        ==> frechet_derivative g (at (sigma y)) (frechet_derivative sigma (at y) h) =
            vector[h$1; h$2; drop(frechet_derivative (\z. lift(psi z)) (at y) h)]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sigma:real^2->real^3`; `g:real^3->real^3`;
                 `frechet_derivative (sigma:real^2->real^3) (at y)`;
                 `frechet_derivative (g:real^3->real^3) (at (sigma (y:real^2)))`;
                 `y:real^2`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(((g:real^3->real^3) o (sigma:real^2->real^3)) has_derivative
     (\h. vector[h$1; h$2; drop(frechet_derivative (\z. lift((psi:real^2->real) z)) (at y) h)]))
    (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`\z:real^2. vector[z$1; z$2; (psi:real^2->real) z]:real^3`;
                          `D:real^2->bool`] THEN
    ASM_SIMP_TAC[SCH3_HAS_DERIVATIVE_GRAPH; o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(g:real^3->real^3) o (sigma:real^2->real^3)`;
                 `frechet_derivative (g:real^3->real^3) (at (sigma (y:real^2))) o
                  frechet_derivative sigma (at y)`;
                 `\h. vector[h$1; h$2; drop(frechet_derivative
                        (\z. lift((psi:real^2->real) z)) (at y) h)]:real^3`;
                 `y:real^2`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `h:real^2`) THEN
  REWRITE_TAC[o_THM]);;

(* An algebraic step for the gradient criterion.                            *)

let SCH3_ALG_CRIT = prove
 (`!n1 n2 n3 a b:real.
        ~(n1 = &0 /\ n2 = &0 /\ n3 = &0)
        ==> n1 * &0 + n2 * &1 + n3 * b = &0
        ==> n1 * &1 + n2 * &0 + n3 * a = &0
        ==> (n1 = &0 /\ n2 = &0 <=> a = &0 /\ b = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_LID] THEN
  ASM_CASES_TAC `n3 = &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `n1 = --(n3 * a) /\ n2 = --(n3 * b)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_NEG_EQ_0; REAL_ENTIRE]);;

(* Critical points in a graph parametrization: the gradient vanishes.        *)

let SCH3_CRIT_GRAPH = prove
 (`!g g':real^3->real^3 (sigma:real^2->real^3) (psi:real^2->real) D y.
        sch_neck g g' /\ open D /\ y IN D /\
        smooth_map_on D sigma /\ smooth_map_on D (\z. lift(psi z)) /\
        (!z. z IN D ==> sigma z IN sphere(vec 0,&1) /\
                        g(sigma z) = vector[z$1; z$2; psi z])
        ==> (sch_crit g (sigma y) <=> sch3_grad psi y = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  SUBGOAL_THEN `(sigma:real^2->real^3) y IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(sigma:real^2->real^3) y IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(sigma:real^2->real^3) differentiable at y /\
                (\z. lift((psi:real^2->real) z)) differentiable at y /\
                (g:real^3->real^3) differentiable at (sigma y)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `D:real^2->bool`; EXISTS_TAC `D:real^2->bool`;
      EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `(sigma:real^2->real^3) y`]
    SCH3_CRIT_CONORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SCH3_GRAD_EQ_0] THEN
  SUBGOAL_THEN
   `!h. sch3_conormal (g:real^3->real^3) ((sigma:real^2->real^3) y) dot
        vector[h$1; h$2; drop(frechet_derivative (\z. lift((psi:real^2->real) z)) (at y) h)] =
        &0`
  MP_TAC THENL
   [X_GEN_TAC `h:real^2` THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `sigma:real^2->real^3`; `psi:real^2->real`;
                   `D:real^2->bool`; `y:real^2`; `h:real^2`] SCH3_GRAPH_CHAIN) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`;
                   `(sigma:real^2->real^3) y`] SCH3_CONORMAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
    MP_TAC(ISPECL [`sigma:real^2->real^3`; `frechet_derivative (sigma:real^2->real^3) (at y)`;
                   `D:real^2->bool`; `y:real^2`] SCH3_SPHERE_MAP_ORTHO) THEN
    ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `basis 1:real^2` th) THEN
                       MP_TAC(SPEC `basis 2:real^2` th)) THEN
  SIMP_TAC[DOT_3; VECTOR_3; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`;
                 `(sigma:real^2->real^3) y`] SCH3_CONORMAL_NZ) THEN
  ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
  ABBREV_TAC `N = sch3_conormal (g:real^3->real^3) ((sigma:real^2->real^3) y)` THEN
  ABBREV_TAC `a = drop(frechet_derivative (\z. lift((psi:real^2->real) z)) (at y) (basis 1))` THEN
  ABBREV_TAC `b = drop(frechet_derivative (\z. lift((psi:real^2->real) z)) (at y) (basis 2))` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[SCH3_ALG_CRIT]);;

(* ------------------------------------------------------------------------- *)
(* The unit normal, the cone map over the Gauss map, Sard, and               *)
(* the choice of the height direction.                                       *)
(* ------------------------------------------------------------------------- *)

let sch3_unormal = new_definition
 `sch3_unormal (g:real^3->real^3) (x:real^3) =
    inv(norm(sch3_conormal g x)) % sch3_conormal g x`;;

let sch3_cone = new_definition
 `sch3_cone (g:real^3->real^3) (x:real^3) =
    norm x % sch3_unormal g (inv(norm x) % x)`;;

let SCH3_NORMALIZE_IN_SPHERE = prove
 (`!x:real^N. x IN annulus (&1 / &2) (&2) ==> inv(norm x) % x IN sphere(vec 0,&1)`,
  REWRITE_TAC[annulus; IN_ELIM_THM; IN_SPHERE_0; NORM_MUL; REAL_ABS_INV;
              REAL_ABS_NORM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC);;

let SCH3_UNORMAL_SMOOTH = prove
 (`!g g':real^3->real^3.
        sch_neck g g'
        ==> smooth_map_on (annulus (&1 / &2) (&2)) (sch3_unormal g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sch3_unormal (g:real^3->real^3) =
                \x. inv(norm(sch3_conormal g x)) % sch3_conormal g x` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; sch3_unormal]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH3_CONORMAL_SMOOTH) THEN
  SUBGOAL_THEN `open(annulus (&1 / &2) (&2):real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_ANNULUS]; ALL_TAC] THEN
  SCH3_SMOOTH_TAC THEN
  ASM_SIMP_TAC[ETA_AX; NORM_EQ_0] THEN ASM_MESON_TAC[SCH3_CONORMAL_NZ]);;

let SCH3_CONE_SMOOTH = prove
 (`!g g':real^3->real^3.
        sch_neck g g'
        ==> smooth_map_on (annulus (&1 / &2) (&2)) (sch3_cone g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sch3_cone (g:real^3->real^3) =
                \x. norm x % sch3_unormal g (inv(norm x) % x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; sch3_cone]; ALL_TAC] THEN
  SUBGOAL_THEN `open(annulus (&1 / &2) (&2):real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN annulus (&1 / &2) (&2) ==> ~(x = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `&1 / &2 < norm(x:real^3)` THEN ASM_REWRITE_TAC[NORM_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (annulus (&1 / &2) (&2))
      (\x:real^3. sch3_unormal (g:real^3->real^3) (inv(norm x) % x))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`annulus (&1 / &2) (&2):real^3->bool`;
                   `annulus (&1 / &2) (&2):real^3->bool`;
                   `sch3_unormal (g:real^3->real^3)`;
                   `\x:real^3. inv(norm x) % x`] SCH3_SV_COMPOSE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SCH3_SMOOTH_TAC THEN ASM_SIMP_TAC[NORM_EQ_0];
      ASM_MESON_TAC[SCH3_UNORMAL_SMOOTH];
      ASM_SIMP_TAC[SCH3_NORMALIZE_IN_SPHERE;
                   REWRITE_RULE[SUBSET] SCH4_SPHERE_SUBSET_ANNULUS]];
    ALL_TAC] THEN
  SCH3_SMOOTH_TAC THEN ASM_SIMP_TAC[NORM_EQ_0]);;

(* Sard: a direction y0 such that the cone has invertible derivative at all  *)
(* points mapped to y0 or to -y0.                                             *)

let SCH3_CONE_SARD = prove
 (`!g g':real^3->real^3.
        sch_neck g g'
        ==> ?y0. y0 IN annulus (&1 / &2) (&2) /\
                 !x. x IN annulus (&1 / &2) (&2) /\
                     (sch3_cone g x = y0 \/ sch3_cone g x = --y0)
                     ==> ~(det(matrix(frechet_derivative (sch3_cone g) (at x))) = &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH3_CONE_SMOOTH) THEN
  ABBREV_TAC `B = {x:real^3 | x IN annulus (&1 / &2) (&2) /\
                   det(matrix(frechet_derivative (sch3_cone (g:real^3->real^3)) (at x))) =
                   &0}` THEN
  SUBGOAL_THEN `negligible(IMAGE (sch3_cone (g:real^3->real^3)) B)` ASSUME_TAC THENL
   [MATCH_MP_TAC BABY_SARD THEN
    EXISTS_TAC `\x. frechet_derivative (sch3_cone (g:real^3->real^3)) (at x)` THEN
    REWRITE_TAC[LE_REFL] THEN EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      MP_TAC(ISPECL [`annulus (&1 / &2) (&2):real^3->bool`;
                     `sch3_cone (g:real^3->real^3)`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[OPEN_ANNULUS];
      ASM_REWRITE_TAC[GSYM DET_EQ_0_RANK]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `negligible(IMAGE (sch3_cone (g:real^3->real^3)) B UNION
               IMAGE (--) (IMAGE (sch3_cone g) B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NEGLIGIBLE_LINEAR_IMAGE THEN ASM_REWRITE_TAC[LINEAR_NEGATION];
    ALL_TAC] THEN
  SUBGOAL_THEN `~negligible(annulus (&1 / &2) (&2):real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_NOT_NEGLIGIBLE THEN REWRITE_TAC[OPEN_ANNULUS] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `basis 1:real^3` THEN
    SIMP_TAC[annulus; IN_ELIM_THM; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?y0:real^3. y0 IN annulus (&1 / &2) (&2) /\
                ~(y0 IN IMAGE (sch3_cone (g:real^3->real^3)) B UNION
                        IMAGE (--) (IMAGE (sch3_cone g) B))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~((s:real^3->bool) SUBSET t) ==> ?y. y IN s /\ ~(y IN t)`) THEN
    ASM_MESON_TAC[NEGLIGIBLE_SUBSET];
    ALL_TAC] THEN
  EXISTS_TAC `y0:real^3` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  UNDISCH_TAC `~((y0:real^3) IN IMAGE (sch3_cone (g:real^3->real^3)) B UNION
                        IMAGE (--) (IMAGE (sch3_cone g) B))` THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
  ASM_MESON_TAC[VECTOR_NEG_NEG]);;

(* The cone on a sphere of radius r.                                         *)

let SCH3_CONE_ON_SPHERE = prove
 (`!g:real^3->real^3 t r.
        t IN sphere(vec 0,&1) /\ &0 < r
        ==> sch3_cone g (r % t) = r % sch3_unormal g t`,
  REWRITE_TAC[IN_SPHERE_0] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[sch3_cone] THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_LINV; REAL_LT_IMP_NZ;
               VECTOR_MUL_LID]);;

(* At a critical point the unit normal is vertical.                          *)

let SCH3_UNIT_VERTICAL = prove
 (`!c. ~(c = &0)
       ==> inv(norm(c % (basis 3:real^3))) % (c % (basis 3:real^3)) = basis 3 \/
           inv(norm(c % (basis 3:real^3))) % (c % (basis 3:real^3)) = --(basis 3)`,
  GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID; VECTOR_MUL_ASSOC] THEN
  ASM_CASES_TAC `&0 < c` THENL
   [DISJ1_TAC THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV;
                                 VECTOR_MUL_LID];
    DISJ2_TAC THEN
    SUBGOAL_THEN `abs c = --c` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_NEG; REAL_MUL_LNEG; VECTOR_MUL_LNEG] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID]]);;

let SCH3_UNORMAL_CRIT = prove
 (`!g g':real^3->real^3 t.
        sch_neck g g' /\ sch_crit g t
        ==> sch3_unormal g t = basis 3 \/ sch3_unormal g t = --(basis 3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sch_crit]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH3_CRIT_CONORMAL) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH3_CONORMAL_NZ) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[sch3_unormal] THEN
  SPEC_TAC(`sch3_conormal (g:real^3->real^3) t`,`N:real^3`) THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `N:real^3 = (N$3) % basis 3` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
                 ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SCH3_UNIT_VERTICAL THEN DISCH_TAC THEN
  UNDISCH_TAC `~(N:real^3 = vec 0)` THEN
  ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT]);;

(* Transport of the unit normal, the cone and its derivative under an        *)
(* orthogonal transformation of the target.                                  *)

let SCH3_UNORMAL_ORTHO = prove
 (`!f f':real^3->real^3 Q x.
        sch_neck f f' /\ orthogonal_transformation Q /\ x IN annulus (&1 / &2) (&2)
        ==> sch3_unormal (Q o f) x = Q(sch3_unormal f x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch3_unormal] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `Q:real^3->real^3`; `x:real^3`]
    SCH3_CONORMAL_ORTHO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ORTHOGONAL_TRANSFORMATION]) THEN
  ASM_SIMP_TAC[LINEAR_CMUL]);;

let SCH3_CONE_ORTHO = prove
 (`!f f':real^3->real^3 Q x.
        sch_neck f f' /\ orthogonal_transformation Q /\ x IN annulus (&1 / &2) (&2)
        ==> sch3_cone (Q o f) x = Q(sch3_cone f x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch3_cone] THEN
  SUBGOAL_THEN `inv(norm x) % (x:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH3_NORMALIZE_IN_SPHERE; SCH4_SPHERE_SUBSET_ANNULUS; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `Q:real^3->real^3`;
                 `inv(norm x) % (x:real^3)`] SCH3_UNORMAL_ORTHO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ORTHOGONAL_TRANSFORMATION]) THEN
  ASM_SIMP_TAC[LINEAR_CMUL]);;

let SCH3_CONE_DERIV_ORTHO = prove
 (`!f f':real^3->real^3 Q x.
        sch_neck f f' /\ orthogonal_transformation Q /\ x IN annulus (&1 / &2) (&2)
        ==> frechet_derivative (sch3_cone (Q o f)) (at x) =
            Q o frechet_derivative (sch3_cone f) (at x)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC [`(Q:real^3->real^3) o sch3_cone (f:real^3->real^3)`;
                        `annulus (&1 / &2) (&2):real^3->bool`] THEN
  REWRITE_TAC[OPEN_ANNULUS; o_THM] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SCH3_CONE_ORTHO THEN EXISTS_TAC `f':real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS] THEN ASM_MESON_TAC[SCH3_CONE_SMOOTH];
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR]]);;

let SCH3_DET_ORTHO_COMPOSE = prove
 (`!Q L:real^3->real^3.
        orthogonal_transformation Q /\ linear L
        ==> (det(matrix(Q o L)) = &0 <=> det(matrix L) = &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; DET_MUL; REAL_ENTIRE] THEN
  SUBGOAL_THEN `~(det(matrix(Q:real^3->real^3)) = &0)` (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPEC `matrix(Q:real^3->real^3)` DET_ORTHOGONAL_MATRIX) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX]; REAL_ARITH_TAC]);;

(* The direction of the height: after a rotation every critical point has a  *)
(* cone point with invertible derivative.                                    *)

let SCH3_GOOD_ROTATION = prove
 (`!f f':real^3->real^3.
        sch_neck f f'
        ==> ?Q Q' r. orthogonal_transformation Q /\ (!x. Q'(Q x) = x) /\
                     (!y. Q(Q' y) = y) /\ diffeomorphism_on (:real^3) (:real^3) Q Q' /\
                     sch_neck (Q o f) (f' o Q') /\ &1 / &2 < r /\ r < &2 /\
                     !t. sch_crit (Q o f) t
                         ==> ~(det(matrix(frechet_derivative (sch3_cone (Q o f))
                                                             (at (r % t)))) = &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC o MATCH_MP SCH3_CONE_SARD) THEN
  ABBREV_TAC `r = norm(y0:real^3)` THEN
  SUBGOAL_THEN `&1 / &2 < r /\ r < &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:real^3) IN annulus (&1 / &2) (&2)` THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`inv(r) % y0:real^3`; `basis 3:real^3`]
    ORTHOGONAL_TRANSFORMATION_EXISTS_1) THEN
  ANTS_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:real^3->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `Q:real^3->real^3`]
    SCH3_NECK_ORTHO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q':real^3->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`Q:real^3->real^3`; `Q':real^3->real^3`; `r:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[sch_crit]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `r % (t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `Q:real^3->real^3`;
                 `r % t:real^3`] SCH3_CONE_DERIV_ORTHO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (sch3_cone (f:real^3->real^3)) (at (r % t)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS] THEN ASM_MESON_TAC[SCH3_CONE_SMOOTH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SCH3_DET_ORTHO_COMPOSE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SCH3_CONE_ON_SPHERE] THEN
  MP_TAC(ISPECL [`(Q:real^3->real^3) o (f:real^3->real^3)`;
                 `(f':real^3->real^3) o (Q':real^3->real^3)`; `t:real^3`]
    SCH3_UNORMAL_CRIT) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `Q:real^3->real^3`;
                 `t:real^3`] SCH3_UNORMAL_ORTHO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `basis 3 = (Q:real^3->real^3)(inv r % y0)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `--((Q:real^3->real^3)(inv r % y0)) = Q(--(inv r % y0))` SUBST1_TAC THENL
   [ASM_MESON_TAC[LINEAR_NEG; ORTHOGONAL_TRANSFORMATION_LINEAR]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b:real^3. (Q:real^3->real^3) a = Q b <=> a = b`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_RNEG] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Critical points are closed, isolated (when the cone has                  *)
(* invertible derivative), hence finite.                                    *)
(* ------------------------------------------------------------------------- *)

let SCH3_CRIT_IN_SPHERE = prove
 (`!g t. sch_crit g t ==> t IN sphere(vec 0,&1)`,
  SIMP_TAC[sch_crit]);;

let SCH3_CRIT_CLOSED = prove
 (`!g g':real^3->real^3. sch_neck g g' ==> closed {t | sch_crit g t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{t | sch_crit (g:real^3->real^3) t} =
    {t | t IN sphere(vec 0,&1) /\
         sch3_conormal g t IN {y:real^3 | y$1 = &0} INTER {y:real^3 | y$2 = &0}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `t:real^3` THEN
    ASM_CASES_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN
    ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`]
        SCH3_CRIT_CONORMAL) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[sch_crit] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
  SIMP_TAC[CLOSED_SPHERE; CLOSED_INTER; CLOSED_STANDARD_HYPERPLANE] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
  REWRITE_TAC[SCH4_SPHERE_SUBSET_ANNULUS] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC SCH3_CONORMAL_SMOOTH THEN EXISTS_TAC `g':real^3->real^3` THEN
  ASM_REWRITE_TAC[]);;

let SCH3_CRIT_FINITE = prove
 (`!g g':real^3->real^3.
        sch_neck g g' /\
        (!t. sch_crit g t
             ==> ?e. &0 < e /\ !s. sch_crit g s /\ norm(s - t) < e ==> s = t)
        ==> FINITE {t | sch_crit g t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact {t | sch_crit (g:real^3->real^3) t}` MP_TAC THENL
   [MATCH_MP_TAC BOUNDED_CLOSED_IMP_COMPACT THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SCH3_CRIT_CLOSED]] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
    REWRITE_TAC[BOUNDED_SPHERE; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[SCH3_CRIT_IN_SPHERE];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{t | sch_crit (g:real^3->real^3) t}` o
    GEN_REWRITE_RULE I [COMPACT_EQ_BOLZANO_WEIERSTRASS]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[INFINITE; SUBSET_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` MP_TAC) THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^3) limit_point_of {t | sch_crit (g:real^3->real^3) t}` THEN
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[GSYM dist] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]);;

let SCH3_E3_FAR = prove
 (`~(dist(basis 3:real^3,--(basis 3)) < &1) /\
   ~(dist(--(basis 3):real^3,basis 3) < &1)`,
  REWRITE_TAC[dist; VECTOR_ARITH `(b:real^3) - --b = &2 % b`;
              VECTOR_ARITH `--(b:real^3) - b = --(&2 % b)`; NORM_NEG; NORM_MUL] THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

(* Isolation of a critical point at which the cone has invertible           *)
(* derivative (inverse function theorem for the cone).                      *)

let SCH3_CRIT_ISOLATED = prove
 (`!g g':real^3->real^3 t r.
        sch_neck g g' /\ sch_crit g t /\ &1 / &2 < r /\ r < &2 /\
        ~(det(matrix(frechet_derivative (sch3_cone g) (at (r % t)))) = &0)
        ==> ?e. &0 < e /\ !s. sch_crit g s /\ norm(s - t) < e ==> s = t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH3_CRIT_IN_SPHERE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3. s IN sphere(vec 0,&1) ==> r % s IN annulus (&1 / &2) (&2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sch3_cone (g:real^3->real^3)`; `annulus (&1 / &2) (&2):real^3->bool`;
                 `r % t:real^3`] SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_SIMP_TAC[OPEN_ANNULUS] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[SCH3_CONE_SMOOTH]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`Td:real^3->bool`; `U:real^3->bool`; `G:real^3->real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `Td:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `r % t:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(sch3_unormal (g:real^3->real^3)) continuous (at t)` MP_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCH3_UNORMAL_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_ANNULUS] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `&1`) THEN
  REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (d1 / r) d2` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV] THEN
  X_GEN_TAC `s:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH3_CRIT_IN_SPHERE]; ALL_TAC] THEN
  SUBGOAL_THEN `r % (s:real^3) IN Td` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; dist; GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    UNDISCH_TAC `norm(s - t:real^3) < d1 / r` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(sch3_unormal (g:real^3->real^3) s,sch3_unormal g t) < &1`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `d2:real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[dist];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch3_unormal (g:real^3->real^3) s = sch3_unormal g t` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `s:real^3`] SCH3_UNORMAL_CRIT) THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH3_UNORMAL_CRIT) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dist(sch3_unormal (g:real^3->real^3) s,sch3_unormal g t) < &1` THEN
    SPEC_TAC(`sch3_unormal (g:real^3->real^3) s`,`a:real^3`) THEN
    SPEC_TAC(`sch3_unormal (g:real^3->real^3) t`,`b:real^3`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
    ASM_MESON_TAC[SCH3_E3_FAR];
    ALL_TAC] THEN
  SUBGOAL_THEN `r % (s:real^3) = r % t` MP_TAC THENL
   [SUBGOAL_THEN `(G:real^3->real^3)(sch3_cone (g:real^3->real^3) (r % s)) = r % s /\
                  G(sch3_cone g (r % t)) = r % t`
      (CONJUNCTS_THEN (SUBST1_TAC o SYM)) THENL
     [UNDISCH_TAC `diffeomorphism_on Td U (sch3_cone (g:real^3->real^3)) G` THEN
      REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      AP_TERM_TAC THEN ASM_SIMP_TAC[SCH3_CONE_ON_SPHERE]];
    ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ]]);;

(* ------------------------------------------------------------------------- *)
(* Graph representations at critical points and their                       *)
(* nondegeneracy (invertible Hessian) from the cone condition.              *)
(* ------------------------------------------------------------------------- *)

(* A local graph representation of the sphere g(S^2) at the critical         *)
(* parameter t over the horizontal coordinates: on the open set D of the      *)
(* plane, sigma parametrizes the unit sphere near t and g(sigma y) is the     *)
(* graph point (y, phi y); near g t every point of g(S^2) is of this form.   *)

let sch3_graph = new_definition
 `sch3_graph (g:real^3->real^3) (t:real^3) (D:real^2->bool) (phi:real^2->real)
             (sigma:real^2->real^3) <=>
    open D /\ vector[(g t)$1; (g t)$2] IN D /\
    smooth_map_on D (\y. lift(phi y)) /\ smooth_map_on D sigma /\
    sigma(vector[(g t)$1; (g t)$2]) = t /\
    (!y. y IN D ==> sigma y IN sphere(vec 0,&1) /\
                    g(sigma y) = vector[y$1; y$2; phi y]) /\
    ?W. open W /\ g t IN W /\
        !s. s IN sphere(vec 0,&1) /\ g s IN W
            ==> vector[(g s)$1; (g s)$2] IN D /\
                s = sigma(vector[(g s)$1; (g s)$2])`;;

(* Nondegenerate critical point: some graph representation has invertible   *)
(* Hessian at the point.                                                     *)

let sch3_nondeg = new_definition
 `sch3_nondeg (g:real^3->real^3) (t:real^3) <=>
    ?D phi sigma. sch3_graph g t D phi sigma /\
                  ~(det(matrix(frechet_derivative (sch3_grad phi)
                                  (at (vector[(g t)$1; (g t)$2])))) = &0)`;;

(* The conormal annihilates the tangent vectors of the graph.                *)

let SCH3_CONORMAL_GRAPH = prove
 (`!g g':real^3->real^3 (sigma:real^2->real^3) (psi:real^2->real) D y.
        sch_neck g g' /\ open D /\ y IN D /\
        smooth_map_on D sigma /\ smooth_map_on D (\z. lift(psi z)) /\
        (!z. z IN D ==> sigma z IN sphere(vec 0,&1) /\
                        g(sigma z) = vector[z$1; z$2; psi z])
        ==> !h. sch3_conormal g (sigma y) dot
                vector[h$1; h$2; drop(frechet_derivative (\z. lift(psi z)) (at y) h)] =
                &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  SUBGOAL_THEN `(sigma:real^2->real^3) y IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(sigma:real^2->real^3) y IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(sigma:real^2->real^3) differentiable at y /\
                (\z. lift((psi:real^2->real) z)) differentiable at y /\
                (g:real^3->real^3) differentiable at (sigma y)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `D:real^2->bool`; EXISTS_TAC `D:real^2->bool`;
      EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `h:real^2` THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `sigma:real^2->real^3`; `psi:real^2->real`;
                 `D:real^2->bool`; `y:real^2`; `h:real^2`] SCH3_GRAPH_CHAIN) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`;
                 `(sigma:real^2->real^3) y`] SCH3_CONORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
  MP_TAC(ISPECL [`sigma:real^2->real^3`; `frechet_derivative (sigma:real^2->real^3) (at y)`;
                 `D:real^2->bool`; `y:real^2`] SCH3_SPHERE_MAP_ORTHO) THEN
  ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

(* The unit normal along the graph: m$j + m$3 * phi_j = 0 (j = 1, 2).        *)

let SCH3_UNORMAL_GRAPH = prove
 (`!g g':real^3->real^3 (sigma:real^2->real^3) (psi:real^2->real) D y.
        sch_neck g g' /\ open D /\ y IN D /\
        smooth_map_on D sigma /\ smooth_map_on D (\z. lift(psi z)) /\
        (!z. z IN D ==> sigma z IN sphere(vec 0,&1) /\
                        g(sigma z) = vector[z$1; z$2; psi z])
        ==> vector[(sch3_unormal g (sigma y))$1; (sch3_unormal g (sigma y))$2] +
            (sch3_unormal g (sigma y))$3 % sch3_grad psi y = vec 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCH3_CONORMAL_GRAPH) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `basis 1:real^2` th) THEN
                       MP_TAC(SPEC `basis 2:real^2` th)) THEN
  SIMP_TAC[DOT_3; VECTOR_3; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[sch3_unormal; sch3_grad; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           VECTOR_2; VEC_COMPONENT] THEN
  CONV_TAC REAL_RING);;

(* The gradient of a smooth function is smooth.                              *)

let SCH3_GRAD_SMOOTH = prove
 (`!(phi:real^2->real) D.
        open D /\ smooth_map_on D (\y. lift(phi y))
        ==> smooth_map_on D (sch3_grad phi)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sch3_grad (phi:real^2->real) =
                \y. vector[drop(frechet_derivative (\z. lift(phi z)) (at y) (basis 1));
                           drop(frechet_derivative (\z. lift(phi z)) (at y) (basis 2))]`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; sch3_grad]; ALL_TAC] THEN
  MATCH_MP_TAC SCH3_SV_VECTOR2 THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]);;

(* The unit normal is a unit vector.                                         *)

let SCH3_UNORMAL_UNIT = prove
 (`!g g':real^3->real^3 x.
        sch_neck g g' /\ x IN annulus (&1 / &2) (&2)
        ==> sch3_unormal g x IN sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch3_unormal; IN_SPHERE_0; NORM_MUL] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NORM] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[NORM_EQ_0] THEN
  ASM_MESON_TAC[SCH3_CONORMAL_NZ]);;

(* Derivatives of the horizontal part and of the third component.          *)

let SCH3_LINEAR_PROJ12 = prove
 (`linear(\v:real^3. vector[v$1; v$2]:real^2)`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT]);;

let SCH3_HAS_DERIVATIVE_PROJ12 = prove
 (`!(m:real^2->real^3) Dm x.
        (m has_derivative Dm) (at x)
        ==> ((\y. vector[m y$1; m y$2]:real^2) has_derivative
             (\h. vector[Dm h$1; Dm h$2])) (at x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:real^2->real^3`; `\v:real^3. vector[v$1; v$2]:real^2`;
                 `Dm:real^2->real^3`; `\v:real^3. vector[v$1; v$2]:real^2`;
                 `x:real^2`] DIFF_CHAIN_AT) THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; SCH3_LINEAR_PROJ12; o_DEF]);;

let SCH3_HAS_DERIVATIVE_COMP3 = prove
 (`!(m:real^2->real^3) Dm x.
        (m has_derivative Dm) (at x)
        ==> ((lift o (\y. m y$3)) has_derivative (lift o (\h. Dm h$3))) (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_DEF] THEN
  MP_TAC(ISPECL [`m:real^2->real^3`; `\v:real^3. lift(v$3)`;
                 `Dm:real^2->real^3`; `\v:real^3. lift(v$3)`;
                 `x:real^2`] DIFF_CHAIN_AT) THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_LIFT_COMPONENT; o_DEF]);;

(* Nondegeneracy from the cone condition.                                    *)

let SCH3_NONDEG_FROM_CONE = prove
 (`!g g':real^3->real^3 t r D phi sigma.
        sch_neck g g' /\ sch_crit g t /\ &1 / &2 < r /\ r < &2 /\
        ~(det(matrix(frechet_derivative (sch3_cone g) (at (r % t)))) = &0) /\
        sch3_graph g t D phi sigma
        ==> ~(det(matrix(frechet_derivative (sch3_grad phi)
                            (at (vector[(g t)$1; (g t)$2])))) = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch3_graph] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  ABBREV_TAC `x0 = vector[(g:real^3->real^3) t$1; g t$2]:real^2` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH3_CRIT_IN_SPHERE]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN D ==> (sigma:real^2->real^3) y IN annulus (&1 / &2) (&2)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `r % (t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID];
    ALL_TAC] THEN
  (* the unit normal along the graph *)
  ABBREV_TAC `m = \y. sch3_unormal (g:real^3->real^3) ((sigma:real^2->real^3) y)` THEN
  SUBGOAL_THEN `smooth_map_on D (m:real^2->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN MATCH_MP_TAC SCH3_SV_COMPOSE THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SCH3_UNORMAL_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^2->real^3) x0 = basis 3 \/ m x0 = --(basis 3)` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SCH3_UNORMAL_CRIT THEN EXISTS_TAC `g':real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch3_grad (phi:real^2->real) x0 = vec 0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `sigma:real^2->real^3`;
                   `phi:real^2->real`; `D:real^2->bool`; `x0:real^2`] SCH3_CRIT_GRAPH) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* derivatives at x0 *)
  ABBREV_TAC `Dm = frechet_derivative (m:real^2->real^3) (at x0)` THEN
  ABBREV_TAC `H = frechet_derivative (sch3_grad (phi:real^2->real)) (at x0)` THEN
  ABBREV_TAC `Ds = frechet_derivative (sigma:real^2->real^3) (at x0)` THEN
  ABBREV_TAC `Dc = frechet_derivative (sch3_cone (g:real^3->real^3)) (at (r % t))` THEN
  SUBGOAL_THEN `((m:real^2->real^3) has_derivative Dm) (at x0)` ASSUME_TAC THENL
   [EXPAND_TAC "Dm" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sch3_grad (phi:real^2->real) has_derivative H) (at x0)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^2->bool` THEN
    ASM_SIMP_TAC[SCH3_GRAD_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `((sigma:real^2->real^3) has_derivative Ds) (at x0)` ASSUME_TAC THENL
   [EXPAND_TAC "Ds" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sch3_cone (g:real^3->real^3) has_derivative Dc) (at (r % t))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Dc" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SCH3_CONE_SMOOTH];
    ALL_TAC] THEN
  (* (ii): differentiate m12 + m3 grad phi = 0 *)
  SUBGOAL_THEN
   `!h. vector[(Dm:real^2->real^3) h$1; Dm h$2] + ((m:real^2->real^3) x0)$3 % H h = vec 0`
  (LABEL_TAC "ii") THENL
   [SUBGOAL_THEN
     `((\y. vector[(m:real^2->real^3) y$1; m y$2] + (m y)$3 % sch3_grad (phi:real^2->real) y)
       has_derivative
       (\h. vector[(Dm:real^2->real^3) h$1; Dm h$2] +
            ((m x0)$3 % (H:real^2->real^2) h + Dm h$3 % sch3_grad phi x0))) (at x0)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
      ASM_SIMP_TAC[SCH3_HAS_DERIVATIVE_PROJ12] THEN
      MP_TAC(ISPECL [`\y. ((m:real^2->real^3) y)$3`; `\h. ((Dm:real^2->real^3) h)$3`;
                     `sch3_grad (phi:real^2->real)`; `H:real^2->real^2`; `x0:real^2`]
        HAS_DERIVATIVE_MUL_AT) THEN
      ASM_SIMP_TAC[SCH3_HAS_DERIVATIVE_COMP3];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((\y. vector[(m:real^2->real^3) y$1; m y$2] + (m y)$3 % sch3_grad (phi:real^2->real) y)
       has_derivative (\h. vec 0)) (at x0)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      MAP_EVERY EXISTS_TAC [`\y:real^2. vec 0:real^2`; `D:real^2->bool`] THEN
      ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      EXPAND_TAC "m" THEN
      MATCH_MP_TAC SCH3_UNORMAL_GRAPH THEN
      MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `D:real^2->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `h:real^2` THEN
    MP_TAC(ISPECL
     [`\y. vector[(m:real^2->real^3) y$1; m y$2] + (m y)$3 % sch3_grad (phi:real^2->real) y`;
      `\h. vector[(Dm:real^2->real^3) h$1; Dm h$2] +
            (((m:real^2->real^3) x0)$3 % (H:real^2->real^2) h +
             Dm h$3 % sch3_grad (phi:real^2->real) x0)`;
      `\h:real^2. vec 0:real^2`; `x0:real^2`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `h:real^2`) THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  (* (iii): m is a unit vector field *)
  SUBGOAL_THEN `!h. ((m:real^2->real^3) x0) dot (Dm:real^2->real^3) h = &0`
  (LABEL_TAC "iii") THENL
   [MATCH_MP_TAC SCH3_SPHERE_MAP_ORTHO THEN EXISTS_TAC `D:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    EXPAND_TAC "m" THEN MATCH_MP_TAC SCH3_UNORMAL_UNIT THEN
    EXISTS_TAC `g':real^3->real^3` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* (iv): the cone along r sigma *)
  SUBGOAL_THEN `!h. (Dc:real^3->real^3) (r % (Ds:real^2->real^3) h) =
                    r % (Dm:real^2->real^3) h`
  (LABEL_TAC "iv") THENL
   [SUBGOAL_THEN
     `((\y. sch3_cone (g:real^3->real^3) (r % (sigma:real^2->real^3) y)) has_derivative
       ((Dc:real^3->real^3) o (\h. r % (Ds:real^2->real^3) h))) (at x0)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\y. r % (sigma:real^2->real^3) y`; `sch3_cone (g:real^3->real^3)`;
                     `\h. r % (Ds:real^2->real^3) h`; `Dc:real^3->real^3`;
                     `x0:real^2`] DIFF_CHAIN_AT) THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_CMUL; o_DEF];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((\y. sch3_cone (g:real^3->real^3) (r % (sigma:real^2->real^3) y)) has_derivative
       (\h. r % (Dm:real^2->real^3) h)) (at x0)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      MAP_EVERY EXISTS_TAC [`\y. r % (m:real^2->real^3) y`; `D:real^2->bool`] THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_CMUL] THEN
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SCH3_CONE_ON_SPHERE THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `h:real^2` THEN
    MP_TAC(ISPECL
     [`\y. sch3_cone (g:real^3->real^3) (r % (sigma:real^2->real^3) y)`;
      `(Dc:real^3->real^3) o (\h. r % (Ds:real^2->real^3) h)`;
      `\h. r % (Dm:real^2->real^3) h`; `x0:real^2`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `h:real^2`) THEN
    REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  (* conclusion: the Hessian is injective *)
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET; NOT_EXISTS_THM] THEN
  X_GEN_TAC `h:real^2` THEN
  SUBGOAL_THEN `linear(H:real^2->real^2) /\ linear(Dc:real^3->real^3) /\
                linear(Ds:real^2->real^3) /\ linear(Dm:real^2->real^3)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  REWRITE_TAC[TAUT `~(~p /\ q) <=> q ==> p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Dm:real^2->real^3) h = vec 0` ASSUME_TAC THENL
   [REMOVE_THEN "ii" (MP_TAC o SPEC `h:real^2`) THEN
    REMOVE_THEN "iii" (MP_TAC o SPEC `h:real^2`) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_2;
                VEC_COMPONENT] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    SIMP_TAC[DOT_BASIS; DOT_LNEG; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Ds:real^2->real^3) h = vec 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(Dc:real^3->real^3) (r % (Ds:real^2->real^3) h) = vec 0` MP_TAC THENL
     [USE_THEN "iv" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_RZERO];
      ALL_TAC] THEN
    UNDISCH_TAC `~(det(matrix(Dc:real^3->real^3)) = &0)` THEN
    REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `r % (Ds:real^2->real^3) h`) THEN
    ASM_SIMP_TAC[MATRIX_WORKS; VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `sigma:real^2->real^3`; `phi:real^2->real`;
                 `D:real^2->bool`; `x0:real^2`; `h:real^2`] SCH3_GRAPH_CHAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
      ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `D:real^2->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `D:real^2->bool` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linear(frechet_derivative (g:real^3->real^3) (at t))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_3;
              VEC_COMPONENT] THEN
  MESON_TAC[]);;

(* Existence of graph representations at critical points (from the chart of *)
(* SCH4_CRITICAL_CHART).                                                     *)

let SCH3_LIFT12_CONTINUOUS = prove
 (`!c y:real^2. (\y. vector[y$1; y$2; c]:real^3) continuous at y`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\y:real^2. vector[y$1; y$2; c]:real^3`; `(:real^2)`]
    CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  SUBGOAL_THEN `open(:real^2)` ASSUME_TAC THENL [REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  SCH3_SMOOTH_TAC);;

let SCH3_GRAPH_EXISTS = prove
 (`!g g':real^3->real^3 t.
        sch_neck g g' /\ sch_crit g t ==> ?D phi sigma. sch3_graph g t D phi sigma`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  SUBGOAL_THEN `(t:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH3_CRIT_IN_SPHERE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`]
    SCH4_CRITICAL_CHART) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`Td:real^3->bool`; `U:real^3->bool`; `Psi:real^3->real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `Td:real^3->bool`;
                 `U:real^3->bool`; `Psi:real^3->real^3`; `U:real^3->bool`]
    SCH4_GRAPH_IN_CHART) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "img") (LABEL_TAC "comp")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  MAP_EVERY EXISTS_TAC
   [`{y:real^2 | vector[y$1; y$2; &1]:real^3 IN U}`;
    `\y:real^2. ((g:real^3->real^3)((Psi:real^3->real^3)(vector[y$1; y$2; &1])))$3`;
    `\y:real^2. (Psi:real^3->real^3)(vector[y$1; y$2; &1])`] THEN
  REWRITE_TAC[sch3_graph; IN_ELIM_THM; VECTOR_2] THEN
  SUBGOAL_THEN `vector[(g:real^3->real^3) t$1; g t$2; &1]:real^3 IN U /\
                (Psi:real^3->real^3)(vector[(g:real^3->real^3) t$1; g t$2; &1]) = t`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `vector[(g:real^3->real^3) t$1; g t$2; &1]:real^3 =
                  vector[(g:real^3->real^3) t$1; g t$2; norm t pow 2]` SUBST1_TAC THENL
     [UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Td:real^3->bool`)) (concl th) &&
      can (find_term ((=) `Psi:real^3->real^3`)) (concl th) &&
      not (can (find_term ((=) `U:real^3->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {y:real^2 | vector[y$1; y$2; &1]:real^3 IN U}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[SCH3_LIFT12_CONTINUOUS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `smooth_map_on {y:real^2 | vector[y$1; y$2; &1]:real^3 IN U}
                  (\y. (Psi:real^3->real^3)(vector[y$1; y$2; &1]))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCH3_SV_COMPOSE THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN SCH3_SMOOTH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SCH3_SL_COMPONENT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SCH3_SV_COMPOSE THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    USE_THEN "comp" (MP_TAC o C MATCH_MP
      (ASSUME `vector[(y:real^2)$1; y$2; &1]:real^3 IN U`)) THEN
    REWRITE_TAC[VECTOR_3] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_SPHERE_0] THEN
      MP_TAC(ISPECL [`norm((Psi:real^3->real^3)(vector[(y:real^2)$1; y$2; &1]))`; `2`]
        REAL_POW_EQ_1) THEN
      ASM_REWRITE_TAC[REAL_ABS_NORM] THEN ARITH_TAC;
      ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3]];
    EXISTS_TAC `IMAGE (g:real^3->real^3) Td` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCH4_DIFFEO_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`annulus (&1 / &2) (&2):real^3->bool`;
                            `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                            `g':real^3->real^3`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[sch_neck];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `s:real^3` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `s:real^3 = u` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `(s:real^3) IN annulus (&1 / &2) (&2) /\ (u:real^3) IN annulus (&1 / &2) (&2)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET]; ASM SET_TAC[]];
        ALL_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?z:real^3. z IN U /\ (Psi:real^3->real^3) z = u` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "comp" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN U`)) THEN STRIP_TAC THEN
    SUBGOAL_THEN `vector[(g:real^3->real^3) u$1; g u$2; &1]:real^3 = z` ASSUME_TAC THENL
     [UNDISCH_TAC `(u:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
      DISCH_TAC THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
        concl th = `norm((Psi:real^3->real^3) z) pow 2 = (z:real^3)$3`)) THEN
      ASM_MESON_TAC[REAL_POW_ONE];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* Nondegeneracy at every critical point under the cone condition.          *)

let SCH3_NONDEG = prove
 (`!g g':real^3->real^3 t r.
        sch_neck g g' /\ sch_crit g t /\ &1 / &2 < r /\ r < &2 /\
        ~(det(matrix(frechet_derivative (sch3_cone g) (at (r % t)))) = &0)
        ==> sch3_nondeg g t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`]
    SCH3_GRAPH_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[sch3_nondeg; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`D:real^2->bool`; `phi:real^2->real`; `sigma:real^2->real^3`] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`D:real^2->bool`; `phi:real^2->real`; `sigma:real^2->real^3`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH3_NONDEG_FROM_CONE THEN
  MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `r:real`; `D:real^2->bool`;
                        `sigma:real^2->real^3`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* After the rotation the critical points are finitely many and              *)
(* nondegenerate.                                                            *)
(* ------------------------------------------------------------------------- *)

let SCH3_MORSE_PREP = prove
 (`!f f':real^3->real^3.
        sch_neck f f'
        ==> ?Phi Phi' g g'.
              diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\
              sch_neck g g' /\
              IMAGE g (sphere(vec 0,&1)) = IMAGE Phi (IMAGE f (sphere(vec 0,&1))) /\
              FINITE {t | sch_crit g t} /\
              (!t. sch_crit g t ==> sch3_nondeg g t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCH3_GOOD_ROTATION) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`Q:real^3->real^3`; `Q':real^3->real^3`; `r:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`Q:real^3->real^3`; `Q':real^3->real^3`;
                        `(Q:real^3->real^3) o (f:real^3->real^3)`;
                        `(f':real^3->real^3) o (Q':real^3->real^3)`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SCH3_CRIT_FINITE THEN
    EXISTS_TAC `(f':real^3->real^3) o (Q':real^3->real^3)` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC SCH3_CRIT_ISOLATED THEN
    MAP_EVERY EXISTS_TAC [`(f':real^3->real^3) o (Q':real^3->real^3)`; `r:real`] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC SCH3_NONDEG THEN
    MAP_EVERY EXISTS_TAC [`(f':real^3->real^3) o (Q':real^3->real^3)`; `r:real`] THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Calculus of functions on the plane (gradient, Hessian                     *)
(* symmetry, quadratic normal form) and derivative bounds on compact sets.   *)
(* ------------------------------------------------------------------------- *)

(* The gradient computes the derivative.                                     *)

let SCH3_GRAD_WORKS = prove
 (`!(f:real^2->real) y.
        (\z. lift(f z)) differentiable at y
        ==> !h. frechet_derivative (\z. lift(f z)) (at y) h = lift(sch3_grad f y dot h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  SUBGOAL_THEN `h:real^2 = h$1 % basis 1 + h$2 % basis 2` SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
  REWRITE_TAC[sch3_grad; DOT_2; VECTOR_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

let SCH3_GRAD_UNIQUE = prove
 (`!(f:real^2->real) y v.
        ((\z. lift(f z)) has_derivative (\h. lift(v dot h))) (at y)
        ==> sch3_grad f y = v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_REWRITE_TAC[sch3_grad; LIFT_DROP] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; DOT_BASIS; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[LIFT_DROP]);;

(* The Hessian (the derivative of the gradient) of a smooth function is      *)
(* symmetric.                                                                *)

let SCH3_HESS_SYM = prove
 (`!(phi:real^2->real) D x0.
        open D /\ x0 IN D /\ smooth_map_on D (\y. lift(phi y))
        ==> symmetric_matrix(matrix(frechet_derivative (sch3_grad phi) (at x0)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `H = frechet_derivative (sch3_grad (phi:real^2->real)) (at x0)` THEN
  SUBGOAL_THEN `(sch3_grad (phi:real^2->real) has_derivative H) (at x0)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^2->bool` THEN
    ASM_SIMP_TAC[SCH3_GRAD_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(H:real^2->real^2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
          ==> lift(((H:real^2->real^2) (basis j))$i) =
              frechet_derivative
                (\z. frechet_derivative (\y. lift((phi:real^2->real) y)) (at z) (basis i))
                (at x0) (basis j)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    SUBGOAL_THEN
     `((\z. frechet_derivative (\y. lift((phi:real^2->real) y)) (at z) (basis i))
       has_derivative (\h. lift(((H:real^2->real^2) h)$i))) (at x0)`
    (fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
    (MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      MAP_EVERY EXISTS_TAC [`\z. lift((sch3_grad (phi:real^2->real) z)$i)`;
                            `D:real^2->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
        REWRITE_TAC[sch3_grad] THEN
        MP_TAC(ARITH_RULE `1 <= i /\ i <= 2 ==> i = 1 \/ i = 2`) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_2; LIFT_DROP];
        UNDISCH_TAC `(sch3_grad (phi:real^2->real) has_derivative H) (at x0)` THEN
        GEN_REWRITE_TAC LAND_CONV [HAS_DERIVATIVE_COMPONENTWISE_AT] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[DIMINDEX_2]]);
    ALL_TAC] THEN
  REWRITE_TAC[symmetric_matrix; CART_EQ; TRANSP_COMPONENT; DIMINDEX_2; FORALL_2] THEN
  ASM_SIMP_TAC[MATRIX_COMPONENT; DIMINDEX_2; ARITH] THEN
  SUBGOAL_THEN `((H:real^2->real^2) (basis 1))$2 = (H (basis 2))$1` (fun th ->
    REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM LIFT_EQ] THEN ASM_SIMP_TAC[ARITH] THEN
  MATCH_MP_TAC SCHWARZ_C2_SCALAR THEN EXISTS_TAC `D:real^2->bool` THEN
  ASM_REWRITE_TAC[IN_NUMSEG; DIMINDEX_2; ARITH] THEN
  ASM_MESON_TAC[smooth_map_on]);;

(* Normal form of a nondegenerate quadratic form on the plane (spectral      *)
(* theorem plus scaling).                                                    *)

let SCH3_SQRT_SCALE = prove
 (`!d. ~(d = &0)
       ==> d * sqrt(&2 / abs d) pow 2 / &2 = &1 \/
           d * sqrt(&2 / abs d) pow 2 / &2 = -- &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&2 / abs d) pow 2 = &2 / abs d` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < d` THENL
   [DISJ1_TAC THEN ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`] THEN
    UNDISCH_TAC `~(d = &0)` THEN CONV_TAC REAL_FIELD;
    DISJ2_TAC THEN SUBGOAL_THEN `abs d = --d` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(d = &0)` THEN CONV_TAC REAL_FIELD]);;

let SCH3_QUAD_NORMAL_FORM = prove
 (`!A:real^2^2.
        symmetric_matrix A /\ ~(det A = &0)
        ==> ?L:real^2->real^2 k1 k2. linear L /\ (!u v. L u = L v ==> u = v) /\
                      (k1 = &1 \/ k1 = -- &1) /\ (k2 = &1 \/ k2 = -- &1) /\
                      !u. ((L u) dot (A ** L u)) / &2 =
                          k1 * (u$1) pow 2 + k2 * (u$2) pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SYMMETRIC_MATRIX_DIAGONALIZABLE_EXPLICIT) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`P:real^2^2`; `d:num->real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `det(A:real^2^2) = (d:num->real) 1 * d 2` ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `det(transp(P:real^2^2) ** A ** P)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[DET_MUL; DET_TRANSP] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP DET_ORTHOGONAL_MATRIX) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[DET_2] THEN SIMP_TAC[LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((d:num->real) 1 = &0) /\ ~(d 2 = &0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(det(A:real^2^2) = &0)` THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM];
    ALL_TAC] THEN
  ABBREV_TAC `s1 = sqrt(&2 / abs((d:num->real) 1))` THEN
  ABBREV_TAC `s2 = sqrt(&2 / abs((d:num->real) 2))` THEN
  SUBGOAL_THEN `&0 < s1 /\ &0 < s2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s1"; "s2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\u:real^2. (P:real^2^2) ** vector[s1 * u$1; s2 * u$2]` THEN
  EXISTS_TAC `(d:num->real) 1 * s1 pow 2 / &2` THEN
  EXISTS_TAC `(d:num->real) 2 * s2 pow 2 / &2` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ADD_LDISTRIB; GSYM MATRIX_VECTOR_MUL_RMUL] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `vector[s1 * (u:real^2)$1; s2 * u$2]:real^2 = vector[s1 * (v:real^2)$1; s2 * v$2]`
    MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `\w:real^2. transp(P:real^2^2) ** w`) THEN
      ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; ORTHOGONAL_MATRIX_TRANSP_LMUL;
                   MATRIX_VECTOR_MUL_LID];
      ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    ASM_SIMP_TAC[REAL_EQ_MUL_LCANCEL; REAL_LT_IMP_NZ];
    MAP_EVERY EXPAND_TAC ["s1"] THEN MATCH_MP_TAC SCH3_SQRT_SCALE THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXPAND_TAC ["s2"] THEN MATCH_MP_TAC SCH3_SQRT_SCALE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `u:real^2` THEN REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[matrix_vector_mul; DOT_2; LAMBDA_BETA; DIMINDEX_2; ARITH; SUM_2;
             VECTOR_2] THEN
    REAL_ARITH_TAC]);;

(* Derivatives of smooth maps are bounded on compact subsets.               *)

let SCH3_DERIV_BOUND = prove
 (`!f:real^M->real^N s K.
        open s /\ smooth_map_on s f /\ compact K /\ K SUBSET s
        ==> ?B. &0 < B /\
                !x h. x IN K ==> norm(frechet_derivative f (at x) h) <= B * norm h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `bounded(UNIONS {IMAGE (\x. frechet_derivative (f:real^M->real^N) (at x) (basis i)) K |
                    i IN 1..dimindex(:M)})`
  MP_TAC THENL
   [MATCH_MP_TAC BOUNDED_UNIONS THEN
    SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `s:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              FORALL_IN_GSPEC; FORALL_IN_IMAGE; IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `B0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&(dimindex(:M)) * B0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MP_TAC(ISPEC `(:M)` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN X_GEN_TAC `h:real^M` THEN
  SUBGOAL_THEN `linear(frechet_derivative (f:real^M->real^N) (at x))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:M)) (\i. norm(h:real^M) * B0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; NORM_MUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM; REAL_ABS_POS; NORM_POS_LE];
    REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(n + 1) - 1 = n`] THEN
    REAL_ARITH_TAC]);;

(* A symmetric matrix gives a symmetric bilinear form.                        *)

let SCH3_HESS_SYM_DOT = prove
 (`!H:real^2->real^2.
        linear H /\ symmetric_matrix(matrix H) ==> !u v. u dot H v = v dot H u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  UNDISCH_TAC `symmetric_matrix(matrix(H:real^2->real^2))` THEN
  SPEC_TAC(`matrix(H:real^2->real^2)`,`A:real^2^2`) THEN
  REWRITE_TAC[symmetric_matrix] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [GSYM th]) THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN MATCH_ACCEPT_TAC DOT_SYM);;

(* Lipschitz bound for the derivative of the gradient near x0.              *)

let SCH3_DG_LIPSCHITZ = prove
 (`!phi:real^2->real D x0 r.
        open D /\ smooth_map_on D (\y. lift(phi y)) /\ &0 < r /\ cball(x0,r) SUBSET D
        ==> ?B. &0 < B /\
                !y h. y IN cball(x0,r)
                      ==> norm(frechet_derivative (sch3_grad phi) (at y) h -
                               frechet_derivative (sch3_grad phi) (at x0) h)
                          <= B * norm(y - x0) * norm h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on D (sch3_grad (phi:real^2->real))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCH3_GRAD_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. ?B. &0 < B /\
            !y. y IN cball(x0,r)
                ==> norm(frechet_derivative (sch3_grad (phi:real^2->real)) (at y) (basis j) -
                         frechet_derivative (sch3_grad phi) (at x0) (basis j))
                    <= B * norm(y - x0)`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`\y. frechet_derivative (sch3_grad (phi:real^2->real)) (at y) (basis j)`;
                   `D:real^2->bool`; `cball(x0:real^2,r)`] SCH3_DERIV_BOUND) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE; COMPACT_CBALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\y. frechet_derivative (sch3_grad (phi:real^2->real)) (at y) (basis j)`;
                   `\y. frechet_derivative (\y. frechet_derivative (sch3_grad (phi:real^2->real))
                                                  (at y) (basis j)) (at y)`;
                   `cball(x0:real^2,r)`; `B:real`] DIFFERENTIABLE_BOUND) THEN
    REWRITE_TAC[CONVEX_CBALL] THEN ANTS_TAC THENL
     [CONJ_TAC THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
        REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^2->bool` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN ASM SET_TAC[];
        SUBGOAL_THEN
         `linear(frechet_derivative (\y. frechet_derivative (sch3_grad (phi:real^2->real))
                                          (at y) (basis j)) (at z))`
        ASSUME_TAC THENL
         [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
          MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^2->bool` THEN
          ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN ASM SET_TAC[];
          ALL_TAC] THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ONORM_LE_EQ th]) THEN
        ASM_SIMP_TAC[]];
      DISCH_THEN(MP_TAC o SPECL [`y:real^2`; `x0:real^2`]) THEN
      ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN ANTS_TAC THENL
       [ASM_MESON_TAC[REAL_LT_IMP_LE]; REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(b:num->real) 1 + b 2` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_ADD]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^2`; `h:real^2`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (sch3_grad (phi:real^2->real)) (at y)) /\
                linear(frechet_derivative (sch3_grad (phi:real^2->real)) (at x0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] (ASSUME `cball(x0:real^2,r) SUBSET D`)) THEN
    ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!L:real^2->real^2. linear L ==> L h = h$1 % L(basis 1) + h$2 % L(basis 2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL] THEN
    REWRITE_TAC[DIMINDEX_2; VSUM_2];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `linear(frechet_derivative (sch3_grad (phi:real^2->real)) (at y))`)]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `linear(frechet_derivative (sch3_grad (phi:real^2->real)) (at x0))`)]) THEN
  REWRITE_TAC[VECTOR_ARITH
   `(a % u + b % v) - (a % u' + b % v'):real^2 = a % (u - u') + b % (v - v')`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((h:real^2)$1) * (b 1 * norm(y - x0:real^2)) +
              abs(h$2) * (b 2 * norm(y - x0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(x:real^2) <= a /\ norm(y:real^2) <= b ==> norm(x + y) <= a + b`) THEN
    REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (b:num->real) 1 * norm(y - x0:real^2) /\
                &0 <= (b:num->real) 2 * norm(y - x0:real^2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(h:real^2) * ((b:num->real) 1 * norm(y - x0:real^2)) +
              norm h * (b 2 * norm(y - x0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[COMPONENT_LE_NORM];
    REAL_ARITH_TAC]);;


(* Second-order Taylor estimates with remainder bounds (by the mean value    *)
(* inequality twice; no Taylor theorem is needed).                           *)

let SCH3_TAYLOR2 = prove
 (`!phi:real^2->real D x0.
        open D /\ x0 IN D /\ smooth_map_on D (\y. lift(phi y))
        ==> ?C r. &0 < r /\ cball(x0,r) SUBSET D /\ &0 < C /\
                  !y. y IN cball(x0,r)
                      ==> norm(sch3_grad phi y - sch3_grad phi x0 -
                               frechet_derivative (sch3_grad phi) (at x0) (y - x0))
                          <= C * norm(y - x0) pow 2 /\
                          abs(phi y - phi x0 - sch3_grad phi x0 dot (y - x0) -
                              ((y - x0) dot
                               frechet_derivative (sch3_grad phi) (at x0) (y - x0)) / &2)
                          <= C * norm(y - x0) pow 3`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x0:real^2` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `D:real^2->bool`; `x0:real^2`; `r:real`]
    SCH3_DG_LIPSCHITZ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`B:real`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `smooth_map_on D (sch3_grad (phi:real^2->real))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCH3_GRAD_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN cball(x0,r) ==> z IN D` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN cball(x0,r)
                ==> (sch3_grad (phi:real^2->real) has_derivative
                     frechet_derivative (sch3_grad phi) (at z)) (at z) /\
                    ((\y. lift(phi y)) has_derivative
                     (\h. lift(sch3_grad phi z dot h))) (at z)`
  (LABEL_TAC "der") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\y. lift((phi:real^2->real) y)) differentiable at z` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^2->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^2->bool` THEN
      ASM_SIMP_TAC[];
      FIRST_ASSUM(MP_TAC o MATCH_MP SCH3_GRAD_WORKS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM(REWRITE_RULE[GSYM FUN_EQ_THM] th)]) THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  ABBREV_TAC `G = sch3_grad (phi:real^2->real)` THEN
  ABBREV_TAC `H = frechet_derivative (G:real^2->real^2) (at x0)` THEN
  SUBGOAL_THEN `(x0:real^2) IN cball(x0,r)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(H:real^2->real^2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  SUBGOAL_THEN `!u v:real^2. u dot (H:real^2->real^2) v = v dot H u` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH3_HESS_SYM_DOT THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "H" THEN EXPAND_TAC "G" THEN MATCH_MP_TAC SCH3_HESS_SYM THEN
    EXISTS_TAC `D:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* first estimate, for all points of the ball *)
  SUBGOAL_THEN
   `!z:real^2. z IN cball(x0,r)
               ==> norm((G:real^2->real^2) z - G x0 - (H:real^2->real^2) (z - x0))
                   <= B * norm(z - x0) pow 2`
  (LABEL_TAC "est1") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\y:real^2. (G:real^2->real^2) y - (H:real^2->real^2) y`;
                   `\y:real^2. \h. frechet_derivative (G:real^2->real^2) (at y) h -
                                  (H:real^2->real^2) h`;
                   `cball(x0:real^2,norm(z - x0))`; `B * norm(z - x0:real^2)`]
      DIFFERENTIABLE_BOUND) THEN
    REWRITE_TAC[CONVEX_CBALL] THEN
    SUBGOAL_THEN `cball(x0:real^2,norm(z - x0)) SUBSET cball(x0,r)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `w:real^2` THEN
      UNDISCH_TAC `(z:real^2) IN cball(x0,r)` THEN REWRITE_TAC[IN_CBALL] THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
      (SUBGOAL_THEN `(w:real^2) IN cball(x0,r)` ASSUME_TAC THENL
        [ASM SET_TAC[]; ALL_TAC]) THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
        MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
        ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; ETA_AX] THEN
        USE_THEN "der" (MP_TAC o SPEC `w:real^2`) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `linear(\h. frechet_derivative (G:real^2->real^2) (at w) h -
                               (H:real^2->real^2) h)` ASSUME_TAC THENL
       [MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^2->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[MATCH_MP ONORM_LE_EQ (ASSUME
        `linear(\h. frechet_derivative (G:real^2->real^2) (at w) h -
                    (H:real^2->real^2) h)`)] THEN
      X_GEN_TAC `h:real^2` THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `B * norm(w - x0:real^2) * norm(h:real^2)` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `B:real`)) (concl th) && is_forall(concl th))) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        UNDISCH_TAC `(w:real^2) IN cball(x0,norm(z - x0))` THEN
        REWRITE_TAC[IN_CBALL] THEN CONV_TAC NORM_ARITH];
      DISCH_THEN(MP_TAC o SPECL [`z:real^2`; `x0:real^2`]) THEN
      ANTS_TAC THENL [REWRITE_TAC[IN_CBALL] THEN CONV_TAC NORM_ARITH; ALL_TAC] THEN
      ASM_SIMP_TAC[LINEAR_SUB] THEN
      MATCH_MP_TAC(REAL_ARITH `a = b /\ c = d ==> a <= c ==> b <= d`) THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN VECTOR_ARITH_TAC;
        REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  USE_THEN "est1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^2) IN cball(x0,r)`)]) THEN
  (* second estimate *)
  SUBGOAL_THEN
   `!z:real^2. z IN cball(x0,r)
      ==> ((\z. lift((phi:real^2->real) z) - lift(phi x0) -
                lift((G:real^2->real^2) x0 dot (z - x0)) -
                inv(&2) % lift((z - x0) dot (H:real^2->real^2) (z - x0)))
           has_derivative (\h. lift((G z - G x0 - H(z - x0)) dot h))) (at z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `((\z. lift((phi:real^2->real) z) - lift(phi x0) -
            lift((G:real^2->real^2) x0 dot (z - x0)) -
            inv(&2) % lift((z - x0) dot (H:real^2->real^2) (z - x0)))
       has_derivative
       (\h. lift(G z dot h) - vec 0 - lift(G x0 dot (h - vec 0)) -
            inv(&2) % (lift((z - x0) dot H(h - vec 0)) + lift((h - vec 0) dot H(z - x0)))))
      (at z)`
    MP_TAC THENL
     [REPEAT(MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC) THENL
       [USE_THEN "der" (MP_TAC o SPEC `z:real^2`) THEN ASM_SIMP_TAC[];
        REWRITE_TAC[HAS_DERIVATIVE_CONST];
        MATCH_MP_TAC HAS_DERIVATIVE_LIFT_DOT THEN
        MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
        REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
        MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
        MP_TAC(ISPECL [`\x y:real^2. lift(x dot y)`; `\z:real^2. z - x0`;
                       `\z:real^2. (H:real^2->real^2)(z - x0)`;
                       `\h:real^2. h - vec 0`; `\h:real^2. (H:real^2->real^2)(h - vec 0)`;
                       `z:real^2`] HAS_DERIVATIVE_BILINEAR_AT) THEN
        REWRITE_TAC[BILINEAR_DOT] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
          REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
          SUBGOAL_THEN `(\z:real^2. (H:real^2->real^2)(z - x0)) = H o (\z. z - x0) /\
                        (\h:real^2. (H:real^2->real^2)(h - vec 0)) = H o (\h. h - vec 0)`
          (CONJUNCTS_THEN SUBST1_TAC) THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
          MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR] THEN
          MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
          REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST]]];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_RZERO] THEN X_GEN_TAC `h:real^2` THEN
    SUBGOAL_THEN `(z - x0:real^2) dot (H:real^2->real^2) h = h dot H(z - x0)`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_SUB; GSYM LIFT_CMUL; LIFT_EQ; VECTOR_SUB_RZERO;
                LIFT_NUM; GSYM LIFT_NUM] THEN
    REWRITE_TAC[DOT_LSUB] THEN REWRITE_TAC[DOT_SYM] THEN
    REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. lift((phi:real^2->real) z) - lift(phi x0) -
         lift((G:real^2->real^2) x0 dot (z - x0)) -
         inv(&2) % lift((z - x0) dot (H:real^2->real^2) (z - x0))`;
    `\z:real^2 h. lift(((G:real^2->real^2) z - G x0 - (H:real^2->real^2)(z - x0)) dot h)`;
    `cball(x0:real^2,norm(y - x0))`; `B * norm(y - x0:real^2) pow 2`]
    DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_CBALL] THEN
  SUBGOAL_THEN `cball(x0:real^2,norm(y - x0)) SUBSET cball(x0,r)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `w:real^2` THEN
    UNDISCH_TAC `(y:real^2) IN cball(x0,r)` THEN REWRITE_TAC[IN_CBALL] THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    (SUBGOAL_THEN `(w:real^2) IN cball(x0,r)` ASSUME_TAC THENL
      [ASM SET_TAC[]; ALL_TAC]) THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `linear(\h. lift(((G:real^2->real^2) w - G x0 - (H:real^2->real^2)(w - x0)) dot h))`
    ASSUME_TAC THENL [REWRITE_TAC[LINEAR_LIFT_DOT]; ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP ONORM_LE_EQ (ASSUME
     `linear(\h. lift(((G:real^2->real^2) w - G x0 - (H:real^2->real^2)(w - x0)) dot h))`)] THEN
    X_GEN_TAC `h:real^2` THEN REWRITE_TAC[NORM_LIFT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((G:real^2->real^2) w - G x0 - (H:real^2->real^2)(w - x0)) * norm(h:real^2)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B * norm(w - x0:real^2) pow 2` THEN CONJ_TAC THENL
     [USE_THEN "est1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
      UNDISCH_TAC `(w:real^2) IN cball(x0,norm(y - x0))` THEN
      REWRITE_TAC[IN_CBALL] THEN CONV_TAC NORM_ARITH];
    DISCH_THEN(MP_TAC o SPECL [`y:real^2`; `x0:real^2`]) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_CBALL] THEN CONV_TAC NORM_ARITH; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; DOT_LZERO; DOT_RZERO; LIFT_NUM; VECTOR_MUL_RZERO;
                VECTOR_SUB_RZERO; VECTOR_SUB_REFL] THEN
    REWRITE_TAC[GSYM LIFT_SUB; GSYM LIFT_CMUL; NORM_LIFT; VECTOR_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b /\ c = d ==> a <= c ==> b <= d`) THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2; ARITH_RULE `3 = SUC 2`; real_pow] THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for the local perturbation (bumps, locality of                    *)
(* smoothness, avoiding finitely many values, gradient bounds).              *)
(* ------------------------------------------------------------------------- *)

let SCH3_FINITE_AVOID = prove
 (`!s d. FINITE s /\ &0 < d ==> ?x. &0 < x /\ x < d /\ ~(x IN s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{x:real | &0 < x /\ x < d}`; `s:real->bool`] INFINITE_DIFF_FINITE) THEN
  ASM_REWRITE_TAC[INFINITE; FINITE_REAL_INTERVAL; REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY o REWRITE_RULE[GSYM INFINITE]) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]);;

let SCH3_SMOOTH_LOCAL = prove
 (`!s (f:real^M->real^N).
        open s /\ (!x. x IN s ==> ?t. open t /\ x IN t /\ smooth_map_on t f)
        ==> smooth_map_on s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s INTER t:real^M->bool` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER; INTER_SUBSET] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
  EXISTS_TAC `t:real^M->bool` THEN REWRITE_TAC[INTER_SUBSET] THEN
  ASM_MESON_TAC[smooth_map_on]);;

(* A derivative bound for the bumps of ns_cutoff (valid everywhere).         *)

let SCH3_BUMP_DERIV = prove
 (`!a b. &0 <= a /\ a < b
         ==> ?M. &0 < M /\
                 !x:real^N h. norm(frechet_derivative (\x. lift(smooth_bump a b x)) (at x) h)
                              <= M * norm h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (\x. lift(smooth_bump a b x))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_BUMP_SMOOTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. lift(smooth_bump a b x)`; `(:real^N)`;
                 `cball(vec 0:real^N,b + &1)`] SCH3_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; COMPACT_CBALL; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `h:real^N`] THEN
  ASM_CASES_TAC `(x:real^N) IN cball(vec 0,b + &1)` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `((\x:real^N. lift(smooth_bump a b x)) has_derivative (\h. vec 0)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`\x:real^N. vec 0:real^1`; `{y:real^N | b < norm y}`] THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `{y:real^N | b < norm y} = (:real^N) DIFF cball(vec 0,b)`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_CBALL_0; IN_ELIM_THM] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL]];
      UNDISCH_TAC `~((x:real^N) IN cball(vec 0,b + &1))` THEN
      REWRITE_TAC[IN_CBALL_0] THEN REAL_ARITH_TAC;
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[NORM_0] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE]);;

(* The gradient is bounded by any derivative bound.                          *)

let SCH3_GRAD_BOUND = prove
 (`!(f:real^2->real) y W.
        (\z. lift(f z)) differentiable at y /\
        (!h. norm(frechet_derivative (\z. lift(f z)) (at y) h) <= W * norm h)
        ==> norm(sch3_grad f y) <= W`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "b")) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH3_GRAD_WORKS) THEN
  SUBGOAL_THEN `&0 <= W` ASSUME_TAC THENL
   [USE_THEN "b" (MP_TAC o SPEC `basis 1:real^2`) THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN
    MESON_TAC[NORM_POS_LE; REAL_MUL_RID; REAL_LE_TRANS];
    ALL_TAC] THEN
  ASM_CASES_TAC `sch3_grad (f:real^2->real) y = vec 0` THEN
  ASM_REWRITE_TAC[NORM_0] THEN
  REMOVE_THEN "b" (MP_TAC o SPEC `sch3_grad (f:real^2->real) y`) THEN
  ASM_REWRITE_TAC[NORM_LIFT; DOT_SQUARE_NORM; REAL_ABS_POW; REAL_ABS_NORM] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ; NORM_POS_LT]);;

(* The derivative of the Taylor remainder e(z) = phi z - phi x0 - q(z - x0). *)

let SCH3_E_DERIV = prove
 (`!(phi:real^2->real) (H:real^2->real^2) x0 y.
        linear H /\ (!u v. u dot H v = v dot H u) /\
        (\z. lift(phi z)) differentiable at y
        ==> ((\z. lift(phi z - phi x0 - ((z - x0) dot H(z - x0)) / &2)) has_derivative
             (\h. lift((sch3_grad phi y - H(y - x0)) dot h))) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\z. lift((phi:real^2->real) z) - lift(phi x0) -
          inv(&2) % lift((z - x0) dot (H:real^2->real^2) (z - x0)))
     has_derivative
     (\h. lift(sch3_grad phi y dot h) - vec 0 -
          inv(&2) % (lift((y - x0) dot H(h - vec 0)) + lift((h - vec 0) dot H(y - x0)))))
    (at y)`
  MP_TAC THENL
   [REPEAT(MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC) THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP SCH3_GRAD_WORKS) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM(REWRITE_RULE[GSYM FUN_EQ_THM] th)]) THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      REWRITE_TAC[HAS_DERIVATIVE_CONST];
      MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
      MP_TAC(ISPECL [`\x y:real^2. lift(x dot y)`; `\z:real^2. z - x0`;
                     `\z:real^2. (H:real^2->real^2)(z - x0)`;
                     `\h:real^2. h - vec 0`; `\h:real^2. (H:real^2->real^2)(h - vec 0)`;
                     `y:real^2`] HAS_DERIVATIVE_BILINEAR_AT) THEN
      REWRITE_TAC[BILINEAR_DOT] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
        REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
        SUBGOAL_THEN `(\z:real^2. (H:real^2->real^2)(z - x0)) = H o (\z. z - x0) /\
                      (\h:real^2. (H:real^2->real^2)(h - vec 0)) = H o (\h. h - vec 0)`
        (CONJUNCTS_THEN SUBST1_TAC) THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
        MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR] THEN
        MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
        REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST]]];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `(F2:real^2->real^1) = F1 /\ (D2:real^2->real^1) = D1
                        ==> (F1 has_derivative D1) (at y) ==> (F2 has_derivative D2) (at y)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^2` THEN
    REWRITE_TAC[GSYM LIFT_SUB; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_RZERO] THEN X_GEN_TAC `h:real^2` THEN
    SUBGOAL_THEN `(y - x0:real^2) dot (H:real^2->real^2) h = h dot H(y - x0)`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_SUB; GSYM LIFT_CMUL; LIFT_EQ; VECTOR_SUB_RZERO;
                LIFT_NUM; GSYM LIFT_NUM] THEN
    REWRITE_TAC[DOT_LSUB] THEN REWRITE_TAC[DOT_SYM] THEN
    REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN REAL_ARITH_TAC]);;

(* The rescaled bump and its derivative.                                     *)

let SCH3_BUMP_COMPOSE_DERIV = prove
 (`!rho (x0:real^2) y.
        ((\z. lift(smooth_bump (&1) (&2) (inv rho % (z - x0)))) has_derivative
         (\h. frechet_derivative (\x. lift(smooth_bump (&1) (&2) x))
                (at (inv rho % (y - x0))) (inv rho % h))) (at y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\z:real^2. inv rho % (z - x0)`;
                 `\x:real^2. lift(smooth_bump (&1) (&2) x)`;
                 `\h:real^2. inv rho % h`;
                 `frechet_derivative (\x:real^2. lift(smooth_bump (&1) (&2) x))
                    (at (inv rho % (y - x0)))`;
                 `y:real^2`] DIFF_CHAIN_AT) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\h:real^2. inv rho % h) = (\h. inv rho % (h - vec 0))` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_SUB_RZERO]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let SCH3_OPEN_OUTSIDE_BALL = prove
 (`!x0:real^N r. open {y | r < norm(y - x0)}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{y:real^N | r < norm(y - x0)} = (:real^N) DIFF cball(x0,r)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_CBALL; IN_ELIM_THM] THEN
    CONV_TAC NORM_ARITH;
    SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL]]);;

(* Smoothness of the perturbation (locality: near the disc it is a product  *)
(* of smooth functions, away from it it vanishes).                           *)

let SCH3_W_SMOOTH = prove
 (`!(phi:real^2->real) D x0 (H:real^2->real^2) rho eps w.
        open D /\ smooth_map_on D (\y. lift(phi y)) /\ linear H /\
        &0 < rho /\ ball(x0,&3 * rho) SUBSET D /\
        (!y. w y = smooth_bump (&1) (&2) (inv rho % (y - x0)) *
                   (eps - (phi y - phi x0 - ((y - x0) dot H(y - x0)) / &2))) /\
        (!y. ~(y IN ball(x0,&2 * rho)) ==> w y = &0)
        ==> smooth_map_on (:real^2) (\y. lift(w y))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH3_SMOOTH_LOCAL THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN X_GEN_TAC `x:real^2` THEN
  ASM_CASES_TAC `(x:real^2) IN ball(x0,&3 * rho)` THENL
   [EXISTS_TAC `ball(x0:real^2,&3 * rho)` THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
    SUBGOAL_THEN `open(ball(x0:real^2,&3 * rho))` ASSUME_TAC THENL
     [REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on (ball(x0:real^2,&3 * rho))
                    (\y. lift(smooth_bump (&1) (&2) (inv rho % (y - x0))))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN
      MP_TAC(ISPECL [`(:real^2)`; `(:real^2)`; `\x:real^2. lift(smooth_bump (&1) (&2) x)`;
                     `\y:real^2. inv rho % (y - x0)`] SCH3_SV_COMPOSE) THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `open(:real^2)` ASSUME_TAC THENL [REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
        SCH3_SMOOTH_TAC;
        MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on (ball(x0:real^2,&3 * rho)) (\y. lift((phi:real^2->real) y))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `D:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on (ball(x0:real^2,&3 * rho)) (\y. (H:real^2->real^2)(y - x0))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(\y. (H:real^2->real^2)(y - x0)) = H o (\y. y - x0)` SUBST1_TAC THENL
       [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN SCH3_SMOOTH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SCH3_SMOOTH_TAC THEN REAL_ARITH_TAC;
    EXISTS_TAC `{y:real^2 | &2 * rho < norm(y - x0)}` THEN
    REWRITE_TAC[SCH3_OPEN_OUTSIDE_BALL; IN_ELIM_THM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~((x:real^2) IN ball(x0,&3 * rho))` THEN
      REWRITE_TAC[IN_BALL] THEN UNDISCH_TAC `&0 < rho` THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\y:real^2. vec 0:real^1` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST; SCH3_OPEN_OUTSIDE_BALL] THEN
    X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^2->real) y = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_BALL] THEN UNDISCH_TAC `&2 * rho < norm(y - x0:real^2)` THEN
      CONV_TAC NORM_ARITH;
      REWRITE_TAC[LIFT_NUM]]]);;

(* The derivative bound for the perturbation.                               *)

let SCH3_W_DERIV = prove
 (`!(phi:real^2->real) D x0 (H:real^2->real^2) C M rho eps w.
        open D /\ smooth_map_on D (\y. lift(phi y)) /\
        linear H /\ (!u v. u dot H v = v dot H u) /\
        &0 < rho /\ ball(x0,&3 * rho) SUBSET D /\ &0 <= C /\
        (!y. y IN ball(x0,&3 * rho)
             ==> norm(sch3_grad phi y - H(y - x0)) <= C * norm(y - x0) pow 2 /\
                 abs(phi y - phi x0 - ((y - x0) dot H(y - x0)) / &2)
                 <= C * norm(y - x0) pow 3) /\
        &0 < M /\
        (!x:real^2 h. norm(frechet_derivative (\x. lift(smooth_bump (&1) (&2) x)) (at x) h)
                      <= M * norm h) /\
        &0 < eps /\
        (!y. w y = smooth_bump (&1) (&2) (inv rho % (y - x0)) *
                   (eps - (phi y - phi x0 - ((y - x0) dot H(y - x0)) / &2))) /\
        (!y. ~(y IN ball(x0,&2 * rho)) ==> w y = &0)
        ==> !y h. norm(frechet_derivative (\y. lift(w y)) (at y) h)
                  <= (M * eps / rho + (&8 * M + &4) * C * rho pow 2) * norm h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^2` THEN X_GEN_TAC `h:real^2` THEN
  SUBGOAL_THEN `&0 <= M * eps / rho + (&8 * M + &4) * C * rho pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_DIV];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^2) IN cball(x0,&2 * rho)` THENL
   [ALL_TAC;
    SUBGOAL_THEN `((\y:real^2. lift(w y)) has_derivative (\h. vec 0)) (at y)` MP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      MAP_EVERY EXISTS_TAC [`\y:real^2. vec 0:real^1`;
                            `{z:real^2 | &2 * rho < norm(z - x0)}`] THEN
      REWRITE_TAC[SCH3_OPEN_OUTSIDE_BALL; HAS_DERIVATIVE_CONST; IN_ELIM_THM] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `~((y:real^2) IN cball(x0,&2 * rho))` THEN REWRITE_TAC[IN_CBALL] THEN
        CONV_TAC NORM_ARITH;
        X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(w:real^2->real) z = &0` SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL] THEN
          UNDISCH_TAC `&2 * rho < norm(z - x0:real^2)` THEN CONV_TAC NORM_ARITH;
          REWRITE_TAC[LIFT_NUM]]];
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      REWRITE_TAC[NORM_0] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[NORM_POS_LE]]] THEN
  SUBGOAL_THEN `(y:real^2) IN ball(x0,&3 * rho)` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^2) IN cball(x0,&2 * rho)` THEN
    REWRITE_TAC[IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(y - x0:real^2) <= &2 * rho` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^2) IN cball(x0,&2 * rho)` THEN REWRITE_TAC[IN_CBALL] THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^2. lift(w z)) =
                (\z. smooth_bump (&1) (&2) (inv rho % (z - x0)) %
                     (lift eps - lift((phi:real^2->real) z - phi x0 -
                                      ((z - x0) dot (H:real^2->real^2)(z - x0)) / &2)))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_SUB; LIFT_CMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift((phi:real^2->real) z)) differentiable at y` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Db = frechet_derivative (\x:real^2. lift(smooth_bump (&1) (&2) x))
                     (at (inv rho % (y - x0)))` THEN
  MP_TAC(ISPECL [`\z:real^2. smooth_bump (&1) (&2) (inv rho % (z - x0))`;
                 `\h:real^2. drop((Db:real^2->real^1) (inv rho % h))`;
                 `\z:real^2. lift eps - lift((phi:real^2->real) z - phi x0 -
                                ((z - x0) dot (H:real^2->real^2)(z - x0)) / &2)`;
                 `\h:real^2. vec 0 - lift((sch3_grad (phi:real^2->real) y -
                                            (H:real^2->real^2)(y - x0)) dot h)`;
                 `y:real^2`] HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_DROP] THEN EXPAND_TAC "Db" THEN
      REWRITE_TAC[SCH3_BUMP_COMPOSE_DERIV];
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
      MATCH_MP_TAC SCH3_E_DERIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o BETA_RULE) THEN
  REWRITE_TAC[VECTOR_SUB_LZERO; GSYM LIFT_SUB; NORM_NEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 * (C * (&2 * rho) pow 2 * norm(h:real^2)) +
              (M * inv rho * norm h) * (eps + C * (&2 * rho) pow 3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(x:real^1) <= a /\ norm(y:real^1) <= b ==> norm(x + y) <= a + b`) THEN
    REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`&1`; `&2`; `inv rho % (y - x0:real^2)`] SMOOTH_BUMP_BOUNDS) THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[NORM_NEG; NORM_LIFT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(sch3_grad (phi:real^2->real) y - (H:real^2->real^2)(y - x0)) *
                  norm(h:real^2)` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C * norm(y - x0:real^2) pow 2` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((Db:real^2->real^1) (inv rho % h))` THEN CONJ_TAC THENL
       [REWRITE_TAC[NORM_REAL; GSYM drop; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * norm(inv rho % h:real^2)` THEN
      CONJ_TAC THENL [EXPAND_TAC "Db" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_LE_REFL];
      REWRITE_TAC[NORM_LIFT] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e /\ abs x <= b ==> abs(e - x) <= e + b`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C * norm(y - x0:real^2) pow 3` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD]);;

(* The perturbation of the graph function near a critical point.            *)

let SCH3_W_PROPS = prove
 (`!(phi:real^2->real) D x0 (H:real^2->real^2) C M rho eps w.
        open D /\ x0 IN D /\ smooth_map_on D (\y. lift(phi y)) /\
        linear H /\ (!u v. u dot H v = v dot H u) /\
        &0 < rho /\ ball(x0,&3 * rho) SUBSET D /\ &0 <= C /\
        (!y. y IN ball(x0,&3 * rho)
             ==> norm(sch3_grad phi y - H(y - x0)) <= C * norm(y - x0) pow 2 /\
                 abs(phi y - phi x0 - ((y - x0) dot H(y - x0)) / &2)
                 <= C * norm(y - x0) pow 3) /\
        &0 < M /\
        (!x:real^2 h. norm(frechet_derivative (\x. lift(smooth_bump (&1) (&2) x)) (at x) h)
                      <= M * norm h) /\
        &0 < eps /\
        (!y. w y = smooth_bump (&1) (&2) (inv rho % (y - x0)) *
                   (eps - (phi y - phi x0 - ((y - x0) dot H(y - x0)) / &2)))
        ==> smooth_map_on (:real^2) (\y. lift(w y)) /\
            (!y. ~(y IN ball(x0,&2 * rho)) ==> w y = &0) /\
            (!y. y IN ball(x0,rho)
                 ==> phi y + w y = phi x0 + eps + ((y - x0) dot H(y - x0)) / &2) /\
            (!y. abs(w y) <= eps + &8 * C * rho pow 3) /\
            (!y h. norm(frechet_derivative (\y. lift(w y)) (at y) h)
                   <= (M * eps / rho + (&8 * M + &4) * C * rho pow 2) * norm h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^2. lift(w y)) =
                (\y. smooth_bump (&1) (&2) (inv rho % (y - x0)) %
                     lift(eps - ((phi:real^2->real) y - phi x0 -
                                 ((y - x0) dot (H:real^2->real^2)(y - x0)) / &2)))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. ~(y IN ball(x0,&2 * rho)) ==> w y = &0` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_BALL; REAL_NOT_LT] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
    UNDISCH_TAC `&2 * rho <= dist(x0:real^2,y)` THEN REWRITE_TAC[dist] THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* smoothness by locality *)
    MATCH_MP_TAC SCH3_W_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`phi:real^2->real`; `D:real^2->bool`; `x0:real^2`;
                          `H:real^2->real^2`; `rho:real`; `eps:real`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    (* exact quadratic near x0 *)
    X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `smooth_bump (&1) (&2) (inv rho % (y - x0:real^2)) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_1 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
      UNDISCH_TAC `dist(x0:real^2,y) < rho` THEN REWRITE_TAC[dist] THEN
      CONV_TAC NORM_ARITH;
      REAL_ARITH_TAC];
    (* sup bound *)
    X_GEN_TAC `y:real^2` THEN
    ASM_CASES_TAC `(y:real^2) IN ball(x0,&2 * rho)` THENL
     [ASM_REWRITE_TAC[];
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `~((y:real^2) IN ball(x0,&2 * rho))`)]) THEN
      REWRITE_TAC[REAL_ABS_0] THEN MATCH_MP_TAC REAL_LE_ADD THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 * abs(eps - (phi y - phi x0 - ((y - x0) dot (H:real^2->real^2)(y - x0)) / &2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MP_TAC(ISPECL [`&1`; `&2`; `inv rho % (y - x0:real^2)`] SMOOTH_BUMP_BOUNDS) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^2) IN ball(x0,&3 * rho)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^2) IN ball(x0,&2 * rho)` THEN REWRITE_TAC[IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `C:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `C * norm(y - x0:real^2) pow 3 <= &8 * C * rho pow 3` MP_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `&8 * C = C * &8`] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&8 * rho pow 3 = (&2 * rho) pow 3` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
      UNDISCH_TAC `(y:real^2) IN ball(x0,&2 * rho)` THEN REWRITE_TAC[IN_BALL] THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    (* derivative bound *)
    MATCH_MP_TAC SCH3_W_DERIV THEN
    MAP_EVERY EXISTS_TAC [`phi:real^2->real`; `D:real^2->bool`; `x0:real^2`;
                          `H:real^2->real^2`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The local planar step: replace phi near a nondegenerate                   *)
(* critical point by its quadratic Taylor polynomial (plus a small shift)    *)
(* without creating critical points.                                         *)
(* ------------------------------------------------------------------------- *)

let SCH3_GRAD_ADD = prove
 (`!(f:real^2->real) g y.
        (\z. lift(f z)) differentiable at y /\ (\z. lift(g z)) differentiable at y
        ==> sch3_grad (\z. f z + g z) y = sch3_grad f y + sch3_grad g y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH3_GRAD_UNIQUE THEN
  REWRITE_TAC[LIFT_ADD; DOT_LADD] THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real^2->real`; `y:real^2`] SCH3_GRAD_WORKS);
    MP_TAC(ISPECL [`g:real^2->real`; `y:real^2`] SCH3_GRAD_WORKS)] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(REWRITE_RULE[GSYM FUN_EQ_THM] th)]) THEN
  REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

let SCH3_GRAD_LOCAL = prove
 (`!(f:real^2->real) g s y.
        open s /\ y IN s /\ (!z. z IN s ==> f z = g z) /\
        (\z. lift(f z)) differentiable at y
        ==> sch3_grad g y = sch3_grad f y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH3_GRAD_UNIQUE THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC [`\z:real^2. lift((f:real^2->real) z)`; `s:real^2->bool`] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCH3_GRAD_WORKS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(REWRITE_RULE[GSYM FUN_EQ_THM] th)]) THEN
  REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

(* The gradient of the quadratic form.                                       *)

let SCH3_GRAD_QUAD = prove
 (`!(H:real^2->real^2) x0 y c.
        linear H /\ (!u v. u dot H v = v dot H u)
        ==> sch3_grad (\z. c + ((z - x0) dot H(z - x0)) / &2) y = H(y - x0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH3_GRAD_UNIQUE THEN
  SUBGOAL_THEN
   `((\z. lift c + inv(&2) % lift((z - x0) dot (H:real^2->real^2)(z - x0))) has_derivative
     (\h. vec 0 + inv(&2) % (lift((y - x0) dot H(h - vec 0)) +
                              lift((h - vec 0) dot H(y - x0))))) (at y)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
    MP_TAC(ISPECL [`\x y:real^2. lift(x dot y)`; `\z:real^2. z - x0`;
                   `\z:real^2. (H:real^2->real^2)(z - x0)`;
                   `\h:real^2. h - vec 0`; `\h:real^2. (H:real^2->real^2)(h - vec 0)`;
                   `y:real^2`] HAS_DERIVATIVE_BILINEAR_AT) THEN
    REWRITE_TAC[BILINEAR_DOT] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
      SUBGOAL_THEN `(\z:real^2. (H:real^2->real^2)(z - x0)) = H o (\z. z - x0) /\
                    (\h:real^2. (H:real^2->real^2)(h - vec 0)) = H o (\h. h - vec 0)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST]];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `(F2:real^2->real^1) = F1 /\ (D2:real^2->real^1) = D1
                        ==> (F1 has_derivative D1) (at y) ==> (F2 has_derivative D2) (at y)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^2` THEN
    REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_RZERO] THEN X_GEN_TAC `h:real^2` THEN
    SUBGOAL_THEN `(y - x0:real^2) dot (H:real^2->real^2) h = h dot H(y - x0)`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_CMUL; VECTOR_ADD_LID; LIFT_EQ] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC]);;

(* Small parameters.                                                         *)

let SCH3_SMALL_POW = prove
 (`!K rho e. &0 <= K /\ &0 < rho /\ rho <= &1 /\ rho * (K + &1) <= e
             ==> K * rho pow 2 <= e /\ K * rho pow 3 <= e /\ K * rho <= e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `K * rho <= e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rho * (K + &1)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < rho` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rho pow 3 <= rho pow 2 /\ rho pow 2 <= rho` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; ARITH_RULE `3 = SUC 2`; real_pow] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * rho * rho` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
        REAL_ARITH_TAC];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `K * rho` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LE_TRANS]);;

(* Choice of the radius and the shift.                                       *)

let SCH3_LT_DIV_IMP = prove
 (`!x e k. &0 < k /\ x < e / k ==> x * k <= e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]);;

let SCH3_EPS_BOUND = prove
 (`!M eps rho e. &0 < rho /\ eps * M < e * rho ==> M * eps / rho < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `M * eps / rho = (eps * M) / rho` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LDIV_EQ]]);;

let SCH3_LOCAL_CONSTS = prove
 (`!rho0 r1 eta NH C M lam (Bv:real->bool) c.
        &0 < rho0 /\ &0 < r1 /\ &0 < eta /\ &0 <= NH /\ &0 <= C /\ &0 < M /\
        &0 < lam /\ FINITE Bv
        ==> ?rho eps.
              &0 < rho /\ rho < rho0 /\ &3 * rho < r1 /\ rho <= &1 /\
              (&9 / &2 * NH + &27 * C) * rho pow 2 <= eta /\
              (&8 * C) * rho pow 3 <= eta / &2 /\
              ((&8 * M + &4) * C) * rho pow 2 <= eta / &2 /\
              ((&8 * M + &13) * C) * rho <= lam / &4 /\
              &0 < eps /\ eps < eta / &2 /\ M * eps / rho <= eta / &2 /\
              M * eps / rho < lam * rho / &2 /\ ~(c + eps IN Bv)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K1 = &9 / &2 * NH + &27 * C` THEN
  ABBREV_TAC `K2 = &8 * C` THEN
  ABBREV_TAC `K3 = (&8 * M + &4) * C` THEN
  ABBREV_TAC `K4 = (&8 * M + &13) * C` THEN
  SUBGOAL_THEN `&0 <= K1 /\ &0 <= K2 /\ &0 <= K3 /\ &0 <= K4` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K1"; "K2"; "K3"; "K4"] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K1 + &1 /\ &0 < K2 + &1 /\ &0 < K3 + &1 /\ &0 < K4 + &1`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`min (min (min rho0 (r1 / &3)) (min (&1) (eta / (K1 + &1))))
                      (min (min (eta / &2 / (K2 + &1)) (eta / &2 / (K3 + &1)))
                           (lam / &4 / (K4 + &1)))`] REAL_DOWN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `rho * (K1 + &1) <= eta /\ rho * (K2 + &1) <= eta / &2 /\
                rho * (K3 + &1) <= eta / &2 /\ rho * (K4 + &1) <= lam / &4`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SCH3_LT_DIV_IMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K1:real`; `rho:real`; `eta:real`] SCH3_SMALL_POW) THEN
  MP_TAC(ISPECL [`K2:real`; `rho:real`; `eta / &2`] SCH3_SMALL_POW) THEN
  MP_TAC(ISPECL [`K3:real`; `rho:real`; `eta / &2`] SCH3_SMALL_POW) THEN
  MP_TAC(ISPECL [`K4:real`; `rho:real`; `lam / &4`] SCH3_SMALL_POW) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (\b. b - c) (Bv:real->bool)`;
                 `min (eta / &2) (min ((eta / &4 * rho) / M) ((lam / &4 * rho pow 2) / M))`]
    SCH3_FINITE_AVOID) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; REAL_LT_MIN] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_LT_DIV; REAL_LT_IMP_NZ;
                 REAL_ARITH `&0 < M ==> &0 < &2 * M /\ &0 < &4 * M`;
                 REAL_ARITH `&0 < e ==> &0 < e / &2 /\ &0 < e / &4`];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_MIN; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `eps * M < eta / &4 * rho /\ eps * M < lam / &4 * rho pow 2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `rho <= &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`rho:real`; `eps:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SCH3_EPS_BOUND THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `eta / &4 * rho` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < rho` THEN UNDISCH_TAC `&0 < eta` THEN
    REWRITE_TAC[REAL_ARITH `eta / &4 * rho < eta / &2 * rho <=> &0 < eta * rho`] THEN
    MESON_TAC[REAL_LT_MUL];
    MATCH_MP_TAC SCH3_EPS_BOUND THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `lam / &4 * rho pow 2` THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN
    REWRITE_TAC[REAL_ARITH `lam / &4 * rho * rho < (lam * rho / &2) * rho <=>
                            &0 < lam * rho * rho`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    DISCH_TAC THEN UNDISCH_TAC `~(?x. eps = x - c /\ (x:real) IN Bv)` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `c + eps` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

(* The local planar step.                                                    *)

let SCH3_LOCAL_2D = prove
 (`!phi:real^2->real D x0 (Bv:real->bool) eta rho0.
        open D /\ x0 IN D /\ smooth_map_on D (\y. lift(phi y)) /\
        sch3_grad phi x0 = vec 0 /\
        ~(det(matrix(frechet_derivative (sch3_grad phi) (at x0))) = &0) /\
        FINITE Bv /\ &0 < eta /\ &0 < rho0
        ==> ?w rho eps (L:real^2->real^2) k1 k2.
              &0 < rho /\ rho < rho0 /\ ball(x0,&3 * rho) SUBSET D /\
              &0 < eps /\ eps < eta /\ ~(phi x0 + eps IN Bv) /\
              smooth_map_on (:real^2) (\y. lift(w y)) /\
              (!y. ~(y IN ball(x0,&2 * rho)) ==> w y = &0) /\
              (!y. abs(w y) <= eta) /\
              (!y h. norm(frechet_derivative (\y. lift(w y)) (at y) h) <= eta * norm h) /\
              (!y. y IN ball(x0,&3 * rho) ==> abs(phi y - phi x0) <= eta) /\
              (!y. y IN ball(x0,&3 * rho)
                   ==> (sch3_grad (\z. phi z + w z) y = vec 0 <=> y = x0)) /\
              linear L /\ (!u v. L u = L v ==> u = v) /\
              (k1 = &1 \/ k1 = -- &1) /\ (k2 = &1 \/ k2 = -- &1) /\
              (!u. norm(L u) < rho
                   ==> phi(x0 + L u) + w(x0 + L u) =
                       phi x0 + eps + k1 * (u$1) pow 2 + k2 * (u$2) pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `H = frechet_derivative (sch3_grad (phi:real^2->real)) (at x0)` THEN
  SUBGOAL_THEN `linear(H:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^2->bool` THEN
    ASM_SIMP_TAC[SCH3_GRAD_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `symmetric_matrix(matrix(H:real^2->real^2))` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC SCH3_HESS_SYM THEN
    EXISTS_TAC `D:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v:real^2. u dot (H:real^2->real^2) v = v dot H u` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH3_HESS_SYM_DOT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^2. (H:real^2->real^2) x = H y ==> x = y` ASSUME_TAC THENL
   [SUBGOAL_THEN `!x:real^2. (H:real^2->real^2) x = vec 0 ==> x = vec 0` MP_TAC THENL
     [UNDISCH_TAC `~(det(matrix(H:real^2->real^2)) = &0)` THEN
      REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET; NOT_EXISTS_THM] THEN
      ASM_SIMP_TAC[MATRIX_WORKS] THEN MESON_TAC[];
      ASM_MESON_TAC[LINEAR_SUB; VECTOR_SUB_EQ]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `H:real^2->real^2` LINEAR_INJECTIVE_BOUNDED_BELOW_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `H:real^2->real^2` LINEAR_BOUNDED_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `NH:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `D:real^2->bool`; `x0:real^2`] SCH3_TAYLOR2) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO; DOT_LZERO; REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `matrix(H:real^2->real^2)` SCH3_QUAD_NORMAL_FORM) THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^2->real^2` (X_CHOOSE_THEN `k1:real`
    (X_CHOOSE_THEN `k2:real` (MAP_EVERY ASSUME_TAC o CONJUNCTS)))) THEN
  MP_TAC(ISPECL [`&1`; `&2`] (INST_TYPE [`:2`,`:N`] SCH3_BUMP_DERIV)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`rho0:real`; `r1:real`; `eta:real`; `NH:real`; `C:real`; `M:real`;
                 `lam:real`; `Bv:real->bool`; `(phi:real^2->real) x0`]
    SCH3_LOCAL_CONSTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `ball(x0:real^2,&3 * rho) SUBSET D` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^2,r1)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LT_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. y IN ball(x0,&3 * rho)
               ==> norm(sch3_grad phi y - (H:real^2->real^2)(y - x0)) <=
                   C * norm(y - x0) pow 2 /\
                   abs(phi y - phi x0 - ((y - x0) dot H(y - x0)) / &2) <=
                   C * norm(y - x0) pow 3`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^2) IN ball(x0,&3 * rho)` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `w = \y:real^2. smooth_bump (&1) (&2) (inv rho % (y - x0)) *
                  (eps - ((phi:real^2->real) y - phi x0 -
                          ((y - x0) dot (H:real^2->real^2)(y - x0)) / &2))` THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `D:real^2->bool`; `x0:real^2`; `H:real^2->real^2`;
                 `C:real`; `M:real`; `rho:real`; `eps:real`; `w:real^2->real`]
    SCH3_W_PROPS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN EXPAND_TAC "w" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`w:real^2->real`; `rho:real`; `eps:real`; `L:real^2->real^2`;
                        `k1:real`; `k2:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y:real^2. (\z. lift((phi:real^2->real) z)) differentiable at y /\
                           (\z. lift((w:real^2->real) z)) differentiable at y
                           \/ ~(y IN ball(x0,&3 * rho))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN ASM_CASES_TAC `(y:real^2) IN ball(x0,&3 * rho)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `D:real^2->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^2` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&8 * C * rho pow 3`)) (concl th))) THEN
    MAP_EVERY UNDISCH_TAC [`eps < eta / &2`; `(&8 * C) * rho pow 3 <= eta / &2`] THEN
    REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`y:real^2`; `h:real^2`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(M * eps / rho + (&8 * M + &4) * C * rho pow 2) * norm(h:real^2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MAP_EVERY UNDISCH_TAC [`M * eps / rho <= eta / &2`;
                           `((&8 * M + &4) * C) * rho pow 2 <= eta / &2`] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `ball(x0:real^2,&3 * rho)`)) (concl th) &&
      can (find_term ((=) `C:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `norm(y - x0:real^2) < &3 * rho` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^2) IN ball(x0,&3 * rho)` THEN REWRITE_TAC[IN_BALL] THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(((y - x0:real^2) dot (H:real^2->real^2)(y - x0)) / &2) <=
                  NH / &2 * norm(y - x0) pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= NH * n ==> x / &2 <= NH / &2 * n`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(y - x0:real^2) * norm((H:real^2->real^2)(y - x0))` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(y - x0:real^2) * (NH * norm(y - x0))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
        REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `NH / &2 * norm(y - x0:real^2) pow 2 <= NH / &2 * (&9 * rho pow 2) /\
                  C * norm(y - x0:real^2) pow 3 <= C * (&27 * rho pow 2)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THENL
       [SUBGOAL_THEN `&9 * rho pow 2 = (&3 * rho) pow 2` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&3 * rho) pow 3` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
          REWRITE_TAC[REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          REWRITE_TAC[ARITH_RULE `3 = SUC 2`; real_pow] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]]];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(&9 / &2 * NH + &27 * C) * rho pow 2 <= eta`;
      `abs(((y - x0:real^2) dot (H:real^2->real^2)(y - x0)) / &2) <=
       NH / &2 * norm(y - x0) pow 2`;
      `NH / &2 * norm(y - x0:real^2) pow 2 <= NH / &2 * (&9 * rho pow 2)`;
      `C * norm(y - x0:real^2) pow 3 <= C * (&27 * rho pow 2)`] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\z. lift((phi:real^2->real) z)) differentiable at y /\
                  (\z. lift((w:real^2->real) z)) differentiable at y`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
        is_forall(concl th) && is_disj(snd(strip_forall(concl th))))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sch3_grad (\z. (phi:real^2->real) z + w z) y =
                  sch3_grad phi y + sch3_grad w y` ASSUME_TAC THENL
     [MATCH_MP_TAC SCH3_GRAD_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(y:real^2) IN ball(x0,rho)` THENL
     [SUBGOAL_THEN `sch3_grad (phi:real^2->real) y + sch3_grad w y =
                    (H:real^2->real^2)(y - x0)` SUBST1_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          can (find_term ((=) `sch3_grad (\z. (phi:real^2->real) z + w z) y`)) (concl th))) THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `sch3_grad (\z. (phi x0 + eps) +
                                   ((z - x0) dot (H:real^2->real^2)(z - x0)) / &2) y` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SCH3_GRAD_LOCAL THEN EXISTS_TAC `ball(x0:real^2,rho)` THEN
          ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
           [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
            FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
              is_forall(concl th) && can (find_term ((=) `ball(x0:real^2,rho)`)) (concl th))) THEN
            ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
            MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
            REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
            SUBGOAL_THEN `open(:real^2)` ASSUME_TAC THENL [REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
            SUBGOAL_THEN `smooth_map_on (:real^2) (\z. (H:real^2->real^2)(z - x0))`
            ASSUME_TAC THENL
             [SUBGOAL_THEN `(\z. (H:real^2->real^2)(z - x0)) = H o (\z. z - x0)`
              SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
              MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
              SCH3_SMOOTH_TAC;
              ALL_TAC] THEN
            SCH3_SMOOTH_TAC THEN REAL_ARITH_TAC];
          MATCH_MP_TAC SCH3_GRAD_QUAD THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      EQ_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `(H:real^2->real^2)(y - x0) = H(vec 0)` MP_TAC THENL
         [ASM_REWRITE_TAC[MATCH_MP LINEAR_0 (ASSUME `linear(H:real^2->real^2)`)];
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ASSUME
          `!x y:real^2. (H:real^2->real^2) x = H y ==> x = y`)) THEN
        VECTOR_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[VECTOR_SUB_REFL; MATCH_MP LINEAR_0 (ASSUME `linear(H:real^2->real^2)`)]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(y:real^2 = x0)` (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((y:real^2) IN ball(x0,rho))` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `rho <= norm(y - x0:real^2) /\ norm(y - x0:real^2) < &3 * rho`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~((y:real^2) IN ball(x0,rho))`;
                             `(y:real^2) IN ball(x0,&3 * rho)`] THEN
      REWRITE_TAC[IN_BALL] THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(sch3_grad (w:real^2->real) y) <=
                  M * eps / rho + (&8 * M + &4) * C * rho pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC SCH3_GRAD_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `norm(sch3_grad (phi:real^2->real) y - (H:real^2->real^2)(y - x0)) <=
                  C * (&9 * rho pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * norm(y - x0:real^2) pow 2` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `ball(x0:real^2,&3 * rho)`)) (concl th) &&
          can (find_term ((=) `C:real`)) (concl th))) THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        SUBGOAL_THEN `&9 * rho pow 2 = (&3 * rho) pow 2` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(y - x0:real^2) * lam <= norm((H:real^2->real^2)(y - x0))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `rho * lam <= norm(y - x0:real^2) * lam` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `((&8 * M + &13) * C) * rho pow 2 <= lam / &4 * rho` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm((H:real^2->real^2)(y - x0)) <=
                  norm(sch3_grad (phi:real^2->real) y - H(y - x0)) +
                  norm(sch3_grad (w:real^2->real) y)` ASSUME_TAC THENL
     [UNDISCH_TAC `sch3_grad (phi:real^2->real) y + sch3_grad w y = vec 0` THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < lam * rho` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`&0 < lam * rho`;
      `norm((H:real^2->real^2)(y - x0)) <=
       norm(sch3_grad (phi:real^2->real) y - H(y - x0)) + norm(sch3_grad (w:real^2->real) y)`;
      `((&8 * M + &13) * C) * rho pow 2 <= lam / &4 * rho`;
      `rho * lam <= norm(y - x0:real^2) * lam`;
      `norm(y - x0:real^2) * lam <= norm((H:real^2->real^2)(y - x0))`;
      `norm(sch3_grad (phi:real^2->real) y - (H:real^2->real^2)(y - x0)) <=
       C * (&9 * rho pow 2)`;
      `norm(sch3_grad (w:real^2->real) y) <= M * eps / rho + (&8 * M + &4) * C * rho pow 2`;
      `M * eps / rho < lam * rho / &2`] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `x0 + (L:real^2->real^2) u IN ball(x0,rho)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN UNDISCH_TAC `norm((L:real^2->real^2) u) < rho` THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x0 + (L:real^2->real^2) u` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `ball(x0:real^2,rho)`)) (concl th))) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(x0 + l) - x0:real^2 = l`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Vertical shears z |-> z + f(z) e3 are diffeomorphisms when                *)
(* the derivative of f is at most 1/2 (SMT_PERTURB_ID); the vertical cutoff. *)
(* ------------------------------------------------------------------------- *)

let SCH3_VSHEAR_DIFFEO = prove
 (`!f:real^3->real.
        smooth_map_on (:real^3) (\z. lift(f z)) /\
        (!z h. norm(frechet_derivative (\z. lift(f z)) (at z) h) <= &1 / &2 * norm h)
        ==> ?Psi'. diffeomorphism_on (:real^3) (:real^3) (\z. z + f z % basis 3) Psi'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(:3)` SMT_PERTURB_ID) THEN REWRITE_TAC[SMT_PERTURB_ID_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`\t:real z:real^3. (f:real^3->real) z % (basis 3:real^3)`; `&1 / &2`]) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV] THEN
      SUBGOAL_THEN `(\z:real^(1,3)finite_sum. (f:real^3->real)(sndcart z) % (basis 3:real^3)) =
                    (\x. f x % (basis 3:real^3)) o sndcart` SUBST1_TAC THENL
       [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(sndcart:real^(1,3)finite_sum->real^3) = sndcart o (\x. x)`
        SUBST1_TAC THENL [REWRITE_TAC[o_DEF; ETA_AX]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
        SUBGOAL_THEN `open(:real^3)` ASSUME_TAC THENL [REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
        SCH3_SMOOTH_TAC];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      MP_TAC(ISPECL [`\z:real^3. lift((f:real^3->real) z)`;
                     `\z:real^3. frechet_derivative (\z. lift((f:real^3->real) z)) (at z)`;
                     `(:real^3)`; `&1 / &2`] DIFFERENTIABLE_BOUND) THEN
      REWRITE_TAC[CONVEX_UNIV; IN_UNIV] THEN ANTS_TAC THENL
       [CONJ_TAC THEN X_GEN_TAC `z:real^3` THENL
         [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
          REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
          MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^3)` THEN
          ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
          SUBGOAL_THEN `linear(frechet_derivative (\z. lift((f:real^3->real) z)) (at z))`
          ASSUME_TAC THENL
           [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
            MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^3)` THEN
            ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
            ALL_TAC] THEN
          FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ONORM_LE_EQ th]) THEN
          ASM_REWRITE_TAC[]];
        DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `y:real^3`]) THEN
        REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT]]];
    DISCH_THEN(X_CHOOSE_THEN `G:real->real^3->real^3` MP_TAC) THEN
    REWRITE_TAC[diffeo_isotopy] THEN
    DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT2 o CONJUNCT2) THEN
    MESON_TAC[]]);;

(* The vertical cutoff around height c at scale delta.                        *)

let SCH3_VCUT = prove
 (`!c delta.
        &0 < delta
        ==> smooth_map_on (:real^3)
              (\z. lift(smooth_bump (&1) (&2) (lift((z$3 - c) / delta)))) /\
            (!z:real^3. abs(z$3 - c) <= delta
                        ==> smooth_bump (&1) (&2) (lift((z$3 - c) / delta)) = &1) /\
            (!z:real^3. &2 * delta <= abs(z$3 - c)
                        ==> smooth_bump (&1) (&2) (lift((z$3 - c) / delta)) = &0) /\
            (!z:real^3. &0 <= smooth_bump (&1) (&2) (lift((z$3 - c) / delta)) /\
                        smooth_bump (&1) (&2) (lift((z$3 - c) / delta)) <= &1) /\
            ?M1. &0 < M1 /\
                 !z h. norm(frechet_derivative
                              (\z:real^3. lift(smooth_bump (&1) (&2) (lift((z$3 - c) / delta))))
                              (at z) h) <= M1 / delta * norm h`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\z:real^3. lift((z$3 - c) / delta))` ASSUME_TAC THENL
   [SUBGOAL_THEN `open(:real^3)` ASSUME_TAC THENL [REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
    SCH3_SMOOTH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^1) (\x. lift(smooth_bump (&1) (&2) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^3)`; `(:real^1)`; `\x:real^1. lift(smooth_bump (&1) (&2) x)`;
                   `\z:real^3. lift((z$3 - c) / delta)`] SCH3_SV_COMPOSE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_1 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_LE_RDIV_EQ];
    REWRITE_TAC[SMOOTH_BUMP_BOUNDS];
    MP_TAC(ISPECL [`&1`; `&2`] (INST_TYPE [`:1`,`:N`] SCH3_BUMP_DERIV)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`z:real^3`; `h:real^3`] THEN
    SUBGOAL_THEN
     `((\z:real^3. lift(smooth_bump (&1) (&2) (lift((z$3 - c) / delta)))) has_derivative
       (frechet_derivative (\x. lift(smooth_bump (&1) (&2) x)) (at (lift((z$3 - c) / delta))) o
        (\h:real^3. lift(h$3 / delta)))) (at z)`
    MP_TAC THENL
     [MP_TAC(ISPECL [`\z:real^3. lift((z$3 - c) / delta)`;
                     `\x:real^1. lift(smooth_bump (&1) (&2) x)`;
                     `\h:real^3. lift(h$3 / delta)`;
                     `frechet_derivative (\x:real^1. lift(smooth_bump (&1) (&2) x))
                        (at (lift(((z:real^3)$3 - c) / delta)))`;
                     `z:real^3`] DIFF_CHAIN_AT) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        REWRITE_TAC[LIFT_CMUL; LIFT_SUB] THEN
        MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
        SUBGOAL_THEN `(\h:real^3. lift(h$3)) = (\h. lift(h$3) - vec 0)` SUBST1_TAC THENL
         [REWRITE_TAC[VECTOR_SUB_RZERO]; ALL_TAC] THEN
        MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
        MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT];
        REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^1)` THEN
        ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * norm(lift((h:real^3)$3 / delta))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M / delta * abs((h:real^3)$3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; COMPONENT_LE_NORM]]]);;

(* The shear function f(z) = beta(z) w(z$1,z$2) and its derivative bound.    *)

let SCH3_SHEAR_FN = prove
 (`!w:real^2->real c delta eta M1.
        &0 < delta /\ &0 <= eta /\ &0 < M1 /\
        smooth_map_on (:real^2) (\y. lift(w y)) /\
        (!y. abs(w y) <= eta) /\
        (!y h. norm(frechet_derivative (\y. lift(w y)) (at y) h) <= eta * norm h) /\
        (!z:real^3 h:real^3. norm(frechet_derivative
                      (\z:real^3. lift(smooth_bump (&1) (&2) (lift((z$3 - c) / delta))))
                      (at z) h) <= M1 / delta * norm h)
        ==> smooth_map_on (:real^3)
              (\z:real^3. lift(smooth_bump (&1) (&2) (lift((z$3 - c) / delta)) *
                        w(vector[z$1; z$2]))) /\
            (!z:real^3 h:real^3. norm(frechet_derivative
                          (\z:real^3. lift(smooth_bump (&1) (&2) (lift((z$3 - c) / delta)) *
                                    w(vector[z$1; z$2]))) (at z) h)
                   <= eta * (M1 / delta + &1) * norm h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real`; `delta:real`] SCH3_VCUT) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC `beta = \z:real^3. smooth_bump (&1) (&2) (lift((z$3 - c) / delta))` THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\z. lift((beta:real^3->real) z))` ASSUME_TAC THENL
   [EXPAND_TAC "beta" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\z:real^3. lift((w:real^2->real)(vector[z$1; z$2])))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^3)`; `(:real^2)`; `\y:real^2. lift((w:real^2->real) y)`;
                   `\z:real^3. vector[z$1; z$2]:real^2`] SCH3_SV_COMPOSE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `open(:real^3)` ASSUME_TAC THENL [REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
    SCH3_SMOOTH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^3. lift(smooth_bump (&1) (&2) (lift((z$3 - c) / delta)) *
                                  (w:real^2->real)(vector[z$1; z$2]))) =
                (\z. lift((beta:real^3->real) z * w(vector[z$1; z$2])))`
  SUBST1_TAC THENL [EXPAND_TAC "beta" THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `open(:real^3)` ASSUME_TAC THENL [REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
    SCH3_SMOOTH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:real^3`; `h:real^3`] THEN
  ABBREV_TAC `Db = frechet_derivative (\z. lift((beta:real^3->real) z)) (at z)` THEN
  ABBREV_TAC `Dw = frechet_derivative (\y. lift((w:real^2->real) y))
                     (at (vector[(z:real^3)$1; z$2]))` THEN
  SUBGOAL_THEN `((\z. lift((beta:real^3->real) z)) has_derivative Db) (at z)` ASSUME_TAC THENL
   [EXPAND_TAC "Db" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z:real^3. lift((w:real^2->real)(vector[z$1; z$2]))) has_derivative
     (\h. (Dw:real^2->real^1) (vector[h$1; h$2]))) (at z)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z:real^3. vector[z$1; z$2]:real^2`; `\y:real^2. lift((w:real^2->real) y)`;
                   `\z:real^3. vector[z$1; z$2]:real^2`; `Dw:real^2->real^1`; `z:real^3`]
      DIFF_CHAIN_AT) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT];
      EXPAND_TAC "Dw" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`beta:real^3->real`; `\h:real^3. drop((Db:real^3->real^1) h)`;
                 `\z:real^3. lift((w:real^2->real)(vector[z$1; z$2]))`;
                 `\h:real^3. (Dw:real^2->real^1)(vector[h$1; h$2])`; `z:real^3`]
    HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^3. lift((beta:real^3->real) z * (w:real^2->real)(vector[z$1; z$2]))) =
                (\z. beta z % lift(w(vector[z$1; z$2])))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o BETA_RULE) THEN
  BETA_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 * (eta * norm(h:real^3)) + (M1 / delta * norm h) * eta` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(x:real^1) <= a /\ norm(y:real^1) <= b ==> norm(x + y) <= a + b`) THEN
    REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "beta" THEN REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_ARITH
       `&0 <= x /\ x <= &1 ==> abs x <= &1`];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `eta * norm(vector[(h:real^3)$1; h$2]:real^2)` THEN
      CONJ_TAC THENL [EXPAND_TAC "Dw" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[NORM_LE; DOT_2; DOT_3; VECTOR_2] THEN
      MP_TAC(SPEC `(h:real^3)$3` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM NORM_1] THEN EXPAND_TAC "Db" THEN EXPAND_TAC "beta" THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[NORM_LIFT] THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Locality of critical points, graph charts and height                      *)
(* charts under maps that agree outside a compact region; affine height      *)
(* charts; the critical set after a local modification.                      *)
(* ------------------------------------------------------------------------- *)

let SCH3_VECTOR_ETA = prove
 (`(!v:real^2. vector[v$1; v$2] = v) /\
   (!p:real^3. vector[p$1; p$2; p$3] = p)`,
  CONJ_TAC THEN GEN_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_2; VECTOR_3]);;

(* Splitting real^3 = real^2 x real for norms.                              *)

let SCH3_NORM3_SPLIT = prove
 (`!z:real^3 x0:real^2 c.
        norm(z - vector[x0$1; x0$2; c]) <= norm(vector[z$1; z$2] - x0) + abs(z$3 - c) /\
        norm(vector[z$1; z$2] - x0) <= norm(z - vector[x0$1; x0$2; c]) /\
        abs(z$3 - c) <= norm(z - vector[x0$1; x0$2; c])`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `norm(vector[(z:real^3)$1; z$2] - x0:real^2) =
                norm(vector[z$1 - x0$1; z$2 - x0$2; &0]:real^3)` SUBST1_TAC THENL
   [REWRITE_TAC[NORM_EQ; DOT_2; DOT_3; VECTOR_2; VECTOR_3; VECTOR_SUB_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(z:real^3) - vector[(x0:real^2)$1; x0$2; c] =
                  vector[z$1 - x0$1; z$2 - x0$2; &0] + (z$3 - c) % basis 3`
    SUBST1_TAC THENL
     [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
               VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vector[(z:real^3)$1 - (x0:real^2)$1; z$2 - x0$2; &0]:real^3) +
                norm((z$3 - c) % basis 3:real^3)` THEN
    REWRITE_TAC[NORM_TRIANGLE; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID; REAL_LE_REFL];
    REWRITE_TAC[NORM_LE; DOT_3; VECTOR_3; VECTOR_SUB_COMPONENT] THEN
    MP_TAC(SPEC `(z:real^3)$3 - c` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`(z:real^3) - vector[(x0:real^2)$1; x0$2; c]`; `3`]
      COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_COMPONENT; VECTOR_3]]);;

(* The region where a vertical shear z |-> z + f z e3 is the identity, for  *)
(* f supported in a cylinder of radius a and half height b around p0.       *)

let SCH3_SHEAR_V = prove
 (`!f:real^3->real x0:real^2 c a b eta R1 V.
        (!z. abs(f z) <= eta) /\
        (!z. ~(f z = &0)
             ==> norm(vector[z$1; z$2] - x0) <= a /\ abs(z$3 - c) <= b) /\
        a + b + eta <= R1 /\
        V = {z:real^3 | a < norm(vector[z$1; z$2] - x0) \/
                        R1 < norm(z - vector[x0$1; x0$2; c])}
        ==> open V /\ (!z. z IN V ==> f z = &0) /\
            (!z. (z + f z % basis 3) IN V <=> z IN V)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fb") (CONJUNCTS_THEN2 (LABEL_TAC "fs")
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `!z:real^3. a < norm(vector[z$1; z$2] - x0:real^2) \/
                           R1 < norm(z - vector[x0$1; x0$2; c])
                           ==> f z = &0` ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN
    ASM_CASES_TAC `(f:real^3->real) z = &0` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fs" (MP_TAC o C MATCH_MP (ASSUME `~((f:real^3->real) z = &0)`)) THEN
    USE_THEN "fb" (MP_TAC o SPEC `z:real^3`) THEN
    MP_TAC(SPECL [`z:real^3`; `x0:real^2`; `c:real`] SCH3_NORM3_SPLIT) THEN
    UNDISCH_TAC `a + b + eta <= R1:real` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SET_RULE `{z:real^3 | P z \/ Q z} = {z | P z} UNION {z | Q z}`] THEN
    MATCH_MP_TAC OPEN_UNION THEN REWRITE_TAC[SCH3_OPEN_OUTSIDE_BALL] THEN
    MP_TAC(ISPECL [`\z:real^3. vector[z$1; z$2]:real^2`; `{y:real^2 | a < norm(y - x0)}`]
      CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    REWRITE_TAC[IN_ELIM_THM; SCH3_OPEN_OUTSIDE_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    REWRITE_TAC[SCH3_LINEAR_PROJ12];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^3` THEN
    ASM_CASES_TAC `(f:real^3->real) z = &0` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    USE_THEN "fs" (MP_TAC o C MATCH_MP (ASSUME `~((f:real^3->real) z = &0)`)) THEN
    USE_THEN "fb" (MP_TAC o SPEC `z:real^3`) THEN
    MP_TAC(SPECL [`z:real^3`; `x0:real^2`; `c:real`] SCH3_NORM3_SPLIT) THEN
    MP_TAC(SPECL [`z + (f:real^3->real) z % basis 3:real^3`; `x0:real^2`; `c:real`]
      SCH3_NORM3_SPLIT) THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_3; ARITH; REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID] THEN
    UNDISCH_TAC `a + b + eta <= R1:real` THEN REAL_ARITH_TAC]);;

(* Derivatives, hence critical points, only depend on the map near t.       *)

let SCH3_CRIT_LOCAL = prove
 (`!g g':real^3->real^3 g1 t V.
        sch_neck g g' /\ open V /\ t IN sphere(vec 0,&1) /\ g t IN V /\
        (!s. g s IN V ==> g1 s = g s)
        ==> (sch_crit g1 t <=> sch_crit g t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))))) THEN
  SUBGOAL_THEN `frechet_derivative (g1:real^3->real^3) (at t) =
                frechet_derivative g (at t)`
    (fun th -> REWRITE_TAC[sch_crit; th]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  SUBGOAL_THEN `(t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) differentiable at t` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) continuous at t` MP_TAC THENL
   [ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT]; ALL_TAC] THEN
  MP_TAC(ISPEC `V:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^3->real^3) t`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `d:real`] THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  X_GEN_TAC `s:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  USE_THEN "loc" MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[]);;

(* Height charts only depend on the surface near the point.                 *)

let SCH3_HCHART_LOCAL = prove
 (`!s s' (p:real^3) k1 k2 V.
        sch_hchart s p k1 k2 /\ open V /\ p IN V /\ s INTER V = s' INTER V
        ==> sch_hchart s' p k1 k2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_hchart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `ph:real^2->real^2`
       (X_CHOOSE_THEN `ph':real^2->real^2` STRIP_ASSUME_TAC)))))
     STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `V:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(ph:real^2->real^2) continuous at (vec 0)` MP_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `ball(vec 0:real^2,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    UNDISCH_TAC `diffeomorphism_on (ball(vec 0,r)) (IMAGE (ph:real^2->real^2) (ball(vec 0,r)))
                   ph ph'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r (min d (e / &2))` THEN
  MAP_EVERY EXISTS_TAC [`ph:real^2->real^2`; `ph':real^2->real^2`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SCH4_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^2,r)`;
                          `IMAGE (ph:real^2->real^2) (ball(vec 0,r))`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`u:real^2`; `z:real`] THEN
    REWRITE_TAC[IN_BALL_0; REAL_LT_MIN] THEN STRIP_TAC THEN
    SUBGOAL_THEN `vector[(ph:real^2->real^2) u$1; ph u$2; z]:real^3 IN V`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
      MP_TAC(SPECL [`vector[(ph:real^2->real^2) u$1; ph u$2; z]:real^3`;
                    `vector[(p:real^3)$1; p$2]:real^2`; `(p:real^3)$3`]
        SCH3_NORM3_SPLIT) THEN
      REWRITE_TAC[VECTOR_2; VECTOR_3; SCH3_VECTOR_ETA] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real^2`) THEN
      ASM_REWRITE_TAC[DIST_0; dist] THEN
      UNDISCH_TAC `abs(z - (p:real^3)$3) < e / &2` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^2`; `z:real`]) THEN
    ASM_REWRITE_TAC[IN_BALL_0] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) INTER V = s' INTER V /\ x IN V
                           ==> (x IN s' <=> x IN s)`) THEN
    ASM_REWRITE_TAC[]]);;

(* Images of a set under maps that agree on the preimage of V.               *)

let SCH3_IMAGE_LOCAL = prove
 (`!g g1:real^3->real^3 V S.
        (!s. s IN S ==> (g1 s IN V <=> g s IN V)) /\
        (!s. g s IN V ==> g1 s = g s)
        ==> IMAGE g S INTER V = IMAGE g1 S INTER V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
  EQ_TAC THEN STRIP_TAC THEN CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* Graph representations, and so nondegeneracy, are local as well.          *)

let SCH3_GRAPH_LOCAL = prove
 (`!g g1:real^3->real^3 t D (phi:real^2->real) sigma V.
        sch3_graph g t D phi sigma /\ open V /\ g t IN V /\
        (!s. s IN sphere(vec 0,&1) ==> (g1 s IN V <=> g s IN V)) /\
        (!s. g s IN V ==> g1 s = g s)
        ==> sch3_graph g1 t {y | y IN D /\ vector[y$1; y$2; phi y] IN V} phi sigma`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch3_graph] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
       (LABEL_TAC "gr") (X_CHOOSE_THEN `W:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
         (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wp"))))))))))
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "iff") (LABEL_TAC "loc"))))) THEN
  SUBGOAL_THEN `(g1:real^3->real^3) t = g t` SUBST1_TAC THENL
   [USE_THEN "loc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{y | y IN D /\ vector[y$1; y$2; (phi:real^2->real) y] IN (V:real^3->bool)}
                SUBSET D` ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN SCH3_SMOOTH_TAC;
    ASM_REWRITE_TAC[];
    USE_THEN "gr" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `vector[(g:real^3->real^3) t$1; g t$2] IN (D:real^2->bool)`))) THEN
    REWRITE_TAC[ASSUME `(sigma:real^2->real^3)(vector[(g:real^3->real^3) t$1; g t$2]) = t`] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `D:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `D:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
    USE_THEN "gr" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^2) IN D`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(g1:real^3->real^3)((sigma:real^2->real^3) y) = g(sigma y)` SUBST1_TAC
    THENL [USE_THEN "loc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    EXISTS_TAC `W INTER V:real^3->bool` THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[OPEN_INTER]; ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    X_GEN_TAC `s:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    USE_THEN "iff" (MP_TAC o C MATCH_MP (ASSUME `(s:real^3) IN sphere(vec 0,&1)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g1:real^3->real^3) s = g s` SUBST_ALL_TAC THENL
     [USE_THEN "loc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "wp" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(s:real^3) IN sphere(vec 0,&1)`)
            (ASSUME `(g:real^3->real^3) s IN W`)))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
    USE_THEN "gr" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `vector[(g:real^3->real^3) s$1; g s$2] IN (D:real^2->bool)`))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
    ASM_REWRITE_TAC[]]);;

let SCH3_NONDEG_LOCAL = prove
 (`!g g1:real^3->real^3 t V.
        sch3_nondeg g t /\ open V /\ g t IN V /\
        (!s. s IN sphere(vec 0,&1) ==> (g1 s IN V <=> g s IN V)) /\
        (!s. g s IN V ==> g1 s = g s)
        ==> sch3_nondeg g1 t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch3_nondeg] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `D:real^2->bool` (X_CHOOSE_THEN
    `phi:real^2->real` (X_CHOOSE_THEN `sigma:real^2->real^3` STRIP_ASSUME_TAC)))
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(g1:real^3->real^3) t = g t` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`{y | y IN D /\ vector[y$1; y$2; (phi:real^2->real) y] IN (V:real^3->bool)}`;
    `phi:real^2->real`; `sigma:real^2->real^3`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH3_GRAPH_LOCAL THEN
  EXISTS_TAC `g:real^3->real^3` THEN ASM_REWRITE_TAC[]);;

(* Affine height charts.                                                      *)

let SCH3_SMOOTH_AFFINE = prove
 (`!s (L:real^M->real^N) x0.
        open s /\ linear L ==> smooth_map_on s (\u. x0 + L u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\u:real^M. u`; `L:real^M->real^N`]
    SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN
  SUBGOAL_THEN `(L:real^M->real^N) o (\u. u) = L` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\u:real^M. x0:real^N`; `L:real^M->real^N`]
    SMOOTH_MAP_ON_ADD_OPEN) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let SCH3_AFFINE_DIFFEO = prove
 (`!(L:real^2->real^2) x0 r.
        linear L /\ (!u v. L u = L v ==> u = v)
        ==> ?ph'. diffeomorphism_on (ball(vec 0,r))
                                    (IMAGE (\u. x0 + L u) (ball(vec 0,r)))
                                    (\u. x0 + L u) ph'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `L:real^2->real^2` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L':real^2->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(L:real^2->real^2) o (L':real^2->real^2) = I` MP_TAC THENL
   [ASM_MESON_TAC[LINEAR_INVERSE_LEFT]; ALL_TAC] THEN
  UNDISCH_TAC `(L':real^2->real^2) o (L:real^2->real^2) = I` THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN REPEAT DISCH_TAC THEN
  EXISTS_TAC `\y:real^2. (L':real^2->real^2)(y - x0)` THEN
  SUBGOAL_THEN `IMAGE (\u:real^2. x0 + (L:real^2->real^2) u) (ball(vec 0,r)) =
                {y | (L':real^2->real^2)(y - x0) IN ball(vec 0,r)}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `y:real^2` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_ARITH `(x0 + a) - x0:real^2 = a`];
      DISCH_TAC THEN EXISTS_TAC `(L':real^2->real^2)(y - x0)` THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\y:real^2. (L':real^2->real^2)(y - x0))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y:real^2. (L':real^2->real^2)(y - x0)) = (\y. --(L' x0) + L' y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN ASM_SIMP_TAC[LINEAR_SUB] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[SCH3_SMOOTH_AFFINE; OPEN_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  REWRITE_TAC[OPEN_BALL; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN REWRITE_TAC[OPEN_BALL] THEN
    MP_TAC(ISPECL [`\y:real^2. (L':real^2->real^2)(y - x0)`; `(:real^2)`]
      CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SCH3_SMOOTH_AFFINE; OPEN_BALL];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ASM_REWRITE_TAC[VECTOR_ARITH `(x0 + a) - x0:real^2 = a`];
    ASM_REWRITE_TAC[VECTOR_ARITH `x0 + (y - x0):real^2 = y`]]);;

let SCH3_HCHART_AFFINE = prove
 (`!s1 (p1:real^3) (L:real^2->real^2) k1 k2 rho r.
        (k1 = &1 \/ k1 = -- &1) /\ (k2 = &1 \/ k2 = -- &1) /\
        linear L /\ (!u v. L u = L v ==> u = v) /\ &0 < rho /\ &0 < r /\
        (!u z. norm(L u) < rho /\ abs(z - p1$3) < r
               ==> (vector[(vector[p1$1; p1$2] + L u:real^2)$1;
                           (vector[p1$1; p1$2] + L u:real^2)$2; z] IN s1 <=>
                    z = p1$3 + k1 * (u$1) pow 2 + k2 * (u$2) pow 2))
        ==> sch_hchart s1 p1 k1 k2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[sch_hchart] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o MATCH_MP LINEAR_BOUNDED_POS) THEN
  MP_TAC(ISPECL [`L:real^2->real^2`; `vector[(p1:real^3)$1; p1$2]:real^2`;
                 `min (min r (rho / B)) (&1 / &2)`] SCH3_AFFINE_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `ph':real^2->real^2`) THEN
  MAP_EVERY EXISTS_TAC [`min (min r (rho / B)) (&1 / &2)`;
                        `\u:real^2. vector[(p1:real^3)$1; p1$2] + (L:real^2->real^2) u`;
                        `ph':real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < rho / B` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP LINEAR_0) THEN REWRITE_TAC[VECTOR_ADD_RID];
    MAP_EVERY X_GEN_TAC [`u:real^2`; `z:real`] THEN
    REWRITE_TAC[IN_BALL_0; REAL_LT_MIN] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `B * norm(u:real^2)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `norm(u:real^2) < rho / B` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The critical set after a modification that is the identity               *)
(* off V and a known graph near the remaining points; the choice of the     *)
(* working radius around one critical point.                                 *)
(* ------------------------------------------------------------------------- *)

let SCH3_STEP_CRIT_EQ = prove
 (`!g g':real^3->real^3 g1 g1' t0 V (E:real^2->bool) sigma psi1 x0.
        sch_neck g g' /\ sch_neck g1 g1' /\ open V /\ open E /\ x0 IN E /\
        (!s. g s IN V ==> g1 s = g s) /\
        (!s. s IN sphere(vec 0,&1) /\ ~(g s IN V) ==> ?y. y IN E /\ s = sigma y) /\
        smooth_map_on E sigma /\ smooth_map_on E (\y. lift(psi1 y)) /\
        (!y. y IN E ==> sigma y IN sphere(vec 0,&1) /\
                        g1(sigma y) = vector[y$1; y$2; psi1 y]) /\
        (!y. y IN E ==> (sch3_grad psi1 y = vec 0 <=> y = x0)) /\ sigma x0 = t0 /\
        (!s. s IN sphere(vec 0,&1) /\ ~(g s IN V) ==> (sch_crit g s <=> s = t0))
        ==> !s. sch_crit g1 s <=> sch_crit g s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "loc") (CONJUNCTS_THEN2 (LABEL_TAC "cov")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "gr") (CONJUNCTS_THEN2 (LABEL_TAC "gd")
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cr"))))))))))))) THEN
  X_GEN_TAC `s:real^3` THEN
  ASM_CASES_TAC `(s:real^3) IN sphere(vec 0,&1)` THENL
   [ALL_TAC; ASM_REWRITE_TAC[sch_crit]] THEN
  ASM_CASES_TAC `(g:real^3->real^3) s IN V` THENL
   [MATCH_MP_TAC SCH3_CRIT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `V:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "cr" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ
    (ASSUME `(s:real^3) IN sphere(vec 0,&1)`) (ASSUME `~((g:real^3->real^3) s IN V)`))]) THEN
  USE_THEN "cov" (MP_TAC o C MATCH_MP (CONJ
    (ASSUME `(s:real^3) IN sphere(vec 0,&1)`) (ASSUME `~((g:real^3->real^3) s IN V)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^2` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  MP_TAC(ISPECL [`g1:real^3->real^3`; `g1':real^3->real^3`; `sigma:real^2->real^3`;
                 `psi1:real^2->real`; `E:real^2->bool`; `y:real^2`] SCH3_CRIT_GRAPH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  USE_THEN "gd" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^2) IN E`)]) THEN
  EQ_TAC THENL [DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "gr" (MP_TAC o C MATCH_MP (ASSUME `(y:real^2) IN E`)) THEN
  USE_THEN "gr" (MP_TAC o C MATCH_MP (ASSUME `(x0:real^2) IN E`)) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(MP_TAC o CONJUNCT2)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  SUBGOAL_THEN `vector[(y:real^2)$1; y$2; (psi1:real^2->real) y]:real^3 =
                vector[(x0:real^2)$1; x0$2; psi1 x0]` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_3] THEN
  MESON_TAC[]);;

(* The working radius around a critical point t0 with graph data.            *)

let SCH3_STEP_R0 = prove
 (`!g g':real^3->real^3 t0 W (D:real^2->bool) x0.
        sch_neck g g' /\ FINITE {t | sch_crit g t} /\ sch_crit g t0 /\
        open W /\ g t0 IN W /\ open D /\ x0 IN D
        ==> ?R0. &0 < R0 /\ ball(g t0,R0) SUBSET W /\ ball(x0,R0) SUBSET D /\
                 !t. sch_crit g t /\ ~(t = t0) ==> R0 < norm(g t - g t0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `W:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^3->real^3) t0`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `D:real^2->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x0:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(g:real^3->real^3) t0`; `IMAGE (g:real^3->real^3) {t | sch_crit g t}`]
    FINITE_SET_AVOID) THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e1 (min e2 (d / &2))` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball((g:real^3->real^3) t0,e1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x0:real^2,e2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((g:real^3->real^3) t = g t0)` ASSUME_TAC THENL
     [SUBGOAL_THEN `!x:real^3. x IN annulus (&1 / &2) (&2) ==> g'((g:real^3->real^3) x) = x`
      ASSUME_TAC THENL [ASM_MESON_TAC[SCH4_NECK_FACTS]; ALL_TAC] THEN
      SUBGOAL_THEN `(t:real^3) IN annulus (&1 / &2) (&2) /\ (t0:real^3) IN annulus (&1 / &2) (&2)`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET; SCH3_CRIT_IN_SPHERE]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^3->real^3) t`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC]);;

(* The effect of a vertical shear supported near one critical point t0:     *)
(* critical points are unchanged, the surface near g1 t0 is an exact affine  *)
(* quadratic graph at the new height c + eps, and everything near the other  *)
(* critical points is unchanged.                                             *)

let SCH3_STEP_ANALYSIS = prove
 (`!g g':real^3->real^3 g1 g1' t0 (D:real^2->bool) (phi:real^2->real) sigma W x0 c R0
    (f:real^3->real) w rho delta eta eps (L:real^2->real^2) k1 k2 Bv.
        sch_neck g g' /\ sch_neck g1 g1' /\
        (!s. g1 s = g s + f(g s) % basis 3) /\
        sch_crit g t0 /\ g t0 = vector[x0$1; x0$2; c] /\ phi x0 = c /\
        open D /\ smooth_map_on D (\y. lift(phi y)) /\ smooth_map_on D sigma /\
        sigma x0 = t0 /\
        (!y. y IN D ==> sigma y IN sphere(vec 0,&1) /\
                        g(sigma y) = vector[y$1; y$2; phi y]) /\
        ball(vector[x0$1; x0$2; c],R0) SUBSET W /\
        (!s. s IN sphere(vec 0,&1) /\ g s IN W
             ==> vector[(g s)$1; (g s)$2] IN D /\
                 s = sigma(vector[(g s)$1; (g s)$2])) /\
        (!t. sch_crit g t /\ ~(t = t0) ==> R0 < norm(g t - vector[x0$1; x0$2; c])) /\
        &0 < rho /\ ball(x0,&3 * rho) SUBSET D /\ &0 <= eps /\ eps <= eta /\
        &8 * rho <= R0 /\ &8 * delta <= R0 /\ &32 * eta <= R0 /\
        (!z. abs(f z) <= eta) /\
        (!z. ~(f z = &0)
             ==> norm(vector[z$1; z$2] - x0) <= &2 * rho /\ abs(z$3 - c) <= &2 * delta) /\
        (!y. y IN ball(x0,&3 * rho) ==> f(vector[y$1; y$2; phi y]) = w y) /\
        smooth_map_on (:real^2) (\y. lift(w y)) /\
        (!y. y IN ball(x0,&3 * rho)
             ==> (sch3_grad (\z. phi z + w z) y = vec 0 <=> y = x0)) /\
        linear L /\
        (!u. norm(L u) < rho
             ==> phi(x0 + L u) + w(x0 + L u) =
                 c + eps + k1 * (u$1) pow 2 + k2 * (u$2) pow 2) /\
        (!t. sch_crit g t /\ ~(t = t0) ==> (g t)$3 IN Bv) /\ ~(c + eps IN Bv)
        ==> (!t. sch_crit g1 t <=> sch_crit g t) /\
            g1 t0 = vector[x0$1; x0$2; c + eps] /\
            (!u z. norm(L u) < rho /\ abs(z - (c + eps)) < R0 / &8
                   ==> (vector[(x0 + L u)$1; (x0 + L u)$2; z] IN
                          IMAGE g1 (sphere(vec 0,&1)) <=>
                        z = (c + eps) + k1 * (u$1) pow 2 + k2 * (u$2) pow 2)) /\
            (!t. sch_crit g t /\ ~(t = t0) ==> ~((g1 t0)$3 = (g t)$3)) /\
            (!t. sch_crit g t /\ ~(t = t0)
                 ==> g1 t = g t /\
                     (!k1 k2. sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) k1 k2
                              ==> sch_hchart (IMAGE g1 (sphere(vec 0,&1))) (g t) k1 k2) /\
                     (sch3_nondeg g t ==> sch3_nondeg g1 t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,th) -> LABEL_TAC s th)
    (zip ["nk";"nk1";"g1d";"c0";"gt0";"phx0";"oD";"sphi";"ssig";"sx0";"gr";"bW";"wp";
          "far";"rho";"bD";"eps0";"epse";"r8";"d8";"e32";"fb";"fs";"fw";"sw";"gd";
          "lin";"quad";"bv";"nbv"] (CONJUNCTS th))) THEN
  SUBGOAL_THEN `&0 <= eta /\ &0 < R0` STRIP_ASSUME_TAC THENL
   [USE_THEN "fb" (MP_TAC o SPEC `vec 0:real^3`) THEN
    USE_THEN "rho" MP_TAC THEN USE_THEN "r8" MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `R1 = &2 * rho + &2 * delta + eta` THEN
  SUBGOAL_THEN `R1 < R0` ASSUME_TAC THENL
   [EXPAND_TAC "R1" THEN
    MAP_EVERY (fun l -> USE_THEN l MP_TAC) ["r8"; "d8"; "e32"; "rho"] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `V = {z:real^3 | &2 * rho < norm(vector[z$1; z$2] - x0:real^2) \/
                              R1 < norm(z - vector[(x0:real^2)$1; x0$2; c])}` THEN
  MP_TAC(ISPECL [`f:real^3->real`; `x0:real^2`; `c:real`; `&2 * rho`; `&2 * delta`;
                 `eta:real`; `R1:real`; `V:real^3->bool`] SCH3_SHEAR_V) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "fb" ACCEPT_TAC; USE_THEN "fs" ACCEPT_TAC;
      EXPAND_TAC "R1" THEN REAL_ARITH_TAC; EXPAND_TAC "V" THEN REFL_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "v0") (LABEL_TAC "vi")))] THEN
  SUBGOAL_THEN `!s. (g:real^3->real^3) s IN V ==> g1 s = g s` (LABEL_TAC "V1") THENL
   [X_GEN_TAC `s:real^3` THEN DISCH_TAC THEN USE_THEN "g1d" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "v0" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(g:real^3->real^3) s IN V`)]) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. (g1:real^3->real^3) s IN V <=> g s IN V` (LABEL_TAC "V2") THENL
   [X_GEN_TAC `s:real^3` THEN USE_THEN "g1d" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "vi" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. ~(z IN V)
                ==> norm(vector[z$1; z$2] - x0:real^2) <= &2 * rho /\
                    norm(z - vector[(x0:real^2)$1; x0$2; c]) <= R1`
  (LABEL_TAC "V3") THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM; DE_MORGAN_THM; REAL_NOT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(x0:real^2,&3 * rho)
                    ==> (sigma:real^2->real^3) y IN sphere(vec 0,&1) /\
                        (g1:real^3->real^3)(sigma y) =
                        vector[y$1; y$2; (phi:real^2->real) y + w y]`
  (LABEL_TAC "G1") THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN D` ASSUME_TAC THENL
     [USE_THEN "bD" (MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "gr" (MP_TAC o C MATCH_MP (ASSUME `(y:real^2) IN D`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gy")) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "g1d" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "gy" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "fw" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(y:real^2) IN ball(x0,&3 * rho)`)]) THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN sphere(vec 0,&1) /\ ~((g:real^3->real^3) s IN V)
                    ==> vector[(g s)$1; (g s)$2] IN ball(x0:real^2,&3 * rho) /\
                        s = (sigma:real^2->real^3)(vector[(g s)$1; (g s)$2])`
  (LABEL_TAC "CV") THENL
   [X_GEN_TAC `s:real^3` THEN STRIP_TAC THEN
    USE_THEN "V3" (MP_TAC o C MATCH_MP (ASSUME `~((g:real^3->real^3) s IN V)`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(g:real^3->real^3) s IN W` ASSUME_TAC THENL
     [USE_THEN "bW" (MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
      UNDISCH_TAC `R1 < R0` THEN
      UNDISCH_TAC `norm((g:real^3->real^3) s - vector[(x0:real^2)$1; x0$2; c]) <= R1` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "wp" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(s:real^3) IN sphere(vec 0,&1)`)
                                              (ASSUME `(g:real^3->real^3) s IN W`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> REWRITE_TAC[GSYM th])) THEN
    REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    UNDISCH_TAC `norm(vector[(g:real^3->real^3) s$1; g s$2] - x0:real^2) <= &2 * rho` THEN
    USE_THEN "rho" MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open(ball(x0:real^2,&3 * rho)) /\ x0 IN ball(x0,&3 * rho) /\
                smooth_map_on (ball(x0,&3 * rho)) (sigma:real^2->real^3) /\
                smooth_map_on (ball(x0,&3 * rho)) (\y. lift((phi:real^2->real) y + w y))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "rho" MP_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `D:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
       [EXISTS_TAC `D:real^2->bool`; EXISTS_TAC `(:real^2)`] THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN sphere(vec 0,&1) /\ ~((g:real^3->real^3) s IN V)
                    ==> ?y. y IN ball(x0:real^2,&3 * rho) /\ s = (sigma:real^2->real^3) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `vector[(g:real^3->real^3) s$1; g s$2]:real^2` THEN
    USE_THEN "CV" (fun th -> ACCEPT_TAC(MATCH_MP th (ASSUME
      `s IN sphere(vec 0,&1) /\ ~((g:real^3->real^3) s IN V)`)));
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN sphere(vec 0,&1) /\ ~((g:real^3->real^3) s IN V)
                    ==> (sch_crit g s <=> s = t0)` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3` THEN STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_CASES_TAC `s:real^3 = t0` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "far" (MP_TAC o C MATCH_MP (CONJ (ASSUME `sch_crit (g:real^3->real^3) s`)
                                                 (ASSUME `~(s:real^3 = t0)`))) THEN
      USE_THEN "V3" (MP_TAC o C MATCH_MP (ASSUME `~((g:real^3->real^3) s IN V)`)) THEN
      UNDISCH_TAC `R1 < R0` THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN USE_THEN "c0" ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `g1:real^3->real^3`;
                 `g1':real^3->real^3`; `t0:real^3`; `V:real^3->bool`;
                 `ball(x0:real^2,&3 * rho)`; `sigma:real^2->real^3`;
                 `\z:real^2. (phi:real^2->real) z + w z`; `x0:real^2`]
    SCH3_STEP_CRIT_EQ) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(LABEL_TAC "C1")] THEN
  SUBGOAL_THEN `(w:real^2->real) x0 = eps` ASSUME_TAC THENL
   [USE_THEN "quad" (MP_TAC o SPEC `vec 0:real^2`) THEN
    USE_THEN "lin" (fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
    REWRITE_TAC[NORM_0; VECTOR_ADD_RID; VEC_COMPONENT] THEN
    USE_THEN "phx0" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "rho" (fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(g1:real^3->real^3) t0 = vector[(x0:real^2)$1; x0$2; c + eps]`
  (LABEL_TAC "C2") THENL
   [USE_THEN "g1d" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "gt0" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "fw" (MP_TAC o C MATCH_MP (ASSUME `(x0:real^2) IN ball(x0,&3 * rho)`)) THEN
    USE_THEN "phx0" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u z. norm((L:real^2->real^2) u) < rho /\ abs(z - (c + eps)) < R0 / &8
          ==> (vector[(x0 + L u:real^2)$1; (x0 + L u:real^2)$2; z] IN
                 IMAGE (g1:real^3->real^3) (sphere(vec 0,&1)) <=>
               z = (c + eps) + k1 * (u$1) pow 2 + k2 * (u$2) pow 2)`
  (LABEL_TAC "C3") THENL
   [MAP_EVERY X_GEN_TAC [`u:real^2`; `z:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(phi:real^2->real)(x0 + L u) + w(x0 + L u) =
                  c + eps + k1 * ((u:real^2)$1) pow 2 + k2 * (u$2) pow 2`
    ASSUME_TAC THENL
     [USE_THEN "quad" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm((x0 + (L:real^2->real^2) u) - x0) < rho` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_ARITH `(x0 + a) - x0:real^2 = a`]; ALL_TAC] THEN
    ABBREV_TAC `y:real^2 = x0 + (L:real^2->real^2) u` THEN
    SUBGOAL_THEN `(y:real^2) IN ball(x0,&3 * rho)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
      UNDISCH_TAC `norm((y:real^2) - x0) < rho` THEN USE_THEN "rho" MP_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `((g:real^3->real^3) s)$1 = (y:real^2)$1 /\ (g s)$2 = y$2 /\
                    (g s)$3 + f(g s) = z` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `vector[(y:real^2)$1; y$2; z]:real^3 = (g1:real^3->real^3) s` THEN
        USE_THEN "g1d" (fun th -> REWRITE_TAC[th]) THEN
        SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^3->real^3) s IN W` ASSUME_TAC THENL
       [USE_THEN "bW" (MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
        MP_TAC(SPECL [`(g:real^3->real^3) s`; `x0:real^2`; `c:real`] SCH3_NORM3_SPLIT) THEN
        ASM_REWRITE_TAC[SCH3_VECTOR_ETA] THEN
        USE_THEN "fb" (MP_TAC o SPEC `(g:real^3->real^3) s`) THEN
        MAP_EVERY (fun l -> USE_THEN l MP_TAC) ["eps0"; "epse"; "r8"; "e32"] THEN
        UNDISCH_TAC `norm((y:real^2) - x0) < rho` THEN
        UNDISCH_TAC `abs(z - (c + eps)) < R0 / &8` THEN
        UNDISCH_TAC `((g:real^3->real^3) s)$3 + f(g s) = z` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "wp" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(s:real^3) IN sphere(vec 0,&1)`)
                                                (ASSUME `(g:real^3->real^3) s IN W`))) THEN
      ASM_REWRITE_TAC[SCH3_VECTOR_ETA] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
      UNDISCH_TAC `vector[(y:real^2)$1; y$2; z]:real^3 = g1((sigma:real^2->real^3) y)` THEN
      USE_THEN "G1" (fun th -> REWRITE_TAC[CONJUNCT2(MATCH_MP th
        (ASSUME `(y:real^2) IN ball(x0,&3 * rho)`))]) THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      UNDISCH_TAC `(phi:real^2->real) y + w y =
                   c + eps + k1 * ((u:real^2)$1) pow 2 + k2 * (u$2) pow 2` THEN
      REAL_ARITH_TAC;
      DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(sigma:real^2->real^3) y` THEN
      USE_THEN "G1" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(y:real^2) IN ball(x0,&3 * rho)`)]) THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      UNDISCH_TAC `z = (c + eps) + k1 * ((u:real^2)$1) pow 2 + k2 * (u$2) pow 2` THEN
      UNDISCH_TAC `(phi:real^2->real) y + w y =
                   c + eps + k1 * ((u:real^2)$1) pow 2 + k2 * (u$2) pow 2` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. sch_crit (g:real^3->real^3) t /\ ~(t = t0)
                    ==> ~((g1:real^3->real^3) t0$3 = g t$3)` (LABEL_TAC "C4") THENL
   [X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
    USE_THEN "C2" (fun th -> REWRITE_TAC[th; VECTOR_3]) THEN
    DISCH_TAC THEN USE_THEN "nbv" MP_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN USE_THEN "bv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. sch_crit (g:real^3->real^3) t /\ ~(t = t0) ==> g t IN V`
  (LABEL_TAC "inV") THENL
   [X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISJ2_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `R0:real` THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "far" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "C1" ACCEPT_TAC;
    USE_THEN "C2" ACCEPT_TAC;
    USE_THEN "C3" ACCEPT_TAC;
    USE_THEN "C4" ACCEPT_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
  USE_THEN "inV" (fun th -> ASSUME_TAC(MATCH_MP th
    (ASSUME `sch_crit (g:real^3->real^3) t /\ ~(t = t0)`))) THEN
  SUBGOAL_THEN `!s. s IN sphere(vec 0,&1)
                    ==> ((g1:real^3->real^3) s IN V <=> g s IN V)` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "V2" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "V1" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY X_GEN_TAC [`a1:real`; `a2:real`] THEN DISCH_TAC THEN
    MATCH_MP_TAC SCH3_HCHART_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`;
                          `V:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC SCH3_IMAGE_LOCAL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN MATCH_MP_TAC SCH3_NONDEG_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `V:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The local step. A nondegenerate critical point t0 is made                *)
(* an exact quadratic one at a height avoiding the other critical heights,   *)
(* by a vertical shear of R^3 supported near g t0.                           *)
(* ------------------------------------------------------------------------- *)

let SCH3_LOCAL_STEP = prove
 (`!g g':real^3->real^3 t0.
        sch_neck g g' /\ FINITE {t | sch_crit g t} /\ sch_crit g t0 /\
        sch3_nondeg g t0
        ==> ?Psi Psi' g1 g1'.
              diffeomorphism_on (:real^3) (:real^3) Psi Psi' /\
              sch_neck g1 g1' /\ g1 = Psi o g /\
              (!t. sch_crit g1 t <=> sch_crit g t) /\
              (?k1 k2. sch_hchart (IMAGE g1 (sphere(vec 0,&1))) (g1 t0) k1 k2) /\
              (!t. sch_crit g t /\ ~(t = t0) ==> ~((g1 t0)$3 = (g t)$3)) /\
              (!t. sch_crit g t /\ ~(t = t0)
                   ==> g1 t = g t /\
                       (!k1 k2. sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) k1 k2
                                ==> sch_hchart (IMAGE g1 (sphere(vec 0,&1))) (g t) k1 k2) /\
                       (sch3_nondeg g t ==> sch3_nondeg g1 t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "fin")
    (CONJUNCTS_THEN2 (LABEL_TAC "c0") (MP_TAC o REWRITE_RULE[sch3_nondeg; sch3_graph])))) THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^2->bool` (X_CHOOSE_THEN `phi:real^2->real`
    (X_CHOOSE_THEN `sigma:real^2->real^3` (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "det"))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "oD") (CONJUNCTS_THEN2 (LABEL_TAC "x0D")
    (CONJUNCTS_THEN2 (LABEL_TAC "sphi") (CONJUNCTS_THEN2 (LABEL_TAC "ssig")
    (CONJUNCTS_THEN2 (LABEL_TAC "sx0") (CONJUNCTS_THEN2 (LABEL_TAC "gr")
    (X_CHOOSE_THEN `W:real^3->bool` (CONJUNCTS_THEN2 (LABEL_TAC "oW")
    (CONJUNCTS_THEN2 (LABEL_TAC "gW") (LABEL_TAC "wp")))))))))) THEN
  SUBGOAL_THEN `?x0:real^2. vector[(g:real^3->real^3) t0$1; g t0$2] = x0`
  (X_CHOOSE_THEN `x0:real^2` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) t0 = vector[(x0:real^2)$1; x0$2; (phi:real^2->real) x0]`
  (LABEL_TAC "gt0") THENL
   [USE_THEN "gr" (MP_TAC o C MATCH_MP (ASSUME `(x0:real^2) IN D`)) THEN
    USE_THEN "sx0" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT2);
    ALL_TAC] THEN
  SUBGOAL_THEN `sch3_grad (phi:real^2->real) x0 = vec 0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `sigma:real^2->real^3`;
                   `phi:real^2->real`; `D:real^2->bool`; `x0:real^2`] SCH3_CRIT_GRAPH) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "sx0" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "c0" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  ABBREV_TAC `Bv = IMAGE (\t. (g:real^3->real^3) t$3) {t | sch_crit g t /\ ~(t = t0)}` THEN
  SUBGOAL_THEN `FINITE(Bv:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Bv" THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t | sch_crit (g:real^3->real^3) t}` THEN
    USE_THEN "fin" (fun th -> REWRITE_TAC[th]) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. sch_crit (g:real^3->real^3) t /\ ~(t = t0) ==> (g t)$3 IN Bv`
  ASSUME_TAC THENL
   [EXPAND_TAC "Bv" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t0:real^3`; `W:real^3->bool`;
                 `D:real^2->bool`; `x0:real^2`] SCH3_STEP_R0) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "gt0" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `R0:real` (CONJUNCTS_THEN2 (LABEL_TAC "R0p")
    (CONJUNCTS_THEN2 (LABEL_TAC "bW") (CONJUNCTS_THEN2 (LABEL_TAC "bD0")
     (LABEL_TAC "far"))))) THEN
  ABBREV_TAC `delta = R0 / &8` THEN
  MP_TAC(SPECL [`(phi:real^2->real) x0`; `delta:real`] SCH3_VCUT) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "delta" THEN USE_THEN "R0p" MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bsm") (CONJUNCTS_THEN2 (LABEL_TAC "b1")
    (CONJUNCTS_THEN2 (LABEL_TAC "b0") (CONJUNCTS_THEN2 (LABEL_TAC "b01")
    (X_CHOOSE_THEN `M1:real` (CONJUNCTS_THEN2 (LABEL_TAC "M1p") (LABEL_TAC "Mb"))))))) THEN
  ABBREV_TAC `eta = min (delta / &4) (inv(&2 * (M1 / delta + &1)))` THEN
  SUBGOAL_THEN `&0 < delta /\ &0 < eta /\ eta <= delta / &4 /\
                eta * (M1 / delta + &1) <= &1 / &2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < delta` ASSUME_TAC THENL
     [EXPAND_TAC "delta" THEN USE_THEN "R0p" MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < M1 / delta + &1` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < x + &1`) THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv(&2 * (M1 / delta + &1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN UNDISCH_TAC `&0 < M1 / delta + &1` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "eta" THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `&0 < delta` THEN UNDISCH_TAC `&0 < inv(&2 * (M1 / delta + &1))` THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&2 * (M1 / delta + &1)) * (M1 / delta + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; UNDISCH_TAC `&0 < M1 / delta + &1` THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < M1 / delta + &1` THEN
        SPEC_TAC(`M1 / delta + &1`,`KK:real`) THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `D:real^2->bool`; `x0:real^2`; `Bv:real->bool`;
                 `eta:real`; `R0 / &8`] SCH3_LOCAL_2D) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    USE_THEN "R0p" MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `eps:real` (X_CHOOSE_THEN `L:real^2->real^2`
    (X_CHOOSE_THEN `k1:real` (X_CHOOSE_THEN `k2:real` MP_TAC)))))) THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,th) -> LABEL_TAC s th)
    (zip ["rho0";"rhoR";"b3D";"eps0";"epse";"nbv";"wsm";"wsupp";"wb";"wd";"phib";"gd";
          "lin";"inj";"k1d";"k2d";"quad"] (CONJUNCTS th))) THEN
  (* The shear function f and the shear Psi. *)
  MP_TAC(ISPECL [`w:real^2->real`; `(phi:real^2->real) x0`; `delta:real`; `eta:real`;
                 `M1:real`] SCH3_SHEAR_FN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fsm") (LABEL_TAC "fD"))] THEN
  MP_TAC(ISPEC `\z:real^3. smooth_bump (&1) (&2) (lift((z$3 - (phi:real^2->real) x0) / delta)) *
                           (w:real^2->real)(vector[z$1; z$2])` SCH3_VSHEAR_DIFFEO) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "fsm" ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`z:real^3`; `h:real^3`] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `eta * (M1 / delta + &1) * norm(h:real^3)` THEN
    CONJ_TAC THENL [USE_THEN "fD" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    DISCH_THEN(X_CHOOSE_THEN `Psi':real^3->real^3` (LABEL_TAC "dPsi"))] THEN
  SUBGOAL_THEN `?f:real^3->real. !z. f z = smooth_bump (&1) (&2)
                    (lift((z$3 - (phi:real^2->real) x0) / delta)) *
                    (w:real^2->real)(vector[z$1; z$2])`
  (X_CHOOSE_THEN `f:real^3->real` (LABEL_TAC "fdef")) THENL
   [EXISTS_TAC `\z:real^3. smooth_bump (&1) (&2) (lift((z$3 - (phi:real^2->real) x0) / delta)) *
                           (w:real^2->real)(vector[z$1; z$2])` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?Psi:real^3->real^3. (!z. Psi z = z + (f:real^3->real) z % basis 3) /\
                diffeomorphism_on (:real^3) (:real^3) Psi Psi'`
  (X_CHOOSE_THEN `Psi:real^3->real^3` (CONJUNCTS_THEN2 (LABEL_TAC "Psid")
     (LABEL_TAC "dPsi2"))) THENL
   [EXISTS_TAC `\z:real^3. z + (f:real^3->real) z % basis 3` THEN REWRITE_TAC[] THEN
    USE_THEN "fdef" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "dPsi" ACCEPT_TAC;
    ALL_TAC] THEN
  (* Facts about f for the analysis. *)
  SUBGOAL_THEN `&0 <= eps /\ eps <= eta /\ &8 * rho <= R0 /\ &8 * delta <= R0 /\
                &32 * eta <= R0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun l -> USE_THEN l MP_TAC) ["eps0"; "epse"; "rhoR"] THEN
    UNDISCH_TAC `eta <= delta / &4` THEN EXPAND_TAC "delta" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. abs((f:real^3->real) z) <= eta` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "fdef" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    USE_THEN "b01" (MP_TAC o SPEC `z:real^3`) THEN
    USE_THEN "wb" (MP_TAC o SPEC `vector[(z:real^3)$1; z$2]:real^2`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. ~((f:real^3->real) z = &0)
                ==> norm(vector[z$1; z$2] - x0:real^2) <= &2 * rho /\
                    abs(z$3 - (phi:real^2->real) x0) <= &2 * delta` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "fdef" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `~((w:real^2->real)(vector[(z:real^3)$1; z$2]) = &0)` THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
      DISCH_TAC THEN USE_THEN "wsupp" MATCH_MP_TAC THEN
      REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
      UNDISCH_TAC `&2 * rho < norm(vector[(z:real^3)$1; z$2] - x0:real^2)` THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `~(smooth_bump (&1) (&2)
                      (lift(((z:real^3)$3 - (phi:real^2->real) x0) / delta)) = &0)` THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
      DISCH_TAC THEN USE_THEN "b0" MATCH_MP_TAC THEN
      UNDISCH_TAC `&2 * delta < abs((z:real^3)$3 - (phi:real^2->real) x0)` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(x0:real^2,&3 * rho)
                    ==> (f:real^3->real)(vector[y$1; y$2; (phi:real^2->real) y]) = w y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN USE_THEN "fdef" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[VECTOR_3; SCH3_VECTOR_ETA] THEN
    USE_THEN "b1" (MP_TAC o SPEC `vector[(y:real^2)$1; y$2; (phi:real^2->real) y]:real^3`) THEN
    REWRITE_TAC[VECTOR_3] THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eta:real` THEN CONJ_TAC THENL
       [USE_THEN "phib" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `eta <= delta / &4` THEN UNDISCH_TAC `&0 < delta` THEN
        REAL_ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_LID]];
    ALL_TAC] THEN
  (* The new neck. *)
  SUBGOAL_THEN `sch_neck ((Psi:real^3->real^3) o (g:real^3->real^3))
                         ((g':real^3->real^3) o (Psi':real^3->real^3))`
  (LABEL_TAC "nk1") THENL
   [REWRITE_TAC[sch_neck; IMAGE_o] THEN MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))` THEN CONJ_TAC THENL
     [USE_THEN "nk" (ACCEPT_TAC o REWRITE_RULE[sch_neck]); ALL_TAC] THEN
    MATCH_MP_TAC SCH4_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`] THEN
    USE_THEN "dPsi2" (fun th -> REWRITE_TAC[th; SUBSET_UNIV]) THEN
    USE_THEN "nk" (fun th -> REWRITE_TAC[MATCH_MP SCH4_NECK_FACTS th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`;
                 `(Psi:real^3->real^3) o (g:real^3->real^3)`;
                 `(g':real^3->real^3) o (Psi':real^3->real^3)`; `t0:real^3`;
                 `D:real^2->bool`; `phi:real^2->real`; `sigma:real^2->real^3`;
                 `W:real^3->bool`; `x0:real^2`; `(phi:real^2->real) x0`; `R0:real`;
                 `f:real^3->real`; `w:real^2->real`; `rho:real`; `delta:real`;
                 `eta:real`; `eps:real`; `L:real^2->real^2`; `k1:real`; `k2:real`;
                 `Bv:real->bool`] SCH3_STEP_ANALYSIS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THEN
    REWRITE_TAC[o_THM] THEN USE_THEN "Psid" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "C2")
    (CONJUNCTS_THEN2 (LABEL_TAC "C3") STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`Psi:real^3->real^3`; `Psi':real^3->real^3`;
                        `(Psi:real^3->real^3) o (g:real^3->real^3)`;
                        `(g':real^3->real^3) o (Psi':real^3->real^3)`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THEN
  MAP_EVERY EXISTS_TAC [`k1:real`; `k2:real`] THEN
  MATCH_MP_TAC SCH3_HCHART_AFFINE THEN
  MAP_EVERY EXISTS_TAC [`L:real^2->real^2`; `rho:real`; `R0 / &8`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [USE_THEN "R0p" MP_TAC THEN REAL_ARITH_TAC;
    USE_THEN "C2" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[VECTOR_3; SCH3_VECTOR_ETA] THEN USE_THEN "C3" ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Induction on the number of critical points that are not                  *)
(* yet in final form, and the main theorem SCH_GENERIC.                      *)
(* ------------------------------------------------------------------------- *)

(* A critical point in final form: an exact quadratic height chart, and a   *)
(* critical value not shared with any other critical point.                  *)

let sch3_good = new_definition
 `sch3_good (g:real^3->real^3) (t:real^3) <=>
    (?k1 k2. sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) k1 k2) /\
    (!t'. sch_crit g t' /\ (g t')$3 = (g t)$3 ==> t' = t)`;;

let SCH3_GOOD_STEP = prove
 (`!g g1:real^3->real^3 t0.
        (!t. sch_crit g1 t <=> sch_crit g t) /\
        (?k1 k2. sch_hchart (IMAGE g1 (sphere(vec 0,&1))) (g1 t0) k1 k2) /\
        (!t. sch_crit g t /\ ~(t = t0) ==> ~((g1 t0)$3 = (g t)$3)) /\
        (!t. sch_crit g t /\ ~(t = t0)
             ==> g1 t = g t /\
                 (!k1 k2. sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) k1 k2
                          ==> sch_hchart (IMAGE g1 (sphere(vec 0,&1))) (g t) k1 k2))
        ==> sch3_good g1 t0 /\
            (!t. sch_crit g t /\ ~(t = t0) /\ sch3_good g t ==> sch3_good g1 t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ce") (CONJUNCTS_THEN2 (LABEL_TAC "h0")
    (CONJUNCTS_THEN2 (LABEL_TAC "dh") (LABEL_TAC "per")))) THEN
  REWRITE_TAC[sch3_good] THEN CONJ_TAC THENL
   [CONJ_TAC THENL [USE_THEN "h0" ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real^3` THEN USE_THEN "ce" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    ASM_CASES_TAC `s:real^3 = t0` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "per" (MP_TAC o C MATCH_MP (CONJ (ASSUME `sch_crit (g:real^3->real^3) s`)
                                               (ASSUME `~(s:real^3 = t0)`))) THEN
    USE_THEN "dh" (MP_TAC o C MATCH_MP (CONJ (ASSUME `sch_crit (g:real^3->real^3) s`)
                                              (ASSUME `~(s:real^3 = t0)`))) THEN
    UNDISCH_TAC `((g1:real^3->real^3) s)$3 = (g1 t0)$3` THEN MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `k1:real` (X_CHOOSE_TAC `k2:real`))
                     (LABEL_TAC "uq")))) THEN
  USE_THEN "per" (MP_TAC o C MATCH_MP (CONJ (ASSUME `sch_crit (g:real^3->real^3) t`)
                                             (ASSUME `~(t:real^3 = t0)`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "eqt") (LABEL_TAC "hct")) THEN
  USE_THEN "eqt" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`k1:real`; `k2:real`] THEN USE_THEN "hct" MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:real^3` THEN USE_THEN "ce" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real^3 = t0` THENL
   [UNDISCH_TAC `((g1:real^3->real^3) s)$3 = ((g:real^3->real^3) t)$3` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "dh" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ
      (ASSUME `sch_crit (g:real^3->real^3) t`) (ASSUME `~(t:real^3 = t0)`))]);
    USE_THEN "uq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "per" (MP_TAC o C MATCH_MP (CONJ (ASSUME `sch_crit (g:real^3->real^3) s`)
                                               (ASSUME `~(s:real^3 = t0)`))) THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `((g1:real^3->real^3) s)$3 = ((g:real^3->real^3) t)$3` THEN
                         REWRITE_TAC[CONJUNCT1 th])]);;

(* Induction on the number of critical points not in final form.            *)

let SCH3_MORSE_INDUCT = prove
 (`!n g g':real^3->real^3.
        sch_neck g g' /\ FINITE {t | sch_crit g t} /\
        (!t. sch_crit g t /\ ~sch3_good g t ==> sch3_nondeg g t) /\
        CARD {t | sch_crit g t /\ ~sch3_good g t} = n
        ==> ?Phi Phi' g1 g1'.
              diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\
              sch_neck g1 g1' /\ sch_morse g1 /\
              IMAGE g1 (sphere(vec 0,&1)) = IMAGE Phi (IMAGE g (sphere(vec 0,&1)))`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `g':real^3->real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "fin")
    (CONJUNCTS_THEN2 (LABEL_TAC "nd") (LABEL_TAC "card")))) THEN
  ASM_CASES_TAC `{t | sch_crit (g:real^3->real^3) t /\ ~sch3_good g t} = {}` THENL
   [MAP_EVERY EXISTS_TAC [`\x:real^3. x`; `\x:real^3. x`; `g:real^3->real^3`;
                          `g':real^3->real^3`] THEN
    SIMP_TAC[DIFFEOMORPHISM_ON_ID; OPEN_UNIV; IMAGE_ID] THEN
    USE_THEN "nk" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `{t | sch_crit (g:real^3->real^3) t /\ ~sch3_good g t} = {}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; sch_morse] THEN
    REWRITE_TAC[TAUT `~(p /\ ~q) <=> (p ==> q)`; sch3_good] THEN DISCH_TAC THEN
    USE_THEN "fin" (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t0:real^3`] SCH3_LOCAL_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "nd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Psi:real^3->real^3` (X_CHOOSE_THEN `Psi':real^3->real^3`
    (X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
    (CONJUNCTS_THEN2 (LABEL_TAC "dPsi") (CONJUNCTS_THEN2 (LABEL_TAC "nk1")
    (CONJUNCTS_THEN2 (LABEL_TAC "g1e") (CONJUNCTS_THEN2 (LABEL_TAC "ce")
    (CONJUNCTS_THEN2 (LABEL_TAC "h0") (CONJUNCTS_THEN2 (LABEL_TAC "dh")
     (LABEL_TAC "per"))))))))))) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g1:real^3->real^3`; `t0:real^3`] SCH3_GOOD_STEP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    USE_THEN "per" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `sch_crit (g:real^3->real^3) t /\ ~(t = t0)`)]);
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gd0") (LABEL_TAC "gdp"))] THEN
  SUBGOAL_THEN `{t | sch_crit (g1:real^3->real^3) t /\ ~sch3_good g1 t} SUBSET
                {t | sch_crit (g:real^3->real^3) t /\ ~sch3_good g t} DELETE t0`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE] THEN X_GEN_TAC `t:real^3` THEN
    USE_THEN "ce" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(t:real^3 = t0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~sch3_good (g1:real^3->real^3) t0` THEN
      USE_THEN "gd0" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~sch3_good (g1:real^3->real^3) t` THEN REWRITE_TAC[] THEN
    USE_THEN "gdp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {t | sch_crit (g:real^3->real^3) t /\ ~sch3_good g t}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t | sch_crit (g:real^3->real^3) t}` THEN
    USE_THEN "fin" (fun th -> REWRITE_TAC[th]) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [USE_THEN "card" (SUBST1_TAC o SYM) THEN
    SIMP_TAC[CARD_EQ_0; ASSUME `FINITE {t | sch_crit (g:real^3->real^3) t /\
                                            ~sch3_good g t}`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {t | sch_crit (g1:real^3->real^3) t /\ ~sch3_good g1 t} < n`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `CARD({t | sch_crit (g:real^3->real^3) t /\ ~sch3_good g t} DELETE t0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC[FINITE_DELETE];
      ASM_SIMP_TAC[CARD_DELETE; IN_ELIM_THM] THEN
      UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`g1:real^3->real^3`; `g1':real^3->real^3`] o
    C MATCH_MP (ASSUME `CARD {t | sch_crit (g1:real^3->real^3) t /\
                                  ~sch3_good g1 t} < n`)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "nk1" ACCEPT_TAC;
      USE_THEN "ce" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "fin" ACCEPT_TAC;
      X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(t:real^3) IN
                    {t | sch_crit (g:real^3->real^3) t /\ ~sch3_good g t} DELETE t0`
      MP_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN STRIP_TAC THEN
      USE_THEN "per" (MP_TAC o C MATCH_MP (CONJ (ASSUME `sch_crit (g:real^3->real^3) t`)
                                                 (ASSUME `~(t:real^3 = t0)`))) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      USE_THEN "nd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REFL_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->real^3` (X_CHOOSE_THEN `Phi':real^3->real^3`
    (X_CHOOSE_THEN `g2:real^3->real^3` (X_CHOOSE_THEN `g2':real^3->real^3`
     STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`(Phi:real^3->real^3) o (Psi:real^3->real^3)`;
                        `(Psi':real^3->real^3) o (Phi':real^3->real^3)`;
                        `g2:real^3->real^3`; `g2':real^3->real^3`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
  ASM_REWRITE_TAC[]);;

(* The main theorem.                                                          *)

let SCH_GENERIC = prove
 (`SCH_GENERIC_STATEMENT`,
  REWRITE_TAC[SCH_GENERIC_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`f:real^3->real^3`; `f':real^3->real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`] SCH3_MORSE_PREP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi0:real^3->real^3` (X_CHOOSE_THEN `Phi0':real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` (X_CHOOSE_THEN `g':real^3->real^3`
     STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`CARD {t | sch_crit (g:real^3->real^3) t /\ ~sch3_good g t}`;
                 `g:real^3->real^3`; `g':real^3->real^3`] SCH3_MORSE_INDUCT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi1:real^3->real^3` (X_CHOOSE_THEN `Phi1':real^3->real^3`
    (X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
     STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`(Phi1:real^3->real^3) o (Phi0:real^3->real^3)`;
                        `(Phi0':real^3->real^3) o (Phi1':real^3->real^3)`;
                        `g1:real^3->real^3`; `g1':real^3->real^3`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
  ASM_REWRITE_TAC[]);;

