(* ========================================================================= *)
(* pc_sch_stmt: statement layer of the smooth Schoenflies theorem in R^3     *)
(* (Alexander's theorem, collared form) for the statement                    *)
(* APX_SCHOENFLIES_REQ_STATEMENT of pc_apx_schreq (the Schoenflies-type fact *)
(* used in the Appendix).                                                    *)
(*                                                                           *)
(* Contents: the definitions (collared spheres, Euclidean ball charts, the   *)
(* collared conclusion, Morse position for the height x$3), the statement    *)
(* constants of the chain and of its links, the glue                         *)
(*   SCH_REQ_CHAIN |- SCH_GENERIC_STATEMENT /\ SCH_BASE0_STATEMENT /\        *)
(*                    SCH_BASE1_STATEMENT /\ SCH_SURGERY_STATEMENT /\        *)
(*                    SCH_COLLAR3_STATEMENT                                  *)
(*                    ==> !u:A->bool. APX_SCHOENFLIES_REQ_STATEMENT u        *)
(* and sanity theorems (the round sphere is a Morse sphere without saddles   *)
(* and bounds a ball: SCH_ROUND_BASE0). The collared conclusion asks for     *)
(* agreement with the collar on the annulus 3/4 < |x| < 2 only: agreement on *)
(* all of 1/2 < |x| < 2 can fail (APX_SCHREQ_V1_FALSE in pc_apx_schreq).     *)
(* ========================================================================= *)

needs "src/pc_apx_schreq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Definitions and statement constants.                                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* 1. Collared spheres, Euclidean ball charts and the collared Schoenflies   *)
(* conclusion in real^N (used for N = 2 and N = 3).                          *)
(* ------------------------------------------------------------------------- *)

(* A neck (collar) of a sphere in real^N: a diffeomorphism of the annulus   *)
(* 1/2 < |x| < 2 onto an open subset; its central sphere is f(sphere 1).     *)

let sch_neck = new_definition
 `sch_neck (f:real^N->real^N) (f':real^N->real^N) <=>
    diffeomorphism_on (annulus (&1 / &2) (&2))
                      (IMAGE f (annulus (&1 / &2) (&2))) f f'`;;

(* A Euclidean ball chart: a diffeomorphism of ball(0,2) onto an open set.   *)

let sch_ball = new_definition
 `sch_ball (c:real^N->real^N) (c':real^N->real^N) <=>
    diffeomorphism_on (ball(vec 0,&2)) (IMAGE c (ball(vec 0,&2))) c c'`;;

(* The collared conclusion: the closed bounded side of f(sphere 1) is        *)
(* c(cball 1) for a ball chart c equal to f, or to f composed with the       *)
(* inversion, on the annulus 3/4 < |x| < 2 (not 1/2 < |x| < 2: the inner     *)
(* end of a collar may degenerate, see APX_SCHREQ_V1_FALSE).                 *)

let sch_fills = new_definition
 `sch_fills (f:real^N->real^N) <=>
    ?c c'. sch_ball c c' /\
           IMAGE c (cball(vec 0,&1)) =
           IMAGE f (sphere(vec 0,&1)) UNION inside(IMAGE f (sphere(vec 0,&1))) /\
           ((!x. x IN annulus (&3 / &4) (&2) ==> c x = f x) \/
            (!x. x IN annulus (&3 / &4) (&2) ==> c x = f(inv(norm x pow 2) % x)))`;;

(* The uncollared conclusion: s and its inside form c(cball 1).             *)

let sch_bounds_ball = new_definition
 `sch_bounds_ball (s:real^N->bool) <=>
    ?c c'. sch_ball c c' /\ IMAGE c (cball(vec 0,&1)) = s UNION inside s`;;

(* ------------------------------------------------------------------------- *)
(* 2. The Euclidean cores.                                                   *)
(* ------------------------------------------------------------------------- *)

(* The main core: collared smooth Schoenflies in R^3. *)

let SCH_R3_STATEMENT = new_definition
 `SCH_R3_STATEMENT <=> !f f':real^3->real^3. sch_neck f f' ==> sch_fills f`;;

(* The planar analogue (smooth 2D Schoenflies with collar matching).        *)

let SCH_R2_STATEMENT = new_definition
 `SCH_R2_STATEMENT <=> !f f':real^2->real^2. sch_neck f f' ==> sch_fills f`;;

(* Uncollared smooth Schoenflies in R^3 (the Hatcher part).                  *)

let SCH_BALL3_STATEMENT = new_definition
 `SCH_BALL3_STATEMENT <=>
    !f f':real^3->real^3. sch_neck f f'
                          ==> sch_bounds_ball (IMAGE f (sphere(vec 0,&1)))`;;

(* Collar matching: a collared sphere bounding some ball bounds one that      *)
(* matches the collar (Smale's theorem plus uniqueness of collars).         *)

let SCH_COLLAR3_STATEMENT = new_definition
 `SCH_COLLAR3_STATEMENT <=>
    !f f':real^3->real^3.
        sch_neck f f' /\ sch_bounds_ball (IMAGE f (sphere(vec 0,&1)))
        ==> sch_fills f`;;

let SCH_COLLAR2_STATEMENT = new_definition
 `SCH_COLLAR2_STATEMENT <=>
    !f f':real^2->real^2.
        sch_neck f f' /\ sch_bounds_ball (IMAGE f (sphere(vec 0,&1)))
        ==> sch_fills f`;;

(* ------------------------------------------------------------------------- *)
(* 3. Morse position of a collared sphere g in R^3 for the height x$3.       *)
(* Critical points are given by their parameters t on the unit sphere; a     *)
(* height-preserving Morse chart at p is (u,z) |-> (ph u, z) in which the    *)
(* surface is exactly the graph z = p$3 + k1 u1^2 + k2 u2^2 (exact quadratic *)
(* graphs are produced by perturbation, so no Morse lemma is needed).        *)
(* ------------------------------------------------------------------------- *)

let sch_crit = new_definition
 `sch_crit (g:real^3->real^3) (t:real^3) <=>
    t IN sphere(vec 0,&1) /\
    !v. orthogonal t v ==> (frechet_derivative g (at t) v)$3 = &0`;;

let sch_hchart = new_definition
 `sch_hchart (s:real^3->bool) (p:real^3) (k1:real) (k2:real) <=>
    (k1 = &1 \/ k1 = -- &1) /\ (k2 = &1 \/ k2 = -- &1) /\
    ?r (ph:real^2->real^2) ph'.
        &0 < r /\ r < &1 /\
        diffeomorphism_on (ball(vec 0,r)) (IMAGE ph (ball(vec 0,r))) ph ph' /\
        ph(vec 0) = vector[p$1; p$2] /\
        !u z. u IN ball(vec 0,r) /\ abs(z - p$3) < r
              ==> ((vector[(ph u)$1; (ph u)$2; z]:real^3) IN s <=>
                   z = p$3 + k1 * (u$1) pow 2 + k2 * (u$2) pow 2)`;;

let sch_morse = new_definition
 `sch_morse (g:real^3->real^3) <=>
    FINITE {t | sch_crit g t} /\
    (!t t'. sch_crit g t /\ sch_crit g t' /\ (g t)$3 = (g t')$3 ==> t = t') /\
    (!t. sch_crit g t
         ==> ?k1 k2. sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) k1 k2)`;;

let sch_saddles = new_definition
 `sch_saddles (g:real^3->real^3) =
    {t | sch_crit g t /\
         sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) (&1) (-- &1)}`;;

let sch_level = new_definition
 `sch_level (g:real^3->real^3) (a:real) =
    {x | x IN IMAGE g (sphere(vec 0,&1)) /\ x$3 = a}`;;

(* ------------------------------------------------------------------------- *)
(* 4. The statements below SCH_BALL3.                                        *)
(* ------------------------------------------------------------------------- *)

(* Morse position after an ambient diffeomorphism (pc_sch_generic).          *)

let SCH_GENERIC_STATEMENT = new_definition
 `SCH_GENERIC_STATEMENT <=>
    !f f':real^3->real^3.
        sch_neck f f'
        ==> ?Phi Phi' g g'.
              diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\
              sch_neck g g' /\ sch_morse g /\
              IMAGE g (sphere(vec 0,&1)) = IMAGE Phi (IMAGE f (sphere(vec 0,&1)))`;;

(* The Hatcher core: spheres in Morse position bound balls.                  *)

let SCH_MORSE_BALL_STATEMENT = new_definition
 `SCH_MORSE_BALL_STATEMENT <=>
    !g g':real^3->real^3.
        sch_neck g g' /\ sch_morse g
        ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1)))`;;

(* A regular level has finitely many components (smooth circles;             *)
(* pc_sch_level).                                                            *)

let SCH_LEVEL_FINITE_STATEMENT = new_definition
 `SCH_LEVEL_FINITE_STATEMENT <=>
    !g g':real^3->real^3 a.
        sch_neck g g' /\ sch_morse g /\ (!t. sch_crit g t ==> ~((g t)$3 = a))
        ==> FINITE(components(sch_level g a))`;;

(* The base cases (no saddle, pc_sch_base0; one saddle, pc_sch_base1).       *)

let SCH_BASE0_STATEMENT = new_definition
 `SCH_BASE0_STATEMENT <=>
    !g g':real^3->real^3.
        sch_neck g g' /\ sch_morse g /\ sch_saddles g = {}
        ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1)))`;;

let SCH_BASE1_STATEMENT = new_definition
 `SCH_BASE1_STATEMENT <=>
    !g g':real^3->real^3.
        sch_neck g g' /\ sch_morse g /\ CARD(sch_saddles g) = 1
        ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1)))`;;

(* Surgery along an innermost circle of a regular level between two saddles, *)
(* with the reverse gluing (the induction scheme of DG, the Lean             *)
(* formalization of Qin et al.).                                             *)

let SCH_SURGERY_STATEMENT = new_definition
 `SCH_SURGERY_STATEMENT <=>
    !g g':real^3->real^3 t1 t2 a.
        sch_neck g g' /\ sch_morse g /\
        t1 IN sch_saddles g /\ t2 IN sch_saddles g /\
        (g t1)$3 < a /\ a < (g t2)$3 /\ (!t. sch_crit g t ==> ~((g t)$3 = a))
        ==> ?g1 g1' g2 g2'.
              sch_neck g1 g1' /\ sch_morse g1 /\
              sch_neck g2 g2' /\ sch_morse g2 /\
              (!t. sch_crit g1 t ==> ~((g1 t)$3 = a)) /\
              (!t. sch_crit g2 t ==> ~((g2 t)$3 = a)) /\
              CARD(sch_saddles g1) <= CARD(sch_saddles g) /\
              CARD(sch_saddles g2) <= CARD(sch_saddles g) /\
              (CARD(sch_saddles g1) = CARD(sch_saddles g)
               ==> (?s1 s2. s1 IN sch_saddles g1 /\ s2 IN sch_saddles g1 /\
                            (g1 s1)$3 < a /\ a < (g1 s2)$3) /\
                   CARD(components(sch_level g1 a)) <
                   CARD(components(sch_level g a))) /\
              (CARD(sch_saddles g2) = CARD(sch_saddles g)
               ==> (?s1 s2. s1 IN sch_saddles g2 /\ s2 IN sch_saddles g2 /\
                            (g2 s1)$3 < a /\ a < (g2 s2)$3) /\
                   CARD(components(sch_level g2 a)) <
                   CARD(components(sch_level g a))) /\
              (sch_bounds_ball (IMAGE g1 (sphere(vec 0,&1))) /\
               sch_bounds_ball (IMAGE g2 (sphere(vec 0,&1)))
               ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1))))`;;

(* ------------------------------------------------------------------------- *)
(* Glue, part 1: the Appendix statement APX_SCHOENFLIES_REQ_STATEMENT        *)
(* follows from the Euclidean core SCH_R3_STATEMENT (transfer through the    *)
(* ball chart b).                                                            *)
(* ------------------------------------------------------------------------- *)

let SCH_INV_ANNULUS = prove
 (`!x:real^N. x IN annulus (&3 / &4) (&2)
              ==> inv(norm x pow 2) % x IN annulus (&1 / &2) (&2)`,
  GEN_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(x:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&3 / &4 < norm(vec 0:real^N)` THEN
    REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SMT_INVERSION_NORM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LINV THEN ASM_REAL_ARITH_TAC);;

let SCH_ANNULUS_SUBSETS = prove
 (`sphere(vec 0:real^N,&1) SUBSET annulus (&1 / &2) (&2) /\
   (annulus (&3 / &4) (&2):real^N->bool) SUBSET annulus (&1 / &2) (&2) /\
   ball(vec 0:real^N,&1) SUBSET ball(vec 0,&2)`,
  REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0; IN_BALL_0] THEN
  REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let SCH_REQ_FROM_R3 = prove
 (`SCH_R3_STATEMENT ==> !u:A->bool. APX_SCHOENFLIES_REQ_STATEMENT u`,
  REWRITE_TAC[SCH_R3_STATEMENT; APX_SCHOENFLIES_REQ_STATEMENT] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `b:real^3->A`; `e:real^3->A`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS o REWRITE_RULE[mfd_ball_chart]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y. y IN annulus (&1 / &2) (&2)
        ==> (b':A->real^3)((e:real^3->A) y) IN ball(vec 0,&1) /\
            (b:real^3->A)(b'(e y)) = e y`
  (LABEL_TAC "EB") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:real^3->A) y IN IMAGE (b:real^3->A) (ball(vec 0,&1))` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN ball(vec 0,&2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(vec 0,&1)` THEN
      REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* The collar in b-coordinates. *)
  SUBGOAL_THEN
   `mfd_param euclidean (open_set_atlas (:real^3)) (annulus (&1 / &2) (&2))
              ((b':A->real^3) o (e:real^3->A))`
  MP_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `IMAGE (b:real^3->A) (ball(vec 0,&2))`;
                          `ball(vec 0:real^3,&2)`; `b:real^3->A`] THEN
    ASM_REWRITE_TAC[APX_SCHREQ_EUCLIDEAN] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `mfd_neck_chart top atlas (e:real^3->A)` THEN
      REWRITE_TAC[mfd_neck_chart];
      MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&1))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SCH_ANNULUS_SUBSETS]];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_param; MFD_DIFFEO_EUCLIDEAN] THEN
  DISCH_THEN(X_CHOOSE_TAC `f':real^3->real^3`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(b':A->real^3) o (e:real^3->A)`; `f':real^3->real^3`]) THEN
  ASM_REWRITE_TAC[sch_neck; sch_fills; sch_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->real^3` (X_CHOOSE_THEN `c':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "IM") (LABEL_TAC "AG"))))) THEN
  (* The sphere and its inside lie in ball(0,1). *)
  SUBGOAL_THEN `IMAGE (c:real^3->real^3) (cball(vec 0,&1)) SUBSET ball(vec 0,&1)`
  (LABEL_TAC "CB1") THENL
   [USE_THEN "IM" SUBST1_TAC THEN REWRITE_TAC[UNION_SUBSET] THEN
    SUBGOAL_THEN `IMAGE ((b':A->real^3) o (e:real^3->A)) (sphere(vec 0,&1)) SUBSET
                  ball(vec 0,&1)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_TAC THEN USE_THEN "EB" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
        REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SIMP_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN
      ASM_REWRITE_TAC[CONVEX_BALL]];
    ALL_TAC] THEN
  (* All of c(ball(0,2)) lies in ball(0,1). *)
  SUBGOAL_THEN `IMAGE (c:real^3->real^3) (ball(vec 0,&2)) SUBSET ball(vec 0,&1)`
  (LABEL_TAC "CB2") THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    ASM_CASES_TAC `norm(x:real^3) <= &1` THENL
     [USE_THEN "CB1" (MP_TAC o SPEC `(c:real^3->real^3) x` o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL_0] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_CBALL_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN annulus (&3 / &4) (&2)` ASSUME_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM IN_BALL_0] THEN
    USE_THEN "AG" (DISJ_CASES_THEN (fun th ->
      REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^3) IN annulus (&3 / &4) (&2)`); o_THM])) THEN
    USE_THEN "EB" (fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP th
      (MATCH_MP (REWRITE_RULE[SUBSET] (CONJUNCT1(CONJUNCT2 SCH_ANNULUS_SUBSETS)))
                (ASSUME `(x:real^3) IN annulus (&3 / &4) (&2)`)))]) THEN
    USE_THEN "EB" (fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP th
      (MATCH_MP SCH_INV_ANNULUS (ASSUME `(x:real^3) IN annulus (&3 / &4) (&2)`)))]);
    ALL_TAC] THEN
  EXISTS_TAC `(b:real^3->A) o (c:real^3->real^3)` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball_chart] THEN MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                          `ball(vec 0:real^3,&2)`;
                          `IMAGE (b:real^3->A) (ball(vec 0,&2))`; `b':A->real^3`] THEN
    ASM_REWRITE_TAC[APX_SCHREQ_EUCLIDEAN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_SCHREQ_PARAM THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (c:real^3->real^3) (ball(vec 0,&2))`;
                            `c':real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^3,&1)` THEN
      ASM_REWRITE_TAC[SCH_ANNULUS_SUBSETS]];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    USE_THEN "AG" (DISJ_CASES_THEN ASSUME_TAC) THENL [DISJ1_TAC; DISJ2_TAC] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THENL
     [FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^3) IN annulus (&3 / &4) (&2)`); o_THM]) THEN
      USE_THEN "EB" (fun th -> REWRITE_TAC[CONJUNCT2(MATCH_MP th
        (MATCH_MP (REWRITE_RULE[SUBSET] (CONJUNCT1(CONJUNCT2 SCH_ANNULUS_SUBSETS)))
                  (ASSUME `(x:real^3) IN annulus (&3 / &4) (&2)`)))]);
      FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^3) IN annulus (&3 / &4) (&2)`); o_THM]) THEN
      USE_THEN "EB" (fun th -> REWRITE_TAC[CONJUNCT2(MATCH_MP th
        (MATCH_MP SCH_INV_ANNULUS (ASSUME `(x:real^3) IN annulus (&3 / &4) (&2)`)))])]]);;

(* ------------------------------------------------------------------------- *)
(* Glue, part 2: SCH_R3 from its two parts; insides under         *)
(* homeomorphisms of R^N; SCH_BALL3 from genericity and the Hatcher core;    *)
(* the Hatcher core from the base cases and the surgery step (induction on   *)
(* the number of saddles, then on the number of components of a level).     *)
(* ------------------------------------------------------------------------- *)

let SCH_R3_FROM_PARTS = prove
 (`SCH_BALL3_STATEMENT /\ SCH_COLLAR3_STATEMENT ==> SCH_R3_STATEMENT`,
  REWRITE_TAC[SCH_BALL3_STATEMENT; SCH_COLLAR3_STATEMENT; SCH_R3_STATEMENT] THEN
  MESON_TAC[]);;

let SCH_HOMEO_INVERSES = prove
 (`!f:real^N->real^N g.
        homeomorphism ((:real^N),(:real^N)) (f,g)
        ==> (!x. g(f x) = x) /\ (!y. f(g y) = y) /\
            f continuous_on (:real^N) /\ g continuous_on (:real^N)`,
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN MESON_TAC[]);;

let SCH_BOUNDED_HOMEO_IMAGE = prove
 (`!f:real^N->real^N g k.
        homeomorphism ((:real^N),(:real^N)) (f,g)
        ==> (bounded(IMAGE f k) <=> bounded k)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP SCH_HOMEO_INVERSES) THEN
  SUBGOAL_THEN `!h:real^N->real^N t. h continuous_on (:real^N) /\ bounded t
                                     ==> bounded(IMAGE h t)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (h:real^N->real^N) (closure t)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[COMPACT_CLOSURE] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[CLOSURE_SUBSET]];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `k = IMAGE (g:real^N->real^N) (IMAGE f k)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
      ASM_SIMP_TAC[]];
    ASM_SIMP_TAC[]]);;

let SCH_INSIDE_HOMEOMORPHISM = prove
 (`!f:real^N->real^N g s.
        homeomorphism ((:real^N),(:real^N)) (f,g)
        ==> inside(IMAGE f s) = IMAGE f (inside s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH_HOMEO_INVERSES) THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) ((:real^N) DIFF s) = (:real^N) DIFF IMAGE f s`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. ~(x IN s)
                ==> connected_component ((:real^N) DIFF IMAGE f s) (f x) =
                    IMAGE f (connected_component ((:real^N) DIFF s) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real^N`; `g:real^N->real^N`; `(:real^N) DIFF s`;
                   `(:real^N) DIFF IMAGE (f:real^N->real^N) s`; `x:real^N`]
      HOMEOMORPHISM_CONNECTED_COMPONENT) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(:real^N)`; `(:real^N)`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; inside; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN
  EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `(g:real^N->real^N) y` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((g:real^N->real^N) y IN s)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^N->real^N) y`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> UNDISCH_TAC
      `bounded(connected_component ((:real^N) DIFF IMAGE (f:real^N->real^N) s) (y:real^N))` THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_MESON_TAC[SCH_BOUNDED_HOMEO_IMAGE];
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[SCH_BOUNDED_HOMEO_IMAGE]]);;

let SCH_DIFFEO_RESTRICT_UNIV = prove
 (`!Phi Phi':real^N->real^N u.
        diffeomorphism_on (:real^N) (:real^N) Phi Phi' /\ open u
        ==> diffeomorphism_on u (IMAGE Phi u) Phi Phi'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on; IN_UNIV]) ASSUME_TAC) THEN
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (Phi:real^N->real^N) u = {y | y IN (:real^N) /\ Phi' y IN u}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]]);;

let SCH_BOUNDS_BALL_DIFFEO = prove
 (`!Phi Phi':real^N->real^N s.
        diffeomorphism_on (:real^N) (:real^N) Phi Phi' /\
        sch_bounds_ball (IMAGE Phi s)
        ==> sch_bounds_ball s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_bounds_ball; sch_ball] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `c:real^N->real^N` (X_CHOOSE_THEN `c':real^N->real^N`
      STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `homeomorphism ((:real^N),(:real^N)) (Phi':real^N->real^N,Phi)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (:real^N) (:real^N) Phi Phi'` THEN
    REWRITE_TAC[diffeomorphism_on; homeomorphism; IN_UNIV] THEN
    MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(Phi':real^N->real^N) o (c:real^N->real^N)`;
                        `(c':real^N->real^N) o (Phi:real^N->real^N)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `IMAGE (c:real^N->real^N) (ball(vec 0,&2))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH_DIFFEO_RESTRICT_UNIV THEN
    ASM_SIMP_TAC[DIFFEOMORPHISM_ON_SYM] THEN
    UNDISCH_TAC `diffeomorphism_on (ball(vec 0,&2)) (IMAGE (c:real^N->real^N)
                   (ball(vec 0,&2))) c c'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN
  MP_TAC(ISPECL [`Phi':real^N->real^N`; `Phi:real^N->real^N`;
                 `IMAGE (Phi:real^N->real^N) s`] SCH_INSIDE_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[IMAGE_UNION] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH_HOMEO_INVERSES) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID]);;

let SCH_BALL3_FROM_PARTS = prove
 (`SCH_GENERIC_STATEMENT /\ SCH_MORSE_BALL_STATEMENT ==> SCH_BALL3_STATEMENT`,
  REWRITE_TAC[SCH_GENERIC_STATEMENT; SCH_MORSE_BALL_STATEMENT; SCH_BALL3_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "GEN") (LABEL_TAC "MB")) THEN
  MAP_EVERY X_GEN_TAC [`f:real^3->real^3`; `f':real^3->real^3`] THEN
  DISCH_TAC THEN USE_THEN "GEN" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `sch_neck (f:real^3->real^3) f'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->real^3` (X_CHOOSE_THEN `Phi':real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` (X_CHOOSE_THEN `g':real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  MATCH_MP_TAC SCH_BOUNDS_BALL_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`Phi:real^3->real^3`; `Phi':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  USE_THEN "MB" MATCH_MP_TAC THEN EXISTS_TAC `g':real^3->real^3` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Glue, part 3: the Hatcher core SCH_MORSE_BALL_STATEMENT from   *)
(* the two base cases and the surgery step (DG's scheme: induction on the    *)
(* number of saddles, inner induction on the number of components of a      *)
(* regular level between two saddles), and the whole chain.                 *)
(* ------------------------------------------------------------------------- *)

let SCH_TWO_SADDLES = prove
 (`!g:real^3->real^3 n.
        sch_morse g /\ CARD(sch_saddles g) = n /\ ~(n = 0) /\ ~(n = 1)
        ==> ?t1 t2. t1 IN sch_saddles g /\ t2 IN sch_saddles g /\
                    (g t1)$3 < (g t2)$3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(sch_saddles (g:real^3->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t | sch_crit (g:real^3->real^3) t}` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[sch_morse];
      REWRITE_TAC[sch_saddles; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u1 u2. u1 IN sch_saddles (g:real^3->real^3) /\
                        u2 IN sch_saddles g /\ ~(u1 = u2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(sch_saddles (g:real^3->real^3) = {})` MP_TAC THENL
     [ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `u1:real^3`) THEN
    SUBGOAL_THEN `~(sch_saddles (g:real^3->real^3) DELETE u1 = {})` MP_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`u1:real^3`; `sch_saddles (g:real^3->real^3)`] CARD_DELETE) THEN
      ASM_REWRITE_TAC[CARD_CLAUSES] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DELETE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((g:real^3->real^3) u1 $3 = g u2 $3)` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_morse (g:real^3->real^3)` THEN REWRITE_TAC[sch_morse] THEN
    UNDISCH_TAC `(u1:real^3) IN sch_saddles g` THEN
    UNDISCH_TAC `(u2:real^3) IN sch_saddles g` THEN
    REWRITE_TAC[sch_saddles; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
    `~(x = y) ==> x < y \/ y < x`)) THEN
  ASM_MESON_TAC[]);;

let SCH_REGULAR_BETWEEN = prove
 (`!g:real^3->real^3 h1 h2.
        sch_morse g /\ h1 < h2
        ==> ?a. h1 < a /\ a < h2 /\ (!t. sch_crit g t ==> ~((g t)$3 = a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (IMAGE (\t. (g:real^3->real^3) t $3) {t | sch_crit g t})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC[sch_morse]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{x | h1 < x /\ x < h2}`;
                 `IMAGE (\t. (g:real^3->real^3) t $3) {t | sch_crit g t}`]
    INFINITE_DIFF_FINITE) THEN
  ASM_REWRITE_TAC[INFINITE; FINITE_REAL_INTERVAL; REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
    (MESON[FINITE_EMPTY] `~FINITE(s:real->bool) ==> ~(s = {})`)) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_ELIM_THM; IN_IMAGE] THEN
  MESON_TAC[]);;

let SCH_MORSE_BALL_FROM_PARTS = prove
 (`SCH_BASE0_STATEMENT /\ SCH_BASE1_STATEMENT /\ SCH_SURGERY_STATEMENT
   ==> SCH_MORSE_BALL_STATEMENT`,
  REWRITE_TAC[SCH_BASE0_STATEMENT; SCH_BASE1_STATEMENT; SCH_SURGERY_STATEMENT;
              SCH_MORSE_BALL_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "B0")
    (CONJUNCTS_THEN2 (LABEL_TAC "B1") (LABEL_TAC "SU"))) THEN
  SUBGOAL_THEN
   `!n g g':real^3->real^3.
        sch_neck g g' /\ sch_morse g /\ CARD(sch_saddles g) = n
        ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1)))`
  (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "IHN") THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `g':real^3->real^3`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [USE_THEN "B0" MATCH_MP_TAC THEN EXISTS_TAC `g':real^3->real^3` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `FINITE(sch_saddles (g:real^3->real^3))` MP_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{t | sch_crit (g:real^3->real^3) t}` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[sch_morse];
        REWRITE_TAC[sch_saddles; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
      ASM_MESON_TAC[CARD_EQ_0]];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [USE_THEN "B1" MATCH_MP_TAC THEN EXISTS_TAC `g':real^3->real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `n:num`] SCH_TWO_SADDLES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^3` (X_CHOOSE_THEN `t2:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `(g:real^3->real^3) t1 $3`;
                 `(g:real^3->real^3) t2 $3`] SCH_REGULAR_BETWEEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!m h h':real^3->real^3.
        sch_neck h h' /\ sch_morse h /\ CARD(sch_saddles h) = n /\
        (?s1 s2. s1 IN sch_saddles h /\ s2 IN sch_saddles h /\
                 (h s1)$3 < a /\ a < (h s2)$3) /\
        (!t. sch_crit h t ==> ~((h t)$3 = a)) /\
        CARD(components(sch_level h a)) = m
        ==> sch_bounds_ball (IMAGE h (sphere(vec 0,&1)))`
  (fun th -> MATCH_MP_TAC th THEN
             EXISTS_TAC `CARD(components(sch_level (g:real^3->real^3) a))` THEN
             EXISTS_TAC `g':real^3->real^3` THEN ASM_REWRITE_TAC[] THEN
             ASM_MESON_TAC[]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN DISCH_THEN(LABEL_TAC "IHM") THEN
  MAP_EVERY X_GEN_TAC [`h:real^3->real^3`; `h':real^3->real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s1:real^3` (X_CHOOSE_THEN `s2:real^3` STRIP_ASSUME_TAC))
      STRIP_ASSUME_TAC)))) THEN
  USE_THEN "SU" (MP_TAC o SPECL [`h:real^3->real^3`; `h':real^3->real^3`;
                                 `s1:real^3`; `s2:real^3`; `a:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
    (X_CHOOSE_THEN `g2:real^3->real^3` (X_CHOOSE_THEN `g2':real^3->real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
         (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 (LABEL_TAC "E1") (CONJUNCTS_THEN2 (LABEL_TAC "E2")
            (LABEL_TAC "GL"))))))))))))))) THEN
  USE_THEN "GL" MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_CASES_TAC `CARD(sch_saddles (g1:real^3->real^3)) = n` THENL
     [SUBGOAL_THEN `CARD(sch_saddles (g1:real^3->real^3)) =
                    CARD(sch_saddles (h:real^3->real^3))`
      (fun th -> USE_THEN "E1" (MP_TAC o C MATCH_MP th)) THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN
      USE_THEN "IHM" (MP_TAC o SPEC `CARD(components(sch_level (g1:real^3->real^3) a))`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `g1':real^3->real^3` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      USE_THEN "IHN" (MP_TAC o SPEC `CARD(sch_saddles (g1:real^3->real^3))`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `g1':real^3->real^3` THEN
      ASM_REWRITE_TAC[]];
    ASM_CASES_TAC `CARD(sch_saddles (g2:real^3->real^3)) = n` THENL
     [SUBGOAL_THEN `CARD(sch_saddles (g2:real^3->real^3)) =
                    CARD(sch_saddles (h:real^3->real^3))`
      (fun th -> USE_THEN "E2" (MP_TAC o C MATCH_MP th)) THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN
      USE_THEN "IHM" (MP_TAC o SPEC `CARD(components(sch_level (g2:real^3->real^3) a))`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `g2':real^3->real^3` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      USE_THEN "IHN" (MP_TAC o SPEC `CARD(sch_saddles (g2:real^3->real^3))`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `g2':real^3->real^3` THEN
      ASM_REWRITE_TAC[]]]);;

(* The whole chain: APX_SCHOENFLIES_REQ_STATEMENT from the statements of     *)
(* the links.                                                                *)

let SCH_REQ_CHAIN = prove
 (`SCH_GENERIC_STATEMENT /\ SCH_BASE0_STATEMENT /\ SCH_BASE1_STATEMENT /\
   SCH_SURGERY_STATEMENT /\ SCH_COLLAR3_STATEMENT
   ==> !u:A->bool. APX_SCHOENFLIES_REQ_STATEMENT u`,
  STRIP_TAC THEN MATCH_MP_TAC SCH_REQ_FROM_R3 THEN
  MATCH_MP_TAC SCH_R3_FROM_PARTS THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SCH_BALL3_FROM_PARTS THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SCH_MORSE_BALL_FROM_PARTS THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Sanity, part 2: the definitions of Morse position are satisfiable by  *)
(* the round sphere (identity collar): its height has exactly the two poles  *)
(* as critical points, each with an exact height-preserving quadratic chart  *)
(* ph u = sqrt(2 - |u|^2) u, and no saddle; it bounds the closed unit ball.  *)
(* So the hypotheses of SCH_BASE0_STATEMENT have a witness and its           *)
(* conclusion holds there.                                                   *)
(* ------------------------------------------------------------------------- *)

let SCH_RCH_SMOOTH1 = prove
 (`smooth_map_on (ball(vec 0:real^2,&1)) (\u. sqrt(&2 - norm u pow 2) % u)`,
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\u:real^2. lift(sqrt(&2 - norm u pow 2))`;
                 `\u:real^2. u`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_BALL; SMOOTH_MAP_ON_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\u:real^2. lift(&2 - norm u pow 2)`]
    SMOOTH_MAP_ON_LIFT_SQRT) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_BALL; IN_BALL_0] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\u:real^2. lift(&2)`;
                   `\u:real^2. lift(norm u pow 2)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_BALL; SMOOTH_MAP_ON_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\u:real^2. u`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_ID];
    X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x < &1 ==> &0 < &2 - x`) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= n /\ n < &1 /\ n pow 2 <= n ==> n pow 2 < &1`) THEN
    ASM_REWRITE_TAC[NORM_POS_LE; REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE]]);;

let SCH_RCH_SMOOTH2 = prove
 (`smooth_map_on (ball(vec 0:real^2,&1))
                 (\w. inv(sqrt(&1 + sqrt(&1 - norm w pow 2))) % w)`,
  SUBGOAL_THEN `!w:real^2. w IN ball(vec 0,&1) ==> &0 < &1 - norm w pow 2`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x < &1 ==> &0 < &1 - x`) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= n /\ n < &1 /\ n pow 2 <= n ==> n pow 2 < &1`) THEN
    ASM_REWRITE_TAC[NORM_POS_LE; REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(vec 0:real^2,&1))
                  (\w. lift(sqrt(&1 + sqrt(&1 - norm w pow 2))))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`;
                   `\w:real^2. lift(&1 + sqrt(&1 - norm w pow 2))`]
      SMOOTH_MAP_ON_LIFT_SQRT) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\w:real^2. lift(&1)`;
                     `\w:real^2. lift(sqrt(&1 - norm w pow 2))`] SMOOTH_MAP_ON_LIFT_ADD) THEN
      REWRITE_TAC[LIFT_DROP; OPEN_BALL; SMOOTH_MAP_ON_CONST] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\w:real^2. lift(&1 - norm w pow 2)`]
        SMOOTH_MAP_ON_LIFT_SQRT) THEN
      REWRITE_TAC[LIFT_DROP; OPEN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\w:real^2. lift(&1)`;
                     `\w:real^2. lift(norm w pow 2)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
      REWRITE_TAC[LIFT_DROP; OPEN_BALL; SMOOTH_MAP_ON_CONST] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`; `\w:real^2. w`]
        SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
      REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_ID];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`;
                 `\w:real^2. lift(inv(sqrt(&1 + sqrt(&1 - norm w pow 2))))`;
                 `\w:real^2. w`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_BALL; SMOOTH_MAP_ON_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`ball(vec 0:real^2,&1)`;
                 `\w:real^2. lift(sqrt(&1 + sqrt(&1 - norm w pow 2)))`]
    SMOOTH_MAP_ON_LIFT_INV) THEN
  ASM_REWRITE_TAC[LIFT_DROP; OPEN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SQRT_POS_LT THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN MATCH_MP_TAC SQRT_POS_LE THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* The algebra of the chart: with s = |u|^2 < 1 and q = |w|^2 < 1.          *)

let SCH_NORM_POW2_LT1 = prove
 (`!x:real^N. norm x < &1 ==> norm x pow 2 < &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm(x:real^N)` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE]);;

let SCH_RCH_NORM1 = prove
 (`!u:real^2. norm u < &1
              ==> norm(sqrt(&2 - norm u pow 2) % u) pow 2 =
                  (&2 - norm u pow 2) * norm u pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; REAL_POW_MUL] THEN
  SUBGOAL_THEN `&0 <= &2 - norm(u:real^2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x < &1 ==> &0 <= &2 - x`) THEN
    ASM_SIMP_TAC[SCH_NORM_POW2_LT1];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_REFL; SQRT_POS_LE; REAL_POW2_ABS; SQRT_POW_2]);;

let SCH_RCH_INV1 = prove
 (`!u:real^2. norm u < &1
              ==> inv(sqrt(&1 + sqrt(&1 - norm(sqrt(&2 - norm u pow 2) % u) pow 2))) %
                  (sqrt(&2 - norm u pow 2) % u) = u`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SCH_RCH_NORM1] THEN
  SUBGOAL_THEN `norm(u:real^2) pow 2 < &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCH_NORM_POW2_LT1]; ALL_TAC] THEN
  ABBREV_TAC `s = norm(u:real^2) pow 2` THEN
  SUBGOAL_THEN `&1 - (&2 - s) * s = (&1 - s) pow 2` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_ARITH `s < &1 ==> &0 <= &1 - s`] THEN
  REWRITE_TAC[REAL_ARITH `&1 + (&1 - s) = &2 - s`; VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
  MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC);;

let SCH_RCH_INV2 = prove
 (`!w:real^2. norm w < &1
              ==> sqrt(&2 - norm(inv(sqrt(&1 + sqrt(&1 - norm w pow 2))) % w) pow 2) %
                  (inv(sqrt(&1 + sqrt(&1 - norm w pow 2))) % w) = w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(w:real^2) pow 2 < &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCH_NORM_POW2_LT1]; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; REAL_POW_MUL; VECTOR_MUL_ASSOC] THEN
  ABBREV_TAC `q = norm(w:real^2) pow 2` THEN
  ABBREV_TAC `sg = sqrt(&1 - q)` THEN
  SUBGOAL_THEN `&0 <= sg /\ sg pow 2 = &1 - q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE; MATCH_MP_TAC SQRT_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&1 + sg)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(inv(sqrt(&1 + sg))) pow 2 = inv(&1 + sg)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW2_ABS; REAL_POW_INV] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 - inv(&1 + sg) * q = &1 + sg` SUBST1_TAC THENL
   [SUBGOAL_THEN `q = &1 - sg pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(&1 + sg = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REAL_MUL_RINV THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]);;

(* ------------------------------------------------------------------------- *)
(* Sanity, part 3: the chart ph is a diffeomorphism of ball(0,1/5) onto  *)
(* ball(0,7/25); the critical points of the height on the round sphere are   *)
(* the poles; the identity collar.                                           *)
(* ------------------------------------------------------------------------- *)

let SCH_LT_FROM_SQ = prove
 (`!x y. &0 <= y /\ x pow 2 < y pow 2 ==> x < y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`2`; `y:real`; `x:real`] REAL_POW_LE2) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SCH_RCH_DIFFEO = prove
 (`diffeomorphism_on (ball(vec 0:real^2,&1 / &5)) (ball(vec 0,&7 / &25))
     (\u. sqrt(&2 - norm u pow 2) % u)
     (\w. inv(sqrt(&1 + sqrt(&1 - norm w pow 2))) % w)`,
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN REWRITE_TAC[OPEN_BALL] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
    REWRITE_TAC[SCH_RCH_SMOOTH1; SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
    REWRITE_TAC[SCH_RCH_SMOOTH2; SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
    X_GEN_TAC `u:real^2` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(u:real^2) < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SCH_RCH_INV1] THEN MATCH_MP_TAC SCH_LT_FROM_SQ THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SCH_RCH_NORM1] THEN
    SUBGOAL_THEN `&0 <= norm(u:real^2) pow 2 /\ norm u pow 2 < &1 / &25`
    MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= n /\ n < &1 / &5 /\ n * n <= &1 / &5 * n
                               ==> n * n < &1 / &25`) THEN
      ASM_REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ABBREV_TAC `s = norm(u:real^2) pow 2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (&1 / &25 - s) * (&49 / &25 - s)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    X_GEN_TAC `w:real^2` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(w:real^2) < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SCH_RCH_INV2] THEN REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `norm(w:real^2) pow 2 < &49 / &625` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= n /\ n < &7 / &25 /\ n * n <= &7 / &25 * n
                               ==> n * n < &49 / &625`) THEN
      ASM_REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&24 / &25 <= sqrt(&1 - norm(w:real^2) pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&576 / &625)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&7 / &5 <= sqrt(&1 + sqrt(&1 - norm(w:real^2) pow 2))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&49 / &25)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `k = sqrt(&1 + sqrt(&1 - norm(w:real^2) pow 2))` THEN
    SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < k ==> abs k = k`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let SCH_ROUND_NECK = prove
 (`sch_neck (\x:real^3. x) (\x. x)`,
  REWRITE_TAC[sch_neck; IMAGE_ID] THEN MATCH_MP_TAC DIFFEOMORPHISM_ON_ID THEN
  REWRITE_TAC[OPEN_ANNULUS]);;

let SCH_BASIS3_EQ = prove
 (`!t:real^3. (t = basis 3 <=> t$1 = &0 /\ t$2 = &0 /\ t$3 = &1) /\
              (t = --basis 3 <=> t$1 = &0 /\ t$2 = &0 /\ t$3 = -- &1)`,
  GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

let SCH_ROUND_CRIT = prove
 (`!t:real^3. sch_crit (\x. x) t <=> t = basis 3 \/ t = --basis 3`,
  GEN_TAC THEN REWRITE_TAC[sch_crit] THEN
  SUBGOAL_THEN `frechet_derivative (\x:real^3. x) (at t) = (\h. h)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; SCH_BASIS3_EQ] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `basis 3 - (t:real^3)$3 % t`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[orthogonal; DOT_RSUB; DOT_RMUL] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_3; ARITH] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `(t:real^3) dot t = &1` THEN REWRITE_TAC[DOT_3] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(t:real^3)$1 * t$1 = &0 /\ t$2 * t$2 = &0` MP_TAC THENL
     [MP_TAC(SPEC `(t:real^3)$1` REAL_LE_SQUARE) THEN
      MP_TAC(SPEC `(t:real^3)$2` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&1 - (t:real^3)$3 * t$3 = &0` THEN CONV_TAC REAL_RING;
    STRIP_TAC THEN ASM_REWRITE_TAC[orthogonal; DOT_3] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Sanity, part 4: exact quadratic height-preserving charts at the poles *)
(* of the round sphere; Morse position; no saddle; the closed unit ball.     *)
(* ------------------------------------------------------------------------- *)

let SCH_VECTOR2_00 = prove
 (`vector[&0; &0]:real^2 = vec 0`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT]);;

let SCH_RCH_GRAPH = prove
 (`!u:real^2 z.
        norm u < &1 / &5
        ==> ((vector[(sqrt(&2 - norm u pow 2) % u)$1;
                     (sqrt(&2 - norm u pow 2) % u)$2; z]:real^3) IN sphere(vec 0,&1) <=>
             z pow 2 = (&1 - (u$1 pow 2 + u$2 pow 2)) pow 2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_3; VECTOR_3] THEN
  SUBGOAL_THEN `norm(u:real^2) < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(sqrt(&2 - norm(u:real^2) pow 2) % u)$1 *
                (sqrt(&2 - norm u pow 2) % u)$1 +
                (sqrt(&2 - norm u pow 2) % u)$2 *
                (sqrt(&2 - norm u pow 2) % u)$2 + z * z =
                (&2 - norm u pow 2) * norm u pow 2 + z * z` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ADD_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM DOT_2; GSYM NORM_POW_2] THEN ASM_SIMP_TAC[SCH_RCH_NORM1];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_POW_2; DOT_2] THEN CONV_TAC REAL_RING);;

let SCH_ROUND_HCHART_N = prove
 (`sch_hchart (sphere(vec 0:real^3,&1)) (basis 3) (-- &1) (-- &1)`,
  REWRITE_TAC[sch_hchart] THEN
  MAP_EVERY EXISTS_TAC [`&1 / &5`; `\u:real^2. sqrt(&2 - norm u pow 2) % u`;
                        `\w:real^2. inv(sqrt(&1 + sqrt(&1 - norm w pow 2))) % w`] THEN
  MP_TAC SCH_RCH_DIFFEO THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; SCH_VECTOR2_00] THEN
  REWRITE_TAC[NORM_0; VECTOR_MUL_RZERO; IN_BALL_0] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `z:real`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SCH_RCH_GRAPH] THEN
  SUBGOAL_THEN `&0 <= (u:real^2)$1 pow 2 + u$2 pow 2 /\ u$1 pow 2 + u$2 pow 2 < &1 / &25`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DOT_2; REAL_POW_2] THEN
    REWRITE_TAC[GSYM REAL_POW_2; GSYM NORM_POW_2] THEN
    SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= n /\ n < &1 / &5 /\ n * n <= &1 / &5 * n
                             ==> n * n < &1 / &25`) THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `s = (u:real^2)$1 pow 2 + u$2 pow 2` THEN
  REWRITE_TAC[REAL_ARITH `&1 + -- &1 * a + -- &1 * b = &1 - (a + b)`] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(z - (&1 - s)) * (z + (&1 - s)) = &0` MP_TAC THENL
     [UNDISCH_TAC `z pow 2 = (&1 - s) pow 2` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let SCH_ROUND_HCHART_S = prove
 (`sch_hchart (sphere(vec 0:real^3,&1)) (--basis 3) (&1) (&1)`,
  REWRITE_TAC[sch_hchart] THEN
  MAP_EVERY EXISTS_TAC [`&1 / &5`; `\u:real^2. sqrt(&2 - norm u pow 2) % u`;
                        `\w:real^2. inv(sqrt(&1 + sqrt(&1 - norm w pow 2))) % w`] THEN
  MP_TAC SCH_RCH_DIFFEO THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_NEG_0; SCH_VECTOR2_00] THEN
  REWRITE_TAC[NORM_0; VECTOR_MUL_RZERO; IN_BALL_0] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `z:real`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SCH_RCH_GRAPH] THEN
  SUBGOAL_THEN `&0 <= (u:real^2)$1 pow 2 + u$2 pow 2 /\ u$1 pow 2 + u$2 pow 2 < &1 / &25`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DOT_2; REAL_POW_2] THEN
    REWRITE_TAC[GSYM REAL_POW_2; GSYM NORM_POW_2] THEN
    SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= n /\ n < &1 / &5 /\ n * n <= &1 / &5 * n
                             ==> n * n < &1 / &25`) THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `s = (u:real^2)$1 pow 2 + u$2 pow 2` THEN
  REWRITE_TAC[REAL_ARITH `-- &1 + &1 * a + &1 * b = --(&1 - (a + b))`] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(z - (&1 - s)) * (z + (&1 - s)) = &0` MP_TAC THENL
     [UNDISCH_TAC `z pow 2 = (&1 - s) pow 2` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RING]);;

let SCH_ROUND_MORSE = prove
 (`sch_morse (\x:real^3. x)`,
  REWRITE_TAC[sch_morse; SCH_ROUND_CRIT; IMAGE_ID] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `{t:real^3 | t = basis 3 \/ t = --basis 3} = {basis 3, --basis 3}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY]; ALL_TAC] THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    REPEAT GEN_TAC THEN REWRITE_TAC[SCH_BASIS3_EQ] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN REAL_ARITH_TAC;
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SCH_ROUND_HCHART_N; SCH_ROUND_HCHART_S]]);;

let SCH_ROUND_SADDLES = prove
 (`sch_saddles (\x:real^3. x) = {}`,
  REWRITE_TAC[sch_saddles; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; SCH_ROUND_CRIT;
              IMAGE_ID] THEN
  X_GEN_TAC `t:real^3` THEN
  SUBGOAL_THEN `!z u:real^3. norm u = &1 /\ u$3 = z ==> abs z <= &1` ASSUME_TAC THENL
   [MESON_TAC[COMPONENT_LE_NORM]; ALL_TAC] THEN
  ASM_CASES_TAC `t:real^3 = basis 3` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[sch_hchart] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < r / &2 * r / &2 /\ r / &2 * r / &2 < r / &2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r / &2 % basis 1:real^2`; `&1 + (r / &2) pow 2`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; BASIS_COMPONENT; DIMINDEX_2; DIMINDEX_3; ARITH] THEN
      REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
    ANTS_TAC THENL
     [SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&1 + (r / &2) pow 2`;
      `vector[((\u:real^2. ph u:real^2) (r / &2 % basis 1))$1;
              ((\u:real^2. ph u:real^2) (r / &2 % basis 1))$2;
              &1 + (r / &2) pow 2]:real^3`]) THEN
    ASM_REWRITE_TAC[VECTOR_3] THEN REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ASM_CASES_TAC `t:real^3 = --basis 3` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[sch_hchart] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < r / &2 * r / &2 /\ r / &2 * r / &2 < r / &2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r / &2 % basis 2:real^2`; `-- &1 - (r / &2) pow 2`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_BALL_0; VECTOR_NEG_COMPONENT] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; BASIS_COMPONENT; DIMINDEX_2; DIMINDEX_3; ARITH] THEN
      REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[VECTOR_NEG_COMPONENT] THEN
      SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`-- &1 - (r / &2) pow 2`;
      `vector[((\u:real^2. ph u:real^2) (r / &2 % basis 2))$1;
              ((\u:real^2. ph u:real^2) (r / &2 % basis 2))$2;
              -- &1 - (r / &2) pow 2]:real^3`]) THEN
    ASM_REWRITE_TAC[VECTOR_3] THEN REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC]);;

let SCH_ROUND_BOUNDS = prove
 (`sch_bounds_ball (IMAGE (\x:real^3. x) (sphere(vec 0,&1)))`,
  REWRITE_TAC[sch_bounds_ball; sch_ball; IMAGE_ID; INSIDE_SPHERE] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^3. x`; `\x:real^3. x`] THEN
  REWRITE_TAC[IMAGE_ID] THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFFEOMORPHISM_ON_ID THEN REWRITE_TAC[OPEN_BALL];
    ONCE_REWRITE_TAC[UNION_COMM] THEN REWRITE_TAC[BALL_UNION_SPHERE]]);;

let SCH_ROUND_BASE0 = prove
 (`sch_neck (\x:real^3. x) (\x. x) /\ sch_morse (\x:real^3. x) /\
   sch_saddles (\x:real^3. x) = {} /\
   sch_bounds_ball (IMAGE (\x:real^3. x) (sphere(vec 0,&1)))`,
  REWRITE_TAC[SCH_ROUND_NECK; SCH_ROUND_MORSE; SCH_ROUND_SADDLES; SCH_ROUND_BOUNDS]);;

