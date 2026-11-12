(* ========================================================================= *)
(* Unit pc_sch_base0: the saddle-free base case of the smooth Schoenflies    *)
(* induction, SCH_BASE0 |- SCH_BASE0_STATEMENT: a collared Morse sphere      *)
(* without saddles bounds a ball.                                            *)
(*                                                                           *)
(* Route.  (1) Exactly two critical points: by the vertical flow of         *)
(* pc_sch_vflow, tangent to S away from the critical points, the            *)
(* components of the sublevel sets S(x3 <= a) meet the level S(x3 = a) in  *)
(* connected sets while only local minima lie below a; hence the lowest     *)
(* local maximum caps one of them to a clopen subset of S, which is all of  *)
(* S; by the flip x3 -> -x3 the highest local minimum is the global         *)
(* minimum.  (2) A vertical field tangent to S on the whole regular band   *)
(* with one first integral: the bottom chart function transported by the   *)
(* flow of pc_sch_vflow, interpolated with the top chart function.  (3) The *)
(* ball chart of a round model ball: the exact bottom chart, joined to the  *)
(* flow cylinder by a time reparametrization, and the top cap, where the    *)
(* holonomy of the flow is absorbed by a vertical reparametrization of the  *)
(* cap as a graph region (it preserves the circles near the boundary).      *)
(* ========================================================================= *)

(* pc_sch_collar first: pc_sch_vflow loads Multivariate/cross.ml, whose      *)
(* prioritize_vector() changes the default overloading of + on real^2 that   *)
(* the closure of pc_sch_collar relies on.  The overload state is saved and  *)
(* restored around cross.ml, so the order of the needs lines does not        *)
(* matter.                                                                   *)

needs "src/pc_sch_collar.ml";;
let schz_saved_interface = !the_interface;;
needs "Multivariate/cross.ml";;
the_interface := schz_saved_interface;;
needs "src/pc_sch_vflow.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Basic facts on the sphere S = g(S^2) of a collar g, the                   *)
(* sublevel sets, and the lift of a planar map to a map of real^3 that      *)
(* keeps the height.                                                         *)
(* ------------------------------------------------------------------------- *)

let schz_low = new_definition
 `schz_low (g:real^3->real^3) (a:real) =
    {x | x IN IMAGE g (sphere(vec 0,&1)) /\ x$3 <= a}`;;

let SCHZ_SURFACE_FACTS = prove
 (`!g g':real^3->real^3.
     sch_neck g g'
     ==> compact(IMAGE g (sphere(vec 0,&1))) /\
         connected(IMAGE g (sphere(vec 0,&1))) /\
         locally connected(IMAGE g (sphere(vec 0,&1))) /\
         ~(IMAGE g (sphere(vec 0,&1)) = {}) /\
         IMAGE g (sphere(vec 0,&1)) SUBSET IMAGE g (annulus (&1 / &2) (&2)) /\
         g continuous_on sphere(vec 0,&1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `&0`] SCH5V_SURFACE_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(g:real^3->real^3) continuous_on sphere(vec 0,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_REWRITE_TAC[SCH4_SPHERE_SUBSET_ANNULUS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_3; ARITH];
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`]
      SCH5V_NECK_SPHERE_HOMEOMORPHIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP HOMEOMORPHIC_LOCAL_CONNECTEDNESS th]) THEN
    REWRITE_TAC[LOCALLY_CONNECTED_SPHERE];
    REAL_ARITH_TAC]);;

(* The lift of a planar map ph: (y1,y2,y3) |-> (ph(y1,y2), y3).             *)

let schz_lift = new_definition
 `schz_lift (ph:real^2->real^2) (y:real^3) = sch5v_at (y$3) (ph(sch5v_pr y))`;;

let SCHZ_LIFT_FACTS = prove
 (`(!(ph:real^2->real^2) y. (schz_lift ph y)$3 = y$3) /\
   (!(ph:real^2->real^2) y. sch5v_pr(schz_lift ph y) = ph(sch5v_pr y)) /\
   (!(ph:real^2->real^2) a u. schz_lift ph (sch5v_at a u) = sch5v_at a (ph u))`,
  REWRITE_TAC[schz_lift; SCH5V_PR_AT]);;

let SCHZ_PR_OPEN = prove
 (`!U:real^2->bool. open U ==> open {y:real^3 | sch5v_pr y IN U}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[SCH5V_PR_AT_SMOOTH]);;

let SCHZ_LIFT_SMOOTH = prove
 (`!(ph:real^2->real^2) U.
     open U /\ smooth_map_on U ph
     ==> smooth_map_on {y:real^3 | sch5v_pr y IN U} (schz_lift ph)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `schz_lift (ph:real^2->real^2) =
                (\y:real^3. vector[(ph(sch5v_pr y))$1; (ph(sch5v_pr y))$2; y$3]:real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schz_lift; sch5v_at]; ALL_TAC] THEN
  SUBGOAL_THEN `open {y:real^3 | sch5v_pr y IN U}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCHZ_PR_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {y:real^3 | sch5v_pr y IN U}
                  (\y. (ph:real^2->real^2)(sch5v_pr y))` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH3_SV_COMPOSE THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SCH5V_PR_AT_SMOOTH; SUBSET_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC SCH3_SV_VECTOR3 THEN ASM_SIMP_TAC[SCH3_SL_COORD] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`{y:real^3 | sch5v_pr y IN U}`; `\y:real^3. (ph:real^2->real^2)(sch5v_pr y)`;
                   `1`] SCH3_SL_COMPONENT);
    MP_TAC(ISPECL [`{y:real^3 | sch5v_pr y IN U}`; `\y:real^3. (ph:real^2->real^2)(sch5v_pr y)`;
                   `2`] SCH3_SL_COMPONENT)] THEN
  ASM_REWRITE_TAC[]);;

let SCHZ_LIFT_DIFFEO = prove
 (`!(ph:real^2->real^2) ph' U.
     diffeomorphism_on U (IMAGE ph U) ph ph'
     ==> diffeomorphism_on {y:real^3 | sch5v_pr y IN U} {x | sch5v_pr x IN IMAGE ph U}
                           (schz_lift ph) (schz_lift ph')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  ASM_SIMP_TAC[SCHZ_PR_OPEN; SCHZ_LIFT_SMOOTH] THEN
  REWRITE_TAC[IN_ELIM_THM; SCHZ_LIFT_FACTS] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    REWRITE_TAC[schz_lift; SCH5V_PR_AT] THEN ASM_SIMP_TAC[SCH5V_PR_AT];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(ph':real^2->real^2)(sch5v_pr y) IN IMAGE ph' (IMAGE (ph:real^2->real^2) U)` MP_TAC THENL
       [ASM_SIMP_TAC[FUN_IN_IMAGE]; ASM_REWRITE_TAC[]];
      REWRITE_TAC[schz_lift; SCH5V_PR_AT] THEN ASM_SIMP_TAC[SCH5V_PR_AT]]]);;

(* ------------------------------------------------------------------------- *)
(* The exact charts (sch_hchart with k1 = k2 = k) as lifted                  *)
(* cylinders in which S is the graph x3 = c + k |u|^2, and the caps cut out *)
(* by height bands around the critical value c.                             *)
(* ------------------------------------------------------------------------- *)

let schz_cyl = new_definition
 `schz_cyl (ph:real^2->real^2) (c:real) (rho:real) =
    IMAGE (schz_lift ph) {y:real^3 | sch5v_pr y IN ball(vec 0,rho) /\ abs(y$3 - c) < rho}`;;

let schz_graph = new_definition
 `schz_graph (ph:real^2->real^2) (c:real) (k:real) (u:real^2) =
    sch5v_at (c + k * norm u pow 2) (ph u)`;;

let SCHZ_NORM_SQRT = prove
 (`!u:real^N e. &0 <= e
                ==> (norm u pow 2 <= e <=> norm u <= sqrt e) /\
                    (norm u pow 2 = e <=> norm u = sqrt e)`,
  REPEAT STRIP_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt e pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
        ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]]];
    EQ_TAC THENL
     [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[POW_2_SQRT; NORM_POS_LE] THEN
      MATCH_MP_TAC(GSYM POW_2_SQRT) THEN REWRITE_TAC[NORM_POS_LE];
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[SQRT_POW_2]]]);;

let SCHZ_HCHART_LIFT = prove
 (`!s (p:real^3) k.
     sch_hchart s p k k
     ==> (k = &1 \/ k = -- &1) /\
         ?r (ph:real^2->real^2) ph'.
           &0 < r /\ r < &1 /\
           diffeomorphism_on (ball(vec 0,r)) (IMAGE ph (ball(vec 0,r))) ph ph' /\
           schz_lift ph (sch5v_at (p$3) (vec 0)) = p /\
           (!y. sch5v_pr y IN ball(vec 0,r) /\ abs(y$3 - p$3) < r
                ==> (schz_lift ph y IN s <=> y$3 = p$3 + k * norm(sch5v_pr y) pow 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_hchart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `ph:real^2->real^2`
      (X_CHOOSE_THEN `ph':real^2->real^2` STRIP_ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `ph:real^2->real^2`; `ph':real^2->real^2`] THEN
  ASM_REWRITE_TAC[SCHZ_LIFT_FACTS] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[sch5v_at; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2];
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[schz_lift; sch5v_at] THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[NORM_POW_2; DOT_2] THEN REAL_ARITH_TAC]);;

let SCHZ_STRIP_OPEN = prove
 (`!c rho. open {y:real^3 | abs(y$3 - c) < rho}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{y:real^3 | abs(y$3 - c) < rho} =
                {y | y$3 > c - rho} INTER {y | y$3 < c + rho}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC OPEN_INTER THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT]]);;

let SCHZ_GRAPH_SMOOTH = prove
 (`!(ph:real^2->real^2) c k U.
     open U /\ smooth_map_on U ph ==> smooth_map_on U (schz_graph ph c k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `schz_graph (ph:real^2->real^2) c k =
                (\u. vector[(ph u)$1; (ph u)$2; c + k * norm u pow 2]:real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schz_graph; sch5v_at]; ALL_TAC] THEN
  MATCH_MP_TAC SCH3_SV_VECTOR3 THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^2->bool`; `ph:real^2->real^2`; `1`] SCH3_SL_COMPONENT) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`U:real^2->bool`; `ph:real^2->real^2`; `2`] SCH3_SL_COMPONENT) THEN
    ASM_REWRITE_TAC[];
    SCH3_SMOOTH_TAC]);;

let SCHZ_CYL = prove
 (`!s c k r (ph:real^2->real^2) ph' rho.
     diffeomorphism_on (ball(vec 0,r)) (IMAGE ph (ball(vec 0,r))) ph ph' /\
     (!y. sch5v_pr y IN ball(vec 0,r) /\ abs(y$3 - c) < r
          ==> (schz_lift ph y IN s <=> y$3 = c + k * norm(sch5v_pr y) pow 2)) /\
     (k = &1 \/ k = -- &1) /\ &0 < rho /\ rho <= r /\ rho < &1
     ==> open(schz_cyl ph c rho) /\
         schz_cyl ph c rho SUBSET schz_cyl ph c r /\
         (!u. (schz_graph ph c k u)$3 = c + k * norm u pow 2) /\
         s INTER schz_cyl ph c rho = IMAGE (schz_graph ph c k) (ball(vec 0,rho)) /\
         (!e. &0 <= e /\ e < rho pow 2
              ==> s INTER schz_cyl ph c rho INTER {x | abs(x$3 - c) <= e} =
                  IMAGE (schz_graph ph c k) (cball(vec 0,sqrt e)) /\
                  s INTER schz_cyl ph c rho INTER {x | abs(x$3 - c) = e} =
                  IMAGE (schz_graph ph c k) (sphere(vec 0,sqrt e)) /\
                  sqrt e < rho) /\
         (schz_graph ph c k) continuous_on ball(vec 0,r)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dph") (CONJUNCTS_THEN2 (LABEL_TAC "ch")
    (CONJUNCTS_THEN2 (LABEL_TAC "k") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!u. abs(k * norm(u:real^2) pow 2) = norm u pow 2` (LABEL_TAC "ak") THENL
   [GEN_TAC THEN USE_THEN "k" (DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_ABS_NEG; REAL_ABS_POW; REAL_ABS_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. (schz_graph (ph:real^2->real^2) c k u)$3 = c + k * norm u pow 2`
  (LABEL_TAC "gh") THENL [REWRITE_TAC[schz_graph; SCH5V_PR_AT]; ALL_TAC] THEN
  (* The cylinder is the image of a set in the domain of the lifted chart. *)
  SUBGOAL_THEN `!t. open {y:real^3 | sch5v_pr y IN ball(vec 0,t) /\ abs(y$3 - c) < t}`
  (LABEL_TAC "wo") THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `{y:real^3 | sch5v_pr y IN ball(vec 0,t) /\ abs(y$3 - c) < t} =
                  {y | sch5v_pr y IN ball(vec 0,t)} INTER {y | abs(y$3 - c) < t}`
    SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN SIMP_TAC[SCHZ_PR_OPEN; OPEN_BALL; SCHZ_STRIP_OPEN];
    ALL_TAC] THEN
  SUBGOAL_THEN `s INTER schz_cyl (ph:real^2->real^2) c rho =
                IMAGE (schz_graph ph c k) (ball(vec 0,rho))` (LABEL_TAC "eq") THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; schz_cyl; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `sch5v_pr y IN ball(vec 0:real^2,r) /\ abs((y:real^3)$3 - c) < r`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `sch5v_pr y IN ball(vec 0:real^2,rho)` THEN
        REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "ch" (fun th -> ASM_SIMP_TAC[th]) THEN DISCH_TAC THEN
      EXISTS_TAC `sch5v_pr y` THEN ASM_REWRITE_TAC[schz_graph] THEN
      REWRITE_TAC[schz_lift] THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `norm(u:real^2) pow 2 < rho` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `rho * rho` THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
          UNDISCH_TAC `(u:real^2) IN ball(vec 0,rho)` THEN
          REWRITE_TAC[IN_BALL_0; NORM_POS_LE];
          MATCH_MP_TAC(REAL_ARITH `rho * rho < rho * &1 ==> rho * rho < rho`) THEN
          MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `schz_lift (ph:real^2->real^2) (sch5v_at (c + k * norm u pow 2) u) = x`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[SCHZ_LIFT_FACTS; schz_graph]; ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN USE_THEN "ch" (fun th ->
          W(MP_TAC o PART_MATCH (lhand o rand) th o snd)) THEN
        REWRITE_TAC[SCH5V_PR_AT] THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [UNDISCH_TAC `(u:real^2) IN ball(vec 0,rho)` THEN
            REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
            REWRITE_TAC[REAL_ADD_SUB] THEN USE_THEN "ak" (fun th -> REWRITE_TAC[th]) THEN
            ASM_REAL_ARITH_TAC];
          SIMP_TAC[]];
        EXISTS_TAC `sch5v_at (c + k * norm u pow 2) (u:real^2)` THEN
        ASM_REWRITE_TAC[SCH5V_PR_AT; REAL_ADD_SUB] THEN
        USE_THEN "ak" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[schz_cyl] THEN MATCH_MP_TAC SCH4_DIFFEO_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`{y:real^3 | sch5v_pr y IN ball(vec 0,r)}`;
                          `{x:real^3 | sch5v_pr x IN IMAGE (ph:real^2->real^2) (ball(vec 0,r))}`;
                          `schz_lift (ph':real^2->real^2)`] THEN
    USE_THEN "dph" (fun th -> REWRITE_TAC[MATCH_MP SCHZ_LIFT_DIFFEO th]) THEN
    USE_THEN "wo" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL_0] THEN ASM_MESON_TAC[REAL_LTE_TRANS];
    REWRITE_TAC[schz_cyl] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL_0] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `sqrt e < rho` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!u:real^2. abs((schz_graph ph c k u)$3 - c) = norm u pow 2`
    (LABEL_TAC "habs") THENL
     [GEN_TAC THEN USE_THEN "gh" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[REAL_ADD_SUB] THEN USE_THEN "ak" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    SUBGOAL_THEN `!u:real^2. (norm u pow 2 <= e <=> norm u <= sqrt e) /\
                             (norm u pow 2 = e <=> norm u = sqrt e)` (LABEL_TAC "sq") THENL
     [GEN_TAC THEN MATCH_MP_TAC SCHZ_NORM_SQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM INTER_ASSOC] THEN USE_THEN "eq" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM; IN_BALL_0; IN_CBALL_0;
                IN_SPHERE_0] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) MP_TAC) THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `x:real^3`)) THEN
      USE_THEN "habs" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "sq" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
      EXISTS_TAC `u:real^2` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `u:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      USE_THEN "habs" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "sq" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `u:real^2` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) MP_TAC) THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `x:real^3`)) THEN
      USE_THEN "habs" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "sq" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
      EXISTS_TAC `u:real^2` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `u:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      USE_THEN "habs" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "sq" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `u:real^2` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC SCHZ_GRAPH_SMOOTH THEN
    REWRITE_TAC[OPEN_BALL] THEN
    USE_THEN "dph" (fun th -> REWRITE_TAC[REWRITE_RULE[diffeomorphism_on] th])]);;

let SCHZ_CYL_MONO = prove
 (`!(ph:real^2->real^2) c r1 r2.
     r1 <= r2 ==> schz_cyl ph c r1 SUBSET schz_cyl ph c r2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[schz_cyl] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL_0] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Extrema of the height on S are critical; without saddles                  *)
(* every critical point is an exact local minimum (k = 1) or an exact local *)
(* maximum (k = -1); the global extrema.                                    *)
(* ------------------------------------------------------------------------- *)

let SCHZ_EXTREMUM_CRIT = prove
 (`!g g':real^3->real^3 t.
     sch_neck g g' /\ t IN sphere(vec 0,&1) /\
     ((!s. s IN sphere(vec 0,&1) ==> (g t)$3 <= (g s)$3) \/
      (!s. s IN sphere(vec 0,&1) ==> (g s)$3 <= (g t)$3))
     ==> sch_crit g t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  ASM_REWRITE_TAC[sch_crit] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `((g:real^3->real^3) has_derivative frechet_derivative g (at t)) (at t)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (g:real^3->real^3) (at t))` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCH4_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  ASM_CASES_TAC `v:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `frechet_derivative (g:real^3->real^3) (at t)` LINEAR_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VEC_COMPONENT];
    ALL_TAC] THEN
  ABBREV_TAC `u:real^3 = inv(norm v) % v` THEN
  SUBGOAL_THEN `norm(u:real^3) = &1 /\ (t:real^3) dot u = &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; DOT_RMUL] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0] THEN
    UNDISCH_TAC `orthogonal (t:real^3) v` THEN SIMP_TAC[orthogonal; REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `v:real^3 = norm v % u` SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_CMUL; VECTOR_MUL_COMPONENT] THEN
  SUBGOAL_THEN `(frechet_derivative (g:real^3->real^3) (at t) u)$3 = &0`
  (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
  (* The great circle through t in the direction u. *)
  ABBREV_TAC `cc = \s:real^1. cos(drop s) % (t:real^3) + sin(drop s) % u` THEN
  SUBGOAL_THEN `!s:real^1. (cc:real^1->real^3) s IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "cc" THEN REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1] THEN
    REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
    UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(u:real^3) dot u = &1 /\ (u:real^3) dot t = &0` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM NORM_EQ_1] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `drop s` SIN_CIRCLE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(cc:real^1->real^3) (vec 0) = t` ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN REWRITE_TAC[DROP_VEC; COS_0; SIN_0] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((cc:real^1->real^3) has_vector_derivative u) (at (vec 0))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^3`; `u:real^3`; `vec 0:real^1`] SCH5_CIRCLE_DERIV) THEN
    EXPAND_TAC "cc" THEN REWRITE_TAC[DROP_VEC; COS_0; SIN_0] THEN
    REWRITE_TAC[REAL_NEG_0; VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cc:real^1->real^3`; `u:real^3`; `g:real^3->real^3`;
                 `frechet_derivative (g:real^3->real^3) (at t)`; `vec 0:real^1`]
    SCH5_CHAIN_VECTOR) THEN
  ASM_REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(g:real^3->real^3) o (cc:real^1->real^3)`;
                 `\h:real^1. drop h % frechet_derivative (g:real^3->real^3) (at t) u`;
                 `vec 0:real^1`; `(:real^1)`; `3`] DIFFERENTIAL_COMPONENT_ZERO_AT_MAXMIN) THEN
  ASM_REWRITE_TAC[IN_UNIV; OPEN_UNIV; DIMINDEX_3; ARITH; o_THM] THEN ANTS_TAC THENL
   [USE_THEN "ext" (DISJ_CASES_THEN (fun th -> ASM_MESON_TAC[th]));
    DISCH_THEN(MP_TAC o SPEC `lift(&1)`) THEN
    REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID]]);;

let SCHZ_CRIT_TYPES = prove
 (`!g:real^3->real^3 t.
     sch_morse g /\ sch_saddles g = {} /\ sch_crit g t
     ==> (sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) (&1) (&1) \/
          sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) (-- &1) (-- &1)) /\
         ~(sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) (&1) (&1) /\
           sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) (-- &1) (-- &1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC; MESON_TAC[SCH5_MAX_NOT_SADDLE]] THEN
  UNDISCH_TAC `sch_morse (g:real^3->real^3)` THEN REWRITE_TAC[sch_morse] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^3` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real` (X_CHOOSE_THEN `k2:real` ASSUME_TAC)) THEN
  SUBGOAL_THEN `(k1 = &1 \/ k1 = -- &1) /\ (k2 = &1 \/ k2 = -- &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_hchart (IMAGE (g:real^3->real^3) (sphere(vec 0,&1))) (g t) k1 k2` THEN
    SIMP_TAC[sch_hchart];
    ALL_TAC] THEN
  SUBGOAL_THEN `~sch_hchart (IMAGE (g:real^3->real^3) (sphere(vec 0,&1))) (g t) (&1) (-- &1)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(t:real^3) IN sch_saddles g` MP_TAC THENL
     [REWRITE_TAC[sch_saddles; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[NOT_IN_EMPTY]];
    ALL_TAC] THEN
  UNDISCH_TAC `(k1 = &1 \/ k1 = -- &1) /\ (k2 = &1 \/ k2 = -- &1)` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_MESON_TAC[SCH5_HCHART_SWAP]);;

let SCHZ_EXTREMA_EXIST = prove
 (`!g g':real^3->real^3.
     sch_neck g g'
     ==> ?t0 t1. t0 IN sphere(vec 0,&1) /\ t1 IN sphere(vec 0,&1) /\
                 !s. s IN sphere(vec 0,&1) ==> (g t0)$3 <= (g s)$3 /\ (g s)$3 <= (g t1)$3`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHZ_SURFACE_FACTS) THEN
  SUBGOAL_THEN `(lift o (\s. (g:real^3->real^3) s$3)) continuous_on sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(lift o (\s. (g:real^3->real^3) s$3)) = (\x:real^3. lift(x$3)) o g`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. (g:real^3->real^3) s$3`; `sphere(vec 0:real^3,&1)`]
    CONTINUOUS_ATTAINS_SUP) THEN
  MP_TAC(ISPECL [`\s. (g:real^3->real^3) s$3`; `sphere(vec 0:real^3,&1)`]
    CONTINUOUS_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[COMPACT_SPHERE; SPHERE_EQ_EMPTY;
                  REAL_ARITH `~(&1 < &0)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^3` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`t0:real^3`; `t1:real^3`] THEN ASM_SIMP_TAC[]);;

(* An exact chart with k1 = k2 = k contains points of s on the side k.     *)

let SCHZ_HCHART_POINT = prove
 (`!s (p:real^3) k.
     sch_hchart s p k k ==> ?x e. &0 < e /\ x IN s /\ x$3 = p$3 + k * e`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SCHZ_HCHART_LIFT) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real`
    (X_CHOOSE_THEN `ph:real^2->real^2` (X_CHOOSE_THEN `ph':real^2->real^2`
      STRIP_ASSUME_TAC)))) THEN
  ABBREV_TAC `y:real^3 = sch5v_at ((p:real^3)$3 + k * (r / &2) pow 2)
                                  ((r / &2) % basis 1:real^2)` THEN
  SUBGOAL_THEN `norm(sch5v_pr(y:real^3)) = r / &2` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[SCH5V_PR_AT; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3)$3 = (p:real^3)$3 + k * (r / &2) pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[SCH5V_PR_AT]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`schz_lift (ph:real^2->real^2) y`; `(r / &2) pow 2`] THEN
  ASM_REWRITE_TAC[SCHZ_LIFT_FACTS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sch5v_pr(y:real^3) IN ball(vec 0,r) /\ abs((y:real^3)$3 - (p:real^3)$3) < r`
  (fun th -> FIRST_X_ASSUM(fun ch -> REWRITE_TAC[MATCH_MP ch th]) THEN
             ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[IN_BALL_0; REAL_ADD_SUB] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(k * (r / &2) pow 2) = (r / &2) pow 2` SUBST1_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_ABS_NEG; REAL_ABS_POW] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `r / &2 * &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* The global minimum is an exact local minimum and the global maximum an    *)
(* exact local maximum.                                                       *)

let SCHZ_GLOBAL_TYPES = prove
 (`!g g':real^3->real^3 t.
     sch_neck g g' /\ sch_morse g /\ sch_saddles g = {} /\ t IN sphere(vec 0,&1)
     ==> ((!s. s IN sphere(vec 0,&1) ==> (g t)$3 <= (g s)$3)
          ==> sch_crit g t /\
              sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) (&1) (&1)) /\
         ((!s. s IN sphere(vec 0,&1) ==> (g s)$3 <= (g t)$3)
          ==> sch_crit g t /\
              sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) (-- &1) (-- &1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
  (SUBGOAL_THEN `sch_crit (g:real^3->real^3) t` ASSUME_TAC THENL
    [MATCH_MP_TAC SCHZ_EXTREMUM_CRIT THEN EXISTS_TAC `g':real^3->real^3` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `t:real^3`] SCHZ_CRIT_TYPES) THEN
  ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(TAUT `~b ==> (a \/ b) /\ c ==> a`);
    MATCH_MP_TAC(TAUT `~a ==> (a \/ b) /\ c ==> b`)] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SCHZ_HCHART_POINT) THEN
  REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `e:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^3` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `x:real^3`)) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The band lemma.  For a complete flow Psi with height                      *)
(* x3 + t that preserves a defining function rho of S along trajectories    *)
(* staying near a compact set C of regular points, a closed part Rest of S  *)
(* inside C, relatively open in the band S(a <= x3 <= b), is invariant      *)
(* within the band.                                                          *)
(* ------------------------------------------------------------------------- *)

let SCHZ_SEG1 = prove
 (`!t:real^1. interval[vec 0,t] UNION interval[t,vec 0] = segment[vec 0,t]`,
  GEN_TAC THEN REWRITE_TAC[SEGMENT_1; EXTENSION; IN_UNION; IN_INTERVAL_1; DROP_VEC] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
  ASM_REAL_ARITH_TAC);;

let SCHZ_BAND = prove
 (`!(Psi:real^1->real^3->real^3) (rho:real^3->real) (S:real^3->bool) C B d Rest a b.
     (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
     (!t x. (Psi t x)$3 = x$3 + drop t) /\
     (!x. (\t. Psi t x) continuous_on (:real^1)) /\
     (!x s t. norm(Psi s x - Psi t x) <= B * abs(drop s - drop t)) /\ &0 < d /\
     (!x t. (!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
                 ==> ?y. y IN C /\ dist(y,Psi u x) < &2 * d)
            ==> rho(Psi t x) = rho x) /\
     (!x. (?y. y IN C /\ dist(y,x) < &2 * d) ==> (x IN S <=> rho x = &1)) /\
     closed Rest /\ Rest SUBSET C /\ Rest SUBSET S /\
     (!x. x IN Rest ==> a <= x$3 /\ x$3 <= b) /\
     (?e. &0 < e /\
          !p q. p IN Rest /\ q IN S /\ a <= q$3 /\ q$3 <= b /\ dist(p,q) < e
                ==> q IN Rest)
     ==> !x t. x IN Rest /\ a <= x$3 + drop t /\ x$3 + drop t <= b ==> Psi t x IN Rest`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P0") (CONJUNCTS_THEN2 (LABEL_TAC "GRP")
    (CONJUNCTS_THEN2 (LABEL_TAC "HT") (CONJUNCTS_THEN2 (LABEL_TAC "CT")
    (CONJUNCTS_THEN2 (LABEL_TAC "LIP") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "FI") (CONJUNCTS_THEN2 (LABEL_TAC "SS")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "RB")
     (X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RO"))))))))))))))) THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real^1`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a <= (x:real^3)$3 /\ x$3 <= b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `J = {u | u IN segment[vec 0:real^1,t] /\ (Psi:real^1->real^3->real^3) u x IN Rest}` THEN
  SUBGOAL_THEN `J = segment[vec 0:real^1,t]` MP_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "J" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN SIMP_TAC[ENDS_IN_SEGMENT]] THEN
  MP_TAC(ISPEC `segment[vec 0:real^1,t]` CONNECTED_CLOPEN) THEN
  REWRITE_TAC[CONNECTED_SEGMENT] THEN DISCH_THEN(MP_TAC o SPEC `J:real^1->bool`) THEN
  MATCH_MP_TAC(TAUT `~c /\ a /\ b ==> (a /\ b ==> c \/ d) ==> d`) THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^1` THEN
    EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    (* J is open in the segment *)
    REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN CONJ_TAC THENL
     [EXPAND_TAC "J" THEN SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `u:real^1` THEN EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    ABBREV_TAC `p:real^3 = (Psi:real^1->real^3->real^3) u x` THEN
    EXISTS_TAC `min e d / (abs B + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!s:real^1. abs(drop s - drop u) < min e d / (abs B + &1)
                             ==> dist(p,(Psi:real^1->real^3->real^3) s x) < min e d`
    (LABEL_TAC "NEAR") THENL
     [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN EXPAND_TAC "p" THEN
      REWRITE_TAC[dist] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `B * abs(drop u - drop s)` THEN
      USE_THEN "LIP" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(abs B + &1) * abs(drop u - drop s)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `abs(drop s - drop u) < min e d / (abs B + &1)` THEN
      SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < abs B + &1`] THEN
      REWRITE_TAC[REAL_ABS_SUB] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(drop w - drop u) < min e d / (abs B + &1)` ASSUME_TAC THENL
     [UNDISCH_TAC `dist(u:real^1,w) < min e d / (abs B + &1)` THEN
      REWRITE_TAC[DIST_REAL; GSYM drop] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3) IN S /\ p IN C` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(rho:real^3->real)((Psi:real^1->real^3->real^3) w x) = rho(p:real^3)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(Psi:real^1->real^3->real^3) w x = Psi (w - u) p` SUBST1_TAC THENL
       [EXPAND_TAC "p" THEN USE_THEN "GRP" (fun th -> REWRITE_TAC[th]) THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "FI" MATCH_MP_TAC THEN
      X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN EXISTS_TAC `p:real^3` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(Psi:real^1->real^3->real^3) v p = Psi (u + v) x` SUBST1_TAC THENL
       [EXPAND_TAC "p" THEN USE_THEN "GRP" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x < min e d /\ &0 < d ==> x < &2 * d`) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "NEAR" MATCH_MP_TAC THEN
      UNDISCH_TAC `abs(drop w - drop u) < min e d / (abs B + &1)` THEN
      UNDISCH_TAC `(v:real^1) IN interval[vec 0,w - u] UNION interval[w - u,vec 0]` THEN
      REWRITE_TAC[IN_UNION; IN_INTERVAL_1; DROP_VEC; DROP_ADD; DROP_SUB] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "RO" MATCH_MP_TAC THEN EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(rho:real^3->real)(p:real^3) = &1` ASSUME_TAC THENL
       [USE_THEN "SS" (MP_TAC o SPEC `p:real^3`) THEN ANTS_TAC THENL
         [EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      USE_THEN "SS" (MP_TAC o SPEC `(Psi:real^1->real^3->real^3) w x`) THEN ANTS_TAC THENL
       [EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `x < min e d /\ &0 < d ==> x < &2 * d`) THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "NEAR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      USE_THEN "HT" (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `(w:real^1) IN segment[vec 0,t]` THEN
      REWRITE_TAC[SEGMENT_1; DROP_VEC] THEN COND_CASES_TAC THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "HT" (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `(w:real^1) IN segment[vec 0,t]` THEN
      REWRITE_TAC[SEGMENT_1; DROP_VEC] THEN COND_CASES_TAC THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x < min e d ==> x < e`) THEN
      USE_THEN "NEAR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* J is closed in the segment *)
    EXPAND_TAC "J" THEN MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^1)` THEN USE_THEN "CT" (fun th -> REWRITE_TAC[th; SUBSET_UNIV])]);;

(* ------------------------------------------------------------------------- *)
(* One step of the sublevel induction.  If the band                          *)
(* S(a1 <= x3 <= a2) is the disjoint union of a compact cap (above a1, with  *)
(* connected top) and a closed flow-invariant part, then the property       *)
(* that points of the level a joined in the sublevel set are joined in    *)
(* the level passes from a1 to a2.                                          *)
(* ------------------------------------------------------------------------- *)

let SCHZ_STEP = prove
 (`!(Psi:real^1->real^3->real^3) (S:real^3->bool) Cap Rest a1 a2.
     (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
     (!t x. (Psi t x)$3 = x$3 + drop t) /\
     (\w. Psi (fstcart w) (sndcart w)) continuous_on (:real^(1,3)finite_sum) /\
     a1 < a2 /\ closed S /\
     {x | x IN S /\ a1 <= x$3 /\ x$3 <= a2} = Cap UNION Rest /\
     Cap INTER Rest = {} /\ compact Cap /\ closed Rest /\
     (!x. x IN Cap ==> a1 < x$3) /\
     connected {x | x IN Cap /\ x$3 = a2} /\
     (!x t. x IN Rest /\ a1 <= x$3 + drop t /\ x$3 + drop t <= a2 ==> Psi t x IN Rest) /\
     (!x y. x IN S /\ x$3 = a1 /\ y IN S /\ y$3 = a1 /\
            connected_component {z | z IN S /\ z$3 <= a1} x y
            ==> connected_component {z | z IN S /\ z$3 = a1} x y)
     ==> (!x y. x IN S /\ x$3 = a2 /\ y IN S /\ y$3 = a2 /\
                connected_component {z | z IN S /\ z$3 <= a2} x y
                ==> connected_component {z | z IN S /\ z$3 = a2} x y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P0") (CONJUNCTS_THEN2 (LABEL_TAC "GRP")
    (CONJUNCTS_THEN2 (LABEL_TAC "HT") (CONJUNCTS_THEN2 (LABEL_TAC "CT")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "SPLIT") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CAPH") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "INV") (LABEL_TAC "IH")))))))))))))) THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
  ABBREV_TAC `L2 = {z:real^3 | z IN S /\ z$3 <= a2}` THEN
  ABBREV_TAC `L1 = {z:real^3 | z IN S /\ z$3 <= a1}` THEN
  ABBREV_TAC `K = connected_component (L2:real^3->bool) x` THEN
  SUBGOAL_THEN `connected (K:real^3->bool) /\ K SUBSET L2 /\ (x:real^3) IN K /\ (y:real^3) IN K`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT;
                                    CONNECTED_COMPONENT_SUBSET] THEN
    REWRITE_TAC[IN] THEN CONJ_TAC THENL
     [REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN EXPAND_TAC "L2" THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L2:real^3->bool) = L1 UNION Cap UNION Rest` ASSUME_TAC THENL
   [USE_THEN "SPLIT" (SUBST1_TAC o SYM) THEN MAP_EVERY EXPAND_TAC ["L1"; "L2"] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    ASM_CASES_TAC `(z:real^3) IN S` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(L1:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L1" THEN
    REWRITE_TAC[SET_RULE `{z:real^3 | z IN S /\ P z} = S INTER {z | P z}`] THEN
    MATCH_MP_TAC CLOSED_INTER THEN ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE];
    ALL_TAC] THEN
  ASM_CASES_TAC `(K:real^3->bool) INTER Cap = {}` THENL
   [ALL_TAC;
    (* The component meets the cap, hence lies in it. *)
    SUBGOAL_THEN `(K:real^3->bool) SUBSET Cap` ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN EXISTS_TAC `L2:real^3->bool` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
        ASM SET_TAC[];
        SUBGOAL_THEN `Cap = (L2:real^3->bool) DIFF (L1 UNION Rest)`
        (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
         [SUBGOAL_THEN `(L1:real^3->bool) INTER Cap = {}` MP_TAC THENL
           [EXPAND_TAC "L1" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
            X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
            USE_THEN "CAPH" (MP_TAC o SPEC `z:real^3`) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
            UNDISCH_TAC `(z:real^3)$3 <= a1` THEN REAL_ARITH_TAC;
            ASM SET_TAC[]];
          MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN ASM_SIMP_TAC[CLOSED_UNION]];
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_OF_SUBSET THEN
    EXISTS_TAC `{z:real^3 | z IN Cap /\ z$3 = a2}` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `{z:real^3 | z IN Cap /\ z$3 = a2}` THEN
    ASM_REWRITE_TAC[SUBSET_REFL; IN_ELIM_THM] THEN ASM SET_TAC[]] THEN
  (* The component lies in L1 and Rest: retract it to the level a1. *)
  SUBGOAL_THEN `(K:real^3->bool) SUBSET L1 UNION Rest` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `r = \z:real^3. if z$3 <= a1 then z
                              else (Psi:real^1->real^3->real^3) (lift(a1 - z$3)) z` THEN
  SUBGOAL_THEN `(r:real^3->real^3) continuous_on (L1 UNION Rest)` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_ON_ID];
      SUBGOAL_THEN `(\z:real^3. (Psi:real^1->real^3->real^3) (lift(a1 - z$3)) z) =
                    (\w. Psi (fstcart w) (sndcart w)) o
                    (\z:real^3. pastecart (lift(a1 - z$3)) z)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
        REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(:real^(1,3)finite_sum)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]];
      X_GEN_TAC `z:real^3` THEN DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [UNDISCH_TAC `(z:real^3) IN L1` THEN EXPAND_TAC "L1" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `(z:real^3)$3 = a1` ASSUME_TAC THENL
         [SUBGOAL_THEN `(z:real^3) IN Cap UNION Rest` MP_TAC THENL
           [ASM SET_TAC[]; ALL_TAC] THEN
          USE_THEN "SPLIT" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN
          ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[REAL_SUB_REFL; LIFT_NUM]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN Rest ==> (Psi:real^1->real^3->real^3) (lift(a1 - z$3)) z IN Rest /\
                                  (Psi (lift(a1 - z$3)) z)$3 = a1`
  (LABEL_TAC "DOWN") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "HT" (fun th -> REWRITE_TAC[th; LIFT_DROP]) THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    USE_THEN "INV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    UNDISCH_TAC `a1 < a2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN Rest ==> z IN S /\ a1 <= z$3 /\ z$3 <= a2` (LABEL_TAC "RB") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN Cap UNION Rest` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "SPLIT" (SUBST1_TAC o SYM) THEN SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (r:real^3->real^3) K SUBSET L1` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    EXPAND_TAC "r" THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN `(z:real^3) IN L1 UNION Rest` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "L1" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `(z:real^3) IN Rest` ASSUME_TAC THENL
       [SUBGOAL_THEN `(z:real^3) IN L1 UNION Rest` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_UNION] THEN EXPAND_TAC "L1" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "DOWN" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN Rest`)) THEN STRIP_TAC THEN
      EXPAND_TAC "L1" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a2 <= a1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN Rest /\ (y:real^3) IN Rest` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `(x:real^3) IN L1 UNION Rest` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC];
      SUBGOAL_THEN `(y:real^3) IN L1 UNION Rest` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC]] THEN
    REWRITE_TAC[IN_UNION] THEN EXPAND_TAC "L1" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^3->real^3) x = Psi (lift(a1 - a2)) x /\
                (r:real^3->real^3) y = Psi (lift(a1 - a2)) y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Joined in L1, hence (by the hypothesis at a1) in the level a1. *)
  SUBGOAL_THEN `(Psi:real^1->real^3->real^3) (lift(a1 - a2)) x IN Rest /\
                (Psi (lift(a1 - a2)) x)$3 = a1` STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `(x:real^3)$3 = a2`)) THEN
    USE_THEN "DOWN" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^3) IN Rest`)]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(Psi:real^1->real^3->real^3) (lift(a1 - a2)) y IN Rest /\
                (Psi (lift(a1 - a2)) y)$3 = a1` STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `(y:real^3)$3 = a2`)) THEN
    USE_THEN "DOWN" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^3) IN Rest`)]);
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_component {z:real^3 | z IN S /\ z$3 = a1}
                  ((Psi:real^1->real^3->real^3) (lift(a1 - a2)) x) (Psi (lift(a1 - a2)) y)`
  ASSUME_TAC THENL
   [USE_THEN "IH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "RB" (MP_TAC o C MATCH_MP
        (ASSUME `(Psi:real^1->real^3->real^3) (lift(a1 - a2)) x IN Rest`)) THEN SIMP_TAC[];
      USE_THEN "RB" (MP_TAC o C MATCH_MP
        (ASSUME `(Psi:real^1->real^3->real^3) (lift(a1 - a2)) y IN Rest`)) THEN SIMP_TAC[];
      REWRITE_TAC[connected_component] THEN
      EXISTS_TAC `IMAGE (r:real^3->real^3) K` THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        ASM_REWRITE_TAC[];
        SUBST1_TAC(SYM(ASSUME `(r:real^3->real^3) x = Psi (lift(a1 - a2)) x`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        SUBST1_TAC(SYM(ASSUME `(r:real^3->real^3) y = Psi (lift(a1 - a2)) y`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* Flow the component of the level a1 back up to the level a2. *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected_component]) THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^3->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `IMAGE ((Psi:real^1->real^3->real^3) (lift(a2 - a1))) G` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Psi:real^1->real^3->real^3) (lift(a2 - a1)) =
                  (\w. Psi (fstcart w) (sndcart w)) o (\z:real^3. pastecart (lift(a2 - a1)) z)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^(1,3)finite_sum)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN S /\ z$3 = a1` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN Rest` ASSUME_TAC THENL
     [SUBGOAL_THEN `(z:real^3) IN Cap UNION Rest` MP_TAC THENL
       [USE_THEN "SPLIT" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "CAPH" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN Cap`)) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Psi:real^1->real^3->real^3) (lift(a2 - a1)) z IN Rest` ASSUME_TAC THENL
     [USE_THEN "INV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "RB" (MP_TAC o SPEC `(Psi:real^1->real^3->real^3) (lift(a2 - a1)) z`) THEN
      ASM_SIMP_TAC[];
      USE_THEN "HT" (fun th -> REWRITE_TAC[th; LIFT_DROP]) THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(Psi:real^1->real^3->real^3) (lift(a1 - a2)) x` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "GRP" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM LIFT_ADD; REAL_ARITH `(a1 - a2) + (a2 - a1) = &0`; LIFT_NUM] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(Psi:real^1->real^3->real^3) (lift(a1 - a2)) y` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "GRP" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM LIFT_ADD; REAL_ARITH `(a1 - a2) + (a2 - a1) = &0`; LIFT_NUM] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Finite-set helpers and the sublevel induction: as long as                 *)
(* only local minima lie below the level a, points of the level that are    *)
(* joined in the sublevel set are joined in the level.                      *)
(* ------------------------------------------------------------------------- *)

let SCHZ_FINITE_GAP = prove
 (`!s:real->bool. FINITE s
                  ==> ?e. &0 < e /\ !x y. x IN s /\ y IN s /\ ~(x = y) ==> e < abs(x - y)`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `t:real->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `t:real->bool = {}` THENL
   [EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\y. abs(a - y)) (t:real->bool)` INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y0:real` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < inf(IMAGE (\y. abs(a - y)) (t:real->bool))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(a:real = y0)` MP_TAC THENL [ASM_MESON_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min e (inf(IMAGE (\y. abs(a - y)) (t:real->bool)) / &2)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT] THEN MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`] o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let SCHZ_FINITE_POS_MIN = prove
 (`!s (f:A->real). FINITE s /\ (!x. x IN s ==> &0 < f x)
                   ==> ?d. &0 < d /\ !x. x IN s ==> d <= f x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (f:A->real) s` INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `inf(IMAGE (f:A->real) s)` THEN ASM_SIMP_TAC[]);;

let SCHZ_INDUCT = prove
 (`!(Psi:real^1->real^3->real^3) (S:real^3->bool) (CV:real->bool) (MINV:real->bool)
    (cap:real->real^3->bool) (rest:real->real^3->bool) eta.
     (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
     (!t x. (Psi t x)$3 = x$3 + drop t) /\
     (\w. Psi (fstcart w) (sndcart w)) continuous_on (:real^(1,3)finite_sum) /\
     closed S /\ FINITE CV /\ &0 < eta /\
     (!c c'. c IN CV /\ c' IN CV /\ ~(c = c') ==> &2 * eta < abs(c - c')) /\
     (!x. x IN S ==> ?c. c IN CV /\ c <= x$3) /\
     (!a1 a2 x t. a1 < a2 /\ (!c z. c IN CV /\ a1 <= z /\ z <= a2 ==> eta <= abs(z - c)) /\
                  x IN S /\ a1 <= x$3 /\ x$3 <= a2 /\
                  a1 <= x$3 + drop t /\ x$3 + drop t <= a2
                  ==> Psi t x IN S) /\
     (!c. c IN CV /\ c IN MINV
          ==> {x | x IN S /\ c - eta <= x$3 /\ x$3 <= c + eta} = cap c UNION rest c /\
              cap c INTER rest c = {} /\ compact(cap c) /\ closed(rest c) /\
              (!x. x IN cap c ==> c - eta < x$3) /\
              connected {x | x IN cap c /\ x$3 = c + eta} /\
              (!x t. x IN rest c /\ c - eta <= x$3 + drop t /\ x$3 + drop t <= c + eta
                     ==> Psi t x IN rest c))
     ==> !a. (!c. c IN CV ==> eta <= abs(a - c)) /\ (!c. c IN CV /\ c < a ==> c IN MINV)
             ==> !x y. x IN S /\ x$3 = a /\ y IN S /\ y$3 = a /\
                       connected_component {z | z IN S /\ z$3 <= a} x y
                       ==> connected_component {z | z IN S /\ z$3 = a} x y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P0") (CONJUNCTS_THEN2 (LABEL_TAC "GRP")
    (CONJUNCTS_THEN2 (LABEL_TAC "HT") (CONJUNCTS_THEN2 (LABEL_TAC "CT")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "GAP") (CONJUNCTS_THEN2 (LABEL_TAC "LOW")
    (CONJUNCTS_THEN2 (LABEL_TAC "REG") (LABEL_TAC "MIN"))))))))))) THEN
  SUBGOAL_THEN
   `!n a. CARD {c | c IN CV /\ c < a} = n /\
          (!c. c IN CV ==> eta <= abs(a - c)) /\ (!c. c IN CV /\ c < a ==> c IN MINV)
          ==> !x y. x IN (S:real^3->bool) /\ x$3 = a /\ y IN S /\ y$3 = a /\
                    connected_component {z | z IN S /\ z$3 <= a} x y
                    ==> connected_component {z | z IN S /\ z$3 = a} x y`
  (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [(* No critical value below a: the level is empty. *)
    X_GEN_TAC `a:real` THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `FINITE {c | c IN CV /\ c < a}` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `CV:real->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `CARD {c | c IN CV /\ c < a} = 0` THEN ASM_SIMP_TAC[CARD_EQ_0] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN DISCH_TAC THEN
    USE_THEN "LOW" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN S`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `c < a` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `c:real` o check (fun th ->
        can (term_match [] `!c:real. c IN CV ==> eta <= abs(a - c)`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `a:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {c | c IN CV /\ c < a}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `CV:real->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~({c | c IN CV /\ c < a} = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `CARD {c | c IN CV /\ c < a} = SUC n` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `{c | c IN CV /\ c < a}` SUP_FINITE) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = sup {c | c IN CV /\ c < a}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "MAX")) THEN
  SUBGOAL_THEN `c0 + eta <= a` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `c0:real` o check (fun th ->
      can (term_match [] `!c:real. c IN CV ==> eta <= abs(a - c)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* The level a' = c0 - eta below the last critical value. *)
  SUBGOAL_THEN
   `!x y. x IN (S:real^3->bool) /\ x$3 = c0 - eta /\ y IN S /\ y$3 = c0 - eta /\
          connected_component {z | z IN S /\ z$3 <= c0 - eta} x y
          ==> connected_component {z | z IN S /\ z$3 = c0 - eta} x y`
  (LABEL_TAC "PA1") THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `{c | c IN CV /\ c < c0 - eta} = {c | c IN CV /\ c < a} DELETE c0`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE] THEN X_GEN_TAC `c:real` THEN
        EQ_TAC THENL [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "MAX" (MP_TAC o SPEC `c:real`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
        USE_THEN "GAP" (MP_TAC o SPECL [`c:real`; `c0:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[CARD_DELETE; IN_ELIM_THM] THEN ARITH_TAC];
      X_GEN_TAC `c:real` THEN DISCH_TAC THEN ASM_CASES_TAC `c:real = c0` THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "GAP" (MP_TAC o SPECL [`c:real`; `c0:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `c:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!c:real. c IN CV /\ c < a ==> c IN MINV`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* Across the local minimum at c0. *)
  SUBGOAL_THEN `(c0:real) IN MINV` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!c:real. c IN CV /\ c < a ==> c IN MINV`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "MIN" (MP_TAC o SPEC `c0:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `S:real^3->bool`; `(cap:real->real^3->bool) c0`;
                 `(rest:real->real^3->bool) c0`; `c0 - eta`; `c0 + eta`] SCHZ_STEP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  (* Up the regular band from c0 + eta to a. *)
  ASM_CASES_TAC `a = c0 + eta` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `S:real^3->bool`; `{}:real^3->bool`;
                 `{x:real^3 | x IN S /\ c0 + eta <= x$3 /\ x$3 <= a}`; `c0 + eta`; `a:real`]
    SCHZ_STEP) THEN
  ASM_REWRITE_TAC[UNION_EMPTY; INTER_EMPTY; COMPACT_EMPTY; NOT_IN_EMPTY; EMPTY_GSPEC;
                  CONNECTED_EMPTY] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SET_RULE `{x:real^3 | x IN S /\ P x} = S INTER {x | P x}`] THEN
    MATCH_MP_TAC CLOSED_INTER THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SET_RULE `{x:real^3 | a <= x$3 /\ x$3 <= b} = {x | a <= x$3} INTER {x | x$3 <= b}`] THEN
    MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE];
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE]];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real^1`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN USE_THEN "HT" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "REG" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`c0 + eta`; `a:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`c:real`; `z:real`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `c < a` THENL
     [USE_THEN "MAX" (MP_TAC o SPEC `c:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `c:real` o check (fun th ->
        can (term_match [] `!c:real. c IN CV ==> eta <= abs(a - c)`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* A cap at a local maximum closes the sublevel component of                 *)
(* its boundary circle to a clopen subset of S, hence to all of S.          *)
(* ------------------------------------------------------------------------- *)

let SCHZ_CAP_CLOSES = prove
 (`!(S:real^3->bool) O a c.
     closed S /\ connected S /\ locally connected S /\ open O /\ a < c /\
     compact(S INTER O INTER {x | a <= x$3}) /\
     (!x. x IN S INTER O ==> x$3 <= c) /\
     connected(S INTER O INTER {x | x$3 = a}) /\
     ~(S INTER O INTER {x | x$3 = a} = {}) /\
     (!x. x IN S INTER O INTER {x | x$3 = a}
          ==> ?e. &0 < e /\
                  !y. y IN S /\ dist(x,y) < e
                      ==> y IN O /\
                          (y$3 <= a
                           ==> ?Q. connected Q /\ Q SUBSET {z | z IN S /\ z$3 <= a} /\
                                   y IN Q /\ ~(Q INTER S INTER O INTER {x | x$3 = a} = {}))) /\
     (!x y. x IN S /\ x$3 = a /\ y IN S /\ y$3 = a /\
            connected_component {z | z IN S /\ z$3 <= a} x y
            ==> connected_component {z | z IN S /\ z$3 = a} x y)
     ==> !x. x IN S ==> x$3 <= c`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "TOP")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "NB") (LABEL_TAC "P"))))))))))) THEN
  ABBREV_TAC `Cap = (S:real^3->bool) INTER O INTER {x | a <= x$3}` THEN
  ABBREV_TAC `Cir = (S:real^3->bool) INTER O INTER {x | x$3 = a}` THEN
  ABBREV_TAC `L = {z:real^3 | z IN S /\ z$3 <= a}` THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  ABBREV_TAC `K = connected_component (L:real^3->bool) x0` THEN
  SUBGOAL_THEN `Cir SUBSET (Cap:real^3->bool) /\ Cir SUBSET (L:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Cap"; "Cir"; "L"] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Cir:real^3->bool) SUBSET K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(L:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    REWRITE_TAC[SET_RULE `{z:real^3 | z IN S /\ P z} = S INTER {z | P z}`] THEN
    MATCH_MP_TAC CLOSED_INTER THEN ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^3->bool) SUBSET L /\ closed K /\ connected K` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    ASM_SIMP_TAC[CONNECTED_COMPONENT_SUBSET; CLOSED_CONNECTED_COMPONENT;
                 CONNECTED_CONNECTED_COMPONENT];
    ALL_TAC] THEN
  (* The points of K on the level a lie on the circle. *)
  SUBGOAL_THEN `!z:real^3. z IN K /\ z$3 = a ==> z IN Cir` (LABEL_TAC "KC") THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `connected_component {w:real^3 | w IN S /\ w$3 = a} x0 z` MP_TAC THENL
     [USE_THEN "P" MATCH_MP_TAC THEN
      SUBGOAL_THEN `(x0:real^3) IN Cir /\ (z:real^3) IN L` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MAP_EVERY EXPAND_TAC ["Cir"; "L"] THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN K` THEN EXPAND_TAC "K" THEN REWRITE_TAC[IN];
      ALL_TAC] THEN
    REWRITE_TAC[connected_component] THEN
    DISCH_THEN(X_CHOOSE_THEN `G:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(G:real^3->bool) SUBSET Cir` MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN
      EXISTS_TAC `{w:real^3 | w IN S /\ w$3 = a}` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL
         [EXPAND_TAC "Cir" THEN REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[];
          SUBGOAL_THEN `Cir = (Cap:real^3->bool) INTER {x | x$3 = a}` SUBST1_TAC THENL
           [MAP_EVERY EXPAND_TAC ["Cap"; "Cir"] THEN
            REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[REAL_LE_REFL];
            MATCH_MP_TAC CLOSED_INTER THEN
            ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_STANDARD_HYPERPLANE]]];
        REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `O:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "Cir" THEN
        REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
        ASM SET_TAC[]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  (* K union Cap is open and closed in S. *)
  SUBGOAL_THEN `(K:real^3->bool) UNION Cap = S` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOPEN] o check
      (fun th -> concl th = `connected(S:real^3->bool)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `(K:real^3->bool) UNION Cap`) THEN
    MATCH_MP_TAC(TAUT `~c /\ a /\ b ==> (a /\ b ==> c \/ d) ==> d`) THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      (* open in S *)
      REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN CONJ_TAC THENL
       [MAP_EVERY EXPAND_TAC ["Cap"] THEN ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `!z:real^3. z IN Cir ==> ?e. &0 < e /\ ball(z,e) INTER S SUBSET K UNION Cap`
      (LABEL_TAC "CIRC") THENL
       [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        USE_THEN "NB" (MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN Cir`)) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_UNION] THEN
        X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        ASM_CASES_TAC `(y:real^3)$3 <= a` THENL
         [DISJ1_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_THEN(X_CHOOSE_THEN `Q:real^3->bool` STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN `(Q:real^3->bool) UNION Cir SUBSET K` MP_TAC THENL
           [EXPAND_TAC "K" THEN MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
            ASM_REWRITE_TAC[IN_UNION] THEN CONJ_TAC THENL
             [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[];
              ASM SET_TAC[]];
            ASM SET_TAC[]];
          DISJ2_TAC THEN EXPAND_TAC "Cap" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
       [ASM_CASES_TAC `(z:real^3)$3 = a` THENL
         [USE_THEN "CIRC" MATCH_MP_TAC THEN USE_THEN "KC" MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `(z:real^3) IN L` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "L" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        ABBREV_TAC `U = {x:real^3 | x IN S /\ x$3 < a}` THEN
        SUBGOAL_THEN `(z:real^3) IN U` ASSUME_TAC THENL
         [EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `open_in (subtopology euclidean S) (U:real^3->bool)` ASSUME_TAC THENL
         [EXPAND_TAC "U" THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
          EXISTS_TAC `{x:real^3 | x$3 < a}` THEN REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN
          SET_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `open_in (subtopology euclidean S) (connected_component U (z:real^3))`
        MP_TAC THENL
         [UNDISCH_TAC `locally connected (S:real^3->bool)` THEN
          REWRITE_TAC[LOCALLY_CONNECTED_OPEN_COMPONENT] THEN DISCH_THEN MATCH_MP_TAC THEN
          EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[IN_COMPONENTS] THEN
          EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
        DISCH_THEN(MP_TAC o SPEC `z:real^3` o CONJUNCT2) THEN ANTS_TAC THENL
         [REWRITE_TAC[IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `connected_component U (z:real^3) SUBSET K` MP_TAC THENL
         [SUBGOAL_THEN `(K:real^3->bool) = connected_component L z` SUBST1_TAC THENL
           [EXPAND_TAC "K" THEN CONV_TAC SYM_CONV THEN
            MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
            UNDISCH_TAC `(z:real^3) IN K` THEN EXPAND_TAC "K" THEN REWRITE_TAC[];
            ALL_TAC] THEN
          MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
          REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT] THEN CONJ_TAC THENL
           [REWRITE_TAC[IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN ASM_REWRITE_TAC[];
            MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U:real^3->bool` THEN
            REWRITE_TAC[CONNECTED_COMPONENT_SUBSET] THEN MAP_EVERY EXPAND_TAC ["U"; "L"] THEN
            REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]];
          UNDISCH_TAC `ball(z:real^3,e) INTER S SUBSET connected_component U z` THEN
          SET_TAC[]];
        (* z in Cap *)
        ASM_CASES_TAC `(z:real^3)$3 = a` THENL
         [USE_THEN "CIRC" MATCH_MP_TAC THEN UNDISCH_TAC `(z:real^3) IN Cap` THEN
          MAP_EVERY EXPAND_TAC ["Cap"; "Cir"] THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
          ASM_SIMP_TAC[];
          SUBGOAL_THEN `open (O INTER {x:real^3 | x$3 > a})` MP_TAC THENL
           [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT];
            ALL_TAC] THEN
          REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
          ANTS_TAC THENL
           [UNDISCH_TAC `(z:real^3) IN Cap` THEN EXPAND_TAC "Cap" THEN
            REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
            ASM_REWRITE_TAC[real_gt] THEN ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
          ASM_REWRITE_TAC[] THEN EXPAND_TAC "Cap" THEN
          UNDISCH_TAC `ball(z:real^3,e) SUBSET O INTER {x | x$3 > a}` THEN
          REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_ELIM_THM; real_gt] THEN
          MESON_TAC[REAL_LT_IMP_LE]]];
      (* closed in S *)
      MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL
       [EXPAND_TAC "Cap" THEN ASM SET_TAC[];
        MATCH_MP_TAC CLOSED_UNION THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN K UNION Cap` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(z:real^3) IN L` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "L" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    USE_THEN "TOP" MATCH_MP_TAC THEN UNDISCH_TAC `(z:real^3) IN Cap` THEN
    EXPAND_TAC "Cap" THEN REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]]);;

(* Near the circle cut out at depth eta below an exact local maximum, the   *)
(* points of S below the circle are joined to it by radial arcs of S.      *)

let SCHZ_MAX_NBHD = prove
 (`!(S:real^3->bool) (ph:real^2->real^2) c rho eta x.
     open(schz_cyl ph c rho) /\
     S INTER schz_cyl ph c rho = IMAGE (schz_graph ph c (-- &1)) (ball(vec 0,rho)) /\
     (schz_graph ph c (-- &1)) continuous_on ball(vec 0,rho) /\
     &0 < eta /\ eta < rho pow 2 /\
     x IN S INTER schz_cyl ph c rho INTER {x | x$3 = c - eta}
     ==> ?e. &0 < e /\
             !y. y IN S /\ dist(x,y) < e
                 ==> y IN schz_cyl ph c rho /\
                     (y$3 <= c - eta
                      ==> ?Q. connected Q /\ Q SUBSET {z | z IN S /\ z$3 <= c - eta} /\
                              y IN Q /\
                              ~(Q INTER S INTER schz_cyl ph c rho INTER {x | x$3 = c - eta} = {}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u:real^2. (schz_graph ph c (-- &1) u)$3 = c - norm u pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[schz_graph; SCH5V_PR_AT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `open(schz_cyl (ph:real^2->real^2) c rho)` THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN schz_cyl ph c rho` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(x:real^3,e) SUBSET schz_cyl ph c rho` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?u:real^2. u IN ball(vec 0,rho) /\ y = schz_graph ph c (-- &1) u`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^3) IN S INTER schz_cyl ph c rho` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER]; ASM_REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `eta <= norm(u:real^2) pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3)$3 <= c - eta` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(u:real^2)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POS_LT] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `eta <= norm(vec 0:real^2) pow 2` THEN REWRITE_TAC[NORM_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `lam = sqrt eta / norm(u:real^2)` THEN
  SUBGOAL_THEN `&0 < lam /\ lam <= &1 /\ norm(lam % u:real^2) = sqrt eta` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    SUBGOAL_THEN `abs(sqrt eta) = sqrt eta /\ &0 < sqrt eta` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT; REAL_ABS_REFL; SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[u:real^2,lam % u] SUBSET ball(vec 0,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] (ISPECL [`vec 0:real^2`; `rho:real`]
      CONVEX_BALL)) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(u:real^2) IN ball(vec 0,rho)` THEN
    REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN
    SUBGOAL_THEN `abs lam = lam` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * norm(u:real^2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (schz_graph ph c (-- &1)) (segment[u:real^2,lam % u])` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_SEGMENT] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `w:real^2` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `schz_graph ph c (-- &1) (w:real^2) IN S INTER schz_cyl ph c rho`
      MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
        SIMP_TAC[IN_INTER]];
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `sqrt eta <= norm(w:real^2)` MP_TAC THENL
       [UNDISCH_TAC `(w:real^2) IN segment[u,lam % u]` THEN
        REWRITE_TAC[segment; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `th:real` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB; NORM_MUL] THEN
        SUBGOAL_THEN `abs(&1 - th + th * lam) = &1 - th + th * lam` SUBST1_TAC THENL
         [REWRITE_TAC[REAL_ABS_REFL] THEN
          MATCH_MP_TAC(REAL_ARITH `&0 <= th * lam /\ th <= &1 ==> &0 <= &1 - th + th * lam`) THEN
          ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
          ALL_TAC] THEN
        UNDISCH_TAC `norm(lam % u:real^2) = sqrt eta` THEN
        REWRITE_TAC[NORM_MUL] THEN
        SUBGOAL_THEN `abs lam = lam` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        MATCH_MP_TAC(REAL_ARITH
          `&0 <= (&1 - th) * (&1 - lam) ==> lam <= &1 - th + th * lam`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `eta <= norm(w:real^2) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt eta pow 2` THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL];
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]];
        REAL_ARITH_TAC]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `schz_graph ph c (-- &1) (lam % u:real^2)` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT];
      SUBGOAL_THEN `schz_graph ph c (-- &1) (lam % u:real^2) IN S INTER schz_cyl ph c rho`
      MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT];
        SIMP_TAC[IN_INTER]];
      SUBGOAL_THEN `schz_graph ph c (-- &1) (lam % u:real^2) IN S INTER schz_cyl ph c rho`
      MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT];
        SIMP_TAC[IN_INTER]];
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]]]);;

(* ------------------------------------------------------------------------- *)
(* The vertical flow of pc_sch_vflow for a compact set of                    *)
(* regular points of S, in the abstract form used by the band lemma.         *)
(* ------------------------------------------------------------------------- *)

let SCHZ_FLOW_SETUP = prove
 (`!g g':real^3->real^3 C.
     sch_neck g g' /\ compact C /\ C SUBSET sch5v_oh g g' /\
     C SUBSET IMAGE g (sphere(vec 0,&1))
     ==> ?Psi:real^1->real^3->real^3 B d.
           (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
           (!t x. (Psi t x)$3 = x$3 + drop t) /\
           (\w. Psi (fstcart w) (sndcart w)) continuous_on (:real^(1,3)finite_sum) /\
           (!x. (\t. Psi t x) continuous_on (:real^1)) /\
           (!x s t. norm(Psi s x - Psi t x) <= B * abs(drop s - drop t)) /\ &0 < d /\
           (!x t. (!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
                       ==> ?y. y IN C /\ dist(y,Psi u x) < &2 * d)
                  ==> norm(g'(Psi t x)) pow 2 = norm(g' x) pow 2) /\
           (!x. (?y. y IN C /\ dist(y,x) < &2 * d)
                ==> (x IN IMAGE g (sphere(vec 0,&1)) <=> norm(g' x) pow 2 = &1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `C:real^3->bool`;
                 `C:real^3->bool`; `&1`] SCH5V_PANCAKE_FIELD) THEN
  ASM_REWRITE_TAC[INTER_SUBSET; REAL_LT_01] THEN
  REWRITE_TAC[SET_RULE `(s:real^3->bool) INTER c SUBSET c`] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->real^3` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPEC `v:real^3->real^3` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ode_vf_flow (v:real^3->real^3) (:real^3)`; `B:real`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\w. ode_vf_flow (v:real^3->real^3) (:real^3) (fstcart w) (sndcart w))
                continuous_on (:real^(1,3)finite_sum)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `v:real^3->real^3` SCH5V_FLOW_HEIGHT) THEN ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^3` THEN
    SUBGOAL_THEN `(\t. ode_vf_flow (v:real^3->real^3) (:real^3) t x) =
                  (\w. ode_vf_flow v (:real^3) (fstcart w) (sndcart w)) o
                  (\t:real^1. pastecart t x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^(1,3)finite_sum)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]];
    MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`] SCH5V_FLOW_DISPLACEMENT) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC SCH5V_IN_SURFACE THEN
    ASM_SIMP_TAC[]]);;

(* The band lemma for a band that contains no cap, and for the part outside *)
(* a compact cap.                                                            *)

let SCHZ_BAND_CAP = prove
 (`!(Psi:real^1->real^3->real^3) (g':real^3->real^3) (S:real^3->bool) C B d Cap Rest a b.
     (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
     (!t x. (Psi t x)$3 = x$3 + drop t) /\
     (!x. (\t. Psi t x) continuous_on (:real^1)) /\
     (!x s t. norm(Psi s x - Psi t x) <= B * abs(drop s - drop t)) /\ &0 < d /\
     (!x t. (!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
                 ==> ?y. y IN C /\ dist(y,Psi u x) < &2 * d)
            ==> norm(g'(Psi t x)) pow 2 = norm(g' x) pow 2) /\
     (!x. (?y. y IN C /\ dist(y,x) < &2 * d) ==> (x IN S <=> norm(g' x) pow 2 = &1)) /\
     {x | x IN S /\ a <= x$3 /\ x$3 <= b} = Cap UNION Rest /\ Cap INTER Rest = {} /\
     compact Cap /\ closed Rest /\ Rest SUBSET C
     ==> !x t. x IN Rest /\ a <= x$3 + drop t /\ x$3 + drop t <= b ==> Psi t x IN Rest`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC SCHZ_BAND THEN
  MAP_EVERY EXISTS_TAC [`\x:real^3. norm((g':real^3->real^3) x) pow 2`; `S:real^3->bool`;
                        `C:real^3->bool`; `B:real`; `d:real`] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:real^3. x IN Rest ==> x IN S /\ a <= x$3 /\ x$3 <= b` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN Cap UNION Rest` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `Cap UNION Rest:real^3->bool`)) THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[];
    ASM_CASES_TAC `Cap:real^3->bool = {}` THENL
     [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
      MAP_EVERY X_GEN_TAC [`p:real^3`; `q:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(q:real^3) IN {x | x IN S /\ a <= x$3 /\ x$3 <= b}` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM]; ASM_REWRITE_TAC[UNION_EMPTY]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Cap:real^3->bool`; `Rest:real^3->bool`] SEPARATE_COMPACT_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`p:real^3`; `q:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(q:real^3) IN Cap UNION Rest` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rand(concl th) = `Cap UNION Rest:real^3->bool`)) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`q:real^3`; `p:real^3`] o check (fun th ->
      can (term_match [] `!x y:real^3. x IN Cap /\ y IN Rest ==> e <= dist(x,y)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The exact charts at all critical points at once, and the                  *)
(* lowest local maximum is the global maximum (SCHZ_MAX_GLOBAL).            *)
(* ------------------------------------------------------------------------- *)

let SCHZ_CHARTS = prove
 (`!g:real^3->real^3.
     sch_morse g /\ sch_saddles g = {}
     ==> ?kk R (PH:real^3->real^2->real^2) PH'.
           !t. sch_crit g t
               ==> (kk t = &1 \/ kk t = -- &1) /\
                   (sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) (&1) (&1) <=> kk t = &1) /\
                   (sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) (-- &1) (-- &1) <=>
                    kk t = -- &1) /\
                   &0 < R t /\ R t < &1 /\
                   diffeomorphism_on (ball(vec 0,R t)) (IMAGE (PH t) (ball(vec 0,R t)))
                                     (PH t) (PH' t) /\
                   schz_lift (PH t) (sch5v_at ((g t)$3) (vec 0)) = g t /\
                   (!y. sch5v_pr y IN ball(vec 0,R t) /\ abs(y$3 - (g t)$3) < R t
                        ==> (schz_lift (PH t) y IN IMAGE g (sphere(vec 0,&1)) <=>
                             y$3 = (g t)$3 + kk t * norm(sch5v_pr y) pow 2))`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
  X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `t:real^3`] SCHZ_CRIT_TYPES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `&1` THEN
    SUBGOAL_THEN `~sch_hchart (IMAGE (g:real^3->real^3) (sphere(vec 0,&1))) (g t)
                    (-- &1) (-- &1)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ARITH `~(&1 = -- &1)`] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP SCHZ_HCHART_LIFT o check (fun th ->
      concl th = `sch_hchart (IMAGE (g:real^3->real^3) (sphere(vec 0,&1))) (g t) (&1) (&1)`)) THEN
    REWRITE_TAC[];
    EXISTS_TAC `-- &1` THEN
    SUBGOAL_THEN `~sch_hchart (IMAGE (g:real^3->real^3) (sphere(vec 0,&1))) (g t)
                    (&1) (&1)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ARITH `~(-- &1 = &1)`] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP SCHZ_HCHART_LIFT o check (fun th ->
      concl th = `sch_hchart (IMAGE (g:real^3->real^3) (sphere(vec 0,&1))) (g t)
                    (-- &1) (-- &1)`)) THEN
    REWRITE_TAC[]]);;

let SCHZ_MAX_GLOBAL = prove
 (`!g g':real^3->real^3 t.
     sch_neck g g' /\ sch_morse g /\ sch_saddles g = {} /\ sch_crit g t /\
     sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) (-- &1) (-- &1)
     ==> !s. s IN sphere(vec 0,&1) ==> (g s)$3 <= (g t)$3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHZ_SURFACE_FACTS) THEN
  SUBGOAL_THEN `FINITE {t:real^3 | sch_crit g t} /\
                (!t t'. sch_crit g t /\ sch_crit g t' /\ (g t)$3 = (g t')$3 ==> t = t')`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[sch_morse]; ALL_TAC] THEN
  MP_TAC(ISPEC `g:real^3->real^3` SCHZ_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:real^3->real` (X_CHOOSE_THEN `R:real^3->real`
    (X_CHOOSE_THEN `PH:real^3->real^2->real^2` (X_CHOOSE_THEN `PH':real^3->real^2->real^2`
     (LABEL_TAC "CH"))))) THEN
  (* Uniform sizes: radius, gap of the critical values, and the band width. *)
  MP_TAC(ISPECL [`{t:real^3 | sch_crit g t}`; `R:real^3->real`] SCHZ_FINITE_POS_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "CH" (MP_TAC o C MATCH_MP (ASSUME `sch_crit (g:real^3->real^3) x`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `CV = IMAGE (\t:real^3. (g:real^3->real^3) t$3) {t | sch_crit g t}` THEN
  MP_TAC(ISPEC `CV:real->bool` SCHZ_FINITE_GAP) THEN ANTS_TAC THENL
   [EXPAND_TAC "CV" THEN ASM_SIMP_TAC[FINITE_IMAGE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `rho1 = min (r0 / &4) (min (g0 / &16) (&1 / &8))` THEN
  ABBREV_TAC `eta = &2 * rho1 pow 2` THEN
  SUBGOAL_THEN `&0 < rho1 /\ rho1 <= r0 / &4 /\ rho1 <= &1 / &8 /\ &0 < eta /\
                rho1 pow 2 < eta /\ eta < (&2 * rho1) pow 2 /\ &4 * eta < g0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < rho1 /\ rho1 <= r0 / &4 /\ rho1 <= &1 / &8 /\ rho1 <= g0 / &16`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "rho1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < rho1 pow 2 /\ rho1 pow 2 <= rho1 / &8` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `r * r <= r * (&1 / &8) ==> r * r <= r / &8`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "eta" THEN
    REWRITE_TAC[REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* The exact cylinders at the critical points. *)
  SUBGOAL_THEN
   `!s:real^3 rho. sch_crit g s /\ &0 < rho /\ rho <= &2 * rho1
      ==> open(schz_cyl (PH s) ((g s)$3) rho) /\
          schz_cyl (PH s) ((g s)$3) rho SUBSET schz_cyl (PH s) ((g s)$3) (R s) /\
          (!u. (schz_graph (PH s) ((g s)$3) (kk s) u)$3 = (g s)$3 + kk s * norm u pow 2) /\
          IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER schz_cyl (PH s) ((g s)$3) rho =
          IMAGE (schz_graph (PH s) ((g s)$3) (kk s)) (ball(vec 0,rho)) /\
          (!e. &0 <= e /\ e < rho pow 2
               ==> IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER schz_cyl (PH s) ((g s)$3) rho INTER
                   {x | abs(x$3 - (g s)$3) <= e} =
                   IMAGE (schz_graph (PH s) ((g s)$3) (kk s)) (cball(vec 0,sqrt e)) /\
                   IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER schz_cyl (PH s) ((g s)$3) rho INTER
                   {x | abs(x$3 - (g s)$3) = e} =
                   IMAGE (schz_graph (PH s) ((g s)$3) (kk s)) (sphere(vec 0,sqrt e)) /\
                   sqrt e < rho) /\
          (schz_graph (PH s) ((g s)$3) (kk s)) continuous_on ball(vec 0,R s)`
  (LABEL_TAC "CYL") THENL
   [MAP_EVERY X_GEN_TAC [`s:real^3`; `rho:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC SCHZ_CYL THEN
    EXISTS_TAC `(PH':real^3->real^2->real^2) s` THEN
    USE_THEN "CH" (MP_TAC o C MATCH_MP (ASSUME `sch_crit (g:real^3->real^3) s`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^3` o check (fun th ->
      can (term_match [] `!x:real^3. sch_crit g x ==> r0 <= R x`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Points of S in the small cylinders lie within eta of the critical value. *)
  SUBGOAL_THEN
   `!s:real^3 x. sch_crit g s /\ x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\
                 x IN schz_cyl (PH s) ((g s)$3) rho1
                 ==> abs(x$3 - (g s)$3) < eta`
  (LABEL_TAC "NEARC") THENL
   [MAP_EVERY X_GEN_TAC [`s:real^3`; `x:real^3`] THEN STRIP_TAC THEN
    USE_THEN "CYL" (MP_TAC o SPECL [`s:real^3`; `rho1:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 th))) THEN
                         ASSUME_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th))))) THEN
    SUBGOAL_THEN `(x:real^3) IN IMAGE (schz_graph (PH (s:real^3)) ((g:real^3->real^3) s$3)
                                        (kk s)) (ball(vec 0,rho1))` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[REAL_ADD_SUB] THEN
    USE_THEN "CH" (MP_TAC o C MATCH_MP (ASSUME `sch_crit (g:real^3->real^3) s`)) THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    SUBGOAL_THEN `abs(kk(s:real^3) * norm(u:real^2) pow 2) = norm u pow 2` SUBST1_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_ABS_NEG; REAL_ABS_POW; REAL_ABS_NORM];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `rho1 pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  (* The compact set of regular points away from the small cylinders. *)
  ABBREV_TAC `KR = IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) DIFF
                   UNIONS (IMAGE (\t. schz_cyl ((PH:real^3->real^2->real^2) t) ((g t)$3) rho1)
                                 {t | sch_crit g t})` THEN
  SUBGOAL_THEN `compact(KR:real^3->bool) /\ KR SUBSET IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\
                KR SUBSET sch5v_oh g g'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "KR" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_DIFF THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^3` THEN DISCH_TAC THEN
      USE_THEN "CYL" (MP_TAC o SPECL [`s:real^3`; `rho1:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      SET_TAC[];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      REWRITE_TAC[sch5v_oh; IN_ELIM_THM] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
        ALL_TAC] THEN
      ASM_CASES_TAC `sch_crit (g:real^3->real^3) s` THENL
       [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
        MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
        EXISTS_TAC `schz_cyl ((PH:real^3->real^2->real^2) s) ((g:real^3->real^3) s$3) rho1` THEN
        CONJ_TAC THENL [EXISTS_TAC `s:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[schz_cyl; IN_IMAGE; IN_ELIM_THM] THEN
        EXISTS_TAC `sch5v_at ((g:real^3->real^3) s$3) (vec 0)` THEN
        USE_THEN "CH" (MP_TAC o C MATCH_MP (ASSUME `sch_crit (g:real^3->real^3) s`)) THEN
        DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
        ASM_REWRITE_TAC[SCH5V_PR_AT; CENTRE_IN_BALL; REAL_SUB_REFL; REAL_ABS_0];
        MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `s:real^3`] SCH5V_CRIT_GRAD) THEN
        ASM_REWRITE_TAC[REAL_SOS_EQ_0] THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `KR:real^3->bool`]
    SCHZ_FLOW_SETUP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Psi:real^1->real^3->real^3` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!s:real^3. sch_crit g s ==> (g:real^3->real^3) s$3 IN CV` (LABEL_TAC "INCV")
  THENL
   [X_GEN_TAC `s:real^3` THEN DISCH_TAC THEN EXPAND_TAC "CV" THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `s:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. c IN CV ==> ?s:real^3. sch_crit g s /\ c = (g:real^3->real^3) s$3`
  (LABEL_TAC "CVIN") THENL
   [EXPAND_TAC "CV" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* Regular bands are flow-invariant. *)
  SUBGOAL_THEN
   `!a1 a2 x t1. a1 < a2 /\ (!c z. c IN CV /\ a1 <= z /\ z <= a2 ==> eta <= abs(z - c)) /\
                 x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\ a1 <= x$3 /\ x$3 <= a2 /\
                 a1 <= x$3 + drop t1 /\ x$3 + drop t1 <= a2
                 ==> (Psi:real^1->real^3->real^3) t1 x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`
  (LABEL_TAC "REG") THENL
   [MAP_EVERY X_GEN_TAC [`a1:real`; `a2:real`; `x:real^3`; `t1:real^1`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "FAR")
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `g':real^3->real^3`;
                   `IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`; `KR:real^3->bool`;
                   `B:real`; `d:real`; `{}:real^3->bool`;
                   `{x:real^3 | x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\ a1 <= x$3 /\ x$3 <= a2}`;
                   `a1:real`; `a2:real`] SCHZ_BAND_CAP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[UNION_EMPTY; INTER_EMPTY; COMPACT_EMPTY] THEN CONJ_TAC THENL
       [REWRITE_TAC[SET_RULE `{x:real^3 | x IN S /\ P x} = S INTER {x | P x}`] THEN
        MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
        REWRITE_TAC[SET_RULE `{x:real^3 | a <= x$3 /\ x$3 <= b} =
                              {x | a <= x$3} INTER {x | x$3 <= b}`] THEN
        MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE];
          REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE]];
        EXPAND_TAC "KR" THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF; IN_UNIONS; IN_IMAGE; NOT_EXISTS_THM] THEN
        X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        X_GEN_TAC `cy:real^3->bool` THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        USE_THEN "NEARC" (MP_TAC o SPECL [`s:real^3`; `y:real^3`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x':real^3` THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        USE_THEN "FAR" (MP_TAC o SPECL [`(g:real^3->real^3) s$3`; `(y:real^3)$3`]) THEN
        USE_THEN "INCV" (fun th -> REWRITE_TAC[MATCH_MP th
          (ASSUME `sch_crit (g:real^3->real^3) s`)]) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `t1:real^1`]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  (* The caps at the local minima. *)
  ABBREV_TAC `tc = \c. @s:real^3. sch_crit g s /\ (g:real^3->real^3) s$3 = c` THEN
  SUBGOAL_THEN `!s:real^3. sch_crit g s ==> (tc:real->real^3) ((g:real^3->real^3) s$3) = s`
  (LABEL_TAC "TC") THENL
   [X_GEN_TAC `s:real^3` THEN DISCH_TAC THEN EXPAND_TAC "tc" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\s':real^3. sch_crit g s' /\ (g:real^3->real^3) s'$3 = (g s)$3`;
                   `s:real^3`] SELECT_AX) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `cap = \c. IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER
                        schz_cyl ((PH:real^3->real^2->real^2) ((tc:real->real^3) c)) c
                                 (&2 * rho1) INTER
                        {x | abs(x$3 - c) <= eta}` THEN
  ABBREV_TAC `rest = \c. {x | x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\
                              c - eta <= x$3 /\ x$3 <= c + eta} DIFF
                         schz_cyl ((PH:real^3->real^2->real^2) ((tc:real->real^3) c)) c
                                  (&2 * rho1)` THEN
  ABBREV_TAC `MINV = IMAGE (\s:real^3. (g:real^3->real^3) s$3)
                           {s | sch_crit g s /\ (kk:real^3->real) s = &1}` THEN
  SUBGOAL_THEN
   `!c. c IN CV /\ c IN MINV
        ==> {x | x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\
                 c - eta <= x$3 /\ x$3 <= c + eta} =
            (cap:real->real^3->bool) c UNION (rest:real->real^3->bool) c /\
            cap c INTER rest c = {} /\ compact(cap c) /\ closed(rest c) /\
            (!x. x IN cap c ==> c - eta < x$3) /\
            connected {x | x IN cap c /\ x$3 = c + eta} /\
            (!x t1. x IN rest c /\ c - eta <= x$3 + drop t1 /\ x$3 + drop t1 <= c + eta
                    ==> (Psi:real^1->real^3->real^3) t1 x IN rest c)`
  (LABEL_TAC "MINF") THENL
   [X_GEN_TAC `c:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?s:real^3. sch_crit g s /\ (kk:real^3->real) s = &1 /\
                             c = (g:real^3->real^3) s$3`
    (X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC) THENL
     [UNDISCH_TAC `(c:real) IN MINV` THEN EXPAND_TAC "MINV" THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "TC" (fun th -> MP_TAC(MATCH_MP th (ASSUME `sch_crit (g:real^3->real^3) s`))) THEN
    DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["cap"; "rest"] THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `O = schz_cyl ((PH:real^3->real^2->real^2) s) ((g:real^3->real^3) s$3)
                             (&2 * rho1)` THEN
    USE_THEN "CYL" (MP_TAC o SPECL [`s:real^3`; `&2 * rho1`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_LID] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "GH") (CONJUNCTS_THEN2 (LABEL_TAC "SO")
      (CONJUNCTS_THEN2 (LABEL_TAC "BAND") (LABEL_TAC "GC")))))) THEN
    USE_THEN "BAND" (MP_TAC o SPEC `eta:real`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CAPE") (CONJUNCTS_THEN2 (LABEL_TAC "TOPE")
      ASSUME_TAC)) THEN
    SUBGOAL_THEN `r0 <= (R:real^3->real) s` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real^3` o check (fun th ->
        can (term_match [] `!x:real^3. sch_crit g x ==> r0 <= R x`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x:real^3. x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER O
                             ==> (g:real^3->real^3) s$3 <= x$3`
    (LABEL_TAC "HC") THENL
     [X_GEN_TAC `x:real^3` THEN USE_THEN "SO" SUBST1_TAC THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "GH" (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC(SPEC `norm(u:real^2)` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{x:real^3 | x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\
                  g s$3 - eta <= x$3 /\ x$3 <= g s$3 + eta} =
      (IMAGE g (sphere(vec 0,&1)) INTER O INTER {x | abs(x$3 - g s$3) <= eta}) UNION
      ({x | x IN IMAGE g (sphere(vec 0,&1)) /\ g s$3 - eta <= x$3 /\ x$3 <= g s$3 + eta}
       DIFF O) /\
      (IMAGE g (sphere(vec 0,&1)) INTER O INTER {x | abs(x$3 - g s$3) <= eta}) INTER
      ({x | x IN IMAGE g (sphere(vec 0,&1)) /\ g s$3 - eta <= x$3 /\ x$3 <= g s$3 + eta}
       DIFF O) = {}`
    (CONJUNCTS_THEN2 (LABEL_TAC "F1") (LABEL_TAC "F2")) THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_DIFF; IN_ELIM_THM; NOT_IN_EMPTY;
                  REAL_ARITH `abs(x - c) <= e <=> c - e <= x /\ x <= c + e`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `compact(IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER O INTER
              {x | abs(x$3 - g s$3) <= eta})`
    (LABEL_TAC "F3") THENL
     [USE_THEN "CAPE" SUBST1_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^2,(R:real^3->real) s)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN GEN_TAC THEN
      UNDISCH_TAC `sqrt eta < &2 * rho1` THEN UNDISCH_TAC `r0 <= (R:real^3->real) s` THEN
      UNDISCH_TAC `rho1 <= r0 / &4` THEN UNDISCH_TAC `&0 < rho1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `closed({x:real^3 | x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\
                         g s$3 - eta <= x$3 /\ x$3 <= g s$3 + eta} DIFF O)`
    (LABEL_TAC "F4") THENL
     [MATCH_MP_TAC CLOSED_DIFF THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SET_RULE `{x:real^3 | x IN S /\ P x} = S INTER {x | P x}`] THEN
      MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      REWRITE_TAC[SET_RULE `{x:real^3 | a <= x$3 /\ x$3 <= b} =
                            {x | a <= x$3} INTER {x | x$3 <= b}`] THEN
      MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE];
        REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE]];
      ALL_TAC] THEN
    USE_THEN "F1" (fun th -> REWRITE_TAC[EQT_INTRO th]) THEN
    USE_THEN "F2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "F3" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "F4" (fun th -> REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      USE_THEN "HC" (MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
      UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC;
      SUBGOAL_THEN
       `{x:real^3 | x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER O INTER
                         {x | abs(x$3 - g s$3) <= eta} /\ x$3 = g s$3 + eta} =
        IMAGE g (sphere(vec 0,&1)) INTER O INTER {x | abs(x$3 - g s$3) = eta}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
        ASM_CASES_TAC `(x:real^3) IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\ x IN O`
        THENL
         [USE_THEN "HC" (MP_TAC o SPEC `x:real^3`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          ASM_MESON_TAC[]];
        ALL_TAC] THEN
      USE_THEN "TOPE" SUBST1_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_2; LE_REFL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^2,(R:real^3->real) s)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_BALL_0] THEN GEN_TAC THEN
      UNDISCH_TAC `sqrt eta < &2 * rho1` THEN UNDISCH_TAC `r0 <= (R:real^3->real) s` THEN
      UNDISCH_TAC `rho1 <= r0 / &4` THEN UNDISCH_TAC `&0 < rho1` THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `g':real^3->real^3`;
                     `IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`; `KR:real^3->bool`;
                     `B:real`; `d:real`;
                     `IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER O INTER
                      {x | abs(x$3 - g s$3) <= eta}`;
                     `{x:real^3 | x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\
                                  g s$3 - eta <= x$3 /\ x$3 <= g s$3 + eta} DIFF O`;
                     `(g:real^3->real^3) s$3 - eta`; `(g:real^3->real^3) s$3 + eta`]
        SCHZ_BAND_CAP) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      USE_THEN "F1" (fun th -> REWRITE_TAC[EQT_INTRO th]) THEN
      USE_THEN "F2" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "F3" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "F4" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "KR" THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; IN_UNIONS; IN_IMAGE; NOT_EXISTS_THM] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `cy:real^3->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s1:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_CASES_TAC `s1:real^3 = s` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        UNDISCH_TAC `~((y:real^3) IN O)` THEN REWRITE_TAC[] THEN EXPAND_TAC "O" THEN
        MP_TAC(ISPECL [`(PH:real^3->real^2->real^2) s`; `(g:real^3->real^3) s$3`;
                       `rho1:real`; `&2 * rho1`] SCHZ_CYL_MONO) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
        ALL_TAC] THEN
      USE_THEN "NEARC" (MP_TAC o SPECL [`s1:real^3`; `y:real^3`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x':real^3` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `g0 < abs((g:real^3->real^3) s$3 - (g s1)$3)` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!x y. x IN CV /\ y IN CV /\ ~(x = y) ==> g0 < abs(x - y)`)
              (concl th))) THEN
        USE_THEN "INCV" (fun th -> REWRITE_TAC[MATCH_MP th
          (ASSUME `sch_crit (g:real^3->real^3) s`)]) THEN
        USE_THEN "INCV" (fun th -> REWRITE_TAC[MATCH_MP th
          (ASSUME `sch_crit (g:real^3->real^3) s1`)]) THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(g:real^3->real^3) s$3 - eta <= (y:real^3)$3` THEN
      UNDISCH_TAC `(y:real^3)$3 <= (g:real^3->real^3) s$3 + eta` THEN
      UNDISCH_TAC `&4 * eta < g0` THEN UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* The sublevel induction. *)
  MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`;
                 `CV:real->bool`; `MINV:real->bool`; `cap:real->real^3->bool`;
                 `rest:real->real^3->bool`; `eta:real`] SCHZ_INDUCT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "CV" THEN ASM_SIMP_TAC[FINITE_IMAGE];
      MAP_EVERY X_GEN_TAC [`c:real`; `c':real`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`c:real`; `c':real`] o check (fun th ->
        can (term_match [] `!x y. x IN CV /\ y IN CV /\ ~(x = y) ==> g0 < abs(x - y)`)
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&4 * eta < g0` THEN UNDISCH_TAC `&0 < eta` THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCHZ_EXTREMA_EXIST) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t0:real^3` (X_CHOOSE_THEN `t1:real^3` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `(g:real^3->real^3) t0$3` THEN CONJ_TAC THENL
       [USE_THEN "INCV" MATCH_MP_TAC THEN
        MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t0:real^3`]
          SCHZ_GLOBAL_TYPES) THEN
        ASM_SIMP_TAC[];
        UNDISCH_TAC `(x:real^3) IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` THEN
        REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
      USE_THEN "REG" ACCEPT_TAC];
    DISCH_THEN(LABEL_TAC "PIND")] THEN
  (* The lowest local maximum. *)
  ABBREV_TAC `LM = {s:real^3 | sch_crit g s /\ (kk:real^3->real) s = -- &1}` THEN
  SUBGOAL_THEN `(t:real^3) IN LM` ASSUME_TAC THENL
   [EXPAND_TAC "LM" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "CH" (fun th -> MP_TAC(MATCH_MP th (ASSUME `sch_crit (g:real^3->real^3) t`))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (LM:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{s:real^3 | sch_crit g s}` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "LM" THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\s:real^3. (g:real^3->real^3) s$3) LM` INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_IMAGE] THEN
  ABBREV_TAC `cs = inf(IMAGE (\s:real^3. (g:real^3->real^3) s$3) LM)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `ts:real^3` STRIP_ASSUME_TAC) (LABEL_TAC "LOWM")) THEN
  SUBGOAL_THEN `sch_crit (g:real^3->real^3) ts /\ (kk:real^3->real) ts = -- &1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(ts:real^3) IN LM` THEN EXPAND_TAC "LM" THEN SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  (* The sublevel property just below cs. *)
  USE_THEN "PIND" (MP_TAC o SPEC `cs - eta`) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `c:real` THEN DISCH_TAC THEN ASM_CASES_TAC `c:real = cs` THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`c:real`; `cs:real`] o check (fun th ->
        can (term_match [] `!x y. x IN CV /\ y IN CV /\ ~(x = y) ==> g0 < abs(x - y)`)
            (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "INCV" (fun th -> ASM_MESON_TAC[th]); ALL_TAC] THEN
      UNDISCH_TAC `&4 * eta < g0` THEN UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC;
      X_GEN_TAC `c:real` THEN STRIP_TAC THEN
      USE_THEN "CVIN" (MP_TAC o C MATCH_MP (ASSUME `(c:real) IN CV`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC) THEN
      EXPAND_TAC "MINV" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `s:real^3` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "CH" (MP_TAC o C MATCH_MP (ASSUME `sch_crit (g:real^3->real^3) s`)) THEN
      DISCH_THEN(DISJ_CASES_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "LOWM" (MP_TAC o SPEC `s:real^3`) THEN ANTS_TAC THENL
       [EXPAND_TAC "LM" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      UNDISCH_TAC `c < cs - eta` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC];
    DISCH_THEN(LABEL_TAC "PCS")] THEN
  (* The cap at the lowest local maximum closes the sublevel component. *)
  USE_THEN "CYL" (MP_TAC o SPECL [`ts:real^3`; `&2 * rho1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "GHt") (CONJUNCTS_THEN2 (LABEL_TAC "SOt")
    (CONJUNCTS_THEN2 (LABEL_TAC "BANDt") (LABEL_TAC "GCt")))))) THEN
  USE_THEN "BANDt" (MP_TAC o SPEC `eta:real`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CAPt") (CONJUNCTS_THEN2 (LABEL_TAC "TOPt")
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `r0 <= (R:real^3->real) ts` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `ts:real^3` o check (fun th ->
      can (term_match [] `!x:real^3. sch_crit g x ==> r0 <= R x`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER
               schz_cyl ((PH:real^3->real^2->real^2) ts) ((g:real^3->real^3) ts$3) (&2 * rho1)
               ==> x$3 <= (g:real^3->real^3) ts$3`
  (LABEL_TAC "HCt") THENL
   [X_GEN_TAC `x:real^3` THEN USE_THEN "SOt" SUBST1_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "GHt" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPEC `norm(u:real^2)` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER
    schz_cyl ((PH:real^3->real^2->real^2) ts) ((g:real^3->real^3) ts$3) (&2 * rho1) INTER
    {x | (g:real^3->real^3) ts$3 - eta <= x$3} =
    IMAGE g (sphere(vec 0,&1)) INTER schz_cyl (PH ts) ((g:real^3->real^3) ts$3) (&2 * rho1)
    INTER {x | abs(x$3 - (g:real^3->real^3) ts$3) <= eta} /\
    IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER
    schz_cyl ((PH:real^3->real^2->real^2) ts) ((g:real^3->real^3) ts$3) (&2 * rho1) INTER
    {x | x$3 = (g:real^3->real^3) ts$3 - eta} =
    IMAGE g (sphere(vec 0,&1)) INTER schz_cyl (PH ts) ((g:real^3->real^3) ts$3) (&2 * rho1)
    INTER {x | abs(x$3 - (g:real^3->real^3) ts$3) = eta}`
  (CONJUNCTS_THEN2 (LABEL_TAC "EQ1") (LABEL_TAC "EQ2")) THENL
   [CONJ_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN
    MATCH_MP_TAC(TAUT `(a /\ b ==> (c <=> d)) ==> (a /\ b /\ c <=> a /\ b /\ d)`) THEN
    STRIP_TAC THEN
    USE_THEN "HCt" (MP_TAC o SPEC `x:real^3`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC]) THEN
    UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`;
                 `schz_cyl ((PH:real^3->real^2->real^2) ts) ((g:real^3->real^3) ts$3)
                           (&2 * rho1)`;
                 `(g:real^3->real^3) ts$3 - eta`; `(g:real^3->real^3) ts$3`]
    SCHZ_CAP_CLOSES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC;
      USE_THEN "EQ1" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "CAPt" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_CBALL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^2,(R:real^3->real) ts)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN GEN_TAC THEN
      UNDISCH_TAC `sqrt eta < &2 * rho1` THEN UNDISCH_TAC `r0 <= (R:real^3->real) ts` THEN
      UNDISCH_TAC `rho1 <= r0 / &4` THEN UNDISCH_TAC `&0 < rho1` THEN REAL_ARITH_TAC;
      USE_THEN "HCt" ACCEPT_TAC;
      USE_THEN "EQ2" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "TOPt" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_2; LE_REFL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^2,(R:real^3->real) ts)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_BALL_0] THEN GEN_TAC THEN
      UNDISCH_TAC `sqrt eta < &2 * rho1` THEN UNDISCH_TAC `r0 <= (R:real^3->real) ts` THEN
      UNDISCH_TAC `rho1 <= r0 / &4` THEN UNDISCH_TAC `&0 < rho1` THEN REAL_ARITH_TAC;
      USE_THEN "EQ2" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "TOPt" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN
      MP_TAC(SPEC `eta:real` SQRT_POS_LE) THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE]; REAL_ARITH_TAC];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC SCHZ_MAX_NBHD THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^2,(R:real^3->real) ts)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_BALL THEN
      UNDISCH_TAC `r0 <= (R:real^3->real) ts` THEN
      UNDISCH_TAC `rho1 <= r0 / &4` THEN UNDISCH_TAC `&0 < rho1` THEN REAL_ARITH_TAC;
      USE_THEN "PCS" MP_TAC THEN
      REWRITE_TAC[ASSUME `cs = (g:real^3->real^3) ts$3`]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ALLB") THEN X_GEN_TAC `s:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(g:real^3->real^3) ts$3` THEN CONJ_TAC THENL
   [USE_THEN "ALLB" MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    USE_THEN "LOWM" (MP_TAC o C MATCH_MP (ASSUME `(t:real^3) IN LM`)) THEN
    REWRITE_TAC[ASSUME `cs = (g:real^3->real^3) ts$3`]]);;

(* ------------------------------------------------------------------------- *)
(* The minimum case by the flip x3 -> -x3, and the two                       *)
(* critical points of a sphere without saddles: one global minimum t0, one   *)
(* global maximum t1, each the only point of S at its height.                *)
(* ------------------------------------------------------------------------- *)

let SCHZ_MIN_GLOBAL = prove
 (`!g g':real^3->real^3 t.
     sch_neck g g' /\ sch_morse g /\ sch_saddles g = {} /\ sch_crit g t /\
     sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) (&1) (&1)
     ==> !s. s IN sphere(vec 0,&1) ==> (g t)$3 <= (g s)$3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC SCH5_FLIP3_FACTS THEN
  MP_TAC(ISPECL [`sch_flip3 o (g:real^3->real^3) o sch_flip3`;
                 `sch_flip3 o (g':real^3->real^3) o sch_flip3`;
                 `sch_flip3 (t:real^3)`] SCHZ_MAX_GLOBAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SCH5_NECK_FLIP THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SCH5_MORSE_FLIP THEN EXISTS_TAC `g':real^3->real^3` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCH5_SADDLES_FLIP) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES];
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `sch_flip3 (t:real^3)`]
        SCH5_CRIT_FLIP) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[SCH5_HCHART_FLIP_NECK; REAL_NEG_NEG]];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `s:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sch_flip3 (s:real^3)`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(s:real^3) IN sphere(vec 0,&1)` THEN ASM_REWRITE_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM] THEN REAL_ARITH_TAC);;

let SCHZ_TWO_CRIT = prove
 (`!g g':real^3->real^3.
     sch_neck g g' /\ sch_morse g /\ sch_saddles g = {}
     ==> ?t0 t1. sch_crit g t0 /\ sch_crit g t1 /\ ~(t0 = t1) /\
                 sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t0) (&1) (&1) /\
                 sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t1) (-- &1) (-- &1) /\
                 (!t. sch_crit g t <=> t = t0 \/ t = t1) /\
                 (!s. s IN sphere(vec 0,&1) ==> (g t0)$3 <= (g s)$3 /\ (g s)$3 <= (g t1)$3) /\
                 (!s. s IN sphere(vec 0,&1) /\ (g s)$3 = (g t0)$3 ==> s = t0) /\
                 (!s. s IN sphere(vec 0,&1) /\ (g s)$3 = (g t1)$3 ==> s = t1) /\
                 (g t0)$3 < (g t1)$3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCHZ_EXTREMA_EXIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^3` (X_CHOOSE_THEN `t1:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EX"))))) THEN
  MAP_EVERY EXISTS_TAC [`t0:real^3`; `t1:real^3`] THEN
  SUBGOAL_THEN `sch_crit (g:real^3->real^3) t0 /\
                sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t0) (&1) (&1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t0:real^3`]
      SCHZ_GLOBAL_TYPES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    X_GEN_TAC `s:real^3` THEN DISCH_TAC THEN
    USE_THEN "EX" (MP_TAC o C MATCH_MP (ASSUME `(s:real^3) IN sphere(vec 0,&1)`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_crit (g:real^3->real^3) t1 /\
                sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t1) (-- &1) (-- &1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t1:real^3`]
      SCHZ_GLOBAL_TYPES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    X_GEN_TAC `s:real^3` THEN DISCH_TAC THEN
    USE_THEN "EX" (MP_TAC o C MATCH_MP (ASSUME `(s:real^3) IN sphere(vec 0,&1)`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t t':real^3. sch_crit g t /\ sch_crit g t' /\
                              (g:real^3->real^3) t$3 = g t'$3 ==> t = t'`
  (LABEL_TAC "INJ") THENL
   [UNDISCH_TAC `sch_morse (g:real^3->real^3)` THEN REWRITE_TAC[sch_morse] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t0:real^3 = t1)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `t1:real^3`] SCHZ_CRIT_TYPES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3. s IN sphere(vec 0,&1) /\ (g:real^3->real^3) s$3 = g t0$3
                           ==> s = t0` (LABEL_TAC "UMIN") THENL
   [X_GEN_TAC `s:real^3` THEN STRIP_TAC THEN USE_THEN "INJ" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCHZ_EXTREMUM_CRIT THEN
    EXISTS_TAC `g':real^3->real^3` THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "EX" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN sphere(vec 0,&1)`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3. s IN sphere(vec 0,&1) /\ (g:real^3->real^3) s$3 = g t1$3
                           ==> s = t1` (LABEL_TAC "UMAX") THENL
   [X_GEN_TAC `s:real^3` THEN STRIP_TAC THEN USE_THEN "INJ" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCHZ_EXTREMUM_CRIT THEN
    EXISTS_TAC `g':real^3->real^3` THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "EX" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN sphere(vec 0,&1)`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real^3` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `t:real^3`] SCHZ_CRIT_TYPES) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(DISJ_CASES_TAC o CONJUNCT1) THENL
       [DISJ1_TAC THEN USE_THEN "UMIN" MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_MESON_TAC[sch_crit]; ALL_TAC] THEN
        MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`]
          SCHZ_MIN_GLOBAL) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t0:real^3`) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(t:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
         [ASM_MESON_TAC[sch_crit]; ALL_TAC] THEN
        USE_THEN "EX" (MP_TAC o C MATCH_MP (ASSUME `(t:real^3) IN sphere(vec 0,&1)`)) THEN
        REAL_ARITH_TAC;
        DISJ2_TAC THEN USE_THEN "UMAX" MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_MESON_TAC[sch_crit]; ALL_TAC] THEN
        MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`]
          SCHZ_MAX_GLOBAL) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t1:real^3`) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(t:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
         [ASM_MESON_TAC[sch_crit]; ALL_TAC] THEN
        USE_THEN "EX" (MP_TAC o C MATCH_MP (ASSUME `(t:real^3) IN sphere(vec 0,&1)`)) THEN
        REAL_ARITH_TAC];
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    USE_THEN "EX" ACCEPT_TAC;
    USE_THEN "UMIN" ACCEPT_TAC;
    USE_THEN "UMAX" ACCEPT_TAC;
    REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
     [USE_THEN "EX" (MP_TAC o C MATCH_MP (ASSUME `(t1:real^3) IN sphere(vec 0,&1)`)) THEN
      SIMP_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~(t0:real^3 = t1)` THEN REWRITE_TAC[] THEN
      USE_THEN "INJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* From a model chart to a ball chart.  Theta is a smooth                    *)
(* injective map with invertible derivative on an open U containing the     *)
(* closed ball cball(cen,rho), and it maps sphere(cen,rho) into S.  A 1D     *)
(* flow gives a radial squeeze of ball(0,2) into ball(0,1 + s), the identity *)
(* on cball(0,1); the chart is Theta o (affine) o squeeze.  Its boundary     *)
(* sphere is all of S (an injective self-map of S^2 is onto), and its open   *)
(* ball is the bounded side of S (clopen argument).                          *)
(* ------------------------------------------------------------------------- *)

(* Smoothness rules for smooth_step, exp and log, and the extended tactic.   *)

let SCHZ_SL_STEP = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x))
     ==> smooth_map_on s (\x. lift(smooth_step(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`]
    SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCHZ_SL_EXP = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x))
     ==> smooth_map_on s (\x. lift(exp(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`] SMOOTH_MAP_ON_LIFT_EXP) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCHZ_SL_LOG = prove
 (`!s (f:real^M->real).
     open s /\ smooth_map_on s (\x. lift(f x)) /\ (!x. x IN s ==> &0 < f x)
     ==> smooth_map_on s (\x. lift(log(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`] SMOOTH_MAP_ON_LIFT_LOG) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let SCHZ_SMOOTH_TAC =
  let rules = [SCH3_SL_NORM_POW2; SCH3_SL_ADD; SCH3_SL_SUB; SCH3_SL_MUL; SCH3_SL_NEG; SCH3_SL_POW;
               SCH3_SL_DIV; SCH3_SL_INV; SCH3_SL_SQRT; SCH3_SL_DOT; SCH3_SL_NORM;
               SCHZ_SL_STEP; SCHZ_SL_EXP; SCHZ_SL_LOG;
               SCH3_SV_CMUL; SCH3_SV_ADD; SCH3_SV_SUB; SCH3_SV_NEG;
               SCH3_SV_VECTOR3; SCH3_SV_VECTOR2] in
  let leaves = [SCH3_SL_CONST; SCH3_SV_CONST; SCH3_SV_ID; SCH3_SL_COORD;
                SMOOTH_MAP_ON_LIFT_COMPONENT; ETA_AX] in
  let step = FIRST (map MATCH_MP_TAC rules) THEN REPEAT CONJ_TAC in
  REPEAT CONJ_TAC THEN
  REPEAT (FIRST [ASM_SIMP_TAC leaves THEN NO_TAC; ASM_REWRITE_TAC[] THEN NO_TAC;
                 step]);;

(* A 1D flow that is the identity below c + e and the exponential           *)
(* z |-> c + (z - c) e^t between c + s1 and zmax.                            *)

let SCHZ_XI = prove
 (`!c e s1 zmax.
     &0 < e /\ e < s1 /\ c + s1 < zmax
     ==> ?Xi:real^1->real^1->real^1.
           (!z. Xi (vec 0) z = z) /\ (!z s t. Xi t (Xi s z) = Xi (s + t) z) /\
           smooth_map_on (:real^(1,1)finite_sum) (\w. Xi (fstcart w) (sndcart w)) /\
           (!t. diffeomorphism_on (:real^1) (:real^1) (Xi t) (Xi (--t))) /\
           (!t z. drop z <= c + e ==> Xi t z = z) /\
           (!t z. c + s1 <= drop z /\ drop z <= zmax /\
                  c + s1 <= c + (drop z - c) * exp(drop t) /\
                  c + (drop z - c) * exp(drop t) <= zmax
                  ==> Xi t z = lift(c + (drop z - c) * exp(drop t)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `mu = \z. (z - c) * smooth_step((z - c - e) / (s1 - e)) *
                       (&1 - smooth_step(z - zmax))` THEN
  ABBREV_TAC `v = \x:real^1. lift((mu:real->real)(drop x))` THEN
  SUBGOAL_THEN `!z. c + s1 <= z /\ z <= zmax ==> (mu:real->real) z = z - c`
  (LABEL_TAC "LIN") THENL
   [X_GEN_TAC `z:real` THEN STRIP_TAC THEN EXPAND_TAC "mu" THEN
    SUBGOAL_THEN `smooth_step((z - c - e) / (s1 - e)) = &1 /\ smooth_step(z - zmax) = &0`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_STEP_1 THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z <= c + e ==> (mu:real->real) z = &0` (LABEL_TAC "ZERO") THENL
   [X_GEN_TAC `z:real` THEN DISCH_TAC THEN EXPAND_TAC "mu" THEN
    SUBGOAL_THEN `smooth_step((z - c - e) / (s1 - e)) = &0` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC SMOOTH_STEP_0 THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^1) (v:real^1->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN EXPAND_TAC "mu" THEN
    SUBGOAL_THEN `open(:real^1)` ASSUME_TAC THENL [REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on (:real^1) (\x:real^1. lift(drop x))` ASSUME_TAC THENL
     [REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_ID]; ALL_TAC] THEN
    SCHZ_SMOOTH_TAC THEN REWRITE_TAC[IN_UNIV] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^1. norm((v:real^1->real^1) x) <= zmax + &1 - c` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN EXPAND_TAC "v" THEN REWRITE_TAC[NORM_LIFT] THEN
    ABBREV_TAC `z = drop(x:real^1)` THEN
    ASM_CASES_TAC `z <= c + e` THENL
     [USE_THEN "ZERO" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `z <= c + e`)]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `zmax + &1 <= z` THENL
     [EXPAND_TAC "mu" THEN
      SUBGOAL_THEN `smooth_step(z - zmax) = &1` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ABS_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "mu" THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    MP_TAC(SPEC `(z - c - e) / (s1 - e)` SMOOTH_STEP_BOUNDS) THEN
    MP_TAC(SPEC `z - zmax` SMOOTH_STEP_BOUNDS) THEN
    ABBREV_TAC `p = smooth_step((z - c - e) / (s1 - e))` THEN
    ABBREV_TAC `q = smooth_step(z - zmax)` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `abs(z - c) <= zmax + &1 - c /\ abs p <= &1 /\ abs(&1 - q) <= &1`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(zmax + &1 - c) * &1 * &1` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^1->real^1`; `zmax + &1 - c`] SCH5V_BOUNDED_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `v:real^1->real^1` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  EXISTS_TAC `ode_vf_flow (v:real^1->real^1) (:real^1)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^1) (v:real^1->real^1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real^1`; `z:real^1`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`v:real^1->real^1`; `(:real^1)`; `z:real^1`] ODE_VF_ZERO) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
     [EXPAND_TAC "v" THEN REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
      USE_THEN "ZERO" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1`; `z:real^1`] THEN STRIP_TAC THEN
  ABBREV_TAC `u = \s:real^1. lift(c + (drop z - c) * exp(drop s))` THEN
  ABBREV_TAC `J = interval[lift(min (&0) (drop t)),lift(max (&0) (drop t))]` THEN
  SUBGOAL_THEN `!s:real^1. s IN J ==> c + s1 <= drop((u:real^1->real^1) s) /\
                                      drop(u s) <= zmax` (LABEL_TAC "UJ") THENL
   [X_GEN_TAC `s:real^1` THEN EXPAND_TAC "J" THEN EXPAND_TAC "u" THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= drop z - c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `min (exp(&0)) (exp(drop t)) <= exp(drop s) /\
                  exp(drop s) <= max (exp(&0)) (exp(drop t))` MP_TAC THENL
     [REWRITE_TAC[REAL_MIN_LE; REAL_LE_MAX; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_0] THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_CASES_TAC `&1 <= exp(drop t)` THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c + (drop z - c) * &1` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> c + x <= c + y`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c + (drop z - c) * exp(drop t)` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> c + x <= c + y`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ASM_CASES_TAC `&1 <= exp(drop t)` THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c + (drop z - c) * exp(drop t)` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> c + x <= c + y`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c + (drop z - c) * &1` THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> c + x <= c + y`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^1->real^1`; `(:real^1)`; `J:real^1->bool`;
                 `u:real^1->real^1`; `vec 0:real^1`] ODE_VF_UNIQUE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC[IS_INTERVAL_INTERVAL]; ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "J" THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    SUBGOAL_THEN `(v:real^1->real^1)((u:real^1->real^1) s) =
                  lift((drop z - c) * exp(drop s))` SUBST1_TAC THENL
     [EXPAND_TAC "v" THEN REWRITE_TAC[LIFT_EQ] THEN
      USE_THEN "UJ" (MP_TAC o C MATCH_MP (ASSUME `(s:real^1) IN J`)) THEN
      DISCH_THEN(fun th -> USE_THEN "LIN" (fun lin -> REWRITE_TAC[MATCH_MP lin th])) THEN
      EXPAND_TAC "u" THEN REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `u = (lift o (\r. c + (drop z - c) * exp r) o drop)` SUBST1_TAC THENL
     [EXPAND_TAC "u" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `((\r. c + (drop z - c) * exp r) has_real_derivative
                   ((drop z - c) * exp(drop s))) (atreal (drop s))` MP_TAC THENL
     [REAL_DIFF_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; LIFT_DROP];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN ANTS_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  SUBGOAL_THEN `(u:real^1->real^1)(vec 0) = z` SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[DROP_VEC; REAL_EXP_0; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH `c + (z - c) = z`; LIFT_DROP];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "u" THEN REWRITE_TAC[]);;

(* A diffeomorphism of the line with two fixed points is increasing.        *)

let SCHZ_LINE_DIFFEO_MONO = prove
 (`!(h:real^1->real^1) h' a b.
     diffeomorphism_on (:real^1) (:real^1) h h' /\ drop a < drop b /\
     h a = a /\ h b = b
     ==> !x y. drop x < drop y ==> drop(h x) < drop(h y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^1->real^1`; `(:real^1)`] CONTINUOUS_INJECTIVE_IFF_MONOTONIC) THEN
  REWRITE_TAC[IS_INTERVAL_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ ~r ==> (p <=> q \/ r) ==> q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `b:real^1`]) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* Radial maps x |-> (xi |x| / |x|) x from a 1D flow fixing [0,c].         *)

let SCHZ_RADIAL_SMOOTH = prove
 (`!(Xi:real^1->real^1->real^1) t c.
     smooth_map_on (:real^(1,1)finite_sum) (\w. Xi (fstcart w) (sndcart w)) /\
     (!z. drop z <= c ==> Xi t z = z) /\ &0 < c
     ==> smooth_map_on (:real^3) (\x. (drop(Xi t (lift(norm x))) / norm x) % x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN X_GEN_TAC `x:real^3` THEN
  ASM_CASES_TAC `norm(x:real^3) < c` THENL
   [EXISTS_TAC `ball(vec 0:real^3,c)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\y:real^3. y` THEN
    REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_ID; IN_BALL_0] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `y:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_RZERO]; ALL_TAC] THEN
    SUBGOAL_THEN `(Xi:real^1->real^1->real^1) t (lift(norm(y:real^3))) = lift(norm y)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LIFT_DROP; REAL_DIV_REFL; NORM_EQ_0; VECTOR_MUL_LID];
    ALL_TAC] THEN
  EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
  SUBGOAL_THEN `open {y:real^3 | ~(y = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{y:real^3 | ~(y = vec 0)} = (:real^3) DIFF {vec 0}`] THEN
    SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(norm(vec 0:real^3) < c)` THEN
    ASM_REWRITE_TAC[NORM_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {y:real^3 | ~(y = vec 0)}
                  (\y. lift(drop((Xi:real^1->real^1->real^1) t (lift(norm y)))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_DROP] THEN
    MP_TAC(ISPECL [`Xi:real^1->real^1->real^1`; `{y:real^3 | ~(y = vec 0)}`;
                   `\y:real^3. drop t`; `\y:real^3. lift(norm y)`]
      SCH5V_FLOW_COMPOSE_SMOOTH) THEN
    ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_LIFT_NORM_NONZERO; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {y:real^3 | ~(y = vec 0)} (\y. lift(norm y))` ASSUME_TAC THENL
   [REWRITE_TAC[SMOOTH_MAP_ON_LIFT_NORM_NONZERO]; ALL_TAC] THEN
  MATCH_MP_TAC SCH3_SV_CMUL THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN
  MATCH_MP_TAC SCH3_SL_DIV THEN ASM_REWRITE_TAC[IN_ELIM_THM; NORM_EQ_0]);;

(* The radial squeeze: a diffeomorphism of R^3, the identity on the closed  *)
(* unit ball, mapping ball(0,2) into ball(0,1 + s1).                         *)

let SCHZ_SQUEEZE = prove
 (`!s1. &0 < s1
        ==> ?sg sg':real^3->real^3.
              diffeomorphism_on (:real^3) (:real^3) sg sg' /\
              (!x. norm x <= &1 ==> sg x = x) /\
              (!x. norm x < &2 ==> norm(sg x) < &1 + s1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = min (s1 / &2) (&1 / &2)` THEN
  SUBGOAL_THEN `&0 < s /\ s < s1 /\ s <= &1 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&1`; `s / &2`; `s:real`; `&3`] SCHZ_XI) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Xi:real^1->real^1->real^1` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (LABEL_TAC "XD") (CONJUNCTS_THEN2 (LABEL_TAC "XF") (LABEL_TAC "XE"))))))) THEN
  SUBGOAL_THEN `!t x y. drop x < drop y
                        ==> drop((Xi:real^1->real^1->real^1) t x) < drop(Xi t y)`
  (LABEL_TAC "XM") THENL
   [GEN_TAC THEN MATCH_MP_TAC SCHZ_LINE_DIFFEO_MONO THEN
    MAP_EVERY EXISTS_TAC [`(Xi:real^1->real^1->real^1) (--t)`; `lift(&0)`; `lift(&1)`] THEN
    REWRITE_TAC[ETA_AX] THEN USE_THEN "XD" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[LIFT_DROP; REAL_LT_01] THEN
    CONJ_TAC THEN USE_THEN "XF" MATCH_MP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `T0 = log(inv s)` THEN
  SUBGOAL_THEN `exp(--T0) = s` ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN REWRITE_TAC[REAL_EXP_NEG] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_LT_INV_EQ; REAL_INV_INV];
    ALL_TAC] THEN
  ABBREV_TAC `xi = \r. drop((Xi:real^1->real^1->real^1) (lift(--T0)) (lift r))` THEN
  ABBREV_TAC `xi' = \r. drop((Xi:real^1->real^1->real^1) (lift T0) (lift r))` THEN
  SUBGOAL_THEN `!r. r <= &1 + s / &2 ==> (xi:real->real) r = r /\ (xi':real->real) r = r`
  (LABEL_TAC "FIX") THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["xi"; "xi'"] THEN
    ASM_SIMP_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. (xi':real->real)((xi:real->real) r) = r /\ xi(xi' r) = r`
  (LABEL_TAC "INV") THENL
   [X_GEN_TAC `r:real` THEN MAP_EVERY EXPAND_TAC ["xi"; "xi'"] THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN
    REWRITE_TAC[GSYM LIFT_ADD; REAL_ADD_LINV; REAL_ADD_RINV; LIFT_NUM] THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r r'. r < r' ==> (xi:real->real) r < xi r' /\ (xi':real->real) r < xi' r'`
  (LABEL_TAC "MONO") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["xi"; "xi'"] THEN
    CONJ_TAC THEN USE_THEN "XM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. &0 < r ==> &0 < (xi:real->real) r /\ &0 < (xi':real->real) r`
  (LABEL_TAC "POS") THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= &1 + s / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "MONO" (fun th -> MP_TAC(MP (SPECL [`&0`; `r:real`] th) (ASSUME `&0 < r`))) THEN
    USE_THEN "FIX" (fun th -> MP_TAC(MP (SPEC `&0` th) (ASSUME `&0 <= &1 + s / &2`))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(xi:real->real) (&2) = &1 + s` ASSUME_TAC THENL
   [EXPAND_TAC "xi" THEN
    USE_THEN "XE" (MP_TAC o SPECL [`lift(--T0)`; `lift(&2)`]) THEN
    REWRITE_TAC[LIFT_DROP; ASSUME `exp(--T0) = s`] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^3. ((xi:real->real)(norm x) / norm x) % x`;
                        `\y:real^3. ((xi':real->real)(norm y) / norm y) % y`] THEN
  SUBGOAL_THEN `!x:real^3. norm(((xi:real->real)(norm x) / norm x) % x) = xi(norm x) /\
                           norm(((xi':real->real)(norm x) / norm x) % x) = xi'(norm x)`
  (LABEL_TAC "NORMS") THENL
   [X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `x:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_RZERO] THEN
      USE_THEN "FIX" (MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    USE_THEN "POS" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `&0 < norm(x:real^3)`))) THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_ARITH `&0 < x ==> abs x = x`];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "xi" THEN MATCH_MP_TAC SCHZ_RADIAL_SMOOTH THEN
      EXISTS_TAC `&1 + s / &2` THEN USE_THEN "XF" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "xi'" THEN MATCH_MP_TAC SCHZ_RADIAL_SMOOTH THEN
      EXISTS_TAC `&1 + s / &2` THEN USE_THEN "XF" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `x:real^3 = vec 0` THENL
       [ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_RZERO]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
      USE_THEN "NORMS" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `x:real^3` th)]) THEN
      USE_THEN "INV" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "POS" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `&0 < norm(x:real^3)`))) THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < (xi:real->real)(norm(x:real^3))` THEN
      UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD;
      X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `x:real^3 = vec 0` THENL
       [ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_RZERO]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
      USE_THEN "NORMS" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `x:real^3` th)]) THEN
      USE_THEN "INV" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "POS" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `&0 < norm(x:real^3)`))) THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < (xi':real->real)(norm(x:real^3))` THEN
      UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN ASM_CASES_TAC `x:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_RZERO]; ALL_TAC] THEN
    USE_THEN "FIX" (MP_TAC o SPEC `norm(x:real^3)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; NORM_EQ_0; VECTOR_MUL_LID];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "NORMS" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `x:real^3` th)]) THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `(xi:real->real)(&2)` THEN CONJ_TAC THENL
     [USE_THEN "MONO" (MP_TAC o SPECL [`norm(x:real^3)`; `&2`]) THEN ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC]]);;

(* An injective continuous self-map of the unit sphere of R^3 is onto: else *)
(* it embeds S^2 in the punctured sphere, which is homeomorphic to R^2.     *)

let SCHZ_SPHERE_ONTO = prove
 (`!k:real^3->real^3.
     k continuous_on sphere(vec 0,&1) /\
     IMAGE k (sphere(vec 0,&1)) SUBSET sphere(vec 0,&1) /\
     (!x y. x IN sphere(vec 0,&1) /\ y IN sphere(vec 0,&1) /\ k x = k y ==> x = y)
     ==> IMAGE k (sphere(vec 0,&1)) = sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `q:real^3`; `(:real^2)`]
    HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE) THEN
  ASM_REWRITE_TAC[REAL_LT_01; AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_2; DIMINDEX_3] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[homeomorphic; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^2` (X_CHOOSE_THEN `h':real^2->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`(h:real^3->real^2) o (k:real^3->real^3)`; `vec 0:real^3`; `&1`]
    NO_EMBEDDING_SPHERE_LOWDIM) THEN
  REWRITE_TAC[DIMINDEX_2; DIMINDEX_3; REAL_LT_01; o_THM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1) ==> (k:real^3->real^3) x IN
                           sphere(vec 0,&1) DELETE q` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_DELETE] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1) DELETE q` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x y. x IN sphere(vec 0:real^3,&1) /\ y IN sphere(vec 0,&1) /\
                                (k:real^3->real^3) x = k y ==> x = y`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* The open ball of a ball chart whose unit sphere goes onto a 2-sphere S  *)
(* is the bounded side of S.                                                 *)

let SCHZ_BALL_INSIDE = prove
 (`!(c:real^3->real^3) c' S.
     sch_ball c c' /\ S homeomorphic sphere(vec 0:real^3,&1) /\
     IMAGE c (sphere(vec 0,&1)) = S
     ==> IMAGE c (ball(vec 0,&1)) = inside S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_ball] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `S:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `(c:real^3->real^3) continuous_on ball(vec 0,&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,&1) SUBSET ball(vec 0,&2) /\
                cball(vec 0:real^3,&1) SUBSET ball(vec 0,&2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t = IMAGE (c:real^3->real^3) (ball(vec 0,&1))` THEN
  SUBGOAL_THEN `open(t:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC SCH4_DIFFEO_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,&2)`; `IMAGE (c:real^3->real^3) (ball(vec 0,&2))`;
                          `c':real^3->real^3`] THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(t:real^3->bool) /\ ~(t = {})` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[IMAGE_EQ_EMPTY; BALL_EQ_EMPTY] THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_BALL] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^3->real^3) (cball(vec 0,&1)) = t UNION S` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(IMAGE (c:real^3->real^3) (cball(vec 0,&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_CBALL] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `t INTER S:real^3->bool = {}` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    UNDISCH_TAC `IMAGE (c:real^3->real^3) (sphere(vec 0,&1)) = S` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a:real^3) IN ball(vec 0,&2) /\ (b:real^3) IN ball(vec 0,&2)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(a:real^3) IN ball(vec 0,&1)` THEN
      UNDISCH_TAC `(b:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_BALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `a:real^3 = b` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(a:real^3) IN ball(vec 0,&1)` THEN
    UNDISCH_TAC `(b:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_BALL_0; IN_SPHERE_0] THEN MESON_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `t SUBSET inside S \/ t SUBSET outside(S:real^3->bool)` MP_TAC THENL
   [MATCH_MP_TAC SCH1_CONNECTED_SIDE THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC SCH1_CLOPEN_EQ THEN
    EXISTS_TAC `IMAGE (c:real^3->real^3) (cball(vec 0,&1))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ASM SET_TAC[]];
    SUBGOAL_THEN `t = outside(S:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC SCH1_CLOPEN_EQ THEN
      EXISTS_TAC `IMAGE (c:real^3->real^3) (cball(vec 0,&1))` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `~bounded(outside(S:real^3->bool))` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN EXPAND_TAC "t" THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (c:real^3->real^3) (cball(vec 0,&1))` THEN
    SIMP_TAC[IMAGE_SUBSET; BALL_SUBSET_CBALL] THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_CBALL] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]]);;

(* A ball chart whose unit sphere goes into S = g(sphere) maps it onto S.  *)

let SCHZ_CHART_SPHERE_ONTO = prove
 (`!g g' (c:real^3->real^3) c'.
     sch_neck g g' /\ sch_ball c c' /\
     IMAGE c (sphere(vec 0,&1)) SUBSET IMAGE g (sphere(vec 0,&1))
     ==> IMAGE c (sphere(vec 0,&1)) = IMAGE g (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_ball] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "SUB"))) THEN
  REWRITE_TAC[diffeomorphism_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CINV") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CSM") ASSUME_TAC)))))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "G'C")
    (CONJUNCTS_THEN2 (LABEL_TAC "GPG") (CONJUNCTS_THEN2 (LABEL_TAC "GGP")
     ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1) ==> x IN ball(vec 0,&2) /\
                           x IN annulus (&1 / &2) (&2)` (LABEL_TAC "SPH") THENL
   [REWRITE_TAC[IN_SPHERE_0; IN_BALL_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1)
                ==> ?y. y IN sphere(vec 0,&1) /\ (c:real^3->real^3) x = (g:real^3->real^3) y`
  (LABEL_TAC "CY") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "SUB" (MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(g':real^3->real^3) o (c:real^3->real^3)` SCHZ_SPHERE_ONTO) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))` THEN
        USE_THEN "G'C" (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        USE_THEN "CY" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN sphere(vec 0,&1)`)) THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        USE_THEN "SPH" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN sphere(vec 0,&1)`)) THEN
        SIMP_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      USE_THEN "CY" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN sphere(vec 0,&1)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "SPH" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN sphere(vec 0,&1)`)) THEN
      STRIP_TAC THEN USE_THEN "GPG" (fun th -> ASM_SIMP_TAC[th]);
      MAP_EVERY X_GEN_TAC [`x:real^3`; `x':real^3`] THEN REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
      USE_THEN "CY" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN sphere(vec 0,&1)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "CY" (MP_TAC o C MATCH_MP (ASSUME `(x':real^3) IN sphere(vec 0,&1)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(g':real^3->real^3)((c:real^3->real^3) x) = g'(c x')` THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "SPH" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN sphere(vec 0,&1)`)) THEN
      USE_THEN "SPH" (MP_TAC o C MATCH_MP (ASSUME `(y':real^3) IN sphere(vec 0,&1)`)) THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `y:real^3 = y'` SUBST_ALL_TAC THENL
       [USE_THEN "GPG" (fun th -> ASM_MESON_TAC[th]); ALL_TAC] THEN
      SUBGOAL_THEN `(c:real^3->real^3) x = c x'` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `c':real^3->real^3`) THEN
      USE_THEN "SPH" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN sphere(vec 0,&1)`)) THEN
      USE_THEN "SPH" (MP_TAC o C MATCH_MP (ASSUME `(x':real^3) IN sphere(vec 0,&1)`)) THEN
      REPEAT STRIP_TAC THEN USE_THEN "CINV" (fun th -> ASM_MESON_TAC[th])];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN USE_THEN "SUB" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE ((g':real^3->real^3) o (c:real^3->real^3))
                                  (sphere(vec 0,&1))` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; o_THM] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "CY" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN sphere(vec 0,&1)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "SPH" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN sphere(vec 0,&1)`)) THEN
  STRIP_TAC THEN USE_THEN "GPG" (fun th -> ASM_SIMP_TAC[th]));;

(* The ball chart from a model chart.                                        *)

let SCHZ_BOUNDS_FROM_CHART = prove
 (`!g g':real^3->real^3 (Theta:real^3->real^3) U (cen:real^3) rho.
     sch_neck g g' /\ open U /\ &0 < rho /\ cball(cen,rho) SUBSET U /\
     smooth_map_on U Theta /\
     (!x y. x IN U /\ y IN U /\ Theta x = Theta y ==> x = y) /\
     (!x. x IN U ==> ~(det(matrix(frechet_derivative Theta (at x))) = &0)) /\
     IMAGE Theta (sphere(cen,rho)) SUBSET IMAGE g (sphere(vec 0,&1))
     ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Theta:real^3->real^3`; `U:real^3->bool`] SCHI_INJ_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Theta':real^3->real^3`) THEN
  MP_TAC(ISPECL [`cball(cen:real^3,rho)`; `(:real^3) DIFF U`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_CBALL; GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SEP"))) THEN
  SUBGOAL_THEN `&0 < d / (&2 * rho) /\ rho * d / (&2 * rho) < d` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    SUBGOAL_THEN `rho * d / (&2 * rho) = d / &2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `s1 = d / (&2 * rho)` THEN
  SUBGOAL_THEN `!w:real^3. norm w < &1 + s1 ==> cen + rho % w IN U` (LABEL_TAC "MARG") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `norm(w:real^3) <= &1` THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (term_match [] `cball(cen:real^3,rho) SUBSET U`) (concl th))) THEN
      REWRITE_TAC[IN_CBALL; NORM_ARITH `dist(c:real^3,c + y) = norm y`; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 < norm(w:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "SEP" (MP_TAC o SPECL [`cen + (rho / norm(w:real^3)) % w`; `cen + rho % w:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_CBALL; NORM_ARITH `dist(c:real^3,c + y) = norm y`;
                      NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_DIV_RMUL; REAL_LT_IMP_NZ;
                   REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x < d ==> d <= x ==> F`) THEN
    REWRITE_TAC[NORM_ARITH `dist(c + x:real^3,c + y) = norm(y - x)`] THEN
    REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
    SUBGOAL_THEN `abs(rho - rho / norm(w:real^3)) * norm w = rho * (norm w - &1)`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `rho / norm(w:real^3) <= rho` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `b <= a ==> abs(a - b) = a - b`] THEN
      UNDISCH_TAC `&0 < norm(w:real^3)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `rho * s1` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `s1:real` SCHZ_SQUEEZE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^3->real^3` (X_CHOOSE_THEN `sg':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "SGI") (LABEL_TAC "SGB"))))) THEN
  ABBREV_TAC `Q = \y:real^3. cen + rho % y` THEN
  ABBREV_TAC `Q' = \z:real^3. inv rho % (z - cen)` THEN
  SUBGOAL_THEN `diffeomorphism_on (:real^3) (:real^3) (Q:real^3->real^3) Q'` ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN MAP_EVERY EXPAND_TAC ["Q"; "Q'"] THEN
    SUBGOAL_THEN `open(:real^3)` ASSUME_TAC THENL [REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SCHZ_SMOOTH_TAC;
      SCHZ_SMOOTH_TAC;
      GEN_TAC THEN REWRITE_TAC[VECTOR_ADD_SUB; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (:real^3) (:real^3) ((Q:real^3->real^3) o (sg:real^3->real^3))
                  ((sg':real^3->real^3) o (Q':real^3->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `W = IMAGE ((Q:real^3->real^3) o (sg:real^3->real^3)) (ball(vec 0,&2))` THEN
  SUBGOAL_THEN `diffeomorphism_on (ball(vec 0,&2)) W ((Q:real^3->real^3) o (sg:real^3->real^3))
                  ((sg':real^3->real^3) o (Q':real^3->real^3))` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC SCH_DIFFEO_RESTRICT_UNIV THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:real^3->bool) SUBSET U` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0; o_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXPAND_TAC "Q" THEN
    USE_THEN "MARG" MATCH_MP_TAC THEN USE_THEN "SGB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(W:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on W (IMAGE (Theta:real^3->real^3) W) Theta Theta'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCH4_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `IMAGE (Theta:real^3->real^3) U`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = (Theta:real^3->real^3) o (Q:real^3->real^3) o (sg:real^3->real^3)` THEN
  SUBGOAL_THEN `sch_ball (c:real^3->real^3) (((sg':real^3->real^3) o (Q':real^3->real^3)) o Theta')`
  ASSUME_TAC THENL
   [REWRITE_TAC[sch_ball] THEN EXPAND_TAC "c" THEN
    SUBGOAL_THEN `IMAGE ((Theta:real^3->real^3) o (Q:real^3->real^3) o (sg:real^3->real^3)) (ball(vec 0,&2)) =
                  IMAGE Theta W` SUBST1_TAC THENL
     [EXPAND_TAC "W" THEN REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `W:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* The boundary sphere. *)
  SUBGOAL_THEN `IMAGE (Q:real^3->real^3) (sphere(vec 0,&1)) = sphere(cen,rho)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE; IN_SPHERE_0] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[NORM_ARITH `dist(c:real^3,c + y) = norm y`; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID];
      DISCH_TAC THEN EXISTS_TAC `inv rho % (z - cen:real^3)` THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
      SUBGOAL_THEN `norm(z - cen:real^3) = rho` ASSUME_TAC THENL
       [ASM_MESON_TAC[dist; NORM_SUB]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < r ==> abs r = r`;
                   REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (sg:real^3->real^3) (sphere(vec 0,&1)) = sphere(vec 0,&1) /\
                IMAGE (sg:real^3->real^3) (cball(vec 0,&1)) = cball(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
      `(!x. x IN s ==> (f:real^3->real^3) x = x) ==> IMAGE f s = s`) THEN
    REWRITE_TAC[IN_SPHERE_0; IN_CBALL_0] THEN
    REPEAT STRIP_TAC THEN USE_THEN "SGI" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^3->real^3) (sphere(vec 0,&1)) SUBSET
                IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^3->real^3) (sphere(vec 0,&1)) =
                IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHZ_CHART_SPHERE_ONTO THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`;
      `((sg':real^3->real^3) o (Q':real^3->real^3)) o (Theta':real^3->real^3)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[sch_bounds_ball] THEN
  MAP_EVERY EXISTS_TAC [`c:real^3->real^3`;
                        `((sg':real^3->real^3) o (Q':real^3->real^3)) o (Theta':real^3->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN
  MP_TAC(ISPECL [`c:real^3->real^3`;
                 `((sg':real^3->real^3) o (Q':real^3->real^3)) o (Theta':real^3->real^3)`;
                 `IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`] SCHZ_BALL_INSIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH1_NECK_HOMEOMORPHIC THEN
    EXISTS_TAC `g':real^3->real^3` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The vertical field of a general defining function Fd (the                 *)
(* analogue of sch5v_grad, sch5v_hfield and SCH5V_FIELD for |g'|^2): for Fd  *)
(* smooth on an open O, V = e3 + chi hfield(Fd) is smooth, bounded, has       *)
(* V3 = 1, and is tangent to the level sets of Fd where chi = 1; Fd is then a  *)
(* first integral of the flow along trajectories staying there.              *)
(* ------------------------------------------------------------------------- *)

let schz_grad = new_definition
 `schz_grad (Fd:real^3->real) (x:real^3) =
    vector[drop(frechet_derivative (\y. lift(Fd y)) (at x) (basis 1));
           drop(frechet_derivative (\y. lift(Fd y)) (at x) (basis 2));
           drop(frechet_derivative (\y. lift(Fd y)) (at x) (basis 3))]:real^3`;;

let schz_oh = new_definition
 `schz_oh (O:real^3->bool) (Fd:real^3->real) =
    {x | x IN O /\ ~((schz_grad Fd x)$1 pow 2 + (schz_grad Fd x)$2 pow 2 = &0)}`;;

let schz_hfield = new_definition
 `schz_hfield (Fd:real^3->real) (x:real^3) =
    (--((schz_grad Fd x)$3) /
     ((schz_grad Fd x)$1 pow 2 + (schz_grad Fd x)$2 pow 2)) %
    vector[(schz_grad Fd x)$1; (schz_grad Fd x)$2; &0]:real^3`;;

let SCHZ_LINEAR_DOT = prove
 (`!L:real^3->real^1.
     linear L
     ==> !v. L v = lift(vector[drop(L(basis 1)); drop(L(basis 2)); drop(L(basis 3))] dot v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v:real^3 = v$1 % basis 1 + v$2 % basis 2 + v$3 % basis 3`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
  REWRITE_TAC[DOT_3; VECTOR_3; GSYM DROP_EQ; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
  REAL_ARITH_TAC);;

let SCHZ_GRAD_HAS_DERIVATIVE = prove
 (`!O (Fd:real^3->real) x.
     open O /\ smooth_map_on O (\x. lift(Fd x)) /\ x IN O
     ==> ((\y. lift(Fd y)) has_derivative (\v. lift(schz_grad Fd x dot v))) (at x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `\x:real^3. lift(Fd x)`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(\v. lift(schz_grad (Fd:real^3->real) x dot v)) =
                frechet_derivative (\y. lift(Fd y)) (at x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^3` THEN
    MP_TAC(ISPEC `frechet_derivative (\y. lift((Fd:real^3->real) y)) (at x)` SCHZ_LINEAR_DOT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[LINEAR_FRECHET_DERIVATIVE; differentiable]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN REWRITE_TAC[schz_grad];
    ASM_REWRITE_TAC[]]);;

let SCHZ_GRAD_SMOOTH = prove
 (`!O (Fd:real^3->real).
     open O /\ smooth_map_on O (\x. lift(Fd x)) ==> smooth_map_on O (schz_grad Fd)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `schz_grad (Fd:real^3->real)`] SMOOTH_MAP_ON_COMPONENTWISE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= k /\ k <= 3 <=> k = 1 \/ k = 2 \/ k = 3`] THEN
  X_GEN_TAC `k:num` THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[schz_grad; VECTOR_3; LIFT_DROP] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]);;

let SCHZ_OH_OPEN = prove
 (`!O (Fd:real^3->real).
     open O /\ smooth_map_on O (\x. lift(Fd x)) ==> open(schz_oh O Fd)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCHZ_GRAD_SMOOTH o CONJ (ASSUME `open(O:real^3->bool)`)) THEN
  SUBGOAL_THEN `!k. smooth_map_on O (\x. lift((schz_grad (Fd:real^3->real) x)$k))`
  (LABEL_TAC "C") THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[schz_oh] THEN
  SUBGOAL_THEN
   `{x | x IN O /\ ~((schz_grad (Fd:real^3->real) x)$1 pow 2 + (schz_grad Fd x)$2 pow 2 = &0)} =
    {x | x IN O /\ (\x. lift((schz_grad Fd x)$1 pow 2 + (schz_grad Fd x)$2 pow 2)) x IN
                   (:real^1) DIFF {vec 0}}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING] THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
  ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  ASM_REWRITE_TAC[] THEN SCHZ_SMOOTH_TAC THEN USE_THEN "C" (fun th -> REWRITE_TAC[th]));;

let SCHZ_HFIELD_SMOOTH = prove
 (`!O (Fd:real^3->real).
     open O /\ smooth_map_on O (\x. lift(Fd x))
     ==> smooth_map_on (schz_oh O Fd) (schz_hfield Fd)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCHZ_OH_OPEN o CONJ (ASSUME `open(O:real^3->bool)`)) THEN
  SUBGOAL_THEN `!k. smooth_map_on (schz_oh O Fd)
                      (\x. lift((schz_grad (Fd:real^3->real) x)$k))` (LABEL_TAC "C") THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_SIMP_TAC[SCHZ_GRAD_SMOOTH] THEN
    REWRITE_TAC[schz_oh; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `schz_hfield (Fd:real^3->real) =
    (\x. (--((schz_grad Fd x)$3) /
          ((schz_grad Fd x)$1 pow 2 + (schz_grad Fd x)$2 pow 2)) %
         vector[(schz_grad Fd x)$1; (schz_grad Fd x)$2; &0])`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schz_hfield]; ALL_TAC] THEN
  SCHZ_SMOOTH_TAC THEN TRY(USE_THEN "C" (fun th -> REWRITE_TAC[th]) THEN NO_TAC) THEN
  REWRITE_TAC[schz_oh; IN_ELIM_THM] THEN SIMP_TAC[]);;

let SCHZ_HFIELD_FACTS = prove
 (`!(Fd:real^3->real) x.
     (schz_hfield Fd x)$3 = &0 /\
     (~((schz_grad Fd x)$1 pow 2 + (schz_grad Fd x)$2 pow 2 = &0)
      ==> schz_grad Fd x dot (basis 3 + schz_hfield Fd x) = &0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[schz_hfield; VECTOR_MUL_COMPONENT; VECTOR_3; REAL_MUL_RZERO] THEN
  SIMP_TAC[DOT_RADD; DOT_RMUL; DOT_BASIS; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[DOT_3; VECTOR_3] THEN
  ABBREV_TAC `p = schz_grad (Fd:real^3->real) x` THEN CONV_TAC REAL_FIELD);;

(* The field (as SCH5V_FIELD).                                             *)

let SCHZ_FIELD = prove
 (`!O (Fd:real^3->real) (chi:real^3->real) L.
     open O /\ smooth_map_on O (\x. lift(Fd x)) /\ smooth_map_on (:real^3) (\x. lift(chi x)) /\
     (!x. &0 <= chi x /\ chi x <= &1) /\
     compact L /\ L SUBSET schz_oh O Fd /\ (!x. ~(x IN L) ==> chi x = &0)
     ==> smooth_map_on (:real^3) (\x. basis 3 + chi x % schz_hfield Fd x) /\
         (?B. !x. norm(basis 3 + chi x % schz_hfield Fd x) <= B) /\
         (!x. (basis 3 + chi x % schz_hfield Fd x)$3 = &1) /\
         (!x. ~(x IN L) ==> basis 3 + chi x % schz_hfield Fd x = basis 3) /\
         (!x. x IN schz_oh O Fd /\ chi x = &1
              ==> schz_grad Fd x dot (basis 3 + chi x % schz_hfield Fd x) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `Fd:real^3->real`] SCHZ_OH_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `Fd:real^3->real`] SCHZ_HFIELD_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. ~(x IN L) ==> basis 3 + (chi:real^3->real) x % schz_hfield (Fd:real^3->real) x = basis 3`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `(x:real^3) IN schz_oh (O:real^3->bool) (Fd:real^3->real)` THENL
     [EXISTS_TAC `schz_oh (O:real^3->bool) (Fd:real^3->real)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      MP_TAC(ISPECL [`schz_oh (O:real^3->bool) (Fd:real^3->real)`; `\x. lift((chi:real^3->real) x)`;
                     `schz_hfield (Fd:real^3->real)`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      EXISTS_TAC `(:real^3) DIFF L` THEN
      ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\x:real^3. basis 3:real^3` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_DIFF; IN_UNIV] THEN ASM_SIMP_TAC[]];
    SUBGOAL_THEN `bounded(IMAGE (schz_hfield (Fd:real^3->real)) L)` MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `schz_oh (O:real^3->bool) (Fd:real^3->real)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      ALL_TAC] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `&1 + M` THEN X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `(x:real^3) IN L` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(basis 3:real^3) + norm((chi:real^3->real) x % schz_hfield (Fd:real^3->real) x)` THEN
      REWRITE_TAC[NORM_TRIANGLE] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; NORM_MUL] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= M ==> &1 + x <= &1 + M`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 * norm(schz_hfield (Fd:real^3->real) x)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        MP_TAC(SPEC `x:real^3` (ASSUME `!x. &0 <= (chi:real^3->real) x /\ chi x <= &1`)) THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_LID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC];
    GEN_TAC THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; SCHZ_HFIELD_FACTS] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
    MATCH_MP_TAC(CONJUNCT2(SPEC_ALL SCHZ_HFIELD_FACTS)) THEN
    UNDISCH_TAC `(x:real^3) IN schz_oh (O:real^3->bool) (Fd:real^3->real)` THEN
    REWRITE_TAC[schz_oh; IN_ELIM_THM] THEN SIMP_TAC[]]);;

(* Fd is a first integral of the flow of V along trajectories staying in an *)
(* open U on which V is tangent to the level sets of Fd.                     *)

let SCHZ_FD_FIRST_INTEGRAL = prove
 (`!O (Fd:real^3->real) (V:real^3->real^3) U x t.
     open O /\ smooth_map_on O (\x. lift(Fd x)) /\
     smooth_map_on (:real^3) V /\ (!y. ode_vf_maxint V (:real^3) y = (:real^1)) /\
     open U /\ U SUBSET O /\ (!y. y IN U ==> schz_grad Fd y dot V y = &0) /\
     (!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
          ==> ode_vf_flow V (:real^3) u x IN U)
     ==> Fd(ode_vf_flow V (:real^3) t x) = Fd x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LIFT_EQ] THEN
  MP_TAC(ISPECL [`V:real^3->real^3`; `\y:real^3. lift(Fd y)`; `U:real^3->bool`;
                 `x:real^3`; `t:real^1`] SCH5V_FLOW_FIRST_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN O` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `Fd:real^3->real`; `y:real^3`]
    SCHZ_GRAD_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  ASM_SIMP_TAC[LIFT_NUM]);;

(* ------------------------------------------------------------------------- *)
(* The setup for the ball chart.  Heights m < M of the two                   *)
(* critical points, exact charts ph0 (bottom, z = m + |u|^2) and ph1 (top,   *)
(* z = M - |u|^2), the regular points between the two critical heights, and  *)
(* a margin eps below which (above which) S lies in the bottom (top) chart  *)
(* cylinder of half radius.                                                   *)
(* ------------------------------------------------------------------------- *)

let SCHZ_REGULAR_OH = prove
 (`!g g':real^3->real^3 x.
     sch_neck g g' /\ x IN IMAGE g (sphere(vec 0,&1)) /\
     (!t. sch_crit g t ==> ~((g t)$3 = x$3))
     ==> x IN sch5v_oh g g'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[sch5v_oh; IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `~sch_crit (g:real^3->real^3) s` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `s:real^3`] SCH5V_CRIT_GRAD) THEN
  ASM_REWRITE_TAC[REAL_SOS_EQ_0] THEN SIMP_TAC[]);;

(* A compact set whose minimum of f is attained only at p lies in a given   *)
(* open neighbourhood of p below the level m + eps.                          *)

let SCHZ_LOCALIZE = prove
 (`!S U (p:real^3) (f:real^3->real) m.
     compact S /\ open U /\ p IN U /\ (lift o f) continuous_on S /\
     (!x. x IN S ==> m <= f x) /\ (!x. x IN S /\ f x = m ==> x = p)
     ==> ?eps. &0 < eps /\ !x. x IN S /\ f x < m + eps ==> x IN U`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `S DIFF U:real^3->bool = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real`; `S DIFF U:real^3->bool`] CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_DIFF] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `m < (f:real^3->real) q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `q:real^3 = p` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  EXISTS_TAC `(f:real^3->real) q - m` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
    can (term_match [] `!y:real^3. y IN S DIFF U ==> (f:real^3->real) q <= f y`) (concl th))) THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN ASM_REAL_ARITH_TAC);;

let SCHZ_SETUP = prove
 (`!g g':real^3->real^3.
     sch_neck g g' /\ sch_morse g /\ sch_saddles g = {}
     ==> ?m M r0 (ph0:real^2->real^2) ph0' r1 (ph1:real^2->real^2) ph1' eps.
           m < M /\
           (!x. x IN IMAGE g (sphere(vec 0,&1)) ==> m <= x$3 /\ x$3 <= M) /\
           (!x. x IN IMAGE g (sphere(vec 0,&1)) /\ m < x$3 /\ x$3 < M
                ==> x IN sch5v_oh g g') /\
           &0 < r0 /\ r0 < &1 /\
           diffeomorphism_on (ball(vec 0,r0)) (IMAGE ph0 (ball(vec 0,r0))) ph0 ph0' /\
           (!y. sch5v_pr y IN ball(vec 0,r0) /\ abs(y$3 - m) < r0
                ==> (schz_lift ph0 y IN IMAGE g (sphere(vec 0,&1)) <=>
                     y$3 = m + norm(sch5v_pr y) pow 2)) /\
           &0 < r1 /\ r1 < &1 /\
           diffeomorphism_on (ball(vec 0,r1)) (IMAGE ph1 (ball(vec 0,r1))) ph1 ph1' /\
           (!y. sch5v_pr y IN ball(vec 0,r1) /\ abs(y$3 - M) < r1
                ==> (schz_lift ph1 y IN IMAGE g (sphere(vec 0,&1)) <=>
                     y$3 = M - norm(sch5v_pr y) pow 2)) /\
           &0 < eps /\
           (!x. x IN IMAGE g (sphere(vec 0,&1)) /\ x$3 < m + eps
                ==> x IN schz_cyl ph0 m (r0 / &2)) /\
           (!x. x IN IMAGE g (sphere(vec 0,&1)) /\ M - eps < x$3
                ==> x IN schz_cyl ph1 M (r1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCHZ_TWO_CRIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^3` (X_CHOOSE_THEN `t1:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "H0") (CONJUNCTS_THEN2 (LABEL_TAC "H1")
    (CONJUNCTS_THEN2 (LABEL_TAC "CR") (CONJUNCTS_THEN2 (LABEL_TAC "EX")
    (CONJUNCTS_THEN2 (LABEL_TAC "U0") (CONJUNCTS_THEN2 (LABEL_TAC "U1")
     ASSUME_TAC))))))))))) THEN
  USE_THEN "H0" (MP_TAC o MATCH_MP SCHZ_HCHART_LIFT) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `ph0:real^2->real^2`
    (X_CHOOSE_THEN `ph0':real^2->real^2` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C0"))))))) o CONJUNCT2) THEN
  USE_THEN "H1" (MP_TAC o MATCH_MP SCHZ_HCHART_LIFT) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `ph1:real^2->real^2`
    (X_CHOOSE_THEN `ph1':real^2->real^2` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C1"))))))) o CONJUNCT2) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHZ_SURFACE_FACTS) THEN
  ABBREV_TAC `S = IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` THEN
  SUBGOAL_THEN `!x:real^3. x IN S ==> (g:real^3->real^3) t0$3 <= x$3 /\ x$3 <= g t1$3`
  (LABEL_TAC "RANGE") THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN USE_THEN "EX" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open(schz_cyl (ph0:real^2->real^2) ((g:real^3->real^3) t0$3) (r0 / &2)) /\
                open(schz_cyl (ph1:real^2->real^2) ((g:real^3->real^3) t1$3) (r1 / &2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^3->bool`; `(g:real^3->real^3) t0$3`; `&1`; `r0:real`;
                     `ph0:real^2->real^2`; `ph0':real^2->real^2`; `r0 / &2`] SCHZ_CYL);
      MP_TAC(ISPECL [`S:real^3->bool`; `(g:real^3->real^3) t1$3`; `-- &1`; `r1:real`;
                     `ph1:real^2->real^2`; `ph1':real^2->real^2`; `r1 / &2`] SCHZ_CYL)] THEN
    ASM_REWRITE_TAC[] THEN (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) t0 IN schz_cyl ph0 ((g:real^3->real^3) t0$3) (r0 / &2) /\
                (g:real^3->real^3) t1 IN schz_cyl ph1 ((g:real^3->real^3) t1$3) (r1 / &2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[schz_cyl; IN_IMAGE; IN_ELIM_THM] THEN CONJ_TAC THENL
     [EXISTS_TAC `sch5v_at ((g:real^3->real^3) t0$3) (vec 0)`;
      EXISTS_TAC `sch5v_at ((g:real^3->real^3) t1$3) (vec 0)`] THEN
    ASM_REWRITE_TAC[SCH5V_PR_AT; CENTRE_IN_BALL; REAL_SUB_REFL; REAL_ABS_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`;
                 `schz_cyl ph0 ((g:real^3->real^3) t0$3) (r0 / &2)`;
                 `(g:real^3->real^3) t0`; `\x:real^3. x$3`; `(g:real^3->real^3) t0$3`]
    SCHZ_LOCALIZE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN
      REWRITE_TAC[DIMINDEX_3; ARITH];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN USE_THEN "U0" MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^3->bool`;
                 `schz_cyl ph1 ((g:real^3->real^3) t1$3) (r1 / &2)`;
                 `(g:real^3->real^3) t1`; `\x:real^3. --(x$3)`; `--((g:real^3->real^3) t1$3)`]
    SCHZ_LOCALIZE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_NEG] THEN MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN REWRITE_TAC[DIMINDEX_3; ARITH];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_NEG2; REAL_EQ_NEG2] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN USE_THEN "U1" MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`(g:real^3->real^3) t0$3`; `(g:real^3->real^3) t1$3`;
                        `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`;
                        `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                        `min e0 e1`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC SCHZ_REGULAR_OH THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^3` THEN
    USE_THEN "CR" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "C0" (fun th -> REWRITE_TAC[REAL_MUL_LID; MATCH_MP th
      (ASSUME `sch5v_pr (y:real^3) IN ball(vec 0,r0) /\ abs(y$3 - (g:real^3->real^3) t0$3) < r0`)]);
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "C1" (fun th -> REWRITE_TAC[REAL_ARITH `a + -- &1 * b = a - b`; MATCH_MP th
      (ASSUME `sch5v_pr (y:real^3) IN ball(vec 0,r1) /\ abs(y$3 - (g:real^3->real^3) t1$3) < r1`)]);
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x:real^3. x IN S /\ x$3 < m + e0 ==> x IN U`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x:real^3. x IN S /\ --(x$3) < --m + e1 ==> x IN U`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* The flow of pc_sch_vflow for the regular band [zA,zB]: S is invariant    *)
(* while the height stays in the band.                                       *)

let SCHZ_BAND_FLOW = prove
 (`!g g':real^3->real^3 zA zB.
     sch_neck g g' /\ zA <= zB /\
     (!x. x IN IMAGE g (sphere(vec 0,&1)) /\ zA <= x$3 /\ x$3 <= zB
          ==> x IN sch5v_oh g g')
     ==> ?Psi0:real^1->real^3->real^3.
           (!x. Psi0 (vec 0) x = x) /\ (!x s t. Psi0 t (Psi0 s x) = Psi0 (s + t) x) /\
           (!t x. (Psi0 t x)$3 = x$3 + drop t) /\
           smooth_map_on (:real^(1,3)finite_sum) (\w. Psi0 (fstcart w) (sndcart w)) /\
           (!t. diffeomorphism_on (:real^3) (:real^3) (Psi0 t) (Psi0 (--t))) /\
           (!x t. x IN IMAGE g (sphere(vec 0,&1)) /\ zA <= x$3 /\ x$3 <= zB /\
                  zA <= x$3 + drop t /\ x$3 + drop t <= zB
                  ==> Psi0 t x IN IMAGE g (sphere(vec 0,&1)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `C = {x | x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\
                       zA <= x$3 /\ x$3 <= zB}` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHZ_SURFACE_FACTS) THEN
  SUBGOAL_THEN `compact(C:real^3->bool) /\ C SUBSET sch5v_oh g g' /\
                C SUBSET IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `{x | x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\
                         zA <= x$3 /\ x$3 <= zB} =
                    IMAGE g (sphere(vec 0,&1)) INTER {x:real^3 | zA <= x$3} INTER
                    {x:real^3 | x$3 <= zB}` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_INTER_CLOSED THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE];
        REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `C:real^3->bool`;
                 `C:real^3->bool`; `&1`] SCH5V_PANCAKE_FIELD) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  REWRITE_TAC[SET_RULE `(s:real^3->bool) INTER c SUBSET c`] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->real^3` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPEC `v:real^3->real^3` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  EXISTS_TAC `ode_vf_flow (v:real^3->real^3) (:real^3)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t x. (ode_vf_flow (v:real^3->real^3) (:real^3) t x)$3 = x$3 + drop t`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `v:real^3->real^3` SCH5V_FLOW_HEIGHT) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ode_vf_flow (v:real^3->real^3) (:real^3)`;
                 `\x:real^3. norm((g':real^3->real^3) x) pow 2`;
                 `IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`; `C:real^3->bool`;
                 `B:real`; `d:real`; `C:real^3->bool`; `zA:real`; `zB:real`] SCHZ_BAND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; SUBSET_REFL] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `y:real^3` THEN
      SUBGOAL_THEN `(\t. ode_vf_flow (v:real^3->real^3) (:real^3) t y) =
                    (\w. ode_vf_flow v (:real^3) (fstcart w) (sndcart w)) o
                    (\t:real^1. pastecart t y)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(:real^(1,3)finite_sum)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`] SCH5V_FLOW_DISPLACEMENT) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC SCH5V_IN_SURFACE THEN
      ASM_SIMP_TAC[];
      EXPAND_TAC "C" THEN SIMP_TAC[IN_ELIM_THM];
      EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN EXPAND_TAC "C" THEN
      SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `t:real^1`]) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "C" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Planar facts for the interpolation of defining functions.                 *)
(* A chart maps a round ball onto the bounded side of the image sphere (any *)
(* dimension >= 2); hence a homeomorphism of R^2 that maps one chart circle *)
(* onto another maps the chart discs onto each other.                        *)
(* ------------------------------------------------------------------------- *)

let SCHZ_CHART_BALL_INSIDE = prove
 (`!(c:real^N->real^N) c' r rho.
     2 <= dimindex(:N) /\
     diffeomorphism_on (ball(vec 0,r)) (IMAGE c (ball(vec 0,r))) c c' /\
     &0 < rho /\ rho < r
     ==> IMAGE c (ball(vec 0,rho)) = inside(IMAGE c (sphere(vec 0,rho)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE (c:real^N->real^N) (sphere(vec 0,rho))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `(c:real^N->real^N) continuous_on ball(vec 0,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^N,rho) SUBSET ball(vec 0,r) /\
                cball(vec 0:real^N,rho) SUBSET ball(vec 0,r) /\
                sphere(vec 0:real^N,rho) SUBSET ball(vec 0,r)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^N->bool) homeomorphic sphere(vec 0:real^N,&1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^N->bool`; `sphere(vec 0:real^N,rho)`;
                   `sphere(vec 0:real^N,&1)`] HOMEOMORPHIC_TRANS) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      EXISTS_TAC `c:real^N->real^N` THEN MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
      ASM_REWRITE_TAC[COMPACT_SPHERE] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM_MESON_TAC[SUBSET]];
      REWRITE_TAC[HOMEOMORPHIC_SPHERES_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `S:real^N->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `t = IMAGE (c:real^N->real^N) (ball(vec 0,rho))` THEN
  SUBGOAL_THEN `open(t:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC SCH4_DIFFEO_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^N,r)`; `IMAGE (c:real^N->real^N) (ball(vec 0,r))`;
                          `c':real^N->real^N`] THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(t:real^N->bool) /\ ~(t = {})` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[IMAGE_EQ_EMPTY; BALL_EQ_EMPTY] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_BALL] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^N->real^N) (cball(vec 0,rho)) = t UNION S` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    SUBST1_TAC(SYM(ASSUME `IMAGE (c:real^N->real^N) (sphere(vec 0,rho)) = S`)) THEN
    REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(IMAGE (c:real^N->real^N) (cball(vec 0,rho)))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_CBALL] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `t INTER S:real^N->bool = {}` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    SUBST1_TAC(SYM(ASSUME `IMAGE (c:real^N->real^N) (sphere(vec 0,rho)) = S`)) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a:real^N) IN ball(vec 0,r) /\ (b:real^N) IN ball(vec 0,r)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `a:real^N = b` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(a:real^N) IN ball(vec 0,rho)` THEN
    UNDISCH_TAC `(b:real^N) IN sphere(vec 0,rho)` THEN
    REWRITE_TAC[IN_BALL_0; IN_SPHERE_0] THEN MESON_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `t SUBSET inside S \/ t SUBSET outside(S:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC SCH1_CONNECTED_SIDE THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC SCH1_CLOPEN_EQ THEN
    EXISTS_TAC `IMAGE (c:real^N->real^N) (cball(vec 0,rho))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ASM SET_TAC[]];
    SUBGOAL_THEN `t = outside(S:real^N->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC SCH1_CLOPEN_EQ THEN
      EXISTS_TAC `IMAGE (c:real^N->real^N) (cball(vec 0,rho))` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `~bounded(outside(S:real^N->bool))` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN EXPAND_TAC "t" THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (c:real^N->real^N) (cball(vec 0,rho))` THEN
    SIMP_TAC[IMAGE_SUBSET; BALL_SUBSET_CBALL] THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_CBALL] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]]);;

(* A homeomorphism of R^2 mapping a chart circle onto a chart circle maps   *)
(* the chart discs onto each other.                                          *)

let SCHZ_PLANAR_DISC_IMAGE = prove
 (`!(P:real^2->real^2) P' (c0:real^2->real^2) c0' r0 rho0
    (c1:real^2->real^2) c1' r1 rho1.
     homeomorphism ((:real^2),(:real^2)) (P,P') /\
     diffeomorphism_on (ball(vec 0,r0)) (IMAGE c0 (ball(vec 0,r0))) c0 c0' /\
     &0 < rho0 /\ rho0 < r0 /\
     diffeomorphism_on (ball(vec 0,r1)) (IMAGE c1 (ball(vec 0,r1))) c1 c1' /\
     &0 < rho1 /\ rho1 < r1 /\
     IMAGE P (IMAGE c0 (sphere(vec 0,rho0))) = IMAGE c1 (sphere(vec 0,rho1))
     ==> IMAGE P (IMAGE c0 (ball(vec 0,rho0))) = IMAGE c1 (ball(vec 0,rho1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c0:real^2->real^2`; `c0':real^2->real^2`; `r0:real`; `rho0:real`]
    SCHZ_CHART_BALL_INSIDE) THEN
  MP_TAC(ISPECL [`c1:real^2->real^2`; `c1':real^2->real^2`; `r1:real`; `rho1:real`]
    SCHZ_CHART_BALL_INSIDE) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`P:real^2->real^2`; `P':real^2->real^2`;
                 `IMAGE (c0:real^2->real^2) (sphere(vec 0,rho0))`] SCH_INSIDE_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

(* The slice maps of a flow with the height law are planar diffeomorphisms.  *)

let SCHZ_SLICE_DIFFEO = prove
 (`!(Psi:real^1->real^3->real^3) a b.
     (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
     (!t x. (Psi t x)$3 = x$3 + drop t) /\
     smooth_map_on (:real^(1,3)finite_sum) (\w. Psi (fstcart w) (sndcart w))
     ==> diffeomorphism_on (:real^2) (:real^2)
           (\p. sch5v_pr(Psi (lift(b - a)) (sch5v_at a p)))
           (\q. sch5v_pr(Psi (lift(a - b)) (sch5v_at b q)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  SUBGOAL_THEN `!c d. smooth_map_on (:real^2)
                  (\p. sch5v_pr((Psi:real^1->real^3->real^3) (lift(c - d)) (sch5v_at d p)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `(\p. sch5v_pr((Psi:real^1->real^3->real^3) (lift(c - d)) (sch5v_at d p))) =
                  sch5v_pr o (\p. Psi (lift((\p:real^2. c - d) p)) (sch5v_at d p))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^3)` THEN REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SCH5V_PR_AT_SMOOTH] THEN
    MATCH_MP_TAC SCH5V_FLOW_COMPOSE_SMOOTH THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SCH5V_PR_AT_SMOOTH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!c d p. sch5v_at c (sch5v_pr((Psi:real^1->real^3->real^3) (lift(c - d))
                          (sch5v_at d p))) = Psi (lift(c - d)) (sch5v_at d p)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM(CONJUNCT1(CONJUNCT2(CONJUNCT2 SCH5V_PR_AT)))] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2 SCH5V_PR_AT); LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC[GSYM LIFT_ADD] THEN
  REWRITE_TAC[REAL_ARITH `(b - a) + (a - b) = &0`; REAL_ARITH `(a - b) + (b - a) = &0`;
              LIFT_NUM] THEN
  ASM_REWRITE_TAC[SCH5V_PR_AT]);;

(* Two functions vanishing at p with the same sign near p: the derivative   *)
(* of the second is >= 0 along a direction where the first increases        *)
(* (Caratheodory along the line p + s v).                                    *)

let SCHZ_LINE_REAL_DERIV = prove
 (`!(f:real^N->real) Df p v.
     ((\x. lift(f x)) has_derivative (\h. lift(Df h))) (at p)
     ==> ((\s. f(p + s % v)) has_real_derivative (Df v)) (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[has_derivative]) THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; has_vector_derivative] THEN
  SUBGOAL_THEN `((\t:real^1. p + drop t % (v:real^N)) has_derivative (\t. drop t % v))
                (at (lift(&0)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t:real^1. p:real^N`; `\t:real^1. vec 0:real^N`;
                   `\t:real^1. drop t % (v:real^N)`; `\t:real^1. drop t % (v:real^N)`;
                   `at (lift(&0))`] HAS_DERIVATIVE_ADD) THEN
    REWRITE_TAC[VECTOR_ADD_LID; HAS_DERIVATIVE_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t:real^1. p + drop t % (v:real^N)`; `\x:real^N. lift((f:real^N->real) x)`;
                 `\t:real^1. drop t % (v:real^N)`; `\h:real^N. lift((Df:real^N->real) h)`;
                 `lift(&0)`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN X_GEN_TAC `t:real^1` THEN
  UNDISCH_TAC `linear(\h. lift((Df:real^N->real) h))` THEN
  DISCH_THEN(MP_TAC o SPECL [`drop t`; `v:real^N`] o CONJUNCT2 o REWRITE_RULE[linear]) THEN
  REWRITE_TAC[]);;

let SCHZ_SAME_SIGN_DERIV = prove
 (`!(f:real^N->real) (g:real^N->real) Df Dg p U v.
     open U /\ p IN U /\
     ((\x. lift(f x)) has_derivative (\h. lift(Df h))) (at p) /\
     ((\x. lift(g x)) has_derivative (\h. lift(Dg h))) (at p) /\
     f p = &0 /\ g p = &0 /\ (!q. q IN U /\ &0 < f q ==> &0 < g q) /\ &0 < Df v
     ==> &0 <= Dg v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real`; `Df:real^N->real`; `p:real^N`; `v:real^N`]
    SCHZ_LINE_REAL_DERIV) THEN
  MP_TAC(ISPECL [`g:real^N->real`; `Dg:real^N->real`; `p:real^N`; `v:real^N`]
    SCHZ_LINE_REAL_DERIV) THEN
  ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CARATHEODORY_ATREAL] THEN
  REWRITE_TAC[REAL_MUL_LZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_SUB_RZERO] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real->real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real->real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c1:real->real`; `&0`] REAL_CONTINUOUS_ATREAL) THEN
  ASM_REWRITE_TAC[REALLIM_ATREAL] THEN DISCH_THEN(MP_TAC o SPEC `(Df:real^N->real) v`) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C1B"))) THEN
  MP_TAC(ISPECL [`c2:real->real`; `&0`] REAL_CONTINUOUS_ATREAL) THEN
  ASM_REWRITE_TAC[REALLIM_ATREAL] THEN DISCH_THEN(MP_TAC o SPEC `--((Dg:real^N->real) v)`) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_NEG_GT0] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C2B"))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def] o check (fun th ->
    can (term_match [] `open(U:real^N->bool)`) (concl th))) THEN
  DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(v:real^N) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d2 / (&2 * (norm(v:real^N) + &1)) /\
                d2 / (&2 * (norm(v:real^N) + &1)) * (norm v + &1) < d2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    SUBGOAL_THEN `d2 / (&2 * (norm(v:real^N) + &1)) * (norm v + &1) = d2 / &2`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < norm(v:real^N) + &1` THEN CONV_TAC REAL_FIELD;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `e2 = d2 / (&2 * (norm(v:real^N) + &1))` THEN
  ABBREV_TAC `s = min (d1 / &2) (min (d3 / &2) e2)` THEN
  SUBGOAL_THEN `&0 < s /\ s < d1 /\ s < d3 /\ s <= e2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s * (norm(v:real^N) + &1) < d2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e2 * (norm(v:real^N) + &1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p + s % v:real^N IN U` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[NORM_ARITH `dist(p + y:real^N,p) = norm y`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `s * (norm(v:real^N) + &1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c1:real->real) s /\ (c2:real->real) s < &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "C1B" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      USE_THEN "C2B" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (f:real^N->real)(p + s % v)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (g:real^N->real)(p + s % v)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_NOT_LT] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
  REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The transport data and the defining function F.  Psi0 is a                *)
(* flow with the height law that preserves S on the band [zA,zB]; ph0 is the *)
(* bottom chart (S: z = m + |u|^2), ph1 the top chart (S: z = M - |u|^2).    *)
(* In the coordinates sig x = ph0'(pr(Psi0 (z0 - x3) x)) / sqrt(z0 - m) of   *)
(* the level z0 the surface is the cylinder |sig| = 1.  The defining function *)
(* F = (1 - lam) |sig|^2 + lam Q interpolates between |sig|^2 and the top    *)
(* normalized radius Q = |ph1'(pr x)|^2 / (M - x3) on [b1,b2].               *)
(* ------------------------------------------------------------------------- *)

let schz_tdata = new_definition
 `schz_tdata (S:real^3->bool) (Psi0:real^1->real^3->real^3) zA zB
             m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 <=>
    (!x. Psi0 (vec 0) x = x) /\ (!x s t. Psi0 t (Psi0 s x) = Psi0 (s + t) x) /\
    (!t x. (Psi0 t x)$3 = x$3 + drop t) /\
    smooth_map_on (:real^(1,3)finite_sum) (\w. Psi0 (fstcart w) (sndcart w)) /\
    (!x t. x IN S /\ zA <= x$3 /\ x$3 <= zB /\ zA <= x$3 + drop t /\ x$3 + drop t <= zB
           ==> Psi0 t x IN S) /\
    m < zA /\ zA < z0 /\ z0 < b1 /\ b1 < b2 /\ b2 < zB /\ zB < M /\
    &0 < r0 /\ diffeomorphism_on (ball(vec 0,r0)) (IMAGE ph0 (ball(vec 0,r0))) ph0 ph0' /\
    z0 - m < r0 pow 2 /\ z0 - m < r0 /\
    (!y. sch5v_pr y IN ball(vec 0,r0) /\ abs(y$3 - m) < r0
         ==> (schz_lift ph0 y IN S <=> y$3 = m + norm(sch5v_pr y) pow 2)) /\
    (!x. x IN S /\ x$3 = z0 ==> x IN schz_cyl ph0 m r0) /\
    &0 < r1 /\ diffeomorphism_on (ball(vec 0,r1)) (IMAGE ph1 (ball(vec 0,r1))) ph1 ph1' /\
    M - b1 < r1 pow 2 /\ M - b1 < r1 /\
    (!y. sch5v_pr y IN ball(vec 0,r1) /\ abs(y$3 - M) < r1
         ==> (schz_lift ph1 y IN S <=> y$3 = M - norm(sch5v_pr y) pow 2)) /\
    (!x. x IN S /\ b1 <= x$3 /\ x$3 <= zB ==> x IN schz_cyl ph1 M r1)`;;

(* A level of S inside an exact chart cylinder is the chart circle.         *)

let SCHZ_CHART_LEVEL = prove
 (`!(S:real^3->bool) (ph:real^2->real^2) ph' r c k z.
     diffeomorphism_on (ball(vec 0,r)) (IMAGE ph (ball(vec 0,r))) ph ph' /\
     (!y. sch5v_pr y IN ball(vec 0,r) /\ abs(y$3 - c) < r
          ==> (schz_lift ph y IN S <=> y$3 = c + k * norm(sch5v_pr y) pow 2)) /\
     (k = &1 \/ k = -- &1) /\
     (!x. x IN S /\ x$3 = z ==> x IN schz_cyl ph c r) /\
     abs(z - c) < r /\ &0 <= k * (z - c) /\ k * (z - c) < r pow 2
     ==> !x. x IN S /\ x$3 = z <=>
             ?w. w IN sphere(vec 0,sqrt(k * (z - c))) /\ x = sch5v_at z (ph w)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "CH")
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CYL") STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `k * k = &1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
      concl th = `k = &1 \/ k = -- &1`)) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(k * (z - c)) < r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^2. norm w = sqrt(k * (z - c)) <=> norm w pow 2 = k * (z - c)`
  (LABEL_TAC "NQ") THENL
   [GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[SQRT_POW_2];
      DISCH_TAC THEN MATCH_MP_TAC(GSYM SQRT_UNIQUE) THEN ASM_REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    USE_THEN "CYL" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(x:real^3) IN S`) (ASSUME `(x:real^3)$3 = z`)))) THEN
    REWRITE_TAC[schz_cyl; IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `sch5v_pr(y:real^3)` THEN
    SUBGOAL_THEN `(y:real^3)$3 = z` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3)$3 = z` THEN ASM_REWRITE_TAC[SCHZ_LIFT_FACTS]; ALL_TAC] THEN
    USE_THEN "CH" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `schz_lift (ph:real^2->real^2) y IN S` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_SPHERE_0] THEN USE_THEN "NQ" (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `(y:real^3)$3 = c + k * norm(sch5v_pr y) pow 2` THEN
      UNDISCH_TAC `(y:real^3)$3 = z` THEN UNDISCH_TAC `k * k = &1` THEN
      CONV_TAC REAL_RING;
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[schz_lift] THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[SCH5V_PR_AT] THEN
    SUBGOAL_THEN `sch5v_at z ((ph:real^2->real^2) w) = schz_lift ph (sch5v_at z w)`
    SUBST1_TAC THENL [REWRITE_TAC[SCHZ_LIFT_FACTS]; ALL_TAC] THEN
    USE_THEN "CH" (MP_TAC o SPEC `sch5v_at z (w:real^2)`) THEN
    REWRITE_TAC[SCH5V_PR_AT] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_BALL_0] THEN
      UNDISCH_TAC `(w:real^2) IN sphere(vec 0,sqrt(k * (z - c)))` THEN
      REWRITE_TAC[IN_SPHERE_0] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `(w:real^2) IN sphere(vec 0,sqrt(k * (z - c)))` THEN
      REWRITE_TAC[IN_SPHERE_0] THEN USE_THEN "NQ" (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `k * k = &1` THEN CONV_TAC REAL_RING]]);;

(* The levels of S at z0 (bottom chart circle) and on [b1,zB] (top chart     *)
(* circle), the slice maps of Psi0, and the disc images.                     *)

let SCHZ_TD_LEVELS = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2
     ==> (!x. x IN S /\ x$3 = z0 <=>
              ?w. w IN sphere(vec 0,sqrt(z0 - m)) /\ x = sch5v_at z0 (ph0 w)) /\
         (!z x. b1 <= z /\ z <= zB
                ==> (x IN S /\ x$3 = z <=>
                     ?w. w IN sphere(vec 0,sqrt(M - z)) /\ x = sch5v_at z (ph1 w)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schz_tdata] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^3->bool`; `ph0:real^2->real^2`; `ph0':real^2->real^2`;
                   `r0:real`; `m:real`; `&1`; `z0:real`] SCHZ_CHART_LEVEL) THEN
    ASM_REWRITE_TAC[REAL_MUL_LID] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                   `r1:real`; `M:real`; `-- &1`; `z:real`] SCHZ_CHART_LEVEL) THEN
    REWRITE_TAC[REAL_ARITH `-- &1 * (z - M) = M - z`; REAL_ARITH `M + -- &1 * n = M - n`] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [X_GEN_TAC `x':real^3` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SIMP_TAC[]]]);;

(* Unfold the schz_tdata assumption (and only it) into its conjuncts.      *)

let SCHZ_TD_TAC : tactic =
  FIRST_ASSUM(fun th ->
    let h,_ = strip_comb(concl th) in
    if is_const h && fst(dest_const h) = "schz_tdata"
    then STRIP_ASSUME_TAC(REWRITE_RULE[schz_tdata] th) else NO_TAC);;

let schz_slice = new_definition
 `schz_slice (Psi:real^1->real^3->real^3) a b (p:real^2) =
    sch5v_pr(Psi (lift(b - a)) (sch5v_at a p))`;;

let SCHZ_SLICE_FACTS = prove
 (`!(Psi:real^1->real^3->real^3) a b.
     (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
     (!t x. (Psi t x)$3 = x$3 + drop t) /\
     smooth_map_on (:real^(1,3)finite_sum) (\w. Psi (fstcart w) (sndcart w))
     ==> diffeomorphism_on (:real^2) (:real^2) (schz_slice Psi a b) (schz_slice Psi b a) /\
         homeomorphism ((:real^2),(:real^2)) (schz_slice Psi a b,schz_slice Psi b a) /\
         (!p. Psi (lift(b - a)) (sch5v_at a p) = sch5v_at b (schz_slice Psi a b p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `a:real`; `b:real`] SCHZ_SLICE_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\p. sch5v_pr((Psi:real^1->real^3->real^3) (lift(b - a)) (sch5v_at a p))) =
                schz_slice Psi a b /\
                (\q. sch5v_pr((Psi:real^1->real^3->real^3) (lift(a - b)) (sch5v_at b q))) =
                schz_slice Psi b a` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; schz_slice]; ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (:real^2) (:real^2) (schz_slice (Psi:real^1->real^3->real^3) a b)
                   (schz_slice Psi b a)` THEN
    REWRITE_TAC[diffeomorphism_on; homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[schz_slice] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT1(CONJUNCT2(CONJUNCT2 SCH5V_PR_AT)))] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[CONJUNCT1(CONJUNCT2 SCH5V_PR_AT); LIFT_DROP] THEN REAL_ARITH_TAC]);;

let SCHZ_TD_SLICE = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 z.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\ zA <= z /\ z <= zB
     ==> !p. p IN IMAGE ph0 (sphere(vec 0,sqrt(z0 - m))) <=>
             sch5v_at z (schz_slice Psi0 z0 z p) IN S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP SCHZ_TD_LEVELS) THEN
  DISCH_THEN(LABEL_TAC "L0") THEN SCHZ_TD_TAC THEN
  MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `z0:real`; `z:real`] SCHZ_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LIFT"))) THEN
  X_GEN_TAC `p:real^2` THEN USE_THEN "LIFT" (fun th -> REWRITE_TAC[GSYM th]) THEN
  EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x t. x IN S /\ a <= x$3 /\ x$3 <= b /\ a <= x$3 + drop t /\
                                x$3 + drop t <= b ==> (Psi0:real^1->real^3->real^3) t x IN S`)
          (concl th))) THEN
    ASM_REWRITE_TAC[SCH5V_PR_AT; LIFT_DROP] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    USE_THEN "L0" (MP_TAC o SPEC `sch5v_at z0 ((ph0:real^2->real^2) w)`) THEN
    REWRITE_TAC[SCH5V_PR_AT] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `w:real^2` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `sch5v_at z0 (p:real^2) IN S` MP_TAC THENL
     [SUBGOAL_THEN `sch5v_at z0 (p:real^2) =
                    (Psi0:real^1->real^3->real^3) (lift(z0 - z))
                      (Psi0 (lift(z - z0)) (sch5v_at z0 p))` SUBST1_TAC THENL
       [REWRITE_TAC[ASSUME `!x s t. (Psi0:real^1->real^3->real^3) t (Psi0 s x) =
                                     Psi0 (s + t) x`] THEN
        REWRITE_TAC[GSYM LIFT_ADD; REAL_ARITH `(z - z0) + (z0 - z) = &0`; LIFT_NUM] THEN
        REWRITE_TAC[ASSUME `!x. (Psi0:real^1->real^3->real^3) (vec 0) x = x`];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x t. x IN S /\ a <= x$3 /\ x$3 <= b /\ a <= x$3 + drop t /\
                                  x$3 + drop t <= b ==> (Psi0:real^1->real^3->real^3) t x IN S`)
            (concl th))) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN
      REWRITE_TAC[ASSUME `!t x. ((Psi0:real^1->real^3->real^3) t x)$3 = x$3 + drop t`;
                  SCH5V_PR_AT; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "L0" (MP_TAC o SPEC `sch5v_at z0 (p:real^2)`) THEN REWRITE_TAC[SCH5V_PR_AT] THEN
    DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:real^2` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SCH5V_PR_AT]]);;

let SCHZ_TD_DISC = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 z.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\ b1 <= z /\ z <= zB
     ==> IMAGE (schz_slice Psi0 z0 z) (IMAGE ph0 (sphere(vec 0,sqrt(z0 - m)))) =
         IMAGE ph1 (sphere(vec 0,sqrt(M - z))) /\
         IMAGE (schz_slice Psi0 z0 z) (IMAGE ph0 (ball(vec 0,sqrt(z0 - m)))) =
         IMAGE ph1 (ball(vec 0,sqrt(M - z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP SCHZ_TD_LEVELS) THEN
  DISCH_THEN(MP_TAC o SPEC `z:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "L1") THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `z:real`] SCHZ_TD_SLICE) THEN
  SCHZ_TD_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "SL") THEN
  MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `z0:real`; `z:real`] SCHZ_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    can (term_match [] `homeomorphism (s,t) (f:real^2->real^2,g)`) (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_UNIV]) THEN
  SUBGOAL_THEN `IMAGE (schz_slice Psi0 z0 z) (IMAGE (ph0:real^2->real^2)
                  (sphere(vec 0,sqrt(z0 - m)))) =
                IMAGE (ph1:real^2->real^2) (sphere(vec 0,sqrt(M - z)))` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `q:real^2` THEN ONCE_REWRITE_TAC[IN_IMAGE] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `p:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      USE_THEN "SL" (fun th -> ASSUME_TAC(EQ_MP (SPEC `p:real^2` th)
        (ASSUME `(p:real^2) IN IMAGE (ph0:real^2->real^2) (sphere(vec 0,sqrt(z0 - m)))`))) THEN
      USE_THEN "L1" (fun th -> MP_TAC(EQ_MP
        (SPEC `sch5v_at z (schz_slice Psi0 z0 z (p:real^2))` th)
        (CONJ (ASSUME `sch5v_at z (schz_slice Psi0 z0 z (p:real^2)) IN S`)
              (ISPECL [`z:real`; `schz_slice Psi0 z0 z (p:real^2)`]
                 (CONJUNCT1(CONJUNCT2 SCH5V_PR_AT)))))) THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `w:real^2` THEN ASM_MESON_TAC[SCH5V_PR_AT];
      DISCH_THEN(X_CHOOSE_THEN `w:real^2` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `sch5v_at z (q:real^2) IN S` ASSUME_TAC THENL
       [USE_THEN "L1" (MP_TAC o SPEC `sch5v_at z (q:real^2)`) THEN
        REWRITE_TAC[SCH5V_PR_AT] THEN DISCH_THEN SUBST1_TAC THEN
        EXISTS_TAC `w:real^2` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `schz_slice Psi0 z z0 (q:real^2)` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "SL" (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `schz_slice Psi0 z0 z (schz_slice Psi0 z z0 (q:real^2)) = q`
        SUBST1_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SCHZ_PLANAR_DISC_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`schz_slice Psi0 z z0`; `ph0':real^2->real^2`; `r0:real`;
                        `ph1':real^2->real^2`; `r1:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < z0 - m /\ &0 < M - z` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POS_LT] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The defining function F of the transport data and its                     *)
(* properties: smooth on its domain, F = 1 exactly on S (in the band), the   *)
(* horizontal gradient is nonzero on S, F = |u|^2 on the bottom chart at z0, *)
(* and F = Q (top normalized radius) above b2.                               *)
(* ------------------------------------------------------------------------- *)

let schz_sig = new_definition
 `schz_sig (Psi0:real^1->real^3->real^3) (ph0':real^2->real^2) z0 m (x:real^3) =
    inv(sqrt(z0 - m)) % ph0'(schz_slice Psi0 (x$3) z0 (sch5v_pr x))`;;

let schz_qtop = new_definition
 `schz_qtop (ph1':real^2->real^2) M (x:real^3) = norm(ph1'(sch5v_pr x)) pow 2 / (M - x$3)`;;

let schz_fd = new_definition
 `schz_fd (Psi0:real^1->real^3->real^3) (ph0':real^2->real^2) z0 m
          (ph1':real^2->real^2) M b1 b2 (x:real^3) =
    (&1 - smooth_step((x$3 - b1) / (b2 - b1))) * norm(schz_sig Psi0 ph0' z0 m x) pow 2 +
    smooth_step((x$3 - b1) / (b2 - b1)) * schz_qtop ph1' M x`;;

let schz_ofd = new_definition
 `schz_ofd (Psi0:real^1->real^3->real^3) (ph0:real^2->real^2) r0 z0
           (ph1:real^2->real^2) r1 M b1 =
    {x:real^3 | schz_slice Psi0 (x$3) z0 (sch5v_pr x) IN IMAGE ph0 (ball(vec 0,r0)) /\
                (b1 <= x$3 ==> sch5v_pr x IN IMAGE ph1 (ball(vec 0,r1)) /\ x$3 < M)}`;;

(* The slice of x down to level z0 is the projection of the flowed point.   *)

let SCHZ_SLICE_POINT = prove
 (`!(Psi:real^1->real^3->real^3) z0 x.
     schz_slice Psi (x$3) z0 (sch5v_pr x) = sch5v_pr(Psi (lift(z0 - x$3)) x)`,
  REWRITE_TAC[schz_slice; SCH5V_PR_AT]);;

let SCHZ_SLICE_POINT_SMOOTH = prove
 (`!(Psi:real^1->real^3->real^3) z0.
     smooth_map_on (:real^(1,3)finite_sum) (\w. Psi (fstcart w) (sndcart w))
     ==> smooth_map_on (:real^3) (\x. schz_slice Psi (x$3) z0 (sch5v_pr x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SCHZ_SLICE_POINT] THEN
  SUBGOAL_THEN `(\x. sch5v_pr((Psi:real^1->real^3->real^3) (lift(z0 - x$3)) x)) =
                sch5v_pr o (\x. Psi (lift((\x:real^3. z0 - x$3) x)) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^3)` THEN REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SCH5V_PR_AT_SMOOTH] THEN
  MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `(:real^3)`; `\x:real^3. z0 - x$3`;
                 `\x:real^3. x`] SCH5V_FLOW_COMPOSE_SMOOTH) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `open(:real^3)` ASSUME_TAC THENL [REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  SCHZ_SMOOTH_TAC);;

let SCHZ_OFD_OPEN = prove
 (`!(Psi0:real^1->real^3->real^3) (ph0:real^2->real^2) ph0' r0 z0 (ph1:real^2->real^2) ph1'
    r1 M b1.
     smooth_map_on (:real^(1,3)finite_sum) (\w. Psi0 (fstcart w) (sndcart w)) /\
     diffeomorphism_on (ball(vec 0,r0)) (IMAGE ph0 (ball(vec 0,r0))) ph0 ph0' /\
     diffeomorphism_on (ball(vec 0,r1)) (IMAGE ph1 (ball(vec 0,r1))) ph1 ph1'
     ==> open(schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))) /\
                open(IMAGE (ph1:real^2->real^2) (ball(vec 0,r1)))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1 =
                {x:real^3 | schz_slice Psi0 (x$3) z0 (sch5v_pr x) IN
                            IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))} INTER
                ({x | x$3 < b1} UNION
                 ({x | sch5v_pr x IN IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))} INTER
                  {x | x$3 < M}))` SUBST1_TAC THENL
   [REWRITE_TAC[schz_ofd; EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM; GSYM REAL_NOT_LE] THEN
    GEN_TAC THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x:real^3. schz_slice Psi0 (x$3) z0 (sch5v_pr x)`; `(:real^3)`;
                   `IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))`] CONTINUOUS_OPEN_PREIMAGE) THEN
    REWRITE_TAC[IN_UNIV; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SCHZ_SLICE_POINT_SMOOTH THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC OPEN_UNION THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN MATCH_MP_TAC OPEN_INTER THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN
    MP_TAC(ISPECL [`sch5v_pr`; `(:real^3)`;
                   `IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))`] CONTINUOUS_OPEN_PREIMAGE) THEN
    REWRITE_TAC[IN_UNIV; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    REWRITE_TAC[SCH5V_PR_AT_SMOOTH]]);;

let SCHZ_SIG_SMOOTH = prove
 (`!(Psi0:real^1->real^3->real^3) (ph0:real^2->real^2) ph0' r0 z0 m.
     smooth_map_on (:real^(1,3)finite_sum) (\w. Psi0 (fstcart w) (sndcart w)) /\
     diffeomorphism_on (ball(vec 0,r0)) (IMAGE ph0 (ball(vec 0,r0))) ph0 ph0'
     ==> open {x:real^3 | schz_slice Psi0 (x$3) z0 (sch5v_pr x) IN IMAGE ph0 (ball(vec 0,r0))} /\
         smooth_map_on {x:real^3 | schz_slice Psi0 (x$3) z0 (sch5v_pr x) IN
                                   IMAGE ph0 (ball(vec 0,r0))}
                       (schz_sig Psi0 ph0' z0 m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  ABBREV_TAC `O0 = {x:real^3 | schz_slice Psi0 (x$3) z0 (sch5v_pr x) IN
                               IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}` THEN
  SUBGOAL_THEN `open(O0:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O0" THEN
    MP_TAC(ISPECL [`\x:real^3. schz_slice Psi0 (x$3) z0 (sch5v_pr x)`; `(:real^3)`;
                   `IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))`] CONTINUOUS_OPEN_PREIMAGE) THEN
    REWRITE_TAC[IN_UNIV; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SCHZ_SLICE_POINT_SMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `schz_sig Psi0 (ph0':real^2->real^2) z0 m =
                (\x. inv(sqrt(z0 - m)) % (ph0' o (\x:real^3. schz_slice Psi0 (x$3) z0 (sch5v_pr x))) x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schz_sig; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "O0" THEN SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SCHZ_SLICE_POINT_SMOOTH THEN
    ASM_REWRITE_TAC[]]);;

let SCHZ_QTOP_SMOOTH = prove
 (`!(ph1:real^2->real^2) ph1' r1 M.
     diffeomorphism_on (ball(vec 0,r1)) (IMAGE ph1 (ball(vec 0,r1))) ph1 ph1'
     ==> open {x:real^3 | sch5v_pr x IN IMAGE ph1 (ball(vec 0,r1)) /\ x$3 < M} /\
         smooth_map_on {x:real^3 | sch5v_pr x IN IMAGE ph1 (ball(vec 0,r1)) /\ x$3 < M}
                       (\x. lift(schz_qtop ph1' M x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  ABBREV_TAC `O1 = {x:real^3 | sch5v_pr x IN IMAGE (ph1:real^2->real^2) (ball(vec 0,r1)) /\
                               x$3 < M}` THEN
  SUBGOAL_THEN `open(O1:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O1" THEN
    REWRITE_TAC[SET_RULE `!P Q. {x:real^3 | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN
    MP_TAC(ISPECL [`sch5v_pr`; `(:real^3)`;
                   `IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))`] CONTINUOUS_OPEN_PREIMAGE) THEN
    REWRITE_TAC[IN_UNIV; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    REWRITE_TAC[SCH5V_PR_AT_SMOOTH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[schz_qtop] THEN
  SUBGOAL_THEN `smooth_map_on O1 (\x:real^3. (ph1':real^2->real^2)(sch5v_pr x))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x:real^3. (ph1':real^2->real^2)(sch5v_pr x)) = ph1' o sch5v_pr`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "O1" THEN SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV; SCH5V_PR_AT_SMOOTH]];
    ALL_TAC] THEN
  SCHZ_SMOOTH_TAC THEN EXPAND_TAC "O1" THEN REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let SCHZ_FD_SMOOTH = prove
 (`!(Psi0:real^1->real^3->real^3) (ph0:real^2->real^2) ph0' r0 z0 m
    (ph1:real^2->real^2) ph1' r1 M b1 b2.
     smooth_map_on (:real^(1,3)finite_sum) (\w. Psi0 (fstcart w) (sndcart w)) /\
     diffeomorphism_on (ball(vec 0,r0)) (IMAGE ph0 (ball(vec 0,r0))) ph0 ph0' /\
     diffeomorphism_on (ball(vec 0,r1)) (IMAGE ph1 (ball(vec 0,r1))) ph1 ph1' /\ b1 < b2
     ==> open(schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1) /\
         smooth_map_on (schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1)
                       (\x. lift(schz_fd Psi0 ph0' z0 m ph1' M b1 b2 x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `ph0:real^2->real^2`; `ph0':real^2->real^2`;
                 `r0:real`; `z0:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `r1:real`; `M:real`; `b1:real`] SCHZ_OFD_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `ph0:real^2->real^2`; `ph0':real^2->real^2`;
                 `r0:real`; `z0:real`; `m:real`] SCHZ_SIG_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ph1:real^2->real^2`; `ph1':real^2->real^2`; `r1:real`; `M:real`]
    SCHZ_QTOP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `O0 = {x:real^3 | schz_slice Psi0 (x$3) z0 (sch5v_pr x) IN
                               IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}` THEN
  ABBREV_TAC `O1 = {x:real^3 | sch5v_pr x IN IMAGE (ph1:real^2->real^2) (ball(vec 0,r1)) /\
                               x$3 < M}` THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[schz_ofd; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^3)$3 < b1` THENL
   [EXISTS_TAC `O0 INTER {y:real^3 | y$3 < b1}` THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_LT; IN_INTER; IN_ELIM_THM] THEN
    CONJ_TAC THENL [EXPAND_TAC "O0" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\y:real^3. lift(norm(schz_sig Psi0 (ph0':real^2->real^2) z0 m y) pow 2)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[schz_fd; LIFT_EQ] THEN
      SUBGOAL_THEN `smooth_step(((y:real^3)$3 - b1) / (b2 - b1)) = &0` SUBST1_TAC THENL
       [MATCH_MP_TAC SMOOTH_STEP_0 THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `open(O0 INTER {y:real^3 | y$3 < b1})` ASSUME_TAC THENL
     [ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on (O0 INTER {y:real^3 | y$3 < b1})
                    (schz_sig Psi0 (ph0':real^2->real^2) z0 m)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O0:real^3->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      ALL_TAC] THEN
    SCHZ_SMOOTH_TAC THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  EXISTS_TAC `O0 INTER O1:real^3->bool` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN
  CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["O0"; "O1"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[REAL_NOT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(O0 INTER O1:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (O0 INTER O1) (schz_sig Psi0 (ph0':real^2->real^2) z0 m) /\
                smooth_map_on (O0 INTER O1) (\x:real^3. lift(schz_qtop ph1' M x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `O0:real^3->bool`; EXISTS_TAC `O1:real^3->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[schz_fd] THEN SCHZ_SMOOTH_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC);;

(* The horizontal gradient of Fd at x is the derivative of the planar       *)
(* restriction p |-> Fd(p,x3) at pr x.                                       *)

let SCHZ_GRAD_PLANAR = prove
 (`!O (Fd:real^3->real) x.
     open O /\ smooth_map_on O (\x. lift(Fd x)) /\ x IN O
     ==> ((\p. lift(Fd(sch5v_at (x$3) p))) has_derivative
          (\h. lift(vector[(schz_grad Fd x)$1; (schz_grad Fd x)$2] dot h)))
         (at (sch5v_pr x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `Fd:real^3->real`; `x:real^3`] SCHZ_GRAD_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\p:real^2. sch5v_at ((x:real^3)$3) p) has_derivative
                 (\h. sch5v_at (&0) h)) (at (sch5v_pr x))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\p:real^2. sch5v_at ((x:real^3)$3) p) =
                  (\p. sch5v_at (&0) p + vector[&0; &0; x$3])` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; sch5v_at; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                  VECTOR_ADD_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ABS_CONV) [GSYM VECTOR_ADD_RID] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; sch5v_at; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p:real^2. sch5v_at ((x:real^3)$3) p`; `\y:real^3. lift((Fd:real^3->real) y)`;
                 `\h:real^2. sch5v_at (&0) h`;
                 `\v:real^3. lift(schz_grad (Fd:real^3->real) x dot v)`;
                 `sch5v_pr(x:real^3)`] DIFF_CHAIN_AT) THEN
  REWRITE_TAC[o_DEF; CONJUNCT1(CONJUNCT2(CONJUNCT2 SCH5V_PR_AT))] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; LIFT_EQ; sch5v_at; DOT_3; DOT_2; VECTOR_3; VECTOR_2] THEN
  REAL_ARITH_TAC);;

(* A nonzero derivative of the planar restriction puts x in schz_oh.        *)

let SCHZ_OH_FROM_PLANAR = prove
 (`!O (Fd:real^3->real) x D h.
     open O /\ smooth_map_on O (\x. lift(Fd x)) /\ x IN O /\
     ((\p. lift(Fd(sch5v_at (x$3) p))) has_derivative (\h. lift(D h))) (at (sch5v_pr x)) /\
     ~(D h = &0)
     ==> x IN schz_oh O Fd`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[schz_oh; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `Fd:real^3->real`; `x:real^3`] SCHZ_GRAD_PLANAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\h:real^2. lift(vector[(schz_grad (Fd:real^3->real) x)$1;
                                         (schz_grad Fd x)$2] dot h)) =
                (\h. lift((D:real^2->real) h))` MP_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\p:real^2. lift((Fd:real^3->real)(sch5v_at ((x:real^3)$3) p))` THEN
    EXISTS_TAC `sch5v_pr(x:real^3)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM; LIFT_EQ] THEN DISCH_THEN(MP_TAC o SPEC `h:real^2`) THEN
  REWRITE_TAC[DOT_2; VECTOR_2] THEN
  UNDISCH_TAC `~((D:real^2->real) h = &0)` THEN
  REWRITE_TAC[REAL_SOS_EQ_0] THEN
  MAP_EVERY ASM_CASES_TAC [`(schz_grad (Fd:real^3->real) x)$1 = &0`;
                           `(schz_grad (Fd:real^3->real) x)$2 = &0`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Membership of chart points in chart balls and spheres.                    *)

let SCHZ_CHART_MEMBER = prove
 (`!(c:real^2->real^2) c' r rho w.
     diffeomorphism_on (ball(vec 0,r)) (IMAGE c (ball(vec 0,r))) c c' /\
     w IN ball(vec 0,r) /\ rho < r
     ==> (c w IN IMAGE c (ball(vec 0,rho)) <=> norm w < rho) /\
         (c w IN IMAGE c (sphere(vec 0,rho)) <=> norm w = rho)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^2. x IN ball(vec 0,r) ==> (c':real^2->real^2)(c x) = x`
  (LABEL_TAC "CC") THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!w':real^2. norm w' <= rho /\ (c:real^2->real^2) w' = c w ==> w' = w`
  (LABEL_TAC "INJ") THENL
   [X_GEN_TAC `w':real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w':real^2) IN ball(vec 0,r)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "CC" (MP_TAC o C MATCH_MP (ASSUME `(w':real^2) IN ball(vec 0,r)`)) THEN
    USE_THEN "CC" (MP_TAC o C MATCH_MP (ASSUME `(w:real^2) IN ball(vec 0,r)`)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_BALL_0; IN_SPHERE_0] THEN CONJ_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w':real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `w':real^2 = w` SUBST_ALL_TAC THENL
     [USE_THEN "INJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN EXISTS_TAC `w:real^2` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `w':real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `w':real^2 = w` SUBST_ALL_TAC THENL
     [USE_THEN "INJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN EXISTS_TAC `w:real^2` THEN ASM_REWRITE_TAC[]]);;

(* A convex combination of two numbers on the same side of 1 equals 1 only  *)
(* when both do.                                                             *)

let SCHZ_CONVEX_EQ1 = prove
 (`!l a b. &0 <= l /\ l <= &1 /\ (a < &1 <=> b < &1) /\ (a = &1 <=> b = &1)
           ==> ((&1 - l) * a + l * b = &1 <=> a = &1)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `a = &1` THENL
   [SUBGOAL_THEN `b = &1` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `a = &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `~(a = &1)`] THEN
  SUBGOAL_THEN `~(b = &1)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `a < &1` THENL
   [SUBGOAL_THEN `b < &1` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&1 - l) * (&1 - a) + l * (&1 - b)` MP_TAC THENL
     [ASM_CASES_TAC `l = &0` THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC] THEN
      ALL_TAC;
      REAL_ARITH_TAC];
    SUBGOAL_THEN `&1 < a /\ &1 < b` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_ARITH `~(x < &1) /\ ~(x = &1) ==> &1 < x`]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&1 - l) * (a - &1) + l * (b - &1)` MP_TAC THENL
     [ASM_CASES_TAC `l = &0` THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC]]);;

(* In the transport data, |sig|^2 = 1 exactly on S, |sig| < 1 on the image  *)
(* of the bottom chart disc.                                                 *)

let SCHZ_SIG_SURF = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 y.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\
     zA <= y$3 /\ y$3 <= zB /\
     schz_slice Psi0 (y$3) z0 (sch5v_pr y) IN IMAGE ph0 (ball(vec 0,r0))
     ==> (y IN S <=> norm(schz_sig Psi0 ph0' z0 m y) pow 2 = &1) /\
         (norm(schz_sig Psi0 ph0' z0 m y) pow 2 < &1 <=>
          schz_slice Psi0 (y$3) z0 (sch5v_pr y) IN IMAGE ph0 (ball(vec 0,sqrt(z0 - m)))) /\
         (norm(schz_sig Psi0 ph0' z0 m y) pow 2 = &1 <=>
          schz_slice Psi0 (y$3) z0 (sch5v_pr y) IN IMAGE ph0 (sphere(vec 0,sqrt(z0 - m))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `(y:real^3)$3`] SCHZ_TD_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "SL") THEN
  SCHZ_TD_TAC THEN
  MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `(y:real^3)$3`; `z0:real`]
    SCHZ_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "INV1") (CONJUNCTS_THEN2 (LABEL_TAC "INV2")
     STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `?w. w IN ball(vec 0,r0) /\
                    schz_slice Psi0 ((y:real^3)$3) z0 (sch5v_pr y) = (ph0:real^2->real^2) w`
    (X_CHOOSE_THEN `w:real^2` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "QW"))) THENL
   [UNDISCH_TAC `schz_slice Psi0 ((y:real^3)$3) z0 (sch5v_pr y) IN
                 IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))` THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "QW" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `&0 < z0 - m /\ sqrt(z0 - m) < r0 /\ &0 < sqrt(z0 - m)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ph0':real^2->real^2)((ph0:real^2->real^2) w) = w` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(
      GEN_REWRITE_RULE I [diffeomorphism_on]
      (ASSUME `diffeomorphism_on (ball(vec 0,r0)) (IMAGE (ph0:real^2->real^2) (ball(vec 0,r0)))
                 ph0 ph0'`))))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(schz_sig Psi0 (ph0':real^2->real^2) z0 m y) pow 2 =
                norm(w:real^2) pow 2 / (z0 - m)` SUBST1_TAC THENL
   [REWRITE_TAC[schz_sig] THEN USE_THEN "QW" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_ABS_INV; REAL_POW_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[real_div; REAL_MUL_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ph0:real^2->real^2`; `ph0':real^2->real^2`; `r0:real`; `sqrt(z0 - m)`;
                 `w:real^2`] SCHZ_CHART_MEMBER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `!t. &0 <= t ==> (t pow 2 / (z0 - m) = &1 <=> t = sqrt(z0 - m)) /\
                               (t pow 2 / (z0 - m) < &1 <=> t < sqrt(z0 - m))`
  (MP_TAC o SPEC `norm(w:real^2)`) THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
    MP_TAC(SPECL [`t:real`; `sqrt(z0 - m)`] REAL_EQ_SQUARE_ABS) THEN
    MP_TAC(SPECL [`t:real`; `sqrt(z0 - m)`] REAL_LT_SQUARE_ABS) THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_ARITH `&0 <= x ==> abs x = x`;
                 REAL_ARITH `&0 < x ==> abs x = x`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "SL" (MP_TAC o SPEC `(ph0:real^2->real^2) w`) THEN
  SUBGOAL_THEN `schz_slice Psi0 z0 ((y:real^3)$3) ((ph0:real^2->real^2) w) = sch5v_pr y`
    SUBST1_TAC THENL
   [USE_THEN "QW" (SUBST1_TAC o SYM) THEN USE_THEN "INV1" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 SCH5V_PR_AT))] THEN
  MP_TAC(ISPECL [`ph0:real^2->real^2`; `ph0':real^2->real^2`; `r0:real`; `sqrt(z0 - m)`;
                 `w:real^2`] SCHZ_CHART_MEMBER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC TAUT);;

let SCHZ_IMAGE_BIJ = prove
 (`!(f:A->B) g s y. (!x. g(f x) = x) /\ (!y. f(g y) = y)
                    ==> (y IN IMAGE f s <=> g y IN s)`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

(* On the top band |sig|^2 and Q lie on the same side of 1.                 *)

let SCHZ_TQ_SIGNS = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 y.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\
     b1 <= y$3 /\ y$3 <= zB /\
     schz_slice Psi0 (y$3) z0 (sch5v_pr y) IN IMAGE ph0 (ball(vec 0,r0)) /\
     sch5v_pr y IN IMAGE ph1 (ball(vec 0,r1))
     ==> (norm(schz_sig Psi0 ph0' z0 m y) pow 2 < &1 <=> schz_qtop ph1' M y < &1) /\
         (norm(schz_sig Psi0 ph0' z0 m y) pow 2 = &1 <=> schz_qtop ph1' M y = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `zA <= (y:real^3)$3` ASSUME_TAC THENL
   [SCHZ_TD_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `y:real^3`] SCHZ_SIG_SURF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `(y:real^3)$3`] SCHZ_TD_DISC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "DS") (LABEL_TAC "DB")) THEN
  SCHZ_TD_TAC THEN
  MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `z0:real`; `(y:real^3)$3`]
    SCHZ_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!A. schz_slice Psi0 ((y:real^3)$3) z0 (sch5v_pr y) IN A <=>
                    sch5v_pr y IN IMAGE (schz_slice Psi0 z0 (y$3)) A`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCHZ_IMAGE_BIJ THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "DS" SUBST1_TAC THEN USE_THEN "DB" SUBST1_TAC THEN
  SUBGOAL_THEN `?w1. w1 IN ball(vec 0,r1) /\ sch5v_pr(y:real^3) = (ph1:real^2->real^2) w1`
    (X_CHOOSE_THEN `w1:real^2` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `sch5v_pr(y:real^3) IN IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))` THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < M - (y:real^3)$3 /\ sqrt(M - y$3) < r1 /\ &0 < sqrt(M - y$3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ph1:real^2->real^2`; `ph1':real^2->real^2`; `r1:real`;
                 `sqrt(M - (y:real^3)$3)`; `w1:real^2`] SCHZ_CHART_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[schz_qtop] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(ph1':real^2->real^2)((ph1:real^2->real^2) w1) = w1` SUBST1_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_EQ_LDIV_EQ; REAL_MUL_LID] THEN
  SUBGOAL_THEN `M - (y:real^3)$3 = sqrt(M - y$3) pow 2` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(ISPEC `w1:real^2` NORM_POS_LE) THEN
  ABBREV_TAC `t = norm(w1:real^2)` THEN ABBREV_TAC `s = sqrt(M - (y:real^3)$3)` THEN
  SUBGOAL_THEN `sqrt(s pow 2) = s` SUBST1_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN UNDISCH_TAC `&0 < s` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ARITH_TAC]);;

(* F = 1 exactly on S in the band.                                           *)

let SCHZ_FD_SURF = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 y.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\
     y IN schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1 /\ zA <= y$3 /\ y$3 <= zB
     ==> (schz_fd Psi0 ph0' z0 m ph1' M b1 b2 y = &1 <=> y IN S)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schz_ofd; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `y:real^3`] SCHZ_SIG_SURF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[schz_fd] THEN
  ABBREV_TAC `l = smooth_step(((y:real^3)$3 - b1) / (b2 - b1))` THEN
  SUBGOAL_THEN `&0 <= l /\ l <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[SMOOTH_STEP_BOUNDS]; ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^3)$3 < b1` THENL
   [SUBGOAL_THEN `l = &0` SUBST1_TAC THENL
     [EXPAND_TAC "l" THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN SCHZ_TD_TAC THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID; REAL_MUL_LZERO; REAL_ADD_RID]];
    ALL_TAC] THEN
  MATCH_MP_TAC SCHZ_CONVEX_EQ1 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ q ==> p /\ q`) THEN
  MATCH_MP_TAC SCHZ_TQ_SIGNS THEN
  MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `zA:real`; `zB:real`; `r0:real`;
                        `ph0:real^2->real^2`; `r1:real`; `ph1:real^2->real^2`; `b1:real`;
                        `b2:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* The derivative of the composite with a chart that turns f into c |v|^2. *)

let SCHZ_NORMSQ_COMPOSE = prove
 (`!(f:real^2->real) Df (Phi:real^2->real^2) DPhi u c U.
     open U /\ u IN U /\ (Phi has_derivative DPhi) (at u) /\
     ((\p. lift(f p)) has_derivative (\h. lift(Df h))) (at (Phi u)) /\
     (!v. v IN U ==> f(Phi v) = c * norm v pow 2)
     ==> Df(DPhi u) = &2 * c * (u dot u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Phi:real^2->real^2`; `\p:real^2. lift((f:real^2->real) p)`;
                 `DPhi:real^2->real^2`; `\h:real^2. lift((Df:real^2->real) h)`;
                 `u:real^2`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o check (fun th ->
    can (term_match [] `open(U:real^2->bool)`) (concl th))) THEN
  DISCH_THEN(MP_TAC o SPEC `u:real^2`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `((\v:real^2. lift((f:real^2->real)((Phi:real^2->real^2) v))) has_derivative
                 (\h. c % (&2 % lift(u dot h)))) (at u)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\v:real^2. c % lift(norm v pow 2)` THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\h. lift((Df:real^2->real)((DPhi:real^2->real^2) h))) =
                (\h. c % (&2 % lift(u dot h)))` MP_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\v:real^2. lift((f:real^2->real)((Phi:real^2->real^2) v))` THEN
    EXISTS_TAC `u:real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `u:real^2`) THEN
  REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC);;

(* F on the bottom chart at the level z0, and on the top band.             *)

let SCHZ_FD_LEVEL0 = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 v.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\
     norm(sqrt(z0 - m) % v) < r0
     ==> schz_sig Psi0 ph0' z0 m (sch5v_at z0 (ph0(sqrt(z0 - m) % v))) = v /\
         schz_fd Psi0 ph0' z0 m ph1' M b1 b2 (sch5v_at z0 (ph0(sqrt(z0 - m) % v))) =
         norm v pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SCHZ_TD_TAC THEN
  SUBGOAL_THEN `schz_sig Psi0 (ph0':real^2->real^2) z0 m
                  (sch5v_at z0 ((ph0:real^2->real^2)(sqrt(z0 - m) % v))) = v`
  ASSUME_TAC THENL
   [REWRITE_TAC[schz_sig; schz_slice; SCH5V_PR_AT; REAL_SUB_REFL; LIFT_NUM] THEN
    ASM_REWRITE_TAC[SCH5V_PR_AT] THEN
    SUBGOAL_THEN `(ph0':real^2->real^2)((ph0:real^2->real^2)(sqrt(z0 - m) % v)) =
                  sqrt(z0 - m) % v` SUBST1_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(
        GEN_REWRITE_RULE I [diffeomorphism_on]
        (ASSUME `diffeomorphism_on (ball(vec 0,r0)) (IMAGE (ph0:real^2->real^2) (ball(vec 0,r0)))
                   ph0 ph0'`))))))) THEN
      ASM_REWRITE_TAC[IN_BALL_0];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `&0 < sqrt(z0 - m)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[schz_fd; SCH5V_PR_AT] THEN
  SUBGOAL_THEN `smooth_step((z0 - b1) / (b2 - b1)) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_0 THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let SCHZ_FD_TOP = prove
 (`!Psi0 (ph0':real^2->real^2) z0 m (ph1':real^2->real^2) M b1 b2 y.
     b1 < b2 /\ b2 <= y$3
     ==> schz_fd Psi0 ph0' z0 m ph1' M b1 b2 y = schz_qtop ph1' M y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[schz_fd] THEN
  SUBGOAL_THEN `smooth_step(((y:real^3)$3 - b1) / (b2 - b1)) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* The planar restrictions of |sig|^2 and of Q have derivative 2 along a     *)
(* suitable direction at points of S.                                        *)

let SCHZ_T_PLANAR = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 y.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\
     y IN S /\ zA <= y$3 /\ y$3 <= zB
     ==> ?DT h0. ((\p. lift(norm(schz_sig Psi0 ph0' z0 m (sch5v_at (y$3) p)) pow 2))
                  has_derivative (\h. lift(DT h))) (at (sch5v_pr y)) /\
                 DT h0 = &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `z = (y:real^3)$3` THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `z:real`] SCHZ_TD_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "SL") THEN
  SCHZ_TD_TAC THEN
  MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `z:real`; `z0:real`] SCHZ_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [diffeomorphism_on]
    (ASSUME `diffeomorphism_on (ball(vec 0,r0)) (IMAGE (ph0:real^2->real^2) (ball(vec 0,r0)))
               ph0 ph0'`)) THEN
  SUBGOAL_THEN `&0 < z0 - m /\ sqrt(z0 - m) < r0 /\ &0 < sqrt(z0 - m)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = schz_slice Psi0 z z0 (sch5v_pr(y:real^3))` THEN
  SUBGOAL_THEN `(q:real^2) IN IMAGE (ph0:real^2->real^2) (sphere(vec 0,sqrt(z0 - m)))`
  ASSUME_TAC THENL
   [USE_THEN "SL" (fun th -> REWRITE_TAC[th]) THEN EXPAND_TAC "q" THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "z" THEN ASM_REWRITE_TAC[SCH5V_PR_AT];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w. w IN sphere(vec 0,sqrt(z0 - m)) /\ q = (ph0:real^2->real^2) w`
    (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `(q:real^2) IN IMAGE (ph0:real^2->real^2) (sphere(vec 0,sqrt(z0 - m)))` THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^2) IN ball(vec 0,r0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^2) IN sphere(vec 0,sqrt(z0 - m))` THEN
    REWRITE_TAC[IN_SPHERE_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u = inv(sqrt(z0 - m)) % (w:real^2)` THEN
  ABBREV_TAC `Phi = \v:real^2. schz_slice Psi0 z0 z ((ph0:real^2->real^2)(sqrt(z0 - m) % v))` THEN
  ABBREV_TAC `U = {v:real^2 | norm(sqrt(z0 - m) % v) < r0}` THEN
  SUBGOAL_THEN `open(U:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    SUBGOAL_THEN `{v:real^2 | sqrt(z0 - m) * norm v < r0} = ball(vec 0,r0 / sqrt(z0 - m))`
      SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL_0] THEN GEN_TAC THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
      REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(z0 - m) % (u:real^2) = w` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^2) IN U` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `(w:real^2) IN ball(vec 0,r0)` THEN REWRITE_TAC[IN_BALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Phi:real^2->real^2) u = sch5v_pr(y:real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(q:real^2) = (ph0:real^2->real^2) w` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "q" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^2. v IN U
                 ==> norm(schz_sig Psi0 (ph0':real^2->real^2) z0 m
                           (sch5v_at z ((Phi:real^2->real^2) v))) pow 2 = &1 * norm v pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^2` THEN EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    EXPAND_TAC "Phi" THEN REWRITE_TAC[schz_sig; SCH5V_PR_AT; REAL_MUL_LID] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(ph0':real^2->real^2)((ph0:real^2->real^2)(sqrt(z0 - m) % v)) =
                  sqrt(z0 - m) % v` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  (* Derivatives of Phi at u and of the planar restriction at pr y. *)
  SUBGOAL_THEN `smooth_map_on U (Phi:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN
    SUBGOAL_THEN `(\v:real^2. schz_slice Psi0 z0 z ((ph0:real^2->real^2)(sqrt(z0 - m) % v))) =
                  schz_slice Psi0 z0 z o (ph0 o (\v. sqrt(z0 - m) % v))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `ball(vec 0:real^2,r0)` THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "U" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_BALL_0] THEN
      SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]];
    ALL_TAC] THEN
  ABBREV_TAC `fT = \p:real^2. norm(schz_sig Psi0 (ph0':real^2->real^2) z0 m (sch5v_at z p)) pow 2` THEN
  ABBREV_TAC `OT = {p:real^2 | schz_slice Psi0 z z0 p IN IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}` THEN
  SUBGOAL_THEN `open(OT:real^2->bool) /\ sch5v_pr(y:real^3) IN OT /\
                smooth_map_on OT (\p. lift((fT:real^2->real) p))` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `ph0:real^2->real^2`; `ph0':real^2->real^2`;
                   `r0:real`; `z0:real`; `m:real`] SCHZ_SIG_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `OT = {p:real^2 | sch5v_at z p IN
                     {x:real^3 | schz_slice Psi0 (x$3) z0 (sch5v_pr x) IN
                                 IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}}` SUBST1_TAC THENL
     [EXPAND_TAC "OT" THEN REWRITE_TAC[IN_ELIM_THM; SCH5V_PR_AT]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`sch5v_at z`; `(:real^2)`;
                     `{x:real^3 | schz_slice Psi0 (x$3) z0 (sch5v_pr x) IN
                                  IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}`]
        CONTINUOUS_OPEN_PREIMAGE) THEN
      REWRITE_TAC[IN_UNIV; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[SCH5V_PR_AT_SMOOTH];
      REWRITE_TAC[IN_ELIM_THM; SCH5V_PR_AT] THEN EXPAND_TAC "z" THEN
      REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 SCH5V_PR_AT))] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "z" THEN
      UNDISCH_TAC `(q:real^2) = (ph0:real^2->real^2) w` THEN EXPAND_TAC "q" THEN
      EXPAND_TAC "z" THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "fT" THEN
      SUBGOAL_THEN `(\p:real^2. lift(norm(schz_sig Psi0 (ph0':real^2->real^2) z0 m
                                     (sch5v_at z p)) pow 2)) =
                    (\x. lift(norm(schz_sig Psi0 ph0' z0 m x) pow 2)) o sch5v_at z`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `{x:real^3 | schz_slice Psi0 (x$3) z0 (sch5v_pr x) IN
                              IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`sch5v_at z`; `(:real^2)`;
                       `{x:real^3 | schz_slice Psi0 (x$3) z0 (sch5v_pr x) IN
                                    IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}`]
          CONTINUOUS_OPEN_PREIMAGE) THEN
        REWRITE_TAC[IN_UNIV; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[SCH5V_PR_AT_SMOOTH];
        SET_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        REWRITE_TAC[SUBSET_UNIV; SCH5V_PR_AT_SMOOTH];
        SUBGOAL_THEN `open {x:real^3 | schz_slice Psi0 (x$3) z0 (sch5v_pr x) IN
                                       IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}`
          ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SCHZ_SMOOTH_TAC THEN ASM_REWRITE_TAC[ETA_AX]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`OT:real^2->bool`; `\p:real^2. lift((fT:real^2->real) p)`]
    SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `sch5v_pr(y:real^3)`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `Phi:real^2->real^2`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `u:real^2`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `DT = \h. drop(frechet_derivative (\p:real^2. lift((fT:real^2->real) p))
                             (at (sch5v_pr(y:real^3))) h)` THEN
  SUBGOAL_THEN `((\p:real^2. lift((fT:real^2->real) p)) has_derivative
                 (\h. lift((DT:real^2->real) h))) (at (sch5v_pr(y:real^3)))` ASSUME_TAC THENL
   [EXPAND_TAC "DT" THEN ASM_REWRITE_TAC[LIFT_DROP; ETA_AX]; ALL_TAC] THEN
  EXISTS_TAC `DT:real^2->real` THEN
  EXISTS_TAC `frechet_derivative (Phi:real^2->real^2) (at u) u` THEN
  CONJ_TAC THENL [UNDISCH_TAC `((\p:real^2. lift((fT:real^2->real) p)) has_derivative
                 (\h. lift((DT:real^2->real) h))) (at (sch5v_pr(y:real^3)))` THEN
                  EXPAND_TAC "fT" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`fT:real^2->real`; `DT:real^2->real`; `Phi:real^2->real^2`;
                 `frechet_derivative (Phi:real^2->real^2) (at u)`; `u:real^2`; `&1`;
                 `U:real^2->bool`] SCHZ_NORMSQ_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN EXPAND_TAC "fT" THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM NORM_POW_2] THEN
  SUBGOAL_THEN `norm(u:real^2) = &1` SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    UNDISCH_TAC `(w:real^2) IN sphere(vec 0,sqrt(z0 - m))` THEN
    REWRITE_TAC[IN_SPHERE_0] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    REAL_ARITH_TAC]);;

let SCHZ_Q_PLANAR = prove
 (`!(ph1:real^2->real^2) ph1' r1 M z p.
     diffeomorphism_on (ball(vec 0,r1)) (IMAGE ph1 (ball(vec 0,r1))) ph1 ph1' /\
     z < M /\ sqrt(M - z) < r1 /\ p IN IMAGE ph1 (sphere(vec 0,sqrt(M - z)))
     ==> ?DQ h1. ((\q. lift(norm(ph1' q) pow 2 / (M - z))) has_derivative
                  (\h. lift(DQ h))) (at p) /\
                 DQ h1 = &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `&0 < M - z /\ &0 < sqrt(M - z)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w. w IN sphere(vec 0,sqrt(M - z)) /\ (ph1:real^2->real^2) w = p`
    (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `(p:real^2) IN IMAGE (ph1:real^2->real^2) (sphere(vec 0,sqrt(M - z)))` THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `u = inv(sqrt(M - z)) % (w:real^2)` THEN
  ABBREV_TAC `Phi = \v:real^2. (ph1:real^2->real^2)(sqrt(M - z) % v)` THEN
  ABBREV_TAC `U = {v:real^2 | norm(sqrt(M - z) % v) < r1}` THEN
  SUBGOAL_THEN `open(U:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    SUBGOAL_THEN `{v:real^2 | sqrt(M - z) * norm v < r1} = ball(vec 0,r1 / sqrt(M - z))`
      SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL_0] THEN GEN_TAC THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
      REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(M - z) % (u:real^2) = w` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^2) IN U /\ (Phi:real^2->real^2) u = p` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "Phi"] THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `(w:real^2) IN sphere(vec 0,sqrt(M - z))` THEN
    REWRITE_TAC[IN_SPHERE_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (Phi:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN
    SUBGOAL_THEN `(\v:real^2. (ph1:real^2->real^2)(sqrt(M - z) % v)) =
                  ph1 o (\v. sqrt(M - z) % v)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `ball(vec 0:real^2,r1)` THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "U" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_BALL_0] THEN
      SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]];
    ALL_TAC] THEN
  ABBREV_TAC `fQ = \q:real^2. norm((ph1':real^2->real^2) q) pow 2 / (M - z)` THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE (ph1:real^2->real^2) (ball(vec 0,r1)))
                  (\q. lift((fQ:real^2->real) q))` ASSUME_TAC THENL
   [EXPAND_TAC "fQ" THEN
    SUBGOAL_THEN `open(IMAGE (ph1:real^2->real^2) (ball(vec 0,r1)))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SCHZ_SMOOTH_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN GEN_TAC THEN DISCH_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^2) IN IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `(ph1:real^2->real^2) w = p`)) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `(w:real^2) IN sphere(vec 0,sqrt(M - z))` THEN
    REWRITE_TAC[IN_SPHERE_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))`;
                 `\q:real^2. lift((fQ:real^2->real) q)`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `p:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `Phi:real^2->real^2`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `u:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  ABBREV_TAC `DQ = \h. drop(frechet_derivative (\q:real^2. lift((fQ:real^2->real) q))
                             (at (p:real^2)) h)` THEN
  SUBGOAL_THEN `((\q:real^2. lift((fQ:real^2->real) q)) has_derivative
                 (\h. lift((DQ:real^2->real) h))) (at (p:real^2))` ASSUME_TAC THENL
   [EXPAND_TAC "DQ" THEN ASM_REWRITE_TAC[LIFT_DROP; ETA_AX]; ALL_TAC] THEN
  EXISTS_TAC `DQ:real^2->real` THEN
  EXISTS_TAC `frechet_derivative (Phi:real^2->real^2) (at u) u` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `((\q:real^2. lift((fQ:real^2->real) q)) has_derivative
                 (\h. lift((DQ:real^2->real) h))) (at (p:real^2))` THEN
    EXPAND_TAC "fQ" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`fQ:real^2->real`; `DQ:real^2->real`; `Phi:real^2->real^2`;
                 `frechet_derivative (Phi:real^2->real^2) (at u)`; `u:real^2`; `&1`;
                 `U:real^2->bool`] SCHZ_NORMSQ_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^2` THEN EXPAND_TAC "U" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["fQ"; "Phi"] THEN
    SUBGOAL_THEN `(ph1':real^2->real^2)((ph1:real^2->real^2)(sqrt(M - z) % v)) =
                  sqrt(M - z) % v` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL; REAL_POW_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `&0 < M - z` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM NORM_POW_2] THEN
  SUBGOAL_THEN `norm(u:real^2) = &1` SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    UNDISCH_TAC `(w:real^2) IN sphere(vec 0,sqrt(M - z))` THEN
    REWRITE_TAC[IN_SPHERE_0] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    REAL_ARITH_TAC]);;

(* Small derivative helpers for planar functions.                            *)

let SCHZ_PLANAR_COMB = prove
 (`!(fT:real^2->real) fQ DT DQ l (p:real^2).
     ((\q. lift(fT q)) has_derivative (\h. lift(DT h))) (at p) /\
     ((\q. lift(fQ q)) has_derivative (\h. lift(DQ h))) (at p)
     ==> ((\q. lift((&1 - l) * fT q + l * fQ q)) has_derivative
          (\h. lift((&1 - l) * DT h + l * DQ h))) (at p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN ASM_REWRITE_TAC[]);;

let SCHZ_HAS_DERIV_SUB_CONST = prove
 (`!(f:real^2->real) Df c (p:real^2).
     ((\q. lift(f q)) has_derivative (\h. lift(Df h))) (at p)
     ==> ((\q. lift(f q - c)) has_derivative (\h. lift(Df h))) (at p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\h:real^2. lift((Df:real^2->real) h)) = (\h. lift(Df h) - vec 0)`
  SUBST1_TAC THENL [REWRITE_TAC[VECTOR_SUB_RZERO]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST]);;

(* F restricted to a horizontal plane.                                       *)

let SCHZ_FD_PLANAR_EQ = prove
 (`!Psi0 (ph0':real^2->real^2) z0 m (ph1':real^2->real^2) M b1 b2 z p.
     schz_fd Psi0 ph0' z0 m ph1' M b1 b2 (sch5v_at z p) =
     (&1 - smooth_step((z - b1) / (b2 - b1))) *
     norm(schz_sig Psi0 ph0' z0 m (sch5v_at z p)) pow 2 +
     smooth_step((z - b1) / (b2 - b1)) * (norm(ph1' p) pow 2 / (M - z))`,
  REWRITE_TAC[schz_fd; schz_qtop; SCH5V_PR_AT]);;

(* Points of S in the top band lie on a top chart circle.                    *)

let SCHZ_TOP_CIRCLE = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 y.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\
     y IN S /\ b1 <= y$3 /\ y$3 <= zB
     ==> y$3 < M /\ sqrt(M - y$3) < r1 /\
         sch5v_pr y IN IMAGE ph1 (sphere(vec 0,sqrt(M - y$3)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `zA <= (y:real^3)$3` ASSUME_TAC THENL
   [SCHZ_TD_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `(y:real^3)$3`] SCHZ_TD_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "SL") THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `(y:real^3)$3`] SCHZ_TD_DISC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "DS" o CONJUNCT1) THEN
  SCHZ_TD_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `(y:real^3)$3`; `z0:real`]
    SCHZ_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "INV1") (CONJUNCTS_THEN2 (LABEL_TAC "INV2")
     STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `sch5v_pr(y:real^3) =
                schz_slice Psi0 z0 (y$3) (schz_slice Psi0 (y$3) z0 (sch5v_pr y))`
  SUBST1_TAC THENL [USE_THEN "INV1" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  USE_THEN "DS" (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN
  USE_THEN "SL" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "INV1" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 SCH5V_PR_AT))] THEN ASM_REWRITE_TAC[]);;

(* Points of S in the band lie in the domain of F.                           *)

let SCHZ_FD_DOMAIN = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 y.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\
     y IN S /\ zA <= y$3 /\ y$3 <= zB
     ==> schz_slice Psi0 (y$3) z0 (sch5v_pr y) IN IMAGE ph0 (sphere(vec 0,sqrt(z0 - m))) /\
         y IN schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `(y:real^3)$3`] SCHZ_TD_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "SL") THEN
  SUBGOAL_THEN `schz_slice Psi0 ((y:real^3)$3) z0 (sch5v_pr y) IN
                IMAGE (ph0:real^2->real^2) (sphere(vec 0,sqrt(z0 - m)))` ASSUME_TAC THENL
   [USE_THEN "SL" (fun th -> REWRITE_TAC[th]) THEN SCHZ_TD_TAC THEN
    MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `(y:real^3)$3`; `z0:real`]
      SCHZ_SLICE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SCH5V_PR_AT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[schz_ofd; IN_ELIM_THM] THEN CONJ_TAC THENL
   [UNDISCH_TAC `schz_slice Psi0 ((y:real^3)$3) z0 (sch5v_pr y) IN
                 IMAGE (ph0:real^2->real^2) (sphere(vec 0,sqrt(z0 - m)))` THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^2) IN IMAGE (f:real^2->real^2) s ==>
                                           x IN IMAGE f t`) THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_BALL_0] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    SCHZ_TD_TAC THEN MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                   `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                   `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                   `b1:real`; `b2:real`; `y:real^3`] SCHZ_TOP_CIRCLE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sch5v_pr(y:real^3) IN
                 IMAGE (ph1:real^2->real^2) (sphere(vec 0,sqrt(M - y$3)))` THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^2) IN IMAGE (f:real^2->real^2) s ==>
                                           x IN IMAGE f t`) THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_BALL_0] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* On the top band, the derivative of Q along a direction in which |sig|^2  *)
(* increases is nonnegative (same sign of |sig|^2 - 1 and Q - 1).           *)

let SCHZ_DQ_NONNEG = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 y
    DT DQ (v:real^2).
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\
     y IN S /\ b1 <= y$3 /\ y$3 <= zB /\
     y IN schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1 /\
     ((\p. lift(norm(schz_sig Psi0 ph0' z0 m (sch5v_at (y$3) p)) pow 2)) has_derivative
      (\h. lift(DT h))) (at (sch5v_pr y)) /\
     ((\q. lift(norm(ph1' q) pow 2 / (M - y$3))) has_derivative (\h. lift(DQ h)))
      (at (sch5v_pr y)) /\
     &0 < DT v
     ==> &0 <= DQ v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schz_ofd; IN_ELIM_THM] THEN STRIP_TAC THEN
  UNDISCH_TAC `b1 <= (y:real^3)$3
               ==> sch5v_pr y IN IMAGE (ph1:real^2->real^2) (ball(vec 0,r1)) /\ y$3 < M` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `zA <= (y:real^3)$3` ASSUME_TAC THENL
   [SCHZ_TD_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(schz_sig Psi0 (ph0':real^2->real^2) z0 m y) pow 2 = &1 /\
                norm((ph1':real^2->real^2)(sch5v_pr y)) pow 2 / (M - (y:real^3)$3) = &1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                   `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                   `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                   `b1:real`; `b2:real`; `y:real^3`] SCHZ_SIG_SURF) THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                   `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                   `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                   `b1:real`; `b2:real`; `y:real^3`] SCHZ_TQ_SIGNS) THEN
    ASM_REWRITE_TAC[schz_qtop] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  ABBREV_TAC `U = {q:real^2 | schz_slice Psi0 ((y:real^3)$3) z0 q IN
                              IMAGE (ph0:real^2->real^2) (ball(vec 0,r0)) /\
                              q IN IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))}` THEN
  SUBGOAL_THEN `open(U:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN
    SUBGOAL_THEN `{q:real^2 | schz_slice Psi0 ((y:real^3)$3) z0 q IN
                              IMAGE (ph0:real^2->real^2) (ball(vec 0,r0)) /\
                              q IN IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))} =
                  {q | q IN (:real^2) /\
                       schz_slice Psi0 (y$3) z0 q IN IMAGE ph0 (ball(vec 0,r0))} INTER
                  IMAGE ph1 (ball(vec 0,r1))` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNIV]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN SCHZ_TD_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `(y:real^3)$3`; `z0:real`]
          SCHZ_SLICE_FACTS) THEN
        ASM_REWRITE_TAC[ETA_AX] THEN SIMP_TAC[diffeomorphism_on];
        MP_TAC(ASSUME `diffeomorphism_on (ball(vec 0,r0))
                         (IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))) ph0 ph0'`) THEN
        SIMP_TAC[diffeomorphism_on]];
      MP_TAC(ASSUME `diffeomorphism_on (ball(vec 0,r1))
                       (IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))) ph1 ph1'`) THEN
      SIMP_TAC[diffeomorphism_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5v_pr(y:real^3) IN U` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((\p. lift(norm(schz_sig Psi0 (ph0':real^2->real^2) z0 m
                                  (sch5v_at ((y:real^3)$3) p)) pow 2 - &1)) has_derivative
                 (\h. lift((DT:real^2->real) h))) (at (sch5v_pr y))` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHZ_HAS_DERIV_SUB_CONST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((\q. lift(norm((ph1':real^2->real^2) q) pow 2 / (M - (y:real^3)$3) - &1))
                 has_derivative (\h. lift((DQ:real^2->real) h))) (at (sch5v_pr y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCHZ_HAS_DERIV_SUB_CONST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN U /\
                    &0 < norm(schz_sig Psi0 (ph0':real^2->real^2) z0 m
                                (sch5v_at ((y:real^3)$3) q)) pow 2 - &1
                    ==> &0 < norm((ph1':real^2->real^2) q) pow 2 / (M - y$3) - &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:real^2` THEN EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                   `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                   `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                   `b1:real`; `b2:real`; `sch5v_at ((y:real^3)$3) q`] SCHZ_TQ_SIGNS) THEN
    ASM_REWRITE_TAC[SCH5V_PR_AT; schz_qtop] THEN
    UNDISCH_TAC `&0 < norm(schz_sig Psi0 (ph0':real^2->real^2) z0 m
                             (sch5v_at ((y:real^3)$3) q)) pow 2 - &1` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p:real^2. norm(schz_sig Psi0 (ph0':real^2->real^2) z0 m
                                  (sch5v_at ((y:real^3)$3) p)) pow 2 - &1`;
                 `\q:real^2. norm((ph1':real^2->real^2) q) pow 2 / (M - (y:real^3)$3) - &1`;
                 `DT:real^2->real`; `DQ:real^2->real`; `sch5v_pr(y:real^3)`; `U:real^2->bool`;
                 `v:real^2`] SCHZ_SAME_SIGN_DERIV) THEN
  BETA_TAC THEN REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 SCH5V_PR_AT))] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL]);;

(* The planar restriction of F has a nonzero derivative at points of S.      *)

let SCHZ_FD_PLANAR_DERIV = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 y.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\
     y IN S /\ zA <= y$3 /\ y$3 <= zB
     ==> ?D h. ((\p. lift(schz_fd Psi0 ph0' z0 m ph1' M b1 b2 (sch5v_at (y$3) p)))
                has_derivative (\h. lift(D h))) (at (sch5v_pr y)) /\
               ~(D h = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `y:real^3`] SCHZ_T_PLANAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `DT:real^2->real` (X_CHOOSE_THEN `h0:real^2` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[SCHZ_FD_PLANAR_EQ] THEN
  ABBREV_TAC `l = smooth_step(((y:real^3)$3 - b1) / (b2 - b1))` THEN
  SUBGOAL_THEN `&0 <= l /\ l <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[SMOOTH_STEP_BOUNDS]; ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^3)$3 < b1` THENL
   [SUBGOAL_THEN `l = &0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "l" THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN SCHZ_TD_TAC THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    MAP_EVERY EXISTS_TAC [`DT:real^2->real`; `h0:real^2`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `b1 <= (y:real^3)$3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `y:real^3`] SCHZ_TOP_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ph1:real^2->real^2`; `ph1':real^2->real^2`; `r1:real`; `M:real`;
                 `(y:real^3)$3`; `sch5v_pr(y:real^3)`] SCHZ_Q_PLANAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SCHZ_TD_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `DQ:real^2->real` (X_CHOOSE_THEN `h1:real^2` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\h:real^2. (&1 - l) * (DT:real^2->real) h + l * (DQ:real^2->real) h` THEN
  REWRITE_TAC[] THEN
  ASM_CASES_TAC `l = &1` THENL
   [EXISTS_TAC `h1:real^2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCHZ_PLANAR_COMB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `h0:real^2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SCHZ_PLANAR_COMB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `y:real^3`] SCHZ_FD_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `y:real^3`; `DT:real^2->real`; `DQ:real^2->real`;
                 `h0:real^2`] SCHZ_DQ_NONNEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= l * (DQ:real^2->real) h0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 <= l * (DQ:real^2->real) h0` THEN UNDISCH_TAC `l <= &1` THEN
  UNDISCH_TAC `~(l = &1)` THEN REAL_ARITH_TAC);;

(* The horizontal gradient of F is nonzero at the points of S in the band.  *)

let SCHZ_FD_OH = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 y.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\
     y IN S /\ zA <= y$3 /\ y$3 <= zB
     ==> y IN schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1 /\
         y IN schz_oh (schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1)
                      (schz_fd Psi0 ph0' z0 m ph1' M b1 b2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `y:real^3`] SCHZ_FD_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `y:real^3`] SCHZ_FD_PLANAR_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^2->real` (X_CHOOSE_THEN `h:real^2` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC SCHZ_OH_FROM_PLANAR THEN
  MAP_EVERY EXISTS_TAC [`D:real^2->real`; `h:real^2`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `ph0:real^2->real^2`; `ph0':real^2->real^2`;
                 `r0:real`; `z0:real`; `m:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `r1:real`; `M:real`; `b1:real`; `b2:real`] SCHZ_FD_SMOOTH) THEN
  ANTS_TAC THENL [SCHZ_TD_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ------------------------------------------------------------------------- *)
(* The new vertical flow Psi of V = e3 + chi hfield(F), with                 *)
(* chi = 1 near the band of S.  Psi preserves S on the band (SCHZ_BAND with *)
(* rho = F) and the level sets of F near the bottom chart circle at z0      *)
(* (tube lemma plus SCHZ_FD_FIRST_INTEGRAL).                                *)
(* ------------------------------------------------------------------------- *)

(* Points near the unit circle stay in an open set along a compact time    *)
(* interval when the circle does.                                            *)

let SCHZ_TUBE = prove
 (`!(Phi:real^(1,2)finite_sum->real^3) G0 U Tm.
     open G0 /\ Phi continuous_on G0 /\ open U /\
     (!u w. &0 <= u /\ u <= Tm /\ norm w = &1
            ==> pastecart (lift u) w IN G0 /\ Phi(pastecart (lift u) w) IN U)
     ==> ?del. &0 < del /\
               !u w. &0 <= u /\ u <= Tm /\ abs(norm w - &1) < del
                     ==> pastecart (lift u) w IN G0 /\ Phi(pastecart (lift u) w) IN U`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H")))) THEN
  ABBREV_TAC `G = {p:real^(1,2)finite_sum | p IN G0 /\
                                            (Phi:real^(1,2)finite_sum->real^3) p IN U}` THEN
  SUBGOAL_THEN `open(G:real^(1,2)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K = interval[vec 0:real^1,lift Tm] PCROSS sphere(vec 0:real^2,&1)` THEN
  SUBGOAL_THEN `compact(K:real^(1,2)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC COMPACT_PCROSS THEN
    REWRITE_TAC[COMPACT_INTERVAL; COMPACT_SPHERE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^(1,2)finite_sum->bool) SUBSET G` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN EXPAND_TAC "G" THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                IN_SPHERE_0; DROP_VEC; LIFT_DROP; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `w:real^2`] THEN STRIP_TAC THEN
    USE_THEN "H" (MP_TAC o SPECL [`drop t`; `w:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LIFT_DROP]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real^(1,2)finite_sum->bool`; `G:real^(1,2)finite_sum->bool`]
    SCH5V_COMPACT_NBHD_IN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  EXISTS_TAC `min d (&1)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `w:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (lift u) (w:real^2) IN G` MP_TAC THENL
   [ALL_TAC; EXPAND_TAC "G" THEN REWRITE_TAC[IN_ELIM_THM]] THEN
  SUBGOAL_THEN `&0 < norm(w:real^2)` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(norm(w:real^2) - &1) < min d (&1)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "D" MATCH_MP_TAC THEN
  EXISTS_TAC `pastecart (lift u) (inv(norm w) % w:real^2)` THEN CONJ_TAC THENL
   [EXPAND_TAC "K" THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; IN_SPHERE_0; DROP_VEC; LIFT_DROP;
                NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  REWRITE_TAC[DIST_PASTECART_CANCEL; dist;
              VECTOR_ARITH `a % w - w:real^N = (a - &1) % w`; NORM_MUL] THEN
  SUBGOAL_THEN `abs(inv(norm(w:real^2)) - &1) * norm w = abs(&1 - norm w)` SUBST1_TAC THENL
   [SUBGOAL_THEN `abs(inv(norm(w:real^2)) - &1) * norm w = abs((inv(norm w) - &1) * norm w)`
    SUBST1_TAC THENL [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM]; ALL_TAC] THEN
    AP_TERM_TAC THEN UNDISCH_TAC `&0 < norm(w:real^2)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  UNDISCH_TAC `abs(norm(w:real^2) - &1) < min d (&1)` THEN REAL_ARITH_TAC);;

(* Continuity in time of a jointly smooth flow.                              *)

let SCHZ_FLOW_TIME_CONTINUOUS = prove
 (`!(Psi:real^1->real^3->real^3) x.
     smooth_map_on (:real^(1,3)finite_sum) (\w. Psi (fstcart w) (sndcart w))
     ==> (\t. Psi t x) continuous_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t. (Psi:real^1->real^3->real^3) t x) =
                (\w. Psi (fstcart w) (sndcart w)) o (\t:real^1. pastecart t x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^(1,3)finite_sum)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]]);;

(* The field: a cutoff of the horizontal correction of F.                    *)

let SCHZ_NEW_FIELD = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 zA' zB'.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\ compact S /\
     zA < zA' /\ zA' < z0 /\ b2 < zB' /\ zB' < zB
     ==> ?V B d.
           smooth_map_on (:real^3) V /\ (!x. norm(V x) <= B) /\ (!x. (V x)$3 = &1) /\
           &0 < d /\
           (!y x. y IN S /\ zA' <= y$3 /\ y$3 <= zB' /\ dist(y,x) < d
                  ==> x IN schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1 /\ zA < x$3 /\ x$3 < zB /\
                      schz_grad (schz_fd Psi0 ph0' z0 m ph1' M b1 b2) x dot V x = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `ph0:real^2->real^2`; `ph0':real^2->real^2`;
                 `r0:real`; `z0:real`; `m:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `r1:real`; `M:real`; `b1:real`; `b2:real`] SCHZ_FD_SMOOTH) THEN
  ANTS_TAC THENL [SCHZ_TD_TAC THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `C = {x:real^3 | x IN S /\ zA' <= x$3 /\ x$3 <= zB'}` THEN
  SUBGOAL_THEN `compact(C:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    SUBGOAL_THEN `{x:real^3 | x IN S /\ zA' <= x$3 /\ x$3 <= zB'} =
                  S INTER {x:real^3 | zA' <= x$3} INTER {x:real^3 | x$3 <= zB'}`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE];
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE]];
    ALL_TAC] THEN
  ABBREV_TAC `W = schz_oh (schz_ofd Psi0 (ph0:real^2->real^2) r0 z0 (ph1:real^2->real^2) r1 M b1)
                          (schz_fd Psi0 (ph0':real^2->real^2) z0 m (ph1':real^2->real^2) M b1 b2)
                  INTER {x:real^3 | zA < x$3} INTER {x:real^3 | x$3 < zB}` THEN
  SUBGOAL_THEN `open(W:real^3->bool) /\ C SUBSET W /\
                (!x:real^3. x IN W
                   ==> x IN schz_oh (schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1)
                                    (schz_fd Psi0 ph0' z0 m ph1' M b1 b2) /\
                       x IN schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1 /\ zA < x$3 /\ x$3 < zB)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
       [MATCH_MP_TAC SCHZ_OH_OPEN THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT];
          REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT]]];
      EXPAND_TAC "C" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                     `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`;
                     `z0:real`; `M:real`; `r1:real`; `ph1:real^2->real^2`;
                     `ph1':real^2->real^2`; `b1:real`; `b2:real`; `x:real^3`] SCHZ_FD_OH) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; schz_oh] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real^3->bool`; `W:real^3->bool`; `&1`] SCH5V_CUTOFF) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `chi:real^3->real`
    (X_CHOOSE_THEN `L:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`schz_ofd Psi0 (ph0:real^2->real^2) r0 z0 (ph1:real^2->real^2) r1 M b1`;
                 `schz_fd Psi0 (ph0':real^2->real^2) z0 m (ph1':real^2->real^2) M b1 b2`;
                 `chi:real^3->real`; `L:real^3->bool`] SCHZ_FIELD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(L:real^3->bool) SUBSET W` THEN
    UNDISCH_TAC `!x:real^3. x IN W
                   ==> x IN schz_oh (schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1)
                                    (schz_fd Psi0 ph0' z0 m ph1' M b1 b2) /\
                       x IN schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1 /\ zA < x$3 /\ x$3 < zB` THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^3. basis 3 + chi x % schz_hfield (schz_fd Psi0 (ph0':real^2->real^2) z0 m
                                                  (ph1':real^2->real^2) M b1 b2) x`;
    `B:real`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `x:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(chi:real^3->real) x = &1 /\ (x:real^3) IN W` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!y x. y IN (C:real^3->bool) /\ dist(y,x) < d
                                ==> (chi:real^3->real) x = &1 /\ x IN W`) (concl th))) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `!x:real^3. x IN W
                 ==> x IN schz_oh (schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1)
                                  (schz_fd Psi0 ph0' z0 m ph1' M b1 b2) /\
                     x IN schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1 /\ zA < x$3 /\ x$3 < zB` THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
    can (term_match [] `!x:real^3. x IN schz_oh O Fd /\ (chi:real^3->real) x = &1
                                   ==> schz_grad Fd x dot (basis 3 + chi x % schz_hfield Fd x) =
                                       &0`) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Continuity of the flow-out map (t,w) |-> Psi t (sch5v_at a (ph0(c w))).   *)

let SCHZ_PHI_CONT = prove
 (`!(Psi:real^1->real^3->real^3) (ph0:real^2->real^2) ph0' r0 a c.
     smooth_map_on (:real^(1,3)finite_sum) (\w. Psi (fstcart w) (sndcart w)) /\
     diffeomorphism_on (ball(vec 0,r0)) (IMAGE ph0 (ball(vec 0,r0))) ph0 ph0'
     ==> open {p:real^(1,2)finite_sum | norm(c % sndcart p) < r0} /\
         (\p. Psi (fstcart p) (sch5v_at a (ph0(c % sndcart p)))) continuous_on
         {p:real^(1,2)finite_sum | norm(c % sndcart p) < r0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear (\p:real^(1,2)finite_sum. c % sndcart p)` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LINEAR_SNDCART]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `{p:real^(1,2)finite_sum | norm(c % sndcart p) < r0} =
                  {p | p IN (:real^(1,2)finite_sum) /\
                       (\p. c % sndcart p) p IN ball(vec 0:real^2,r0)}` SUBST1_TAC THENL
     [REWRITE_TAC[IN_UNIV; IN_BALL_0]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_UNIV; OPEN_BALL; LINEAR_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\p:real^(1,2)finite_sum. (Psi:real^1->real^3->real^3) (fstcart p)
                                (sch5v_at a ((ph0:real^2->real^2)(c % sndcart p)))) =
    (\w. Psi (fstcart w) (sndcart w)) o
    (\p. pastecart (fstcart p) (sch5v_at a (ph0(c % sndcart p))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\p:real^(1,2)finite_sum. sch5v_at a ((ph0:real^2->real^2)(c % sndcart p))) =
      sch5v_at a o ph0 o (\p. c % sndcart p)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,r0)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
          UNDISCH_TAC `diffeomorphism_on (ball(vec 0,r0))
                         (IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))) ph0 ph0'` THEN
          SIMP_TAC[diffeomorphism_on];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_BALL_0] THEN SIMP_TAC[]]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV; SCH5V_PR_AT_SMOOTH]];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(1,3)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[]]);;

(* The new flow: S-invariance on the band and level invariance of F near   *)
(* the bottom chart circle at z0.                                            *)

let SCHZ_NEW_FLOW = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 zA' zB'.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\ compact S /\
     zA < zA' /\ zA' < z0 /\ b2 < zB' /\ zB' < zB
     ==> ?Psi:real^1->real^3->real^3.
           (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
           (!t x. (Psi t x)$3 = x$3 + drop t) /\
           smooth_map_on (:real^(1,3)finite_sum) (\w. Psi (fstcart w) (sndcart w)) /\
           (!t. diffeomorphism_on (:real^3) (:real^3) (Psi t) (Psi (--t))) /\
           (!x t. x IN S /\ zA' <= x$3 /\ x$3 <= zB' /\
                  zA' <= x$3 + drop t /\ x$3 + drop t <= zB'
                  ==> Psi t x IN S) /\
           (?kap. &0 < kap /\
                  !w y. abs(norm w - &1) < kap /\ z0 <= y /\ y <= zB'
                        ==> norm(sqrt(z0 - m) % w) < r0 /\
                            Psi (lift(y - z0)) (sch5v_at z0 (ph0(sqrt(z0 - m) % w))) IN
                              schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1 /\
                            schz_fd Psi0 ph0' z0 m ph1' M b1 b2
                              (Psi (lift(y - z0)) (sch5v_at z0 (ph0(sqrt(z0 - m) % w)))) =
                            norm w pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `zA':real`; `zB':real`] SCHZ_NEW_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->real^3` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NB")))))))) THEN
  MP_TAC(ISPECL [`V:real^3->real^3`; `B:real`] SCH5V_BOUNDED_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `V:real^3->real^3` SCH5V_FLOW_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `V:real^3->real^3` SCH5V_FLOW_HEIGHT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:real^3->real^3`; `B:real`] SCH5V_FLOW_DISPLACEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `ph0:real^2->real^2`; `ph0':real^2->real^2`;
                 `r0:real`; `z0:real`; `m:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `r1:real`; `M:real`; `b1:real`; `b2:real`] SCHZ_FD_SMOOTH) THEN
  ANTS_TAC THENL [SCHZ_TD_TAC THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `C = {x:real^3 | x IN S /\ zA' <= x$3 /\ x$3 <= zB'}` THEN
  SUBGOAL_THEN `compact(C:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    SUBGOAL_THEN `{x:real^3 | x IN S /\ zA' <= x$3 /\ x$3 <= zB'} =
                  S INTER {x:real^3 | zA' <= x$3} INTER {x:real^3 | x$3 <= zB'}`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE];
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE]];
    ALL_TAC] THEN
  (* the tube of radius d around C *)
  SUBGOAL_THEN `!x:real^3. (?y. y IN C /\ dist(y,x) < d)
                 ==> x IN schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1 /\ zA < x$3 /\ x$3 < zB /\
                     schz_grad (schz_fd Psi0 ph0' z0 m ph1' M b1 b2) x dot V x = &0`
  (LABEL_TAC "TB") THENL
   [X_GEN_TAC `x:real^3` THEN EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "NB" MATCH_MP_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* F is a first integral along trajectories in the tube *)
  SUBGOAL_THEN `!x t. (!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
                          ==> ?y. y IN C /\ dist(y,ode_vf_flow V (:real^3) u x) < d)
                      ==> schz_fd Psi0 (ph0':real^2->real^2) z0 m (ph1':real^2->real^2) M b1 b2
                            (ode_vf_flow V (:real^3) t x) =
                          schz_fd Psi0 ph0' z0 m ph1' M b1 b2 x`
  (LABEL_TAC "FI") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`schz_ofd Psi0 (ph0:real^2->real^2) r0 z0 (ph1:real^2->real^2) r1 M b1`;
                   `schz_fd Psi0 (ph0':real^2->real^2) z0 m (ph1':real^2->real^2) M b1 b2`;
                   `V:real^3->real^3`; `{x:real^3 | ?y. y IN C /\ dist(y,x) < d}`;
                   `x:real^3`; `t:real^1`] SCHZ_FD_FIRST_INTEGRAL) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SCH5V_OPEN_NBHD; IN_ELIM_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_THEN(fun th -> USE_THEN "TB" (MP_TAC o C MATCH_MP th)) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^3` THEN
      DISCH_THEN(fun th -> USE_THEN "TB" (MP_TAC o C MATCH_MP th)) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* invariance of the band C of S *)
  SUBGOAL_THEN `!x. (\t. ode_vf_flow V (:real^3) t x) continuous_on (:real^1)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SCHZ_FLOW_TIME_CONTINUOUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. (?y. y IN C /\ dist(y,x) < d)
                 ==> (x IN S <=> schz_fd Psi0 ph0' z0 m ph1' M b1 b2 x = &1)` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(fun th -> USE_THEN "TB" (MP_TAC o C MATCH_MP th)) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                   `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                   `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                   `b1:real`; `b2:real`; `x:real^3`] SCHZ_FD_SURF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(C:real^3->bool) /\ C SUBSET S /\
                (!x:real^3. x IN C ==> zA' <= x$3 /\ x$3 <= zB') /\
                (?e. &0 < e /\ !p q. p IN C /\ q IN S /\ zA' <= q$3 /\ q$3 <= zB' /\
                                     dist(p,q) < e ==> q IN C)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[] THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x t. x IN C /\ zA' <= x$3 + drop t /\ x$3 + drop t <= zB'
                      ==> ode_vf_flow V (:real^3) t x IN C` (LABEL_TAC "INV") THENL
   [MP_TAC(ISPECL [`ode_vf_flow V (:real^3)`;
                   `schz_fd Psi0 (ph0':real^2->real^2) z0 m (ph1':real^2->real^2) M b1 b2`;
                   `S:real^3->bool`; `C:real^3->bool`; `B:real`; `d / &2`; `C:real^3->bool`;
                   `zA':real`; `zB':real`] SCHZ_BAND) THEN
    SUBGOAL_THEN `&2 * d / &2 = d` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_HALF; SUBSET_REFL] THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* level invariance near the bottom chart circle *)
  MP_TAC(ISPECL [`ode_vf_flow V (:real^3)`; `ph0:real^2->real^2`; `ph0':real^2->real^2`;
                 `r0:real`; `z0:real`; `sqrt(z0 - m)`] SCHZ_PHI_CONT) THEN
  ANTS_TAC THENL [SCHZ_TD_TAC THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!w:real^2. norm w = &1 ==> norm(sqrt(z0 - m) % w) < r0 /\
                  sch5v_at z0 ((ph0:real^2->real^2)(sqrt(z0 - m) % w)) IN C`
  (LABEL_TAC "XC") THENL
   [X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN SCHZ_TD_TAC THEN
    SUBGOAL_THEN `norm(sqrt(z0 - m) % w:real^2) = sqrt(z0 - m)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN MATCH_MP_TAC SQRT_POS_LE THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(z0 - m) < r0` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM; SCH5V_PR_AT] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `sch5v_at z0 ((ph0:real^2->real^2)(sqrt(z0 - m) % w)) =
                  schz_lift ph0 (sch5v_at z0 (sqrt(z0 - m) % w))` SUBST1_TAC THENL
     [REWRITE_TAC[SCHZ_LIFT_FACTS]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sch5v_at z0 (sqrt(z0 - m) % w:real^2)` o check (fun th ->
      can (term_match [] `!y. sch5v_pr y IN ball(vec 0,r0) /\ abs(y$3 - m) < r0
                              ==> (schz_lift (ph0:real^2->real^2) y IN S <=>
                                   y$3 = m + norm(sch5v_pr y) pow 2)`) (concl th))) THEN
    REWRITE_TAC[SCH5V_PR_AT; IN_BALL_0] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(z0 - m) pow 2 = z0 - m` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\p:real^(1,2)finite_sum. ode_vf_flow V (:real^3) (fstcart p)
                                (sch5v_at z0 ((ph0:real^2->real^2)(sqrt(z0 - m) % sndcart p)))`;
    `{p:real^(1,2)finite_sum | norm(sqrt(z0 - m) % sndcart p) < r0}`;
    `{x:real^3 | ?y. y IN C /\ dist(y,x) < d}`; `zB' - z0`] SCHZ_TUBE) THEN
  ASM_REWRITE_TAC[SCH5V_OPEN_NBHD; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `w:real^2`] THEN STRIP_TAC THEN
    USE_THEN "XC" (MP_TAC o C MATCH_MP (ASSUME `norm(w:real^2) = &1`)) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `ode_vf_flow V (:real^3) (lift u)
                  (sch5v_at z0 ((ph0:real^2->real^2)(sqrt(z0 - m) % w)))` THEN
    REWRITE_TAC[DIST_REFL] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "INV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[SCH5V_PR_AT; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kap:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TU"))) THEN
  EXISTS_TAC `ode_vf_flow V (:real^3)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real^1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `ode_vf_flow V (:real^3) t x IN C` MP_TAC THENL
     [USE_THEN "INV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      EXPAND_TAC "C" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  EXISTS_TAC `kap:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`w:real^2`; `y:real`] THEN STRIP_TAC THEN
  USE_THEN "TU" (MP_TAC o SPECL [`y - z0`; `w:real^2`]) THEN
  ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> USE_THEN "TB" (MP_TAC o C MATCH_MP th)))] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `w:real^2`] SCHZ_FD_LEVEL0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  USE_THEN "FI" MATCH_MP_TAC THEN
  X_GEN_TAC `u:real^1` THEN REWRITE_TAC[IN_UNION; IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
  DISCH_TAC THEN
  USE_THEN "TU" (MP_TAC o SPECL [`drop u`; `w:real^2`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[LIFT_DROP] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The data of the new flow (schz_ndata) and the top holonomy                *)
(* K: it preserves the normalized radius near the boundary circle, and maps *)
(* the discs of radius near the boundary radius onto themselves (2D circle  *)
(* onto lemma plus SCHZ_PLANAR_DISC_IMAGE).                                  *)
(* ------------------------------------------------------------------------- *)

let schz_ndata = new_definition
 `schz_ndata (S:real^3->bool) (Psi0:real^1->real^3->real^3) zA zB m r0
             (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
             (Psi:real^1->real^3->real^3) zA' zB' kap <=>
    schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\
    zA < zA' /\ zA' < z0 /\ b2 < zB' /\ zB' < zB /\
    (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
    (!t x. (Psi t x)$3 = x$3 + drop t) /\
    smooth_map_on (:real^(1,3)finite_sum) (\w. Psi (fstcart w) (sndcart w)) /\
    (!t. diffeomorphism_on (:real^3) (:real^3) (Psi t) (Psi (--t))) /\
    (!x t. x IN S /\ zA' <= x$3 /\ x$3 <= zB' /\
           zA' <= x$3 + drop t /\ x$3 + drop t <= zB'
           ==> Psi t x IN S) /\
    &0 < kap /\ kap <= &1 / &2 /\
    (!w y. abs(norm w - &1) < kap /\ z0 <= y /\ y <= zB'
           ==> norm(sqrt(z0 - m) % w) < r0 /\
               Psi (lift(y - z0)) (sch5v_at z0 (ph0(sqrt(z0 - m) % w))) IN
                 schz_ofd Psi0 ph0 r0 z0 ph1 r1 M b1 /\
               schz_fd Psi0 ph0' z0 m ph1' M b1 b2
                 (Psi (lift(y - z0)) (sch5v_at z0 (ph0(sqrt(z0 - m) % w)))) =
               norm w pow 2)`;;

(* Unfold the schz_ndata assumption (and the schz_tdata inside it).         *)

let SCHZ_ND_TAC : tactic =
  FIRST_ASSUM(fun th ->
    let h,_ = strip_comb(concl th) in
    if is_const h && fst(dest_const h) = "schz_ndata"
    then STRIP_ASSUME_TAC(REWRITE_RULE[schz_ndata] th) else NO_TAC) THEN
  SCHZ_TD_TAC;;

let SCHZ_NDATA_EXISTS = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2 zA' zB'.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\ compact S /\
     zA < zA' /\ zA' < z0 /\ b2 < zB' /\ zB' < zB
     ==> ?Psi kap. schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2
                              Psi zA' zB' kap`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `zA':real`; `zB':real`] SCHZ_NEW_FLOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Psi:real^1->real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `kap:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LI")))))))))) THEN
  MAP_EVERY EXISTS_TAC [`Psi:real^1->real^3->real^3`; `min kap (&1 / &2)`] THEN
  ASM_REWRITE_TAC[schz_ndata] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:real^2`; `y:real`] THEN STRIP_TAC THEN
  USE_THEN "LI" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* An injective continuous self-map of the unit circle is onto.            *)

let SCHZ_CIRCLE_ONTO = prove
 (`!k:real^2->real^2.
     k continuous_on sphere(vec 0,&1) /\
     IMAGE k (sphere(vec 0,&1)) SUBSET sphere(vec 0,&1) /\
     (!x y. x IN sphere(vec 0,&1) /\ y IN sphere(vec 0,&1) /\ k x = k y ==> x = y)
     ==> IMAGE k (sphere(vec 0,&1)) = sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`; `q:real^2`; `(:real^1)`]
    HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE) THEN
  ASM_REWRITE_TAC[REAL_LT_01; AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_1; DIMINDEX_2] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[homeomorphic; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^1` (X_CHOOSE_THEN `h':real^1->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`(h:real^2->real^1) o (k:real^2->real^2)`; `vec 0:real^2`; `&1`]
    NO_EMBEDDING_SPHERE_LOWDIM) THEN
  REWRITE_TAC[DIMINDEX_1; DIMINDEX_2; REAL_LT_01; o_THM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:real^2. x IN sphere(vec 0,&1) ==> (k:real^2->real^2) x IN
                           sphere(vec 0,&1) DELETE q` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[IN_DELETE] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `sphere(vec 0:real^2,&1) DELETE q` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x y. x IN sphere(vec 0:real^2,&1) /\ y IN sphere(vec 0,&1) /\
                                (k:real^2->real^2) x = k y ==> x = y`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* A homeomorphism of the plane that maps a chart circle into a chart circle *)
(* maps it onto that circle.                                                 *)

let SCHZ_CHART_CIRCLE_ONTO = prove
 (`!(P:real^2->real^2) P' (c0:real^2->real^2) c0' r0 rho0 (c1:real^2->real^2) c1' r1 rho1.
     homeomorphism ((:real^2),(:real^2)) (P,P') /\
     diffeomorphism_on (ball(vec 0,r0)) (IMAGE c0 (ball(vec 0,r0))) c0 c0' /\
     &0 < rho0 /\ rho0 < r0 /\
     diffeomorphism_on (ball(vec 0,r1)) (IMAGE c1 (ball(vec 0,r1))) c1 c1' /\
     &0 < rho1 /\ rho1 < r1 /\
     IMAGE P (IMAGE c0 (sphere(vec 0,rho0))) SUBSET IMAGE c1 (sphere(vec 0,rho1))
     ==> IMAGE P (IMAGE c0 (sphere(vec 0,rho0))) = IMAGE c1 (sphere(vec 0,rho1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "D0")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "D1")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SUB")))))))) THEN
  USE_THEN "D0" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  USE_THEN "D1" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `!x:real^2. x IN sphere(vec 0,&1)
                 ==> rho0 % x IN ball(vec 0:real^2,r0) /\ rho0 % x IN sphere(vec 0,rho0)`
  (LABEL_TAC "S0") THENL
   [REWRITE_TAC[IN_SPHERE_0; IN_BALL_0; NORM_MUL] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN sphere(vec 0,&1)
                 ==> ?y. y IN sphere(vec 0,rho1) /\
                         (P:real^2->real^2)((c0:real^2->real^2)(rho0 % x)) =
                         (c1:real^2->real^2) y`
  (LABEL_TAC "S1") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "SUB" (MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
    DISCH_THEN(MP_TAC o SPEC `rho0 % x:real^2`) THEN
    USE_THEN "S0" (fun th -> REWRITE_TAC[CONJUNCT2(MATCH_MP th (ASSUME `(x:real^2) IN sphere(vec 0,&1)`))]) THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. y IN sphere(vec 0,rho1) ==> y IN ball(vec 0,r1)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; IN_BALL_0] THEN ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
  ABBREV_TAC `k = \x:real^2. inv(rho1) % (c1':real^2->real^2)
                               ((P:real^2->real^2)((c0:real^2->real^2)(rho0 % x)))` THEN
  SUBGOAL_THEN `!x:real^2. x IN sphere(vec 0,&1)
                 ==> (P:real^2->real^2)((c0:real^2->real^2)(rho0 % x)) IN
                     IMAGE (c1:real^2->real^2) (ball(vec 0,r1))`
  (LABEL_TAC "S2") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "S1" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN sphere(vec 0,&1)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `k:real^2->real^2` SCHZ_CIRCLE_ONTO) THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "k" THEN
      SUBGOAL_THEN `(\x:real^2. inv(rho1) % (c1':real^2->real^2)
                                  ((P:real^2->real^2)((c0:real^2->real^2)(rho0 % x)))) =
                    (\z. inv(rho1) % z) o c1' o P o c0 o (\x. rho0 % x)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LINEAR_ID]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (c1:real^2->real^2) (ball(vec 0,r1))` THEN CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM_MESON_TAC[]]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LINEAR_ID];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,r0)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      USE_THEN "S1" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN sphere(vec 0,&1)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      EXPAND_TAC "k" THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(c1':real^2->real^2)((c1:real^2->real^2) y) = y` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^2) IN sphere(vec 0,rho1)` THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
      MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
      UNDISCH_TAC `(k:real^2->real^2) x = k y` THEN EXPAND_TAC "k" THEN
      REWRITE_TAC[VECTOR_MUL_LCANCEL; REAL_INV_EQ_0] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
      DISCH_THEN(MP_TAC o AP_TERM `c1:real^2->real^2`) THEN
      USE_THEN "S2" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN sphere(vec 0,&1)`)) THEN
      USE_THEN "S2" (MP_TAC o C MATCH_MP (ASSUME `(y:real^2) IN sphere(vec 0,&1)`)) THEN
      ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `(c0:real^2->real^2)(rho0 % x) = c0(rho0 % y)` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `c0':real^2->real^2`) THEN
      USE_THEN "S0" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN sphere(vec 0,&1)`)) THEN
      USE_THEN "S0" (MP_TAC o C MATCH_MP (ASSUME `(y:real^2) IN sphere(vec 0,&1)`)) THEN
      ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv(rho1) % y:real^2 IN IMAGE (k:real^2->real^2) (sphere(vec 0,&1))` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV] THEN
    UNDISCH_TAC `(y:real^2) IN sphere(vec 0,rho1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(c0:real^2->real^2)(rho0 % x)` THEN CONJ_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `rho0 % x:real^2` THEN REWRITE_TAC[] THEN
    USE_THEN "S0" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN sphere(vec 0,&1)`)) THEN
    SIMP_TAC[]] THEN
  UNDISCH_TAC `inv(rho1) % y:real^2 = (k:real^2->real^2) x` THEN EXPAND_TAC "k" THEN
  REWRITE_TAC[VECTOR_MUL_LCANCEL; REAL_INV_EQ_0] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `c1:real^2->real^2`) THEN
  USE_THEN "S2" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN sphere(vec 0,&1)`)) THEN
  ASM_SIMP_TAC[] THEN MESON_TAC[]);;

(* On the top band the new flow carries the bottom circle of normalized     *)
(* radius |w| at z0 to the top circle of normalized radius |w|.             *)

let SCHZ_ND_TOP_NORM = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap w y.
     schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap /\
     b2 <= y /\ y <= zB' /\ abs(norm w - &1) < kap
     ==> norm(sqrt(z0 - m) % w) < r0 /\ y < M /\
         schz_slice Psi z0 y (ph0(sqrt(z0 - m) % w)) IN IMAGE ph1 (ball(vec 0,r1)) /\
         norm(ph1'(schz_slice Psi z0 y (ph0(sqrt(z0 - m) % w)))) pow 2 =
         (M - y) * norm w pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SCHZ_ND_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^2`; `y:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `((Psi:real^1->real^3->real^3) (lift(y - z0)) (sch5v_at z0 ((ph0:real^2->real^2)(sqrt(z0 - m) % w))))$3 = y`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SCH5V_PR_AT; LIFT_DROP] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(Psi:real^1->real^3->real^3) (lift(y - z0)) (sch5v_at z0 ((ph0:real^2->real^2)(sqrt(z0 - m) % w))) IN
               schz_ofd Psi0 ph0 r0 z0 (ph1:real^2->real^2) r1 M b1` THEN
  REWRITE_TAC[schz_ofd; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`Psi0:real^1->real^3->real^3`; `ph0':real^2->real^2`; `z0:real`; `m:real`;
                 `ph1':real^2->real^2`; `M:real`; `b1:real`; `b2:real`;
                 `(Psi:real^1->real^3->real^3) (lift(y - z0)) (sch5v_at z0 ((ph0:real^2->real^2)(sqrt(z0 - m) % w)))`]
    SCHZ_FD_TOP) THEN
  ASM_REWRITE_TAC[schz_qtop] THEN DISCH_TAC THEN
  REWRITE_TAC[schz_slice] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_SUB_LT]);;

let SCHZ_ND_TOP_DISC = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap y s.
     schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap /\
     b2 <= y /\ y <= zB' /\ abs(s - &1) < kap
     ==> &0 < s /\ sqrt(z0 - m) * s < r0 /\ sqrt(M - y) * s < r1 /\
         IMAGE (schz_slice Psi z0 y) (IMAGE ph0 (sphere(vec 0,sqrt(z0 - m) * s))) =
         IMAGE ph1 (sphere(vec 0,sqrt(M - y) * s)) /\
         IMAGE (schz_slice Psi z0 y) (IMAGE ph0 (ball(vec 0,sqrt(z0 - m) * s))) =
         IMAGE ph1 (ball(vec 0,sqrt(M - y) * s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [SCHZ_ND_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^2. norm w = s
                 ==> norm(sqrt(z0 - m) % w) < r0 /\ y < M /\
                     schz_slice Psi z0 y ((ph0:real^2->real^2)(sqrt(z0 - m) % w)) IN
                       IMAGE (ph1:real^2->real^2) (ball(vec 0,r1)) /\
                     norm((ph1':real^2->real^2)
                       (schz_slice Psi z0 y (ph0(sqrt(z0 - m) % w)))) pow 2 =
                     (M - y) * s pow 2`
  (LABEL_TAC "TN") THENL
   [X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                   `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                   `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                   `b1:real`; `b2:real`; `Psi:real^1->real^3->real^3`; `zA':real`; `zB':real`;
                   `kap:real`; `w:real^2`; `y:real`] SCHZ_ND_TOP_NORM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SCHZ_ND_TAC THEN
  SUBGOAL_THEN `&0 < z0 - m /\ &0 < sqrt(z0 - m)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "TN" (MP_TAC o SPEC `s % basis 1:real^2`) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < M - y /\ &0 < sqrt(M - y)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(M - y) * s < r1` ASSUME_TAC THENL
   [UNDISCH_TAC `schz_slice Psi z0 y ((ph0:real^2->real^2)(sqrt(z0 - m) % s % basis 1)) IN
                 IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))` THEN
    REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^2` (CONJUNCTS_THEN2 (SUBST_ALL_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `(ph1':real^2->real^2)((ph1:real^2->real^2) k) = k` ASSUME_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(
        GEN_REWRITE_RULE I [diffeomorphism_on]
        (ASSUME `diffeomorphism_on (ball(vec 0,r1)) (IMAGE (ph1:real^2->real^2) (ball(vec 0,r1)))
                   ph1 ph1'`))))))) THEN
      ASM_REWRITE_TAC[IN_BALL_0];
      ALL_TAC] THEN
    UNDISCH_TAC `norm((ph1':real^2->real^2)((ph1:real^2->real^2) k)) pow 2 =
                 (M - y) * s pow 2` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(k:real^2) = sqrt(M - y) * s` (fun th -> ASM_REWRITE_TAC[SYM th]) THEN
    MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_MUL;
                 SQRT_POS_LE; ARITH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `z0:real`; `y:real`] SCHZ_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
  SUBGOAL_THEN `IMAGE (schz_slice Psi z0 y) (IMAGE (ph0:real^2->real^2)
                  (sphere(vec 0,sqrt(z0 - m) * s))) =
                IMAGE (ph1:real^2->real^2) (sphere(vec 0,sqrt(M - y) * s))` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHZ_CHART_CIRCLE_ONTO THEN
    MAP_EVERY EXISTS_TAC [`schz_slice Psi y z0`; `ph0':real^2->real^2`; `r0:real`;
                          `ph1':real^2->real^2`; `r1:real`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `a:real^2` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `norm(inv(sqrt(z0 - m)) % a:real^2) = s /\
                  sqrt(z0 - m) % inv(sqrt(z0 - m)) % a:real^2 = a` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                   VECTOR_MUL_LID] THEN
      UNDISCH_TAC `&0 < sqrt(z0 - m)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    USE_THEN "TN" (MP_TAC o SPEC `inv(sqrt(z0 - m)) % a:real^2`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[ASSUME
      `sqrt(z0 - m) % inv(sqrt(z0 - m)) % a:real^2 = a`]) THEN
    STRIP_TAC THEN
    UNDISCH_TAC `schz_slice Psi z0 y ((ph0:real^2->real^2) a) IN
                 IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))` THEN
    REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k:real^2` THEN ASM_REWRITE_TAC[IN_SPHERE_0] THEN
    SUBGOAL_THEN `(ph1':real^2->real^2)((ph1:real^2->real^2) k) = k` ASSUME_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(
        GEN_REWRITE_RULE I [diffeomorphism_on]
        (ASSUME `diffeomorphism_on (ball(vec 0,r1)) (IMAGE (ph1:real^2->real^2) (ball(vec 0,r1)))
                   ph1 ph1'`))))))) THEN
      ASM_REWRITE_TAC[IN_BALL_0];
      ALL_TAC] THEN
    UNDISCH_TAC `norm((ph1':real^2->real^2)(schz_slice Psi z0 y ((ph0:real^2->real^2) a))) pow 2 =
                 (M - y) * s pow 2` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_MUL;
                 SQRT_POS_LE; ARITH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SCHZ_PLANAR_DISC_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`schz_slice Psi y z0`; `ph0':real^2->real^2`; `r0:real`;
                        `ph1':real^2->real^2`; `r1:real`] THEN
  ASM_SIMP_TAC[REAL_LT_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Generic tools for the model chart.  A smooth map with a                   *)
(* smooth left inverse (schz_lip) has an invertible derivative and is        *)
(* injective; such pairs compose; derivatives of locally equal maps agree;   *)
(* the ramp functions used to reparametrize heights.                         *)
(* ------------------------------------------------------------------------- *)

let schz_lip = new_definition
 `schz_lip (s:real^N->bool) t (f:real^N->real^N) g <=>
    open s /\ open t /\ IMAGE f s SUBSET t /\ smooth_map_on s f /\ smooth_map_on t g /\
    (!x. x IN s ==> g(f x) = x)`;;

let SCHZ_LIP_DET = prove
 (`!(f:real^N->real^N) g s t x.
     schz_lip s t f g /\ x IN s
     ==> ~(det(matrix(frechet_derivative f (at x))) = &0)`,
  REWRITE_TAC[schz_lip] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((f:real^N->real^N) has_derivative frechet_derivative f (at x)) (at x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->real^N) x IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((g:real^N->real^N) has_derivative frechet_derivative g (at ((f:real^N->real^N) x)))
                (at (f x))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^N->bool`; `g:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (g:real^N->real^N) (at ((f:real^N->real^N) x)) o
                frechet_derivative f (at x) = (\h. h)` ASSUME_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `(g:real^N->real^N) o (f:real^N->real^N)` THEN EXISTS_TAC `x:real^N` THEN
    CONJ_TAC THENL [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\y:real^N. y` THEN
    UNDISCH_TAC `open(s:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x:real^N. x IN s ==> (g:real^N->real^N)((f:real^N->real^N) x) = x`)
          (concl th))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `frechet_derivative (f:real^N->real^N) (at x)` SMT_DET_NONZERO_INJECTIVE) THEN
  ANTS_TAC THENL
   [MP_TAC(ASSUME `((f:real^N->real^N) has_derivative frechet_derivative f (at x)) (at x)`) THEN
    SIMP_TAC[has_derivative];
    DISCH_THEN SUBST1_TAC] THEN
  X_GEN_TAC `h:real^N` THEN DISCH_TAC THEN
  UNDISCH_TAC `frechet_derivative (g:real^N->real^N) (at ((f:real^N->real^N) x)) o
               frechet_derivative f (at x) = (\h. h)` THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN DISCH_THEN(MP_TAC o SPEC `h:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(ISPEC `frechet_derivative (g:real^N->real^N) (at ((f:real^N->real^N) x))`
    LINEAR_0) THEN
  MP_TAC(ASSUME `((g:real^N->real^N) has_derivative
                  frechet_derivative g (at ((f:real^N->real^N) x))) (at (f x))`) THEN
  SIMP_TAC[has_derivative]);;

let SCHZ_LIP_INJ = prove
 (`!(f:real^N->real^N) g s t x y.
     schz_lip s t f g /\ x IN s /\ y IN s /\ f x = f y ==> x = y`,
  REWRITE_TAC[schz_lip] THEN MESON_TAC[]);;

let SCHZ_LIP_SUBSET = prove
 (`!(f:real^N->real^N) g s t s'.
     schz_lip s t f g /\ open s' /\ s' SUBSET s ==> schz_lip s' t f g`,
  REWRITE_TAC[schz_lip] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

let SCHZ_LIP_EQ = prove
 (`!(f:real^N->real^N) f' g s t.
     schz_lip s t f g /\ (!x. x IN s ==> f' x = f x) ==> schz_lip s t f' g`,
  REWRITE_TAC[schz_lip] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^N->real^N) s SUBSET t` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `f:real^N->real^N` THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let SCHZ_LIP_COMPOSE = prove
 (`!(f1:real^N->real^N) g1 s1 t1 (f2:real^N->real^N) g2 s2 t2.
     schz_lip s1 t1 f1 g1 /\ schz_lip s2 t2 f2 g2 /\ IMAGE f1 s1 SUBSET s2
     ==> schz_lip s1 {q | q IN t2 /\ g2 q IN t1} (f2 o f1) (g1 o g2)`,
  REWRITE_TAC[schz_lip] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f1:real^N->real^N) x IN s2` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[] THEN ASM SET_TAC[]];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `s2:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `t1:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `t2:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f1:real^N->real^N) x IN s2` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

(* Derivatives of maps that agree on an open neighbourhood.                  *)

let SCHZ_FD_LOCAL_EQ = prove
 (`!(f:real^M->real^N) g s x.
     open s /\ x IN s /\ (!y. y IN s ==> f y = g y) /\ g differentiable at x
     ==> frechet_derivative f (at x) = frechet_derivative g (at x)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN EXISTS_TAC `g:real^M->real^N` THEN
  UNDISCH_TAC `open(s:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (term_match [] `!y:real^M. y IN s ==> (f:real^M->real^N) y = g y`) (concl th))) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]);;

(* The ramp z |-> z - s((z - c)/w) (z - d): z below c, d above c + w.       *)

let schz_ramp = new_definition
 `schz_ramp c w d (z:real) = z - smooth_step((z - c) / w) * (z - d)`;;

let SCHZ_RAMP = prove
 (`!c w d z. &0 < w
             ==> (z <= c ==> schz_ramp c w d z = z) /\
                 (c + w <= z ==> schz_ramp c w d z = d) /\
                 min z d <= schz_ramp c w d z /\ schz_ramp c w d z <= max z d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[schz_ramp] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `smooth_step((z - c) / w) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_0 THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    DISCH_TAC THEN
    SUBGOAL_THEN `smooth_step((z - c) / w) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_1 THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    MP_TAC(SPEC `(z - c) / w` SMOOTH_STEP_BOUNDS) THEN
    ABBREV_TAC `l = smooth_step((z - c) / w)` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `z - l * (z - d) = (&1 - l) * z + l * d`] THEN
    REWRITE_TAC[real_min] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= l * (d - z) ==> z <= (&1 - l) * z + l * d`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - l) * (z - d) ==> d <= (&1 - l) * z + l * d`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    MP_TAC(SPEC `(z - c) / w` SMOOTH_STEP_BOUNDS) THEN
    ABBREV_TAC `l = smooth_step((z - c) / w)` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `z - l * (z - d) = (&1 - l) * z + l * d`] THEN
    REWRITE_TAC[real_max] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - l) * (d - z) ==> (&1 - l) * z + l * d <= d`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= l * (z - d) ==> (&1 - l) * z + l * d <= z`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]);;

let SCHZ_RAMP_SMOOTH = prove
 (`!c w d s (h:real^N->real).
     open s /\ smooth_map_on s (\x. lift(h x))
     ==> smooth_map_on s (\x. lift(schz_ramp c w d (h x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[schz_ramp; real_div] THEN SCHZ_SMOOTH_TAC);;

(* Maps of the form x |-> sch5v_at (h x) (p x).                              *)

let SCHZ_AT_SMOOTH = prove
 (`!s (h:real^N->real) (p:real^N->real^2).
     open s /\ smooth_map_on s (\x. lift(h x)) /\ smooth_map_on s p
     ==> smooth_map_on s (\x. sch5v_at (h x) (p x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch5v_at] THEN SCHZ_SMOOTH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The pieces of the model chart and their smooth left                       *)
(* inverses: the bottom chart P1, the flow cylinder P2 (with the time ramp), *)
(* and the factors of the top cap: T1 (u = v / sqrt(z - m)), the vertical   *)
(* reparametrization VS, and the frozen holonomy Kp.                         *)
(* ------------------------------------------------------------------------- *)

let SCHZ_OPEN_PRE = prove
 (`!(g:real^N->real^M) s t.
     open s /\ smooth_map_on s g /\ open t ==> open {x | x IN s /\ g x IN t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]);;

let SCHZ_POS_TAC =
  REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  TRY(MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SQRT_POS_LT) THEN
  TRY(MATCH_MP_TAC REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC;;

(* P1: the bottom chart.                                                     *)

let schz_p1 = new_definition
 `schz_p1 (ph0:real^2->real^2) M (x:real^3) =
    sch5v_at (x$3) (ph0(inv(sqrt(M - x$3)) % sch5v_pr x))`;;

let schz_p1i = new_definition
 `schz_p1i (ph0':real^2->real^2) M (q:real^3) =
    sch5v_at (q$3) (sqrt(M - q$3) % ph0'(sch5v_pr q))`;;

let SCHZ_P1_LIP = prove
 (`!(ph0:real^2->real^2) ph0' r0 M.
     diffeomorphism_on (ball(vec 0,r0)) (IMAGE ph0 (ball(vec 0,r0))) ph0 ph0'
     ==> schz_lip {x:real^3 | x IN {x | x$3 < M} /\
                              inv(sqrt(M - x$3)) % sch5v_pr x IN ball(vec 0,r0)}
                  {q:real^3 | q IN {q | q$3 < M} /\
                              sch5v_pr q IN IMAGE ph0 (ball(vec 0,r0))}
                  (schz_p1 ph0 M) (schz_p1i ph0' M)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open {x:real^3 | x$3 < M}` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {x:real^3 | x$3 < M} (\x. inv(sqrt(M - x$3)) % sch5v_pr x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[sch5v_pr] THEN SCHZ_SMOOTH_TAC THEN SCHZ_POS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {x:real^3 | x$3 < M} (sch5v_pr:real^3->real^2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV; SCH5V_PR_AT_SMOOTH];
    ALL_TAC] THEN
  ABBREV_TAC `D = {x:real^3 | x IN {x | x$3 < M} /\
                              inv(sqrt(M - x$3)) % sch5v_pr x IN ball(vec 0,r0)}` THEN
  ABBREV_TAC `E = {q:real^3 | q IN {q | q$3 < M} /\
                              sch5v_pr q IN IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}` THEN
  SUBGOAL_THEN `open(D:real^3->bool) /\ open(E:real^3->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN EXPAND_TAC "E" THEN CONJ_TAC THEN MATCH_MP_TAC SCHZ_OPEN_PRE THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `D SUBSET {x:real^3 | x$3 < M} /\ E SUBSET {x:real^3 | x$3 < M}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN EXPAND_TAC "E" THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[schz_lip] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "D" THEN EXPAND_TAC "E" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; schz_p1; SCH5V_PR_AT] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `schz_p1 (ph0:real^2->real^2) M =
                  (\x. sch5v_at (x$3) ((ph0 o (\x:real^3. inv(sqrt(M - x$3)) % sch5v_pr x)) x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schz_p1; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SCHZ_AT_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [SCHZ_SMOOTH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `ball(vec 0:real^2,r0)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [EXPAND_TAC "D" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | x$3 < M}` THEN
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `schz_p1i (ph0':real^2->real^2) M =
                  (\q. sch5v_at (q$3) (sqrt(M - q$3) % (ph0' o sch5v_pr) q))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schz_p1i; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SCHZ_AT_SMOOTH THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SCHZ_SMOOTH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SCH3_SV_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [SCHZ_SMOOTH_TAC THEN UNDISCH_TAC `(E:real^3->bool) SUBSET {x:real^3 | x$3 < M}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_SUB_LT];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "E" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV; SCH5V_PR_AT_SMOOTH]];
    EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM; schz_p1; schz_p1i; SCH5V_PR_AT] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `sqrt(M - (x:real^3)$3) * inv(sqrt(M - x$3)) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_MUL_LID; SCH5V_PR_AT]]]);;

(* T1: (v,z) |-> (v / sqrt(z - m), z).                                       *)

let schz_t1 = new_definition
 `schz_t1 m (x:real^3) = sch5v_at (x$3) (inv(sqrt(x$3 - m)) % sch5v_pr x)`;;

let schz_t1i = new_definition
 `schz_t1i m (q:real^3) = sch5v_at (q$3) (sqrt(q$3 - m) % sch5v_pr q)`;;

let SCHZ_T1_LIP = prove
 (`!m. schz_lip {x:real^3 | m < x$3} {q:real^3 | m < q$3} (schz_t1 m) (schz_t1i m)`,
  GEN_TAC THEN REWRITE_TAC[schz_lip] THEN
  SUBGOAL_THEN `open {x:real^3 | m < x$3}` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; schz_t1; SCH5V_PR_AT];
    SUBGOAL_THEN `schz_t1 m = (\x:real^3. sch5v_at (x$3) (inv(sqrt(x$3 - m)) % sch5v_pr x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schz_t1]; ALL_TAC] THEN
    MATCH_MP_TAC SCHZ_AT_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [SCHZ_SMOOTH_TAC; REWRITE_TAC[sch5v_pr] THEN SCHZ_SMOOTH_TAC THEN SCHZ_POS_TAC];
    SUBGOAL_THEN `schz_t1i m = (\q:real^3. sch5v_at (q$3) (sqrt(q$3 - m) % sch5v_pr q))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schz_t1i]; ALL_TAC] THEN
    MATCH_MP_TAC SCHZ_AT_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [SCHZ_SMOOTH_TAC; REWRITE_TAC[sch5v_pr] THEN SCHZ_SMOOTH_TAC THEN SCHZ_POS_TAC];
    REWRITE_TAC[IN_ELIM_THM; schz_t1; schz_t1i; SCH5V_PR_AT] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `sqrt((x:real^3)$3 - m) * inv(sqrt(x$3 - m)) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_MUL_LID; SCH5V_PR_AT]]]);;

(* VS: (u,z) |-> (u, Xi_{L u}(z)), a vertical reparametrization.             *)

let schz_vs = new_definition
 `schz_vs (Xi:real^1->real^1->real^1) (L:real^2->real) (x:real^3) =
    sch5v_at (drop(Xi (lift(L(sch5v_pr x))) (lift(x$3)))) (sch5v_pr x)`;;

let SCHZ_VS_SMOOTH = prove
 (`!(Xi:real^1->real^1->real^1) (L:real^2->real).
     smooth_map_on (:real^(1,1)finite_sum) (\w. Xi (fstcart w) (sndcart w)) /\
     smooth_map_on (:real^2) (\u. lift(L u))
     ==> smooth_map_on (:real^3) (schz_vs Xi L)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `schz_vs Xi (L:real^2->real) =
                (\x. sch5v_at (drop((Xi:real^1->real^1->real^1)
                                (lift(L(sch5v_pr x))) (lift(x$3)))) (sch5v_pr x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schz_vs]; ALL_TAC] THEN
  MATCH_MP_TAC SCHZ_AT_SMOOTH THEN
  REWRITE_TAC[OPEN_UNIV; LIFT_DROP; ETA_AX; SCH5V_PR_AT_SMOOTH] THEN
  MP_TAC(ISPECL [`Xi:real^1->real^1->real^1`; `(:real^3)`;
                 `\x:real^3. (L:real^2->real)(sch5v_pr x)`; `\x:real^3. lift(x$3)`]
    SCH5V_FLOW_COMPOSE_SMOOTH) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:real^3. lift((L:real^2->real)(sch5v_pr x))) = (\u. lift(L u)) o sch5v_pr`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SCH5V_PR_AT_SMOOTH];
    ASSUME_TAC(INST_TYPE [`:3`,`:N`] OPEN_UNIV) THEN SCHZ_SMOOTH_TAC]);;

let SCHZ_VS_LIP = prove
 (`!(Xi:real^1->real^1->real^1) (L:real^2->real).
     (!z. Xi (vec 0) z = z) /\ (!z s t. Xi t (Xi s z) = Xi (s + t) z) /\
     smooth_map_on (:real^(1,1)finite_sum) (\w. Xi (fstcart w) (sndcart w)) /\
     smooth_map_on (:real^2) (\u. lift(L u))
     ==> schz_lip (:real^3) (:real^3) (schz_vs Xi L) (schz_vs Xi (\u. --(L u)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[schz_lip; OPEN_UNIV; SUBSET_UNIV; IN_UNIV] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SCHZ_VS_SMOOTH THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SCHZ_VS_SMOOTH THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SCH3_SL_NEG THEN ASM_REWRITE_TAC[OPEN_UNIV];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[schz_vs; SCH5V_PR_AT; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM LIFT_ADD; REAL_ADD_RINV; LIFT_NUM] THEN
    ASM_REWRITE_TAC[LIFT_DROP; SCH5V_PR_AT]]);;

(* Kp: the holonomy of the new flow from level z0, frozen at the level      *)
(* zeta(z) = schz_ramp (zt - e) e zt z, in u-coordinates.                     *)

let SCHZ_ZETA_LE = prove
 (`!e zt z. &0 < e ==> schz_ramp (zt - e) e zt z <= zt`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`zt - e`; `e:real`; `zt:real`; `z:real`] SCHZ_RAMP) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let schz_kp = new_definition
 `schz_kp (Psi:real^1->real^3->real^3) (ph0:real^2->real^2) m M z0 zt e (x:real^3) =
    sch5v_at (x$3)
      (schz_slice Psi z0 (schz_ramp (zt - e) e zt (x$3))
        (ph0((sqrt(z0 - m) / sqrt(M - schz_ramp (zt - e) e zt (x$3))) % sch5v_pr x)))`;;

let schz_kpi = new_definition
 `schz_kpi (Psi:real^1->real^3->real^3) (ph0':real^2->real^2) m M z0 zt e (q:real^3) =
    sch5v_at (q$3)
      ((sqrt(M - schz_ramp (zt - e) e zt (q$3)) / sqrt(z0 - m)) %
       ph0'(schz_slice Psi (schz_ramp (zt - e) e zt (q$3)) z0 (sch5v_pr q)))`;;

let SCHZ_KP_LIP = prove
 (`!(Psi:real^1->real^3->real^3) (ph0:real^2->real^2) ph0' r0 m M z0 zt e.
     (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
     (!t x. (Psi t x)$3 = x$3 + drop t) /\
     smooth_map_on (:real^(1,3)finite_sum) (\w. Psi (fstcart w) (sndcart w)) /\
     diffeomorphism_on (ball(vec 0,r0)) (IMAGE ph0 (ball(vec 0,r0))) ph0 ph0' /\
     m < z0 /\ &0 < e /\ zt < M
     ==> schz_lip {x:real^3 | x IN (:real^3) /\
                    (sqrt(z0 - m) / sqrt(M - schz_ramp (zt - e) e zt (x$3))) % sch5v_pr x IN
                    ball(vec 0,r0)}
                  {q:real^3 | q IN (:real^3) /\
                    schz_slice Psi (schz_ramp (zt - e) e zt (q$3)) z0 (sch5v_pr q) IN
                    IMAGE ph0 (ball(vec 0,r0))}
                  (schz_kp Psi ph0 m M z0 zt e) (schz_kpi Psi ph0' m M z0 zt e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `diffeomorphism_on (ball(vec 0,r0)) (IMAGE (ph0:real^2->real^2) (ball(vec 0,r0)))
                 ph0 ph0'` THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ASSUME_TAC(INST_TYPE [`:3`,`:N`] OPEN_UNIV) THEN
  SUBGOAL_THEN `!z. schz_ramp (zt - e) e zt z < M` (LABEL_TAC "ZM") THENL
   [GEN_TAC THEN MP_TAC(SPECL [`e:real`; `zt:real`; `z:real`] SCHZ_ZETA_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\x. lift(schz_ramp (zt - e) e zt ((x:real^3)$3)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCHZ_RAMP_SMOOTH THEN REWRITE_TAC[OPEN_UNIV] THEN SCHZ_SMOOTH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real. diffeomorphism_on (:real^2) (:real^2) (schz_slice Psi z0 y)
                                             (schz_slice Psi y z0)` (LABEL_TAC "SD") THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `z0:real`; `y:real`]
      SCHZ_SLICE_FACTS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y p. schz_slice Psi y z0 (schz_slice Psi z0 y p) = p` (LABEL_TAC "SI") THENL
   [REPEAT GEN_TAC THEN USE_THEN "SD" (MP_TAC o SPEC `y:real`) THEN
    REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^3)
                  (\x. (sqrt(z0 - m) / sqrt(M - schz_ramp (zt - e) e zt ((x:real^3)$3))) %
                       sch5v_pr x)` ASSUME_TAC THENL
   [REWRITE_TAC[sch5v_pr] THEN SCHZ_SMOOTH_TAC THEN
    REWRITE_TAC[IN_UNIV] THEN REPEAT GEN_TAC THEN
    TRY(MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SQRT_POS_LT) THEN
    ASM_SIMP_TAC[REAL_SUB_LT];
    ALL_TAC] THEN
  ABBREV_TAC `D = {x:real^3 | x IN (:real^3) /\
                    (sqrt(z0 - m) / sqrt(M - schz_ramp (zt - e) e zt (x$3))) % sch5v_pr x IN
                    ball(vec 0,r0)}` THEN
  SUBGOAL_THEN `smooth_map_on (:real^3)
                  (\q. sch5v_pr((Psi:real^1->real^3->real^3)
                         (lift(z0 - schz_ramp (zt - e) e zt (q$3)))
                         (sch5v_at (schz_ramp (zt - e) e zt (q$3)) (sch5v_pr q))))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\q. sch5v_pr((Psi:real^1->real^3->real^3)
                         (lift(z0 - schz_ramp (zt - e) e zt (q$3)))
                         (sch5v_at (schz_ramp (zt - e) e zt (q$3)) (sch5v_pr q)))) =
                  sch5v_pr o (\q. Psi (lift(z0 - schz_ramp (zt - e) e zt (q$3)))
                                     (sch5v_at (schz_ramp (zt - e) e zt (q$3)) (sch5v_pr q)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SCH5V_PR_AT_SMOOTH] THEN
    MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `(:real^3)`;
                   `\q:real^3. z0 - schz_ramp (zt - e) e zt (q$3)`;
                   `\q:real^3. sch5v_at (schz_ramp (zt - e) e zt (q$3)) (sch5v_pr q)`]
      SCH5V_FLOW_COMPOSE_SMOOTH) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
    CONJ_TAC THENL
     [SCHZ_SMOOTH_TAC;
      MATCH_MP_TAC SCHZ_AT_SMOOTH THEN ASM_REWRITE_TAC[OPEN_UNIV; ETA_AX; SCH5V_PR_AT_SMOOTH]];
    ALL_TAC] THEN
  ABBREV_TAC `E = {q:real^3 | q IN (:real^3) /\
                    schz_slice Psi (schz_ramp (zt - e) e zt (q$3)) z0 (sch5v_pr q) IN
                    IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}` THEN
  SUBGOAL_THEN `open(D:real^3->bool) /\ open(E:real^3->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN EXPAND_TAC "E" THEN CONJ_TAC THEN MATCH_MP_TAC SCHZ_OPEN_PRE THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REWRITE_TAC[schz_slice; REAL_ARITH `a - (a - b) = b`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[schz_lip] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "D" THEN EXPAND_TAC "E" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV; schz_kp; SCH5V_PR_AT] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "SI" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `schz_kp Psi (ph0:real^2->real^2) m M z0 zt e =
      (\x. sch5v_at (x$3)
             (sch5v_pr((Psi:real^1->real^3->real^3) (lift(schz_ramp (zt - e) e zt (x$3) - z0))
                (sch5v_at z0 ((ph0 o (\x:real^3. (sqrt(z0 - m) /
                   sqrt(M - schz_ramp (zt - e) e zt (x$3))) % sch5v_pr x)) x)))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schz_kp; schz_slice; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SCHZ_AT_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [SCHZ_SMOOTH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. sch5v_pr((Psi:real^1->real^3->real^3) (lift(schz_ramp (zt - e) e zt (x$3) - z0))
             (sch5v_at z0 (((ph0:real^2->real^2) o (\x:real^3. (sqrt(z0 - m) /
                sqrt(M - schz_ramp (zt - e) e zt (x$3))) % sch5v_pr x)) x)))) =
      sch5v_pr o (\x. Psi (lift(schz_ramp (zt - e) e zt (x$3) - z0))
             (sch5v_at z0 ((ph0 o (\x:real^3. (sqrt(z0 - m) /
                sqrt(M - schz_ramp (zt - e) e zt (x$3))) % sch5v_pr x)) x)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SCH5V_PR_AT_SMOOTH] THEN
    MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `D:real^3->bool`;
                   `\x:real^3. schz_ramp (zt - e) e zt (x$3) - z0`;
                   `\x:real^3. sch5v_at z0 (((ph0:real^2->real^2) o (\x:real^3. (sqrt(z0 - m) /
                      sqrt(M - schz_ramp (zt - e) e zt (x$3))) % sch5v_pr x)) x)`]
      SCH5V_FLOW_COMPOSE_SMOOTH) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN SCHZ_SMOOTH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SCHZ_AT_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [SCHZ_SMOOTH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `ball(vec 0:real^2,r0)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [EXPAND_TAC "D" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    SUBGOAL_THEN
     `schz_kpi Psi (ph0':real^2->real^2) m M z0 zt e =
      (\q. sch5v_at (q$3)
             ((sqrt(M - schz_ramp (zt - e) e zt (q$3)) / sqrt(z0 - m)) %
              (ph0' o (\q. sch5v_pr((Psi:real^1->real^3->real^3)
                         (lift(z0 - schz_ramp (zt - e) e zt (q$3)))
                         (sch5v_at (schz_ramp (zt - e) e zt (q$3)) (sch5v_pr q))))) q))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schz_kpi; schz_slice; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SCHZ_AT_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [SCHZ_SMOOTH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SCH3_SV_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN SCHZ_SMOOTH_TAC THEN
      REWRITE_TAC[IN_UNIV] THEN REPEAT GEN_TAC THEN
      TRY(MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SQRT_POS_LT) THEN
      ASM_SIMP_TAC[REAL_SUB_LT];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "E" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV; schz_slice;
                  REAL_ARITH `a - (a - b) = b`] THEN
      SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV; schz_kp; schz_kpi; SCH5V_PR_AT] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "SI" (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `sqrt(M - schz_ramp (zt - e) e zt ((x:real^3)$3)) / sqrt(z0 - m) *
                  sqrt(z0 - m) / sqrt(M - schz_ramp (zt - e) e zt (x$3)) = &1`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `&0 < sqrt(M - schz_ramp (zt - e) e zt ((x:real^3)$3)) /\
                    &0 < sqrt(z0 - m)` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THENL
         [USE_THEN "ZM" (MP_TAC o SPEC `(x:real^3)$3`) THEN REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        CONV_TAC REAL_FIELD];
      REWRITE_TAC[VECTOR_MUL_LID; SCH5V_PR_AT]]]);;

(* P2: the flow cylinder, with the time ramp psi(z) = schz_ramp z0 eta z0 z  *)
(* (psi = z below z0, = z0 above z0 + eta).                                  *)

let SCHZ_PSI_GT = prove
 (`!m z0 eta z. &0 < eta /\ m < z0 /\ m < z ==> m < schz_ramp z0 eta z0 z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z0:real`; `eta:real`; `z0:real`; `z:real`] SCHZ_RAMP) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let schz_p2 = new_definition
 `schz_p2 (Psi:real^1->real^3->real^3) (ph0:real^2->real^2) m M z0 eta (x:real^3) =
    Psi (lift(x$3 - schz_ramp z0 eta z0 (x$3)))
        (sch5v_at (schz_ramp z0 eta z0 (x$3))
           (ph0((sqrt(schz_ramp z0 eta z0 (x$3) - m) / sqrt((x$3 - m) * (M - x$3))) %
                sch5v_pr x)))`;;

let schz_p2i = new_definition
 `schz_p2i (Psi:real^1->real^3->real^3) (ph0':real^2->real^2) m M z0 eta (q:real^3) =
    sch5v_at (q$3)
      ((sqrt((q$3 - m) * (M - q$3)) / sqrt(schz_ramp z0 eta z0 (q$3) - m)) %
       ph0'(sch5v_pr(Psi (lift(schz_ramp z0 eta z0 (q$3) - q$3)) q)))`;;

let SCHZ_P2_HEIGHT = prove
 (`!(Psi:real^1->real^3->real^3) (ph0:real^2->real^2) m M z0 eta x.
     (!t x. (Psi t x)$3 = x$3 + drop t)
     ==> (schz_p2 Psi ph0 m M z0 eta x)$3 = x$3`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[schz_p2; SCH5V_PR_AT; LIFT_DROP] THEN
  REAL_ARITH_TAC);;

let SCHZ_P2_LIP = prove
 (`!(Psi:real^1->real^3->real^3) (ph0:real^2->real^2) ph0' r0 m M z0 eta.
     (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
     (!t x. (Psi t x)$3 = x$3 + drop t) /\
     smooth_map_on (:real^(1,3)finite_sum) (\w. Psi (fstcart w) (sndcart w)) /\
     diffeomorphism_on (ball(vec 0,r0)) (IMAGE ph0 (ball(vec 0,r0))) ph0 ph0' /\
     m < z0 /\ &0 < eta
     ==> schz_lip {x:real^3 | x IN {x | m < x$3 /\ x$3 < M} /\
                    (sqrt(schz_ramp z0 eta z0 (x$3) - m) / sqrt((x$3 - m) * (M - x$3))) %
                    sch5v_pr x IN ball(vec 0,r0)}
                  {q:real^3 | q IN {q | m < q$3 /\ q$3 < M} /\
                    sch5v_pr(Psi (lift(schz_ramp z0 eta z0 (q$3) - q$3)) q) IN
                    IMAGE ph0 (ball(vec 0,r0))}
                  (schz_p2 Psi ph0 m M z0 eta) (schz_p2i Psi ph0' m M z0 eta)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `diffeomorphism_on (ball(vec 0,r0)) (IMAGE (ph0:real^2->real^2) (ball(vec 0,r0)))
                 ph0 ph0'` THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ASSUME_TAC(INST_TYPE [`:3`,`:N`] OPEN_UNIV) THEN
  ABBREV_TAC `S0 = {x:real^3 | m < x$3 /\ x$3 < M}` THEN
  SUBGOAL_THEN `open(S0:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S0" THEN
    SUBGOAL_THEN `{x:real^3 | m < x$3 /\ x$3 < M} = {x | x$3 > m} INTER {x | x$3 < M}`
    SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN S0 ==> m < x$3 /\ x$3 < M` (LABEL_TAC "S0M") THENL
   [EXPAND_TAC "S0" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. m < z ==> m < schz_ramp z0 eta z0 z` (LABEL_TAC "PG") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SCHZ_PSI_GT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) (\x. lift(schz_ramp z0 eta z0 ((x:real^3)$3)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCHZ_RAMP_SMOOTH THEN REWRITE_TAC[OPEN_UNIV] THEN SCHZ_SMOOTH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S0 (\x. lift(schz_ramp z0 eta z0 ((x:real^3)$3)))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S0
                  (\x. (sqrt(schz_ramp z0 eta z0 ((x:real^3)$3) - m) /
                        sqrt((x$3 - m) * (M - x$3))) % sch5v_pr x)` ASSUME_TAC THENL
   [REWRITE_TAC[sch5v_pr] THEN SCHZ_SMOOTH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> USE_THEN "S0M" (STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
    TRY(MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SQRT_POS_LT) THEN
    TRY(MATCH_MP_TAC REAL_LT_MUL) THEN ASM_SIMP_TAC[REAL_SUB_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^3)
                  (\q. sch5v_pr((Psi:real^1->real^3->real^3)
                         (lift(schz_ramp z0 eta z0 (q$3) - q$3)) q))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\q. sch5v_pr((Psi:real^1->real^3->real^3)
                         (lift(schz_ramp z0 eta z0 (q$3) - q$3)) q)) =
                  sch5v_pr o (\q. Psi (lift(schz_ramp z0 eta z0 (q$3) - q$3)) q)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SCH5V_PR_AT_SMOOTH] THEN
    MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `(:real^3)`;
                   `\q:real^3. schz_ramp z0 eta z0 (q$3) - q$3`; `\q:real^3. q`]
      SCH5V_FLOW_COMPOSE_SMOOTH) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN SCHZ_SMOOTH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `D = {x:real^3 | x IN S0 /\
                    (sqrt(schz_ramp z0 eta z0 (x$3) - m) / sqrt((x$3 - m) * (M - x$3))) %
                    sch5v_pr x IN ball(vec 0,r0)}` THEN
  ABBREV_TAC `E = {q:real^3 | q IN S0 /\
                    sch5v_pr((Psi:real^1->real^3->real^3)
                      (lift(schz_ramp z0 eta z0 (q$3) - q$3)) q) IN
                    IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}` THEN
  SUBGOAL_THEN `open(D:real^3->bool) /\ open(E:real^3->bool) /\ D SUBSET S0 /\ E SUBSET S0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN EXPAND_TAC "E" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SCHZ_OPEN_PRE THEN ASM_REWRITE_TAC[OPEN_BALL];
      MATCH_MP_TAC SCHZ_OPEN_PRE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN D
                 ==> sch5v_pr((Psi:real^1->real^3->real^3)
                       (lift(schz_ramp z0 eta z0 (x$3) - x$3))
                       (schz_p2 Psi ph0 m M z0 eta x)) =
                     (ph0:real^2->real^2)
                       ((sqrt(schz_ramp z0 eta z0 (x$3) - m) / sqrt((x$3 - m) * (M - x$3))) %
                        sch5v_pr x)` (LABEL_TAC "BACK") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[schz_p2] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM LIFT_ADD] THEN
    REWRITE_TAC[REAL_ARITH `(a - b) + (b - a) = &0`; LIFT_NUM] THEN
    ASM_REWRITE_TAC[SCH5V_PR_AT];
    ALL_TAC] THEN
  REWRITE_TAC[schz_lip] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN S0` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN D` THEN UNDISCH_TAC `(D:real^3->bool) SUBSET S0` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `ph0:real^2->real^2`; `m:real`; `M:real`;
                   `z0:real`; `eta:real`; `x:real^3`] SCHZ_P2_HEIGHT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "BACK" (fun th -> ASM_SIMP_TAC[th]) THEN CONJ_TAC THENL
     [EXPAND_TAC "S0" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "S0M" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN UNDISCH_TAC `(x:real^3) IN D` THEN EXPAND_TAC "D" THEN
      SIMP_TAC[IN_ELIM_THM]];
    SUBGOAL_THEN
     `schz_p2 Psi (ph0:real^2->real^2) m M z0 eta =
      (\x. (Psi:real^1->real^3->real^3) (lift(x$3 - schz_ramp z0 eta z0 (x$3)))
             (sch5v_at (schz_ramp z0 eta z0 (x$3))
               ((ph0 o (\x:real^3. (sqrt(schz_ramp z0 eta z0 (x$3) - m) /
                         sqrt((x$3 - m) * (M - x$3))) % sch5v_pr x)) x)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schz_p2; o_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `D:real^3->bool`;
                   `\x:real^3. x$3 - schz_ramp z0 eta z0 (x$3)`;
                   `\x:real^3. sch5v_at (schz_ramp z0 eta z0 (x$3))
                       (((ph0:real^2->real^2) o (\x:real^3. (sqrt(schz_ramp z0 eta z0 (x$3) - m) /
                         sqrt((x$3 - m) * (M - x$3))) % sch5v_pr x)) x)`]
      SCH5V_FLOW_COMPOSE_SMOOTH) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN SCHZ_SMOOTH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SCHZ_AT_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `ball(vec 0:real^2,r0)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [EXPAND_TAC "D" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `S0:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN
     `schz_p2i Psi (ph0':real^2->real^2) m M z0 eta =
      (\q. sch5v_at (q$3)
             ((sqrt((q$3 - m) * (M - q$3)) / sqrt(schz_ramp z0 eta z0 (q$3) - m)) %
              (ph0' o (\q. sch5v_pr((Psi:real^1->real^3->real^3)
                         (lift(schz_ramp z0 eta z0 (q$3) - q$3)) q))) q))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schz_p2i; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SCHZ_AT_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN SCHZ_SMOOTH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SCH3_SV_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `S0:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN SCHZ_SMOOTH_TAC THEN REPEAT GEN_TAC THEN
      DISCH_THEN(fun th -> USE_THEN "S0M" (STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
      TRY(MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SQRT_POS_LT) THEN
      TRY(MATCH_MP_TAC REAL_LT_MUL) THEN ASM_SIMP_TAC[REAL_SUB_LT];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "E" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[schz_p2i] THEN
    MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `ph0:real^2->real^2`; `m:real`; `M:real`;
                   `z0:real`; `eta:real`; `x:real^3`] SCHZ_P2_HEIGHT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "BACK" (fun th -> ASM_SIMP_TAC[th]) THEN
    SUBGOAL_THEN `(sqrt(schz_ramp z0 eta z0 ((x:real^3)$3) - m) / sqrt((x$3 - m) * (M - x$3))) %
                  sch5v_pr x IN ball(vec 0:real^2,r0)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN D` THEN EXPAND_TAC "D" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `m < (x:real^3)$3 /\ x$3 < M` STRIP_ASSUME_TAC THENL
     [USE_THEN "S0M" MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:real^3) IN D` THEN UNDISCH_TAC `(D:real^3->bool) SUBSET S0` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt(((x:real^3)$3 - m) * (M - x$3)) /\
                  &0 < sqrt(schz_ramp z0 eta z0 (x$3) - m)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        USE_THEN "PG" (MP_TAC o SPEC `(x:real^3)$3`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(((x:real^3)$3 - m) * (M - x$3)) / sqrt(schz_ramp z0 eta z0 (x$3) - m) *
                  sqrt(schz_ramp z0 eta z0 (x$3) - m) / sqrt((x$3 - m) * (M - x$3)) = &1`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < sqrt(((x:real^3)$3 - m) * (M - x$3))` THEN
      UNDISCH_TAC `&0 < sqrt(schz_ramp z0 eta z0 ((x:real^3)$3) - m)` THEN
      CONV_TAC REAL_FIELD;
      REWRITE_TAC[VECTOR_MUL_LID; SCH5V_PR_AT]]]);;

(* ------------------------------------------------------------------------- *)
(* The top holonomy K (schz_kmap) in u-coordinates, the                      *)
(* vertical stretch exponent L (schz_lfun, smooth, 0 near and beyond the     *)
(* rim), and the top cap piece Kp o VS o T1 with its smooth left inverse.    *)
(* ------------------------------------------------------------------------- *)

let schz_kmap = new_definition
 `schz_kmap (Psi:real^1->real^3->real^3) (ph0:real^2->real^2) (ph1':real^2->real^2)
            m M z0 y (u:real^2) =
    ph1'(schz_slice Psi z0 y (ph0((sqrt(z0 - m) / sqrt(M - y)) % u)))`;;

let schz_lfun = new_definition
 `schz_lfun (Psi:real^1->real^3->real^3) (ph0:real^2->real^2) (ph1':real^2->real^2)
            m M z0 zt s1 (u:real^2) =
    if norm u pow 2 < M - zt - s1 / &2
    then log((M - zt - norm(schz_kmap Psi ph0 ph1' m M z0 zt u) pow 2) /
             (M - zt - norm u pow 2))
    else &0`;;

(* K preserves the radius near the rim.                                      *)

let SCHZ_KMAP_NORM = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap y u.
     schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap /\
     b2 <= y /\ y <= zB' /\ abs(norm u / sqrt(M - y) - &1) < kap
     ==> norm((sqrt(z0 - m) / sqrt(M - y)) % u) < r0 /\
         schz_slice Psi z0 y (ph0((sqrt(z0 - m) / sqrt(M - y)) % u)) IN
           IMAGE ph1 (ball(vec 0,r1)) /\
         norm(schz_kmap Psi ph0 ph1' m M z0 y u) = norm u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < M - y /\ &0 < sqrt(M - y)` STRIP_ASSUME_TAC THENL
   [SCHZ_ND_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(sqrt(z0 - m) / sqrt(M - y)) % u:real^2 =
                sqrt(z0 - m) % (inv(sqrt(M - y)) % u)`
  (fun th -> REWRITE_TAC[th; schz_kmap]) THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC; real_div]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `Psi:real^1->real^3->real^3`; `zA':real`; `zB':real`;
                 `kap:real`; `inv(sqrt(M - y)) % u:real^2`; `y:real`] SCHZ_ND_TOP_NORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    UNDISCH_TAC `abs(norm(u:real^2) / sqrt(M - y) - &1) < kap` THEN
    REWRITE_TAC[real_div; REAL_MUL_SYM];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN REWRITE_TAC[NORM_POS_LE; ARITH] THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_POW_MUL; REAL_POW_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; SQRT_POW_2; REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `&0 < M - y` THEN CONV_TAC REAL_FIELD);;

(* K maps discs of radius near the rim radius into themselves.               *)

let SCHZ_KMAP_DISC = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap y rho u.
     schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap /\
     b2 <= y /\ y <= zB' /\ abs(rho / sqrt(M - y) - &1) < kap /\ norm u < rho
     ==> norm((sqrt(z0 - m) / sqrt(M - y)) % u) < r0 /\
         schz_slice Psi z0 y (ph0((sqrt(z0 - m) / sqrt(M - y)) % u)) IN
           IMAGE ph1 (ball(vec 0,rho)) /\
         rho < r1 /\
         norm(schz_kmap Psi ph0 ph1' m M z0 y u) < rho`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < M - y /\ &0 < sqrt(M - y) /\ &0 < z0 - m /\ &0 < sqrt(z0 - m)`
  STRIP_ASSUME_TAC THENL
   [SCHZ_ND_TAC THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SQRT_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `Psi:real^1->real^3->real^3`; `zA':real`; `zB':real`;
                 `kap:real`; `y:real`; `rho / sqrt(M - y)`] SCHZ_ND_TOP_DISC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt(M - y) * rho / sqrt(M - y) = rho` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sqrt(M - y)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `norm((sqrt(z0 - m) / sqrt(M - y)) % u:real^2) <
                sqrt(z0 - m) * rho / sqrt(M - y)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `&0 < sqrt(z0 - m) / sqrt(M - y)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    SUBGOAL_THEN `sqrt(z0 - m) * rho / sqrt(M - y) = (sqrt(z0 - m) / sqrt(M - y)) * rho`
    SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `schz_slice Psi z0 y ((ph0:real^2->real^2)((sqrt(z0 - m) / sqrt(M - y)) % u)) IN
                IMAGE (ph1:real^2->real^2) (ball(vec 0,rho))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) &&
      can (term_match [] `IMAGE (f:real^2->real^2) (IMAGE (g:real^2->real^2)
                            (ball(vec 0:real^2,r))) =
                          IMAGE (h:real^2->real^2) (ball(vec 0:real^2,rho))`) (concl th))) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_BALL_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `schz_slice Psi z0 y ((ph0:real^2->real^2)((sqrt(z0 - m) / sqrt(M - y)) % u)) IN
               IMAGE (ph1:real^2->real^2) (ball(vec 0,rho))` THEN
  REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[schz_kmap] THEN
  SCHZ_ND_TAC THEN
  SUBGOAL_THEN `(ph1':real^2->real^2)((ph1:real^2->real^2) k) = k` SUBST1_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(
      GEN_REWRITE_RULE I [diffeomorphism_on]
      (ASSUME `diffeomorphism_on (ball(vec 0,r1)) (IMAGE (ph1:real^2->real^2) (ball(vec 0,r1)))
                 ph1 ph1'`))))))) THEN
    REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* A radius t whose square is close to a has ratio t / sqrt a close to 1.    *)

let SCHZ_RATIO_NEAR1 = prove
 (`!t a kap. &0 < a /\ &0 < kap /\ &0 <= t /\ abs(t pow 2 - a) <= kap * a / &2
             ==> abs(t / sqrt a - &1) < kap`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt a /\ sqrt a pow 2 = a` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `t / sqrt a - &1 = (t - sqrt a) / sqrt a` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sqrt a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `abs(t - sqrt a) * sqrt a <= abs(t pow 2 - a)` ASSUME_TAC THENL
   [SUBGOAL_THEN `t pow 2 - a = (t - sqrt a) * (t + sqrt a)` SUBST1_TAC THENL
     [UNDISCH_TAC `sqrt a pow 2 = a` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `kap * a / &2 = (kap * sqrt a / &2) * sqrt a` ASSUME_TAC THENL
   [UNDISCH_TAC `sqrt a pow 2 = a` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `abs(t - sqrt a) <= kap * sqrt a / &2` MP_TAC THENL
   [SUBGOAL_THEN `abs(t - sqrt a) * sqrt a <= (kap * sqrt a / &2) * sqrt a` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LE_TRANS]; ASM_SIMP_TAC[REAL_LE_RMUL_EQ]];
    MP_TAC(SPECL [`kap:real`; `sqrt a`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

(* K is smooth on the disc of radius sqrt(M - zt), with values in it.        *)

let SCHZ_KMAP_SMOOTH = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap zt.
     schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap /\
     b2 <= zt /\ zt <= zB'
     ==> smooth_map_on (ball(vec 0,sqrt(M - zt))) (schz_kmap Psi ph0 ph1' m M z0 zt) /\
         (!u. u IN ball(vec 0,sqrt(M - zt))
              ==> norm(schz_kmap Psi ph0 ph1' m M z0 zt u) < sqrt(M - zt))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < M - zt /\ &0 < sqrt(M - zt)` STRIP_ASSUME_TAC THENL
   [SCHZ_ND_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:real^2. u IN ball(vec 0,sqrt(M - zt))
      ==> norm((sqrt(z0 - m) / sqrt(M - zt)) % u) < r0 /\
          schz_slice Psi z0 zt ((ph0:real^2->real^2)((sqrt(z0 - m) / sqrt(M - zt)) % u)) IN
            IMAGE (ph1:real^2->real^2) (ball(vec 0,sqrt(M - zt))) /\
          sqrt(M - zt) < r1 /\
          norm(schz_kmap Psi ph0 ph1' m M z0 zt u) < sqrt(M - zt)`
  (LABEL_TAC "KD") THENL
   [X_GEN_TAC `u:real^2` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    MATCH_MP_TAC SCHZ_KMAP_DISC THEN
    MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`;
      `zB:real`; `ph0':real^2->real^2`; `b1:real`; `b2:real`; `zA':real`; `zB':real`;
      `kap:real`] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; REAL_SUB_REFL; REAL_ABS_NUM] THEN
    SCHZ_ND_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; USE_THEN "KD" (fun th -> SIMP_TAC[th])] THEN
  SCHZ_ND_TAC THEN
  MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `z0:real`; `zt:real`] SCHZ_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  UNDISCH_TAC `diffeomorphism_on (ball(vec 0,r0)) (IMAGE (ph0:real^2->real^2) (ball(vec 0,r0)))
                 ph0 ph0'` THEN
  UNDISCH_TAC `diffeomorphism_on (ball(vec 0,r1)) (IMAGE (ph1:real^2->real^2) (ball(vec 0,r1)))
                 ph1 ph1'` THEN
  REWRITE_TAC[diffeomorphism_on] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `schz_kmap Psi (ph0:real^2->real^2) (ph1':real^2->real^2) m M z0 zt =
                ph1' o schz_slice Psi z0 zt o ph0 o (\u. (sqrt(z0 - m) / sqrt(M - zt)) % u)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; schz_kmap]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))` THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
    USE_THEN "KD" (MP_TAC o C MATCH_MP (ASSUME `(u:real^2) IN ball(vec 0,sqrt(M - zt))`)) THEN
    STRIP_TAC THEN
    UNDISCH_TAC `schz_slice Psi z0 zt ((ph0:real^2->real^2)((sqrt(z0 - m) / sqrt(M - zt)) % u)) IN
                 IMAGE (ph1:real^2->real^2) (ball(vec 0,sqrt(M - zt)))` THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^2) IN IMAGE (f:real^2->real^2) s ==>
                                           x IN IMAGE f t`) THEN
    MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
  ASM_REWRITE_TAC[OPEN_BALL; OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `ball(vec 0:real^2,r0)` THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `u:real^2` THEN
    DISCH_TAC THEN
    USE_THEN "KD" (MP_TAC o C MATCH_MP (ASSUME `(u:real^2) IN ball(vec 0,sqrt(M - zt))`)) THEN
    SIMP_TAC[IN_BALL_0];
    ASSUME_TAC(INST_TYPE [`:2`,`:N`] OPEN_UNIV) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN SCHZ_SMOOTH_TAC]);;

let SCHZ_NORM_LT_SQRT = prove
 (`!(v:real^2) c. &0 <= c ==> (norm v < sqrt c <=> norm v pow 2 < c)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `c = sqrt c pow 2` SUBST1_TAC THENL
     [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN ARITH_TAC;
    MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]]);;

(* L vanishes near and beyond the rim.                                       *)

let SCHZ_LFUN_RIM = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap zt s1 u.
     schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap /\
     b2 <= zt /\ zt <= zB' /\ &0 < s1 /\ s1 <= kap * (M - zt) / &2 /\
     M - zt - s1 <= norm u pow 2
     ==> schz_lfun Psi ph0 ph1' m M z0 zt s1 u = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[schz_lfun] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < M - zt` ASSUME_TAC THENL [SCHZ_ND_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `Psi:real^1->real^3->real^3`; `zA':real`; `zB':real`;
                 `kap:real`; `zt:real`; `u:real^2`] SCHZ_KMAP_NORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCHZ_RATIO_NEAR1 THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN
    CONJ_TAC THENL [SCHZ_ND_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < M - zt - norm(u:real^2) pow 2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; LOG_1]);;

(* L is smooth.                                                              *)

let SCHZ_LFUN_SMOOTH = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap zt s1.
     schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap /\
     b2 <= zt /\ zt <= zB' /\ &0 < s1 /\ s1 <= kap * (M - zt) / &2
     ==> smooth_map_on (:real^2) (\u. lift(schz_lfun Psi ph0 ph1' m M z0 zt s1 u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < M - zt /\ &0 < kap /\ kap <= &1 / &2` STRIP_ASSUME_TAC THENL
   [SCHZ_ND_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s1 < M - zt` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `kap * (M - zt) / &2` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a /\ k * a <= a / &2 ==> k * a / &2 < a`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `k * a <= (&1 / &2) * a ==> k * a <= a / &2`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `Psi:real^1->real^3->real^3`; `zA':real`; `zB':real`;
                 `kap:real`; `zt:real`] SCHZ_KMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KB")) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `u:real^2` THEN
  ASM_CASES_TAC `norm(u:real^2) pow 2 < M - zt - s1 / &2` THENL
   [EXISTS_TAC `ball(vec 0:real^2,sqrt(M - zt - s1 / &2))` THEN
    REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
    SUBGOAL_THEN `&0 <= M - zt - s1 / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SCHZ_NORM_LT_SQRT] THEN
    SUBGOAL_THEN `ball(vec 0:real^2,sqrt(M - zt - s1 / &2)) SUBSET ball(vec 0,sqrt(M - zt))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\v:real^2. lift(log((M - zt - norm(schz_kmap Psi (ph0:real^2->real^2)
                                       (ph1':real^2->real^2) m M z0 zt v) pow 2) /
                                    (M - zt - norm v pow 2)))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `v:real^2` THEN REWRITE_TAC[IN_BALL_0] THEN ASM_SIMP_TAC[SCHZ_NORM_LT_SQRT] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[schz_lfun];
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on (ball(vec 0:real^2,sqrt(M - zt - s1 / &2)))
                    (schz_kmap Psi (ph0:real^2->real^2) (ph1':real^2->real^2) m M z0 zt)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,sqrt(M - zt))` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASSUME_TAC(ISPECL [`vec 0:real^2`; `sqrt(M - zt - s1 / &2)`] OPEN_BALL) THEN
    SUBGOAL_THEN `!v:real^2. v IN ball(vec 0,sqrt(M - zt - s1 / &2))
                   ==> norm(schz_kmap Psi (ph0:real^2->real^2) (ph1':real^2->real^2)
                              m M z0 zt v) pow 2 < M - zt /\
                       norm v pow 2 < M - zt - s1 / &2` (LABEL_TAC "PV") THENL
     [X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
       [SUBGOAL_THEN `norm(schz_kmap Psi (ph0:real^2->real^2) (ph1':real^2->real^2)
                             m M z0 zt v) < sqrt(M - zt)` MP_TAC THENL
         [USE_THEN "KB" MATCH_MP_TAC THEN ASM SET_TAC[];
          ASM_SIMP_TAC[SCHZ_NORM_LT_SQRT; REAL_LT_IMP_LE]];
        UNDISCH_TAC `(v:real^2) IN ball(vec 0,sqrt(M - zt - s1 / &2))` THEN
        ASM_SIMP_TAC[IN_BALL_0; SCHZ_NORM_LT_SQRT]];
      ALL_TAC] THEN
    SCHZ_SMOOTH_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> USE_THEN "PV" (STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
    TRY(MATCH_MP_TAC REAL_LT_DIV) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(:real^2) DIFF cball(vec 0,sqrt(M - zt - s1))` THEN
  SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; IN_CBALL_0; REAL_NOT_LE] THEN
  SUBGOAL_THEN `&0 <= M - zt - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^2. sqrt(M - zt - s1) < norm v <=> M - zt - s1 < norm v pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `M - zt - s1 = sqrt(M - zt - s1) pow 2` SUBST1_TAC THENL
       [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\v:real^2. lift(&0)` THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_CBALL_0; REAL_NOT_LE] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`2`; `sqrt(M - zt - s1)`; `norm(v:real^2)`] REAL_POW_LT2) THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; ARITH] THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_EQ] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCHZ_LFUN_RIM THEN
    MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`;
      `zB:real`; `r0:real`; `ph0':real^2->real^2`; `r1:real`; `ph1:real^2->real^2`;
      `b1:real`; `b2:real`; `zA':real`; `zB':real`; `kap:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open((:real^2) DIFF cball(vec 0,sqrt(M - zt - s1)))` ASSUME_TAC THENL
   [SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL]; ALL_TAC] THEN
  SCHZ_SMOOTH_TAC);;

(* The top cap piece Kp o VS o T1 has a smooth left inverse.                *)

let SCHZ_TOP_LIP = prove
 (`!(Psi:real^1->real^3->real^3) (ph0:real^2->real^2) ph0' r0 m M z0 zt e
    (Xi:real^1->real^1->real^1) (L:real^2->real).
     (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
     (!t x. (Psi t x)$3 = x$3 + drop t) /\
     smooth_map_on (:real^(1,3)finite_sum) (\w. Psi (fstcart w) (sndcart w)) /\
     diffeomorphism_on (ball(vec 0,r0)) (IMAGE ph0 (ball(vec 0,r0))) ph0 ph0' /\
     m < z0 /\ &0 < e /\ zt < M /\
     (!z. Xi (vec 0) z = z) /\ (!z s t. Xi t (Xi s z) = Xi (s + t) z) /\
     smooth_map_on (:real^(1,1)finite_sum) (\w. Xi (fstcart w) (sndcart w)) /\
     smooth_map_on (:real^2) (\u. lift(L u))
     ==> ?E3 g. schz_lip {x:real^3 | x IN {x | m < x$3} /\
                            (schz_vs Xi L o schz_t1 m) x IN
                            {y:real^3 | y IN (:real^3) /\
                              (sqrt(z0 - m) / sqrt(M - schz_ramp (zt - e) e zt (y$3))) %
                              sch5v_pr y IN ball(vec 0,r0)}}
                        E3 (schz_kp Psi ph0 m M z0 zt e o (schz_vs Xi L o schz_t1 m)) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `m:real` SCHZ_T1_LIP) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Xi:real^1->real^1->real^1`; `L:real^2->real`] SCHZ_VS_LIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`schz_t1 m`; `schz_t1i m`; `{x:real^3 | m < x$3}`; `{q:real^3 | m < q$3}`;
                 `schz_vs Xi (L:real^2->real)`; `schz_vs Xi (\u. --((L:real^2->real) u))`;
                 `(:real^3)`; `(:real^3)`] SCHZ_LIP_COMPOSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_UNIV]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `ph0:real^2->real^2`; `ph0':real^2->real^2`;
                 `r0:real`; `m:real`; `M:real`; `z0:real`; `zt:real`; `e:real`] SCHZ_KP_LIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `DK = {y:real^3 | y IN (:real^3) /\
                     (sqrt(z0 - m) / sqrt(M - schz_ramp (zt - e) e zt (y$3))) %
                     sch5v_pr y IN ball(vec 0,r0)}` THEN
  ABBREV_TAC `E12 = {q:real^3 | q IN (:real^3) /\
                       schz_vs Xi (\u. --((L:real^2->real) u)) q IN {q:real^3 | m < q$3}}` THEN
  ABBREV_TAC `D3 = {x:real^3 | x IN {x | m < x$3} /\
                     (schz_vs Xi (L:real^2->real) o schz_t1 m) x IN DK}` THEN
  SUBGOAL_THEN `schz_lip (D3:real^3->bool) E12 (schz_vs Xi (L:real^2->real) o schz_t1 m)
                  (schz_t1i m o schz_vs Xi (\u. --(L u)))` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHZ_LIP_SUBSET THEN EXISTS_TAC `{x:real^3 | m < x$3}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "D3" THEN MATCH_MP_TAC SCHZ_OPEN_PRE THEN
      UNDISCH_TAC `schz_lip {x:real^3 | m < x$3} E12
                     (schz_vs Xi (L:real^2->real) o schz_t1 m)
                     (schz_t1i m o schz_vs Xi (\u. --(L u)))` THEN
      UNDISCH_TAC `schz_lip DK
                     {q:real^3 | q IN (:real^3) /\
                       schz_slice Psi (schz_ramp (zt - e) e zt (q$3)) z0 (sch5v_pr q) IN
                       IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}
                     (schz_kp Psi ph0 m M z0 zt e) (schz_kpi Psi ph0' m M z0 zt e)` THEN
      SIMP_TAC[schz_lip; ETA_AX];
      EXPAND_TAC "D3" THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`schz_vs Xi (L:real^2->real) o schz_t1 m`;
                 `schz_t1i m o schz_vs Xi (\u. --((L:real^2->real) u))`;
                 `D3:real^3->bool`; `E12:real^3->bool`;
                 `schz_kp Psi (ph0:real^2->real^2) m M z0 zt e`;
                 `schz_kpi Psi (ph0':real^2->real^2) m M z0 zt e`; `DK:real^3->bool`;
                 `{q:real^3 | q IN (:real^3) /\
                     schz_slice Psi (schz_ramp (zt - e) e zt (q$3)) z0 (sch5v_pr q) IN
                     IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}`] SCHZ_LIP_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "D3" THEN SET_TAC[];
    DISCH_TAC] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  EXISTS_TAC `(schz_t1i m o schz_vs Xi (\u. --((L:real^2->real) u))) o
              schz_kpi Psi (ph0':real^2->real^2) m M z0 zt e` THEN
  EXISTS_TAC `{q:real^3 | q IN {q:real^3 | q IN (:real^3) /\
                     schz_slice Psi (schz_ramp (zt - e) e zt (q$3)) z0 (sch5v_pr q) IN
                     IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))} /\
                   schz_kpi Psi ph0' m M z0 zt e q IN E12}` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Gluing three pieces with smooth left inverses on                          *)
(* overlapping height bands.  The glued map is smooth, has an invertible    *)
(* derivative, and is injective when the pieces preserve heights below hT    *)
(* and the top piece moves heights above hT to heights above hT.            *)
(* ------------------------------------------------------------------------- *)

let schz_gset = new_definition
 `schz_gset (D1:real^3->bool) D2 D3 a1 a2 tau =
    ({x:real^3 | a1 + tau / &2 < x$3} UNION D1) INTER
    ({x | x$3 < a1 - tau / &2} UNION {x | a2 + tau / &2 < x$3} UNION D2) INTER
    ({x | x$3 < a2 - tau / &2} UNION D3)`;;

let schz_gmap = new_definition
 `schz_gmap (P1:real^3->real^3) P2 P3 a1 a2 (x:real^3) =
    if x$3 < a1 then P1 x else if x$3 < a2 then P2 x else P3 x`;;

let SCHZ_GSET_FACTS = prove
 (`!(D1:real^3->bool) D2 D3 a1 a2 tau x.
     &0 < tau /\ a1 + tau < a2 - tau /\ x IN schz_gset D1 D2 D3 a1 a2 tau
     ==> (x$3 <= a1 + tau / &2 ==> x IN D1) /\
         (a1 - tau / &2 <= x$3 /\ x$3 <= a2 + tau / &2 ==> x IN D2) /\
         (a2 - tau / &2 <= x$3 ==> x IN D3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schz_gset; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN DISCH_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC));;

let SCHZ_GSET_OPEN = prove
 (`!(D1:real^3->bool) D2 D3 a1 a2 tau.
     open D1 /\ open D2 /\ open D3 ==> open(schz_gset D1 D2 D3 a1 a2 tau)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[schz_gset] THEN
  REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC OPEN_UNION THEN CONJ_TAC) THEN
  ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; GSYM real_gt;
                  OPEN_HALFSPACE_COMPONENT_GT]);;

let SCHZ_GLUE_LOCAL = prove
 (`!(P1:real^3->real^3) P2 P3 D1 D2 D3 a1 a2 tau x.
     open D1 /\ open D2 /\ open D3 /\ &0 < tau /\ a1 + tau < a2 - tau /\
     (!x. x IN D1 /\ x IN D2 /\ abs(x$3 - a1) < tau ==> P1 x = P2 x) /\
     (!x. x IN D2 /\ x IN D3 /\ abs(x$3 - a2) < tau ==> P2 x = P3 x) /\
     x IN schz_gset D1 D2 D3 a1 a2 tau
     ==> ?N. open N /\ x IN N /\ N SUBSET schz_gset D1 D2 D3 a1 a2 tau /\
             ((N SUBSET D1 /\ !y. y IN N ==> schz_gmap P1 P2 P3 a1 a2 y = P1 y) \/
              (N SUBSET D2 /\ !y. y IN N ==> schz_gmap P1 P2 P3 a1 a2 y = P2 y) \/
              (N SUBSET D3 /\ !y. y IN N ==> schz_gmap P1 P2 P3 a1 a2 y = P3 y))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "A1") (CONJUNCTS_THEN2 (LABEL_TAC "A2") ASSUME_TAC))))))) THEN
  ABBREV_TAC `U = schz_gset (D1:real^3->bool) D2 D3 a1 a2 tau` THEN
  SUBGOAL_THEN `open(U:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC SCHZ_GSET_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN U
                 ==> (y$3 <= a1 + tau / &2 ==> y IN D1) /\
                     (a1 - tau / &2 <= y$3 /\ y$3 <= a2 + tau / &2 ==> y IN D2) /\
                     (a2 - tau / &2 <= y$3 ==> y IN D3)` (LABEL_TAC "GF") THENL
   [X_GEN_TAC `y:real^3` THEN EXPAND_TAC "U" THEN DISCH_TAC THEN
    MATCH_MP_TAC SCHZ_GSET_FACTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^3)$3 < a1 + tau / &2` THENL
   [EXISTS_TAC `U INTER {y:real^3 | y$3 < a1 + tau / &2}` THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_LT; IN_INTER; IN_ELIM_THM] THEN
    REWRITE_TAC[INTER_SUBSET] THEN DISJ1_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      USE_THEN "GF" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN U`)) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "GF" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN U`)) THEN STRIP_TAC THEN
    REWRITE_TAC[schz_gmap] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^3)$3 < a2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN USE_THEN "A1" MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^3)$3 < a2 + tau / &2` THENL
   [EXISTS_TAC `U INTER {y:real^3 | a1 - tau / &2 < y$3 /\ y$3 < a2 + tau / &2}` THEN
    SUBGOAL_THEN `open {y:real^3 | a1 - tau / &2 < y$3 /\ y$3 < a2 + tau / &2}` ASSUME_TAC THENL
     [SUBGOAL_THEN `{y:real^3 | a1 - tau / &2 < y$3 /\ y$3 < a2 + tau / &2} =
                    {y | y$3 > a1 - tau / &2} INTER {y | y$3 < a2 + tau / &2}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_INTER THEN
      REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_INTER; IN_INTER; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INTER_SUBSET] THEN DISJ2_TAC THEN DISJ1_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      USE_THEN "GF" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN U`)) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "GF" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN U`)) THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN D2` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `a <= (y:real^3)$3 /\ y$3 <= b ==> y IN (D2:real^3->bool)`) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[schz_gmap] THEN COND_CASES_TAC THENL
     [USE_THEN "A1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `(y:real^3)$3 <= a ==> y IN (D1:real^3->bool)`) (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    USE_THEN "A2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `a <= (y:real^3)$3 ==> y IN (D3:real^3->bool)`) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `U INTER {y:real^3 | y$3 > a2 - tau / &2}` THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_GT; IN_INTER; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INTER_SUBSET] THEN DISJ2_TAC THEN DISJ2_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; real_gt] THEN X_GEN_TAC `y:real^3` THEN
    STRIP_TAC THEN
    USE_THEN "GF" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN U`)) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt] THEN STRIP_TAC THEN
  USE_THEN "GF" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN U`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((y:real^3)$3 < a1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[schz_gmap] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "A2" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `a <= (y:real^3)$3 /\ y$3 <= b ==> y IN (D2:real^3->bool)`) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `a <= (y:real^3)$3 ==> y IN (D3:real^3->bool)`) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SCHZ_GLUE_HEIGHT = prove
 (`!(P1:real^3->real^3) P2 P3 D1 D2 D3 a1 a2 tau hT y.
     &0 < tau /\ a1 + tau < a2 - tau /\ a2 < hT /\
     (!x. x IN D1 ==> (P1 x)$3 = x$3) /\
     (!x. x IN D2 ==> (P2 x)$3 = x$3) /\
     (!x. x IN D3 /\ x$3 <= hT ==> (P3 x)$3 = x$3) /\
     (!x. x IN D3 /\ hT < x$3 ==> hT < (P3 x)$3) /\
     y IN schz_gset D1 D2 D3 a1 a2 tau
     ==> (y$3 < a1 ==> y IN D1 /\ schz_gmap P1 P2 P3 a1 a2 y = P1 y) /\
         (a1 <= y$3 /\ y$3 < a2 ==> y IN D2 /\ schz_gmap P1 P2 P3 a1 a2 y = P2 y) /\
         (a2 <= y$3 ==> y IN D3 /\ schz_gmap P1 P2 P3 a1 a2 y = P3 y) /\
         (y$3 <= hT ==> (schz_gmap P1 P2 P3 a1 a2 y)$3 = y$3) /\
         (hT < y$3 ==> hT < (schz_gmap P1 P2 P3 a1 a2 y)$3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`D1:real^3->bool`; `D2:real^3->bool`; `D3:real^3->bool`; `a1:real`;
                 `a2:real`; `tau:real`; `y:real^3`] SCHZ_GSET_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((y:real^3)$3 < a1 ==> y IN D1 /\ schz_gmap P1 P2 P3 a1 a2 y = P1 y) /\
                (a1 <= y$3 /\ y$3 < a2 ==> y IN D2 /\ schz_gmap P1 P2 P3 a1 a2 y = P2 y) /\
                (a2 <= y$3 ==> y IN D3 /\ schz_gmap P1 P2 P3 a1 a2 y = P3 y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[schz_gmap] THEN REPEAT CONJ_TAC THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `a <= (y:real^3)$3 /\ y$3 <= b ==> y IN (D2:real^3->bool)`) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~((y:real^3)$3 < a1) /\ ~(y$3 < a2)` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `a <= (y:real^3)$3 ==> y IN (D3:real^3->bool)`) (concl th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_TAC THENL
   [ASM_CASES_TAC `(y:real^3)$3 < a1` THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^3)$3 < a1`)) THEN
      STRIP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(y:real^3)$3 < a2` THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (CONJ (REWRITE_RULE[REAL_NOT_LT]
        (ASSUME `~((y:real^3)$3 < a1)`)) (ASSUME `(y:real^3)$3 < a2`))) THEN
      STRIP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (REWRITE_RULE[REAL_NOT_LT]
      (ASSUME `~((y:real^3)$3 < a2)`))) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN `a2 <= (y:real^3)$3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `a2 <= (y:real^3)$3`)) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[]]);;

let SCHZ_GLUE3 = prove
 (`!(P1:real^3->real^3) P2 P3 D1 D2 D3 E1 E2 E3 Q1 Q2 Q3 a1 a2 tau hT.
     schz_lip D1 E1 P1 Q1 /\ schz_lip D2 E2 P2 Q2 /\ schz_lip D3 E3 P3 Q3 /\
     &0 < tau /\ a1 + tau < a2 - tau /\ a2 < hT /\
     (!x. x IN D1 /\ x IN D2 /\ abs(x$3 - a1) < tau ==> P1 x = P2 x) /\
     (!x. x IN D2 /\ x IN D3 /\ abs(x$3 - a2) < tau ==> P2 x = P3 x) /\
     (!x. x IN D1 ==> (P1 x)$3 = x$3) /\
     (!x. x IN D2 ==> (P2 x)$3 = x$3) /\
     (!x. x IN D3 /\ x$3 <= hT ==> (P3 x)$3 = x$3) /\
     (!x. x IN D3 /\ hT < x$3 ==> hT < (P3 x)$3)
     ==> open(schz_gset D1 D2 D3 a1 a2 tau) /\
         smooth_map_on (schz_gset D1 D2 D3 a1 a2 tau) (schz_gmap P1 P2 P3 a1 a2) /\
         (!x y. x IN schz_gset D1 D2 D3 a1 a2 tau /\ y IN schz_gset D1 D2 D3 a1 a2 tau /\
                schz_gmap P1 P2 P3 a1 a2 x = schz_gmap P1 P2 P3 a1 a2 y ==> x = y) /\
         (!x. x IN schz_gset D1 D2 D3 a1 a2 tau
              ==> ~(det(matrix(frechet_derivative (schz_gmap P1 P2 P3 a1 a2) (at x))) =
                    &0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L1") (CONJUNCTS_THEN2 (LABEL_TAC "L2")
    (CONJUNCTS_THEN2 (LABEL_TAC "L3") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `open(D1:real^3->bool) /\ open(D2:real^3->bool) /\ open(D3:real^3->bool) /\
                smooth_map_on D1 (P1:real^3->real^3) /\ smooth_map_on D2 (P2:real^3->real^3) /\
                smooth_map_on D3 (P3:real^3->real^3)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun l -> USE_THEN l (MP_TAC o GEN_REWRITE_RULE I [schz_lip])) ["L1";"L2";"L3"] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `U = schz_gset (D1:real^3->bool) D2 D3 a1 a2 tau` THEN
  ABBREV_TAC `Th = schz_gmap (P1:real^3->real^3) P2 P3 a1 a2` THEN
  SUBGOAL_THEN `open(U:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC SCHZ_GSET_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN U
      ==> ?N P D E Q. open N /\ x IN N /\ N SUBSET U /\ N SUBSET D /\
                      schz_lip D E P Q /\ !y. y IN N ==> (Th:real^3->real^3) y = P y`
  (LABEL_TAC "LOC") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`P1:real^3->real^3`; `P2:real^3->real^3`; `P3:real^3->real^3`;
                   `D1:real^3->bool`; `D2:real^3->bool`; `D3:real^3->bool`;
                   `a1:real`; `a2:real`; `tau:real`; `x:real^3`] SCHZ_GLUE_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
    STRIP_TAC THEN EXISTS_TAC `N:real^3->bool` THENL
     [MAP_EVERY EXISTS_TAC [`P1:real^3->real^3`; `D1:real^3->bool`; `E1:real^3->bool`;
                            `Q1:real^3->real^3`];
      MAP_EVERY EXISTS_TAC [`P2:real^3->real^3`; `D2:real^3->bool`; `E2:real^3->bool`;
                            `Q2:real^3->real^3`];
      MAP_EVERY EXISTS_TAC [`P3:real^3->real^3`; `D3:real^3->bool`; `E3:real^3->bool`;
                            `Q3:real^3->real^3`]] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "LOC" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN U`)) THEN
    REWRITE_TAC[schz_lip] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `P:real^3->real^3`
      (X_CHOOSE_THEN `D:real^3->bool` (X_CHOOSE_THEN `E:real^3->bool`
      (X_CHOOSE_THEN `Q:real^3->real^3` STRIP_ASSUME_TAC))))) THEN
    EXISTS_TAC `N:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `P:real^3->real^3` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `D:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC;
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "LOC" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN U`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `P:real^3->real^3`
      (X_CHOOSE_THEN `D:real^3->bool` (X_CHOOSE_THEN `E:real^3->bool`
      (X_CHOOSE_THEN `Q:real^3->real^3` STRIP_ASSUME_TAC))))) THEN
    SUBGOAL_THEN `(x:real^3) IN D` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `frechet_derivative (Th:real^3->real^3) (at x) =
                  frechet_derivative (P:real^3->real^3) (at x)` SUBST1_TAC THENL
     [MATCH_MP_TAC SCHZ_FD_LOCAL_EQ THEN EXISTS_TAC `N:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `D:real^3->bool` THEN
      UNDISCH_TAC `schz_lip D E (P:real^3->real^3) Q` THEN SIMP_TAC[schz_lip] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SCHZ_LIP_DET THEN
      MAP_EVERY EXISTS_TAC [`Q:real^3->real^3`; `D:real^3->bool`; `E:real^3->bool`] THEN
      ASM_REWRITE_TAC[]]] THEN
  (* injectivity *)
  SUBGOAL_THEN
   `!y:real^3. y IN U
      ==> (y$3 < a1 ==> y IN D1 /\ (Th:real^3->real^3) y = P1 y) /\
          (a1 <= y$3 /\ y$3 < a2 ==> y IN D2 /\ Th y = P2 y) /\
          (a2 <= y$3 ==> y IN D3 /\ Th y = P3 y) /\
          (y$3 <= hT ==> (Th y)$3 = y$3) /\
          (hT < y$3 ==> hT < (Th y)$3)` (LABEL_TAC "HT") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXPAND_TAC "Th" THEN
    MATCH_MP_TAC SCHZ_GLUE_HEIGHT THEN
    MAP_EVERY EXISTS_TAC [`tau:real`] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3)$3 = (y:real^3)$3 \/ (hT < x$3 /\ hT < y$3)` MP_TAC THENL
   [USE_THEN "HT" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^3) IN U`))) THEN
    MATCH_MP_TAC(TAUT `(d /\ e ==> g) ==> a /\ b /\ c /\ d /\ e ==> g`) THEN
    USE_THEN "HT" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^3) IN U`))) THEN
    MATCH_MP_TAC(TAUT `(d /\ e ==> g) ==> a /\ b /\ c /\ d /\ e ==> g`) THEN
    MP_TAC(AP_TERM `\z:real^3. z$3` (ASSUME `(Th:real^3->real^3) x = Th y`)) THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SCHZ_LIP_INJ THEN
    MAP_EVERY EXISTS_TAC [`P3:real^3->real^3`; `Q3:real^3->real^3`; `D3:real^3->bool`;
                          `E3:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a2 <= (x:real^3)$3 /\ a2 <= (y:real^3)$3` STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `a2 < hT`) THEN MP_TAC(ASSUME `hT < (x:real^3)$3`) THEN
      MP_TAC(ASSUME `hT < (y:real^3)$3`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "HT" (fun th ->
      MP_TAC(MP (CONJUNCT1(CONJUNCT2(CONJUNCT2(MATCH_MP th (ASSUME `(x:real^3) IN U`)))))
                (ASSUME `a2 <= (x:real^3)$3`)) THEN
      MP_TAC(MP (CONJUNCT1(CONJUNCT2(CONJUNCT2(MATCH_MP th (ASSUME `(y:real^3) IN U`)))))
                (ASSUME `a2 <= (y:real^3)$3`))) THEN
    MP_TAC(ASSUME `(Th:real^3->real^3) x = Th y`) THEN MESON_TAC[]] THEN
  ASM_CASES_TAC `(x:real^3)$3 < a1` THENL
   [MATCH_MP_TAC SCHZ_LIP_INJ THEN
    MAP_EVERY EXISTS_TAC [`P1:real^3->real^3`; `Q1:real^3->real^3`; `D1:real^3->bool`;
                          `E1:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^3)$3 < a1` ASSUME_TAC THENL
     [MP_TAC(ASSUME `(x:real^3)$3 = (y:real^3)$3`) THEN MP_TAC(ASSUME `(x:real^3)$3 < a1`) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "HT" (fun th ->
      MP_TAC(MP (CONJUNCT1(MATCH_MP th (ASSUME `(x:real^3) IN U`)))
                (ASSUME `(x:real^3)$3 < a1`)) THEN
      MP_TAC(MP (CONJUNCT1(MATCH_MP th (ASSUME `(y:real^3) IN U`)))
                (ASSUME `(y:real^3)$3 < a1`))) THEN
    MP_TAC(ASSUME `(Th:real^3->real^3) x = Th y`) THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^3)$3 < a2` THENL
   [MATCH_MP_TAC SCHZ_LIP_INJ THEN
    MAP_EVERY EXISTS_TAC [`P2:real^3->real^3`; `Q2:real^3->real^3`; `D2:real^3->bool`;
                          `E2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a1 <= (x:real^3)$3 /\ a1 <= (y:real^3)$3 /\ y$3 < a2` STRIP_ASSUME_TAC THENL
     [MP_TAC(ASSUME `(x:real^3)$3 = (y:real^3)$3`) THEN MP_TAC(ASSUME `~((x:real^3)$3 < a1)`) THEN
      MP_TAC(ASSUME `(x:real^3)$3 < a2`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "HT" (fun th ->
      MP_TAC(MP (CONJUNCT1(CONJUNCT2(MATCH_MP th (ASSUME `(x:real^3) IN U`))))
                (CONJ (ASSUME `a1 <= (x:real^3)$3`) (ASSUME `(x:real^3)$3 < a2`))) THEN
      MP_TAC(MP (CONJUNCT1(CONJUNCT2(MATCH_MP th (ASSUME `(y:real^3) IN U`))))
                (CONJ (ASSUME `a1 <= (y:real^3)$3`) (ASSUME `(y:real^3)$3 < a2`)))) THEN
    MP_TAC(ASSUME `(Th:real^3->real^3) x = Th y`) THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SCHZ_LIP_INJ THEN
  MAP_EVERY EXISTS_TAC [`P3:real^3->real^3`; `Q3:real^3->real^3`; `D3:real^3->bool`;
                        `E3:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a2 <= (x:real^3)$3 /\ a2 <= (y:real^3)$3` STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `(x:real^3)$3 = (y:real^3)$3`) THEN MP_TAC(ASSUME `~((x:real^3)$3 < a2)`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "HT" (fun th ->
    MP_TAC(MP (CONJUNCT1(CONJUNCT2(CONJUNCT2(MATCH_MP th (ASSUME `(x:real^3) IN U`)))))
              (ASSUME `a2 <= (x:real^3)$3`)) THEN
    MP_TAC(MP (CONJUNCT1(CONJUNCT2(CONJUNCT2(MATCH_MP th (ASSUME `(y:real^3) IN U`)))))
              (ASSUME `a2 <= (y:real^3)$3`))) THEN
  MP_TAC(ASSUME `(Th:real^3->real^3) x = Th y`) THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Helper facts for the assembly of the model chart: the 1D                  *)
(* stretch Xi keeps heights above its fixed band, zeta o Xi = zeta, bounds  *)
(* for the time ramp psi, and the round model ball in (v, z) coordinates.    *)
(* ------------------------------------------------------------------------- *)

let SCHZ_XI_ABOVE = prove
 (`!(Xi:real^1->real^1->real^1) c t z.
     (!t z. drop z <= c ==> Xi t z = z) /\
     (!t. diffeomorphism_on (:real^1) (:real^1) (Xi t) (Xi (--t))) /\
     c < drop z
     ==> c < drop(Xi t z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Xi:real^1->real^1->real^1) (--t) (Xi t z) = z` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th -> is_forall(concl th) &&
      can (term_match [] `diffeomorphism_on s t' (f:real^1->real^1) g`) (snd(dest_forall(concl th))))) THEN
    REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `drop((Xi:real^1->real^1->real^1) t z) <= c` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let SCHZ_ZETA_XI = prove
 (`!(Xi:real^1->real^1->real^1) e zt e1 t z.
     &0 < e /\ &0 < e1 /\
     (!t z. drop z <= zt + e1 ==> Xi t z = z) /\
     (!t. diffeomorphism_on (:real^1) (:real^1) (Xi t) (Xi (--t)))
     ==> schz_ramp (zt - e) e zt (drop(Xi t z)) = schz_ramp (zt - e) e zt (drop z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `drop z <= zt + e1` THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`Xi:real^1->real^1->real^1`; `zt + e1`; `t:real^1`; `z:real^1`]
    SCHZ_XI_ABOVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`zt - e`; `e:real`; `zt:real`; `drop((Xi:real^1->real^1->real^1) t z)`]
    SCHZ_RAMP) THEN
  MP_TAC(ISPECL [`zt - e`; `e:real`; `zt:real`; `drop(z:real^1)`] SCHZ_RAMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

let SCHZ_PSI_BOUNDS = prove
 (`!z0 eta z.
     &0 < eta
     ==> schz_ramp z0 eta z0 z <= z0 + eta /\
         (z <= z0 ==> schz_ramp z0 eta z0 z = z) /\
         (z0 + eta <= z ==> schz_ramp z0 eta z0 z = z0) /\
         (z0 <= z ==> z0 <= schz_ramp z0 eta z0 z /\ schz_ramp z0 eta z0 z <= z) /\
         min z z0 <= schz_ramp z0 eta z0 z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`z0:real`; `eta:real`; `z0:real`; `z:real`] SCHZ_RAMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `z <= z0` THENL
   [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `z0 + eta <= z` THENL
   [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The round model ball with poles at heights m and M.                       *)

let SCHZ_NORM_SPLIT = prove
 (`!x:real^3. norm x pow 2 = norm(sch5v_pr x) pow 2 + x$3 pow 2`,
  REWRITE_TAC[NORM_POW_2; DOT_3; DOT_2; sch5v_pr; VECTOR_2] THEN REAL_ARITH_TAC);;

let SCHZ_MODEL_BALL = prove
 (`!m M (x:real^3).
     m < M
     ==> (x IN cball(sch5v_at ((m + M) / &2) (vec 0),(M - m) / &2) <=>
          norm(sch5v_pr x) pow 2 <= (x$3 - m) * (M - x$3)) /\
         (x IN sphere(sch5v_at ((m + M) / &2) (vec 0),(M - m) / &2) <=>
          norm(sch5v_pr x) pow 2 = (x$3 - m) * (M - x$3)) /\
         (norm(sch5v_pr x) pow 2 <= (x$3 - m) * (M - x$3) ==> m <= x$3 /\ x$3 <= M)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `dist(sch5v_at ((m + M) / &2) (vec 0),x:real^3) pow 2 =
                norm(sch5v_pr x) pow 2 + (x$3 - (m + M) / &2) pow 2` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist; SCHZ_NORM_SPLIT] THEN
    SUBGOAL_THEN `sch5v_pr(x - sch5v_at ((m + M) / &2) (vec 0)) = sch5v_pr(x:real^3)`
    SUBST1_TAC THENL
     [MP_TAC(CONJUNCT1 SCH5V_PR_AT_SMOOTH) THEN DISCH_THEN(fun th ->
        REWRITE_TAC[MATCH_MP LINEAR_SUB th]) THEN
      REWRITE_TAC[SCH5V_PR_AT; VECTOR_SUB_RZERO];
      REWRITE_TAC[VECTOR_SUB_COMPONENT; SCH5V_PR_AT]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_CBALL; IN_SPHERE] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`dist(sch5v_at ((m + M) / &2) (vec 0),x:real^3)`; `(M - m) / &2`]
      REAL_LE_SQUARE_ABS) THEN
    REWRITE_TAC[REAL_ABS_DIST] THEN
    SUBGOAL_THEN `abs((M - m) / &2) = (M - m) / &2` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`dist(sch5v_at ((m + M) / &2) (vec 0),x:real^3)`; `(M - m) / &2`]
      REAL_EQ_SQUARE_ABS) THEN
    REWRITE_TAC[REAL_ABS_DIST] THEN
    SUBGOAL_THEN `abs((M - m) / &2) = (M - m) / &2` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= ((x:real^3)$3 - m) * (M - x$3)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(sch5v_pr(x:real^3)) pow 2` THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:real^3)$3 < m` THENL
     [SUBGOAL_THEN `((x:real^3)$3 - m) * (M - x$3) < &0` MP_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < (m - x) * y ==> (x - m) * y < &0`) THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `M < (x:real^3)$3` THENL
     [SUBGOAL_THEN `((x:real^3)$3 - m) * (M - x$3) < &0` MP_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < x * (y - M) ==> x * (M - y) < &0`) THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC]]);;

(* All the parameters of the model chart.                                    *)

let schz_pdata = new_definition
 `schz_pdata (S:real^3->bool) (Psi0:real^1->real^3->real^3) zA zB m r0
             (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
             (Psi:real^1->real^3->real^3) zA' zB' kap eta zt e e1 s1 tau
             (Xi:real^1->real^1->real^1) <=>
    schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap /\
    &0 < eta /\ z0 + eta - m < r0 pow 2 /\ z0 + eta - m < r0 /\
    b2 < zt /\ zt < zB' /\
    &0 < e /\ e <= kap * (M - zt) / &4 /\ b2 + &3 * e < zt /\ z0 + eta + &3 * e <= zt /\
    &0 < e1 /\ e1 < s1 /\ s1 <= kap * (M - zt) / &4 /\
    &0 < tau /\ tau <= (z0 - m) / &4 /\ tau <= e / &2 /\
    (!z. Xi (vec 0) z = z) /\ (!z s t. Xi t (Xi s z) = Xi (s + t) z) /\
    smooth_map_on (:real^(1,1)finite_sum) (\w. Xi (fstcart w) (sndcart w)) /\
    (!t. diffeomorphism_on (:real^1) (:real^1) (Xi t) (Xi (--t))) /\
    (!t z. drop z <= zt + e1 ==> Xi t z = z) /\
    (!t z. zt + s1 <= drop z /\ drop z <= M + &1 /\
           zt + s1 <= zt + (drop z - zt) * exp(drop t) /\
           zt + (drop z - zt) * exp(drop t) <= M + &1
           ==> Xi t z = lift(zt + (drop z - zt) * exp(drop t)))`;;

let SCHZ_PD_TAC : tactic =
  FIRST_ASSUM(fun th ->
    let h,_ = strip_comb(concl th) in
    if is_const h && fst(dest_const h) = "schz_pdata"
    then STRIP_ASSUME_TAC(REWRITE_RULE[schz_pdata] th) else NO_TAC) THEN
  SCHZ_ND_TAC;;

let SCHZ_PARAMS_EXIST = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap.
     schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
     ==> ?eta zt e e1 s1 tau Xi.
           schz_pdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
                      eta zt e e1 s1 tau Xi`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(REWRITE_RULE[schz_ndata; schz_tdata] th)) THEN STRIP_TAC THEN
  ABBREV_TAC `eta = min (min ((r0 pow 2 - (z0 - m)) / &2) ((r0 - (z0 - m)) / &2))
                        ((b1 - z0) / &2)` THEN
  ABBREV_TAC `zt = (b2 + zB') / &2` THEN
  SUBGOAL_THEN `&0 < eta /\ z0 + eta - m < r0 pow 2 /\ z0 + eta - m < r0 /\ z0 + eta < b1 /\
                b2 < zt /\ zt < zB' /\ zt < M` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN EXPAND_TAC "zt" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `e = min (min (kap * (M - zt) / &4) ((zt - b2) / &4)) ((zt - z0 - eta) / &3)` THEN
  ABBREV_TAC `s1 = kap * (M - zt) / &4` THEN
  SUBGOAL_THEN `&0 < kap * (M - zt) / &4 /\ kap * (M - zt) / &4 < M - zt` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * (M - zt) / &4` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e /\ e <= kap * (M - zt) / &4 /\ b2 + &3 * e < zt /\
                z0 + eta + &3 * e <= zt` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`zt:real`; `s1 / &2`; `s1:real`; `M + &1`] SCHZ_XI) THEN
  ANTS_TAC THENL [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Xi:real^1->real^1->real^1` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`eta:real`; `zt:real`; `e:real`; `s1 / &2`; `s1:real`;
                        `min ((z0 - m) / &4) (e / &2)`; `Xi:real^1->real^1->real^1`] THEN
  ASM_REWRITE_TAC[schz_pdata] THEN EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC);;

(* The domains of the three pieces and the top cap map.                      *)

let schz_dom1 = new_definition
 `schz_dom1 r0 M =
    {x:real^3 | x IN {x | x$3 < M} /\ inv(sqrt(M - x$3)) % sch5v_pr x IN ball(vec 0,r0)}`;;

let schz_dom2 = new_definition
 `schz_dom2 r0 m M z0 eta =
    {x:real^3 | x IN {x | m < x$3 /\ x$3 < M} /\
                (sqrt(schz_ramp z0 eta z0 (x$3) - m) / sqrt((x$3 - m) * (M - x$3))) %
                sch5v_pr x IN ball(vec 0,r0)}`;;

let schz_dom3 = new_definition
 `schz_dom3 (Xi:real^1->real^1->real^1) (L:real^2->real) r0 m M z0 zt e =
    {x:real^3 | x IN {x | m < x$3} /\
                (schz_vs Xi L o schz_t1 m) x IN
                {y:real^3 | y IN (:real^3) /\
                   (sqrt(z0 - m) / sqrt(M - schz_ramp (zt - e) e zt (y$3))) % sch5v_pr y IN
                   ball(vec 0,r0)}}`;;

let schz_top = new_definition
 `schz_top (Psi:real^1->real^3->real^3) (ph0:real^2->real^2) m M z0 zt e
           (Xi:real^1->real^1->real^1) (L:real^2->real) =
    schz_kp Psi ph0 m M z0 zt e o (schz_vs Xi L o schz_t1 m)`;;

let SCHZ_PD_LIPS = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap eta zt e e1 s1 tau Xi.
     schz_pdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
                eta zt e e1 s1 tau Xi
     ==> (?E Q. schz_lip (schz_dom1 r0 M) E (schz_p1 ph0 M) Q) /\
         (?E Q. schz_lip (schz_dom2 r0 m M z0 eta) E (schz_p2 Psi ph0 m M z0 eta) Q) /\
         (?E Q. schz_lip (schz_dom3 Xi (schz_lfun Psi ph0 ph1' m M z0 zt s1) r0 m M z0 zt e) E
                  (schz_top Psi ph0 m M z0 zt e Xi (schz_lfun Psi ph0 ph1' m M z0 zt s1)) Q)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `Psi:real^1->real^3->real^3`; `zA':real`; `zB':real`;
                 `kap:real`; `zt:real`; `s1:real`] SCHZ_LFUN_SMOOTH) THEN
  ANTS_TAC THENL
   [SCHZ_PD_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `kap * (M - zt) / &4` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= k * a ==> k * a / &4 <= k * a / &2`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SCHZ_PD_TAC THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`{q:real^3 | q IN {q | q$3 < M} /\ sch5v_pr q IN IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}`;
      `schz_p1i (ph0':real^2->real^2) M`] THEN
    REWRITE_TAC[schz_dom1] THEN MATCH_MP_TAC SCHZ_P1_LIP THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC
     [`{q:real^3 | q IN {q | m < q$3 /\ q$3 < M} /\
                   sch5v_pr(Psi (lift(schz_ramp z0 eta z0 (q$3) - q$3)) q) IN
                   IMAGE (ph0:real^2->real^2) (ball(vec 0,r0))}`;
      `schz_p2i Psi (ph0':real^2->real^2) m M z0 eta`] THEN
    REWRITE_TAC[schz_dom2] THEN MATCH_MP_TAC SCHZ_P2_LIP THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[schz_dom3; schz_top] THEN MATCH_MP_TAC SCHZ_TOP_LIP THEN
    EXISTS_TAC `ph0':real^2->real^2` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Agreement of the pieces on the overlaps and their heights.               *)

let SCHZ_SQRT_SPLIT = prove
 (`!a b. &0 < a /\ &0 < b ==> sqrt(a * b) = sqrt a * sqrt b /\ &0 < sqrt a /\ &0 < sqrt b`,
  SIMP_TAC[SQRT_MUL; REAL_LT_IMP_LE; SQRT_POS_LT]);;

let SCHZ_PD_AGREE1 = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap eta zt e e1 s1 tau Xi x.
     schz_pdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
                eta zt e e1 s1 tau Xi /\
     x IN schz_dom1 r0 M /\ x IN schz_dom2 r0 m M z0 eta /\ abs(x$3 - (m + z0) / &2) < tau
     ==> schz_p1 ph0 M x = schz_p2 Psi ph0 m M z0 eta x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schz_dom1; schz_dom2; IN_ELIM_THM] THEN STRIP_TAC THEN
  SCHZ_PD_TAC THEN
  SUBGOAL_THEN `schz_ramp z0 eta z0 ((x:real^3)$3) = x$3` ASSUME_TAC THENL
   [MP_TAC(SPECL [`z0:real`; `eta:real`; `(x:real^3)$3`] SCHZ_PSI_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[schz_p1; schz_p2] THEN ASM_REWRITE_TAC[REAL_SUB_REFL; LIFT_NUM] THEN
  MP_TAC(SPECL [`(x:real^3)$3 - m`; `M - (x:real^3)$3`] SCHZ_SQRT_SPLIT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt((x:real^3)$3 - m) / (sqrt(x$3 - m) * sqrt(M - x$3)) = inv(sqrt(M - x$3))`
  (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `&0 < sqrt((x:real^3)$3 - m)` THEN UNDISCH_TAC `&0 < sqrt(M - (x:real^3)$3)` THEN
  CONV_TAC REAL_FIELD);;

let SCHZ_PD_TOP_EQ = prove
 (`!(Psi:real^1->real^3->real^3) (ph0:real^2->real^2) m M z0 zt e
    (Xi:real^1->real^1->real^1) (L:real^2->real) (x:real^3).
     schz_top Psi ph0 m M z0 zt e Xi L x =
     sch5v_at (drop(Xi (lift(L(inv(sqrt(x$3 - m)) % sch5v_pr x))) (lift(x$3))))
       (schz_slice Psi z0
          (schz_ramp (zt - e) e zt (drop(Xi (lift(L(inv(sqrt(x$3 - m)) % sch5v_pr x)))
                                            (lift(x$3)))))
          (ph0((sqrt(z0 - m) /
                sqrt(M - schz_ramp (zt - e) e zt (drop(Xi (lift(L(inv(sqrt(x$3 - m)) %
                                                   sch5v_pr x))) (lift(x$3)))))) %
               (inv(sqrt(x$3 - m)) % sch5v_pr x))))`,
  REWRITE_TAC[schz_top; schz_kp; schz_vs; schz_t1; o_THM; SCH5V_PR_AT]);;

let SCHZ_PD_AGREE2 = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap eta zt e e1 s1 tau Xi x.
     schz_pdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
                eta zt e e1 s1 tau Xi /\
     x IN schz_dom2 r0 m M z0 eta /\ abs(x$3 - (zt - &2 * e)) < tau
     ==> schz_p2 Psi ph0 m M z0 eta x =
         schz_top Psi ph0 m M z0 zt e Xi (schz_lfun Psi ph0 ph1' m M z0 zt s1) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schz_dom2; IN_ELIM_THM] THEN STRIP_TAC THEN
  SCHZ_PD_TAC THEN
  SUBGOAL_THEN `schz_ramp z0 eta z0 ((x:real^3)$3) = z0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`z0:real`; `eta:real`; `(x:real^3)$3`] SCHZ_PSI_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. (Xi:real^1->real^1->real^1) t (lift((x:real^3)$3)) = lift(x$3)`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!t z. drop z <= zt + e1 ==> (Xi:real^1->real^1->real^1) t z = z`)
          (concl th))) THEN
    REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `schz_ramp (zt - e) e zt ((x:real^3)$3) = x$3` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`zt - e`; `e:real`; `zt:real`; `(x:real^3)$3`] SCHZ_RAMP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SCHZ_PD_TOP_EQ] THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  REWRITE_TAC[schz_p2] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `z0:real`; `(x:real^3)$3`] SCHZ_SLICE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2 th)]) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`(x:real^3)$3 - m`; `M - (x:real^3)$3`] SCHZ_SQRT_SPLIT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < sqrt((x:real^3)$3 - m)` THEN UNDISCH_TAC `&0 < sqrt(M - (x:real^3)$3)` THEN
  CONV_TAC REAL_FIELD);;

let SCHZ_PD_HEIGHTS = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap eta zt e e1 s1 tau Xi.
     schz_pdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
                eta zt e e1 s1 tau Xi
     ==> (!x. x IN schz_dom1 r0 M ==> (schz_p1 ph0 M x)$3 = x$3) /\
         (!x. x IN schz_dom2 r0 m M z0 eta ==> (schz_p2 Psi ph0 m M z0 eta x)$3 = x$3) /\
         (!x. x IN schz_dom3 Xi (schz_lfun Psi ph0 ph1' m M z0 zt s1) r0 m M z0 zt e /\
              x$3 <= zt + e1
              ==> (schz_top Psi ph0 m M z0 zt e Xi (schz_lfun Psi ph0 ph1' m M z0 zt s1) x)$3 =
                  x$3) /\
         (!x. x IN schz_dom3 Xi (schz_lfun Psi ph0 ph1' m M z0 zt s1) r0 m M z0 zt e /\
              zt + e1 < x$3
              ==> zt + e1 <
                  (schz_top Psi ph0 m M z0 zt e Xi (schz_lfun Psi ph0 ph1' m M z0 zt s1) x)$3)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SCHZ_PD_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[schz_p1; SCH5V_PR_AT];
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SCHZ_P2_HEIGHT THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SCHZ_PD_TOP_EQ; SCH5V_PR_AT] THEN
    SUBGOAL_THEN `!t. (Xi:real^1->real^1->real^1) t (lift((x:real^3)$3)) = lift(x$3)`
      (fun th -> REWRITE_TAC[th; LIFT_DROP]) THEN
    GEN_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!t z. drop z <= zt + e1 ==> (Xi:real^1->real^1->real^1) t z = z`)
          (concl th))) THEN
    REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SCHZ_PD_TOP_EQ; SCH5V_PR_AT] THEN
    MATCH_MP_TAC SCHZ_XI_ABOVE THEN ASM_REWRITE_TAC[LIFT_DROP]]);;

(* A margin for the bottom chart radius.                                     *)

let SCHZ_ND_R0_MARGIN = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap.
     schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
     ==> (z0 - m) * (&1 + kap / &4) < r0 pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SCHZ_ND_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(&1 + kap / &2) % basis 1:real^2`; `z0:real`]) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `&0 <= sqrt(z0 - m)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `&0 < k ==> abs(&1 + k / &2) = &1 + k / &2`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(sqrt(z0 - m) * (&1 + kap / &2)) pow 2 < r0 pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  SUBGOAL_THEN `sqrt(z0 - m) pow 2 = z0 - m` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a * b <= a * c ==> a * c < r ==> a * b < r`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= k /\ &0 <= k * k ==> &1 + k / &4 <= (&1 + k / &2) pow 2`) THEN
  REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC);;

(* The closed model ball lies in the glued domain.                           *)

let SCHZ_NORM_LT_FROM_SQ = prove
 (`!(v:real^2) r. &0 < r /\ norm v pow 2 < r pow 2 ==> norm v < r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`norm(v:real^2)`; `r:real`] REAL_LT_SQUARE_ABS) THEN
  ASM_REWRITE_TAC[REAL_ABS_NORM] THEN ASM_REAL_ARITH_TAC);;

let SCHZ_PD_DOM1 = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap eta zt e e1 s1 tau Xi x.
     schz_pdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
                eta zt e e1 s1 tau Xi /\
     norm(sch5v_pr x) pow 2 <= (x$3 - m) * (M - x$3) /\ m <= x$3 /\
     x$3 <= (m + z0) / &2 + tau / &2
     ==> x IN schz_dom1 r0 M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SCHZ_PD_TAC THEN
  REWRITE_TAC[schz_dom1; IN_ELIM_THM; IN_BALL_0] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SCHZ_NORM_LT_FROM_SQ THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_ABS_INV; REAL_POW_INV] THEN
  SUBGOAL_THEN `&0 < M - (x:real^3)$3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(x:real^3)$3 - m` THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let SCHZ_PD_DOM2 = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap eta zt e e1 s1 tau Xi x.
     schz_pdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
                eta zt e e1 s1 tau Xi /\
     norm(sch5v_pr x) pow 2 <= (x$3 - m) * (M - x$3) /\
     (m + z0) / &2 - tau / &2 <= x$3 /\ x$3 <= zt - &2 * e + tau / &2
     ==> x IN schz_dom2 r0 m M z0 eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SCHZ_PD_TAC THEN
  REWRITE_TAC[schz_dom2; IN_ELIM_THM; IN_BALL_0] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m < (x:real^3)$3 /\ x$3 < M` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`z0:real`; `eta:real`; `(x:real^3)$3`] SCHZ_PSI_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `m < schz_ramp z0 eta z0 ((x:real^3)$3)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHZ_PSI_GT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = sqrt(((x:real^3)$3 - m) * (M - x$3))` THEN
  SUBGOAL_THEN `&0 < r /\ norm(sch5v_pr(x:real^3)) <= r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN `&0 < sqrt(schz_ramp z0 eta z0 ((x:real^3)$3) - m) /\
                sqrt(schz_ramp z0 eta z0 (x$3) - m) < r0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sqrt(schz_ramp z0 eta z0 ((x:real^3)$3) - m)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID]);;

let SCHZ_PD_DOM3 = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap eta zt e e1 s1 tau Xi x.
     schz_pdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
                eta zt e e1 s1 tau Xi /\
     norm(sch5v_pr x) pow 2 <= (x$3 - m) * (M - x$3) /\
     zt - &2 * e - tau / &2 <= x$3 /\ x$3 <= M
     ==> x IN schz_dom3 Xi (schz_lfun Psi ph0 ph1' m M z0 zt s1) r0 m M z0 zt e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP SCHZ_ND_R0_MARGIN
    (CONJUNCT1(REWRITE_RULE[schz_pdata] th)))) THEN DISCH_TAC THEN
  SCHZ_PD_TAC THEN
  REWRITE_TAC[schz_dom3; IN_ELIM_THM; IN_UNIV; IN_BALL_0; o_THM] THEN
  SUBGOAL_THEN `m < (x:real^3)$3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[schz_vs; schz_t1; SCH5V_PR_AT; LIFT_DROP] THEN
  MP_TAC(ISPECL [`Xi:real^1->real^1->real^1`; `e:real`; `zt:real`; `e1:real`;
                 `lift(schz_lfun Psi (ph0:real^2->real^2) (ph1':real^2->real^2) m M z0 zt s1
                     (inv(sqrt((x:real^3)$3 - m)) % sch5v_pr x))`;
                 `lift((x:real^3)$3)`] SCHZ_ZETA_XI) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `y = schz_ramp (zt - e) e zt ((x:real^3)$3)` THEN
  SUBGOAL_THEN `y <= zt /\ M - (x:real^3)$3 <= (M - y) + e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCHZ_ZETA_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`zt - e`; `e:real`; `zt:real`; `(x:real^3)$3`] SCHZ_RAMP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x:real^3)$3 <= zt - e` THENL
     [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`e:real`; `zt:real`; `(x:real^3)$3`] SCHZ_ZETA_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < M - y /\ M - zt <= M - y` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SCHZ_NORM_LT_FROM_SQ THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_ABS_INV; REAL_POW_INV; REAL_ABS_DIV;
              REAL_POW_DIV] THEN
  SUBGOAL_THEN `&0 < z0 - m /\ &0 < (x:real^3)$3 - m` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; SQRT_POS_LT; SQRT_POW_2;
               REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `norm(sch5v_pr(x:real^3)) pow 2 / (x$3 - m) <= M - x$3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(z0 - m) * (&1 + kap / &4)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z0 - m) / (M - y) * inv((x:real^3)$3 - m) * norm(sch5v_pr x) pow 2 =
                (z0 - m) * ((norm(sch5v_pr x) pow 2 / (x$3 - m)) / (M - y))` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(M - (x:real^3)$3) / (M - y)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `e <= (kap / &4) * (M - y)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `kap * (M - zt) / &4` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `kap * (M - zt) / &4 = (kap / &4) * (M - zt)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `M - (x:real^3)$3 <= (M - y) + e` THEN REAL_ARITH_TAC]);;

let SCHZ_PD_CBALL = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap eta zt e e1 s1 tau Xi.
     schz_pdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
                eta zt e e1 s1 tau Xi
     ==> cball(sch5v_at ((m + M) / &2) (vec 0),(M - m) / &2) SUBSET
         schz_gset (schz_dom1 r0 M) (schz_dom2 r0 m M z0 eta)
                   (schz_dom3 Xi (schz_lfun Psi ph0 ph1' m M z0 zt s1) r0 m M z0 zt e)
                   ((m + z0) / &2) (zt - &2 * e) tau`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `m < M /\ m < z0 /\ z0 < zt /\ zt < M /\ &0 < e /\ &0 < tau /\
                tau <= (z0 - m) / &4 /\ tau <= e / &2 /\ z0 + eta + &3 * e <= zt /\ &0 < eta`
  STRIP_ASSUME_TAC THENL [SCHZ_PD_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN
  MP_TAC(SPECL [`m:real`; `M:real`; `x:real^3`] SCHZ_MODEL_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `m <= (x:real^3)$3 /\ x$3 <= M` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[schz_gset; IN_INTER; IN_UNION; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `(x:real^3)$3 <= (m + z0) / &2 + tau / &2` THENL
     [DISJ2_TAC THEN MATCH_MP_TAC SCHZ_PD_DOM1 THEN
      MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`;
        `zB:real`; `m:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`; `r1:real`;
        `ph1:real^2->real^2`; `ph1':real^2->real^2`; `b1:real`; `b2:real`;
        `Psi:real^1->real^3->real^3`; `zA':real`; `zB':real`; `kap:real`; `eta:real`;
        `zt:real`; `e:real`; `e1:real`; `s1:real`; `tau:real`;
        `Xi:real^1->real^1->real^1`] THEN
      ASM_REWRITE_TAC[];
      DISJ1_TAC THEN ASM_REAL_ARITH_TAC];
    ASM_CASES_TAC `(m + z0) / &2 - tau / &2 <= (x:real^3)$3 /\
                   x$3 <= zt - &2 * e + tau / &2` THENL
     [DISJ2_TAC THEN DISJ2_TAC THEN MATCH_MP_TAC SCHZ_PD_DOM2 THEN
      MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`;
        `zB:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `r1:real`;
        `ph1:real^2->real^2`; `ph1':real^2->real^2`; `b1:real`; `b2:real`;
        `Psi:real^1->real^3->real^3`; `zA':real`; `zB':real`; `kap:real`;
        `zt:real`; `e:real`; `e1:real`; `s1:real`; `tau:real`;
        `Xi:real^1->real^1->real^1`] THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ASM_CASES_TAC `zt - &2 * e - tau / &2 <= (x:real^3)$3` THENL
     [DISJ2_TAC THEN MATCH_MP_TAC SCHZ_PD_DOM3 THEN
      MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`;
        `zB:real`; `ph0':real^2->real^2`; `r1:real`;
        `ph1:real^2->real^2`; `b1:real`; `b2:real`;
        `zA':real`; `zB':real`; `kap:real`; `eta:real`;
        `e1:real`; `tau:real`] THEN
      ASM_REWRITE_TAC[];
      DISJ1_TAC THEN ASM_REAL_ARITH_TAC]]);;

(* The boundary sphere goes into S.                                          *)

let SCHZ_TOP_CHART_IN = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap h k.
     schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap /\
     k IN ball(vec 0,r1) /\ h = M - norm k pow 2 /\ norm k pow 2 < r1
     ==> sch5v_at h (ph1 k) IN S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SCHZ_ND_TAC THEN
  REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2 SCHZ_LIFT_FACTS))] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sch5v_at h (k:real^2)` o check (fun th ->
    can (term_match [] `!y. sch5v_pr y IN ball(vec 0,r1) /\ abs(y$3 - M) < r1
                            ==> (schz_lift (ph1:real^2->real^2) y IN S <=>
                                 y$3 = M - norm(sch5v_pr y) pow 2)`) (concl th))) THEN
  REWRITE_TAC[SCH5V_PR_AT] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `k:real^2` NORM_POS_LE) THEN
    MP_TAC(SPEC `norm(k:real^2)` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let SCHZ_TOP_POINT_NORM = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap y h u.
     schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap /\
     b2 <= y /\ y <= zB' /\ norm u pow 2 = M - h /\ M - h < r1 /\
     abs(norm u / sqrt(M - y) - &1) < kap
     ==> sch5v_at h (schz_slice Psi z0 y (ph0((sqrt(z0 - m) / sqrt(M - y)) % u))) IN S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `Psi:real^1->real^3->real^3`; `zA':real`; `zB':real`;
                 `kap:real`; `y:real`; `u:real^2`] SCHZ_KMAP_NORM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `schz_slice Psi z0 y ((ph0:real^2->real^2)((sqrt(z0 - m) / sqrt(M - y)) % u)) IN
               IMAGE (ph1:real^2->real^2) (ball(vec 0,r1))` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `k:real^2` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `schz_kmap Psi (ph0:real^2->real^2) (ph1':real^2->real^2) m M z0 y u = k`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[schz_kmap] THEN SCHZ_ND_TAC THEN
    MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(
      GEN_REWRITE_RULE I [diffeomorphism_on]
      (ASSUME `diffeomorphism_on (ball(vec 0,r1)) (IMAGE (ph1:real^2->real^2) (ball(vec 0,r1)))
                 ph1 ph1'`))))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SCHZ_TOP_CHART_IN THEN
  MAP_EVERY EXISTS_TAC [`Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`; `m:real`;
    `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`; `M:real`; `r1:real`;
    `ph1':real^2->real^2`; `b1:real`; `b2:real`; `Psi:real^1->real^3->real^3`; `zA':real`;
    `zB':real`; `kap:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `norm(k:real^2) = norm(u:real^2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SCHZ_BOT_CHART_IN = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    h a.
     schz_tdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 /\
     h = m + norm a pow 2 /\ norm a pow 2 < r0 pow 2 /\ norm a pow 2 < r0
     ==> sch5v_at h (ph0 a) IN S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SCHZ_TD_TAC THEN
  REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2 SCHZ_LIFT_FACTS))] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sch5v_at h (a:real^2)` o check (fun th ->
    can (term_match [] `!y. sch5v_pr y IN ball(vec 0,r0) /\ abs(y$3 - m) < r0
                            ==> (schz_lift (ph0:real^2->real^2) y IN S <=>
                                 y$3 = m + norm(sch5v_pr y) pow 2)`) (concl th))) THEN
  REWRITE_TAC[SCH5V_PR_AT; IN_BALL_0] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SCHZ_NORM_LT_FROM_SQ THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `norm(a:real^2)` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let SCHZ_PD_BDRY1 = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap eta zt e e1 s1 tau Xi x.
     schz_pdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
                eta zt e e1 s1 tau Xi /\
     norm(sch5v_pr x) pow 2 = (x$3 - m) * (M - x$3) /\ m <= x$3 /\ x$3 < (m + z0) / &2
     ==> schz_p1 ph0 M x IN S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[schz_ndata] o
    CONJUNCT1 o REWRITE_RULE[schz_pdata]) THEN
  SCHZ_PD_TAC THEN
  SUBGOAL_THEN `&0 < M - (x:real^3)$3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(inv(sqrt(M - (x:real^3)$3)) % sch5v_pr x) pow 2 = x$3 - m` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_ABS_INV; REAL_POW_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; SQRT_POS_LT; SQRT_POW_2;
                 REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `&0 < M - (x:real^3)$3` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[schz_p1] THEN
  MATCH_MP_TAC SCHZ_BOT_CHART_IN THEN
  MAP_EVERY EXISTS_TAC [`Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`; `m:real`;
    `r0:real`; `ph0':real^2->real^2`; `z0:real`; `M:real`; `r1:real`; `ph1:real^2->real^2`;
    `ph1':real^2->real^2`; `b1:real`; `b2:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SCHZ_PD_BDRY2 = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap eta zt e e1 s1 tau Xi x.
     schz_pdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
                eta zt e e1 s1 tau Xi /\
     norm(sch5v_pr x) pow 2 = (x$3 - m) * (M - x$3) /\
     (m + z0) / &2 <= x$3 /\ x$3 < zt - &2 * e
     ==> schz_p2 Psi ph0 m M z0 eta x IN S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[schz_ndata] o
    CONJUNCT1 o REWRITE_RULE[schz_pdata]) THEN
  SCHZ_PD_TAC THEN
  SUBGOAL_THEN `m < (x:real^3)$3 /\ x$3 < M` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`z0:real`; `eta:real`; `(x:real^3)$3`] SCHZ_PSI_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `p = schz_ramp z0 eta z0 ((x:real^3)$3)` THEN
  SUBGOAL_THEN `m < p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC SCHZ_PSI_GT THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((sqrt(p - m) / sqrt(((x:real^3)$3 - m) * (M - x$3))) % sch5v_pr x) pow 2 =
                p - m` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < ((x:real^3)$3 - m) * (M - x$3)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_POW2_ABS; REAL_POW_DIV] THEN
    SUBGOAL_THEN `sqrt(p - m) pow 2 = p - m /\
                  sqrt(((x:real^3)$3 - m) * (M - x$3)) pow 2 = (x$3 - m) * (M - x$3)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < ((x:real^3)$3 - m) * (M - x$3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5v_at p ((ph0:real^2->real^2)
                  ((sqrt(p - m) / sqrt(((x:real^3)$3 - m) * (M - x$3))) % sch5v_pr x)) IN S`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCHZ_BOT_CHART_IN THEN
    MAP_EVERY EXISTS_TAC [`Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`; `m:real`;
      `r0:real`; `ph0':real^2->real^2`; `z0:real`; `M:real`; `r1:real`; `ph1:real^2->real^2`;
      `ph1':real^2->real^2`; `b1:real`; `b2:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[schz_p2] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(x:real^3)$3 <= z0` THENL
   [SUBGOAL_THEN `p = (x:real^3)$3` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `sch5v_at p ((ph0:real^2->real^2)
                  ((sqrt(p - m) / sqrt(((x:real^3)$3 - m) * (M - x$3))) % sch5v_pr x)) IN S` THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; LIFT_NUM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `z0 <= p /\ p <= (x:real^3)$3` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (term_match [] `!(x:real^3) t. x IN S /\ zA' <= x$3 /\ x$3 <= zB' /\
                              zA' <= x$3 + drop t /\ x$3 + drop t <= zB'
                              ==> (Psi:real^1->real^3->real^3) t x IN S`) (concl th))) THEN
  ASM_REWRITE_TAC[SCH5V_PR_AT; LIFT_DROP] THEN ASM_REAL_ARITH_TAC);;

let SCHZ_PD_BDRY3 = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap eta zt e e1 s1 tau Xi x.
     schz_pdata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
                eta zt e e1 s1 tau Xi /\
     norm(sch5v_pr x) pow 2 = (x$3 - m) * (M - x$3) /\ zt - &2 * e <= x$3 /\ x$3 <= M
     ==> schz_top Psi ph0 m M z0 zt e Xi (schz_lfun Psi ph0 ph1' m M z0 zt s1) x IN S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[schz_pdata]) THEN
  SCHZ_PD_TAC THEN
  SUBGOAL_THEN `m < (x:real^3)$3 /\ b1 < zt - &2 * e /\ &0 < M - zt /\ &0 <= kap`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SCHZ_PD_TOP_EQ] THEN
  ABBREV_TAC `u = inv(sqrt((x:real^3)$3 - m)) % sch5v_pr x` THEN
  SUBGOAL_THEN `norm(u:real^2) pow 2 = M - (x:real^3)$3` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_ABS_INV; REAL_POW_INV] THEN
    SUBGOAL_THEN `&0 < (x:real^3)$3 - m` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; SQRT_POS_LT; SQRT_POW_2;
                 REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `&0 < (x:real^3)$3 - m` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `L = schz_lfun Psi (ph0:real^2->real^2) (ph1':real^2->real^2) m M z0 zt s1` THEN
  ABBREV_TAC `h = drop((Xi:real^1->real^1->real^1) (lift((L:real^2->real) u))
                         (lift((x:real^3)$3)))` THEN
  SUBGOAL_THEN `M - (x:real^3)$3 < r1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^3)$3 <= zt + e1` THENL
   [SUBGOAL_THEN `h = (x:real^3)$3` SUBST1_TAC THENL
     [EXPAND_TAC "h" THEN
      SUBGOAL_THEN `!t. (Xi:real^1->real^1->real^1) t (lift((x:real^3)$3)) = lift(x$3)`
        (fun th -> REWRITE_TAC[th; LIFT_DROP]) THEN
      GEN_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!t z. drop z <= zt + e1 ==> (Xi:real^1->real^1->real^1) t z = z`)
            (concl th))) THEN
      REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `y = schz_ramp (zt - e) e zt ((x:real^3)$3)` THEN
    SUBGOAL_THEN `abs(y - (x:real^3)$3) <= e + e1 /\ y <= zt /\ zt - &2 * e <= y`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`zt - e`; `e:real`; `zt:real`; `(x:real^3)$3`] SCHZ_RAMP) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_CASES_TAC `(x:real^3)$3 <= zt - e` THENL
       [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3)$3 <= zt - e`)) THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC SCHZ_TOP_POINT_NORM THEN
    MAP_EVERY EXISTS_TAC [`Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`; `r0:real`;
      `ph0':real^2->real^2`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
      `b1:real`; `b2:real`; `zA':real`; `zB':real`; `kap:real`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SCHZ_RATIO_NEAR1 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e + e1` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `kap * (M - zt) / &2` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `kap * (M - zt) / &2 = (kap / &2) * (M - zt) /\
                    kap * (M - y) / &2 = (kap / &2) * (M - y)` (fun th -> REWRITE_TAC[th]) THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `zt + e1 < h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC SCHZ_XI_ABOVE THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `schz_ramp (zt - e) e zt h = zt` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`zt - e`; `e:real`; `zt:real`; `h:real`] SCHZ_RAMP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `M - zt - s1 <= norm(u:real^2) pow 2` THENL
   [SUBGOAL_THEN `(L:real^2->real) u = &0` ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC SCHZ_LFUN_RIM THEN
      MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`;
        `zB:real`; `r0:real`; `ph0':real^2->real^2`; `r1:real`; `ph1:real^2->real^2`;
        `b1:real`; `b2:real`; `zA':real`; `zB':real`; `kap:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `h = (x:real^3)$3` SUBST1_TAC THENL
     [EXPAND_TAC "h" THEN REWRITE_TAC[ASSUME `(L:real^2->real) u = &0`; LIFT_NUM] THEN
      ASM_REWRITE_TAC[LIFT_DROP];
      ALL_TAC] THEN
    MATCH_MP_TAC SCHZ_TOP_POINT_NORM THEN
    MAP_EVERY EXISTS_TAC [`Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`; `r0:real`;
      `ph0':real^2->real^2`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
      `b1:real`; `b2:real`; `zA':real`; `zB':real`; `kap:real`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SCHZ_RATIO_NEAR1 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
    TRY(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `kap * (M - zt) / &4` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= k * a ==> k * a / &4 <= k * a / &2`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the stretched part of the cap *)
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  SUBGOAL_THEN `&0 <= M - zt - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `Psi:real^1->real^3->real^3`; `zA':real`; `zB':real`;
                 `kap:real`; `zt:real`; `sqrt(M - zt - s1)`; `u:real^2`] SCHZ_KMAP_DISC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SCHZ_RATIO_NEAR1 THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN
      TRY(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `kap * (M - zt) / &4` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= k * a ==> k * a / &4 <= k * a / &2`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SCHZ_NORM_LT_SQRT]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `schz_slice Psi z0 zt ((ph0:real^2->real^2)((sqrt(z0 - m) / sqrt(M - zt)) % u)) IN
               IMAGE (ph1:real^2->real^2) (ball(vec 0,sqrt(M - zt - s1)))` THEN
  REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `schz_kmap Psi (ph0:real^2->real^2) (ph1':real^2->real^2) m M z0 zt u = k`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[schz_kmap] THEN
    MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(
      GEN_REWRITE_RULE I [diffeomorphism_on]
      (ASSUME `diffeomorphism_on (ball(vec 0,r1)) (IMAGE (ph1:real^2->real^2) (ball(vec 0,r1)))
                 ph1 ph1'`))))))) THEN
    REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(k:real^2) pow 2 < M - zt - s1` ASSUME_TAC THENL
   [ASM_MESON_TAC[SCHZ_NORM_LT_SQRT]; ALL_TAC] THEN
  SUBGOAL_THEN `h = M - norm(k:real^2) pow 2` ASSUME_TAC THENL
   [ABBREV_TAC `A = M - zt - norm(k:real^2) pow 2` THEN
    ABBREV_TAC `B = M - zt - norm(u:real^2) pow 2` THEN
    SUBGOAL_THEN `&0 < A /\ &0 < B /\ (x:real^3)$3 - zt = B /\
                  M - norm(k:real^2) pow 2 = zt + A` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(L:real^2->real) u = log(A / B)` ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC[schz_lfun] THEN
      SUBGOAL_THEN `norm(u:real^2) pow 2 < M - zt - s1 / &2` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY EXPAND_TAC ["A"; "B"] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(log(A / B)) = A / B` ASSUME_TAC THENL
     [MATCH_MP_TAC EXP_LOG THEN ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    SUBGOAL_THEN `zt + ((x:real^3)$3 - zt) * A / B = M - norm(k:real^2) pow 2` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < B` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[ASSUME `(L:real^2->real) u = log(A / B)`] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`lift(log(A / B))`; `lift((x:real^3)$3)`] o check (fun th ->
      can (term_match [] `!t z. zt + s1 <= drop z /\ drop z <= M + &1 /\
                                zt + s1 <= zt + (drop z - zt) * exp(drop t) /\
                                zt + (drop z - zt) * exp(drop t) <= M + &1
                                ==> (Xi:real^1->real^1->real^1) t z =
                                    lift(zt + (drop z - zt) * exp(drop t))`) (concl th))) THEN
    REWRITE_TAC[LIFT_DROP; ASSUME `exp(log(A / B)) = A / B`;
                ASSUME `zt + ((x:real^3)$3 - zt) * A / B = M - norm(k:real^2) pow 2`] THEN
    ANTS_TAC THENL
     [MP_TAC(SPEC `norm(k:real^2)` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[LIFT_DROP]];
    ALL_TAC] THEN
  MATCH_MP_TAC SCHZ_TOP_CHART_IN THEN
  MAP_EVERY EXISTS_TAC [`Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`; `m:real`;
    `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`; `M:real`; `r1:real`;
    `ph1':real^2->real^2`; `b1:real`; `b2:real`; `Psi:real^1->real^3->real^3`; `zA':real`;
    `zB':real`; `kap:real`] THEN
  ASM_REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC);;

(* The model chart from the data of the new flow.                            *)

let SCHZ_MODEL_FROM_ND = prove
 (`!S Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2
    Psi zA' zB' kap.
     schz_ndata S Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1' b1 b2 Psi zA' zB' kap
     ==> ?(Theta:real^3->real^3) U (cen:real^3) rho.
           open U /\ &0 < rho /\ cball(cen,rho) SUBSET U /\ smooth_map_on U Theta /\
           (!x y. x IN U /\ y IN U /\ Theta x = Theta y ==> x = y) /\
           (!x. x IN U ==> ~(det(matrix(frechet_derivative Theta (at x))) = &0)) /\
           IMAGE Theta (sphere(cen,rho)) SUBSET S`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCHZ_PARAMS_EXIST) THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (X_CHOOSE_THEN `zt:real` (X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `tau:real`
    (X_CHOOSE_THEN `Xi:real^1->real^1->real^1` ASSUME_TAC))))))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCHZ_PD_LIPS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `E1:real^3->bool` (X_CHOOSE_THEN `Q1:real^3->real^3`
    ASSUME_TAC)) (CONJUNCTS_THEN2 (X_CHOOSE_THEN `E2:real^3->bool`
    (X_CHOOSE_THEN `Q2:real^3->real^3` ASSUME_TAC)) (X_CHOOSE_THEN `E3:real^3->bool`
    (X_CHOOSE_THEN `Q3:real^3->real^3` ASSUME_TAC)))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCHZ_PD_HEIGHTS) THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCHZ_PD_CBALL) THEN
  SUBGOAL_THEN `m < M /\ &0 < tau /\
                (m + z0) / &2 + tau < (zt - &2 * e) - tau /\ zt - &2 * e < zt + e1`
  STRIP_ASSUME_TAC THENL
   [SCHZ_PD_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`schz_p1 (ph0:real^2->real^2) M`; `schz_p2 Psi (ph0:real^2->real^2) m M z0 eta`;
    `schz_top Psi (ph0:real^2->real^2) m M z0 zt e Xi
       (schz_lfun Psi ph0 (ph1':real^2->real^2) m M z0 zt s1)`;
    `schz_dom1 r0 M`; `schz_dom2 r0 m M z0 eta`;
    `schz_dom3 Xi (schz_lfun Psi (ph0:real^2->real^2) (ph1':real^2->real^2) m M z0 zt s1)
               r0 m M z0 zt e`;
    `E1:real^3->bool`; `E2:real^3->bool`; `E3:real^3->bool`;
    `Q1:real^3->real^3`; `Q2:real^3->real^3`; `Q3:real^3->real^3`;
    `(m + z0) / &2`; `zt - &2 * e`; `tau:real`; `zt + e1`] SCHZ_GLUE3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SCHZ_PD_AGREE1 THEN
      MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`;
        `zB:real`; `r0:real`; `ph0':real^2->real^2`; `r1:real`; `ph1:real^2->real^2`;
        `ph1':real^2->real^2`; `b1:real`; `b2:real`; `zA':real`; `zB':real`; `kap:real`;
        `zt:real`; `e:real`; `e1:real`; `s1:real`; `tau:real`;
        `Xi:real^1->real^1->real^1`] THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SCHZ_PD_AGREE2 THEN
      MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `Psi0:real^1->real^3->real^3`; `zA:real`;
        `zB:real`; `r0:real`; `ph0':real^2->real^2`; `r1:real`; `ph1:real^2->real^2`;
        `b1:real`; `b2:real`; `zA':real`; `zB':real`; `kap:real`;
        `e1:real`; `tau:real`] THEN
      ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`schz_gmap (schz_p1 (ph0:real^2->real^2) M) (schz_p2 Psi ph0 m M z0 eta)
       (schz_top Psi ph0 m M z0 zt e Xi (schz_lfun Psi ph0 (ph1':real^2->real^2) m M z0 zt s1))
       ((m + z0) / &2) (zt - &2 * e)`;
    `schz_gset (schz_dom1 r0 M) (schz_dom2 r0 m M z0 eta)
       (schz_dom3 Xi (schz_lfun Psi (ph0:real^2->real^2) (ph1':real^2->real^2) m M z0 zt s1)
                  r0 m M z0 zt e)
       ((m + z0) / &2) (zt - &2 * e) tau`;
    `sch5v_at ((m + M) / &2) (vec 0)`; `(M - m) / &2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
  MP_TAC(SPECL [`m:real`; `M:real`; `x:real^3`] SCHZ_MODEL_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `m <= (x:real^3)$3 /\ x$3 <= M` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[schz_gmap] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC SCHZ_PD_BDRY1 THEN
    MAP_EVERY EXISTS_TAC [`Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`; `m:real`;
      `r0:real`; `ph0':real^2->real^2`; `z0:real`; `r1:real`; `ph1:real^2->real^2`;
      `ph1':real^2->real^2`; `b1:real`; `b2:real`; `Psi:real^1->real^3->real^3`; `zA':real`;
      `zB':real`; `kap:real`; `eta:real`; `zt:real`; `e:real`; `e1:real`; `s1:real`;
      `tau:real`; `Xi:real^1->real^1->real^1`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC SCHZ_PD_BDRY2 THEN
    MAP_EVERY EXISTS_TAC [`Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
      `r0:real`; `ph0':real^2->real^2`; `r1:real`; `ph1:real^2->real^2`;
      `ph1':real^2->real^2`; `b1:real`; `b2:real`; `zA':real`;
      `zB':real`; `kap:real`; `zt:real`; `e:real`; `e1:real`; `s1:real`;
      `tau:real`; `Xi:real^1->real^1->real^1`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SCHZ_PD_BDRY3 THEN
  MAP_EVERY EXISTS_TAC [`Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
    `r0:real`; `ph0':real^2->real^2`; `r1:real`; `ph1:real^2->real^2`;
    `b1:real`; `b2:real`; `zA':real`; `zB':real`; `kap:real`; `eta:real`;
    `e1:real`; `tau:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The model chart.  The setup (two critical points, exact                   *)
(* charts at the extremal points, the margin eps) gives the transport data  *)
(* (SCHZ_TDATA_EXISTS), the new flow gives schz_ndata (SCHZ_NDATA_EXISTS),   *)
(* and the pieces glued above give the model chart.                          *)
(* ------------------------------------------------------------------------- *)

let SCHZ_TDATA_EXISTS = prove
 (`!g g':real^3->real^3.
     sch_neck g g' /\ sch_morse g /\ sch_saddles g = {}
     ==> ?Psi0 zA zB m r0 (ph0:real^2->real^2) ph0' z0 M r1 (ph1:real^2->real^2) ph1' b1 b2.
           schz_tdata (IMAGE g (sphere(vec 0,&1))) Psi0 zA zB m r0 ph0 ph0' z0 M r1 ph1 ph1'
                      b1 b2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCHZ_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (X_CHOOSE_THEN `M:real` (X_CHOOSE_THEN `r0:real`
    (X_CHOOSE_THEN `ph0:real^2->real^2` (X_CHOOSE_THEN `ph0':real^2->real^2`
    (X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `ph1:real^2->real^2`
    (X_CHOOSE_THEN `ph1':real^2->real^2` (X_CHOOSE_THEN `eps:real`
     STRIP_ASSUME_TAC))))))))) THEN
  ABBREV_TAC `del = min (min (min eps (r0 pow 2)) (min r0 (r1 pow 2))) (min r1 (M - m)) / &4` THEN
  SUBGOAL_THEN `&0 < del /\ del <= eps / &4 /\ del <= r0 pow 2 / &4 /\ del <= r0 / &4 /\
                del <= r1 pow 2 / &4 /\ del <= r1 / &4 /\ del <= (M - m) / &4`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < r0 pow 2 /\ &0 < r1 pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "del" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `m + del / &2`; `M - del / &2`]
    SCHZ_BAND_FLOW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Psi0:real^1->real^3->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`Psi0:real^1->real^3->real^3`; `m + del / &2`; `M - del / &2`;
    `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `m + del`; `M:real`;
    `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`; `M - del`;
    `M - &3 * del / &4`] THEN
  ASM_REWRITE_TAC[schz_tdata] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
    EXISTS_TAC `schz_cyl (ph0:real^2->real^2) m (r0 / &2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCHZ_CYL_MONO THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x. x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\ x$3 < m + eps
             ==> x IN schz_cyl (ph0:real^2->real^2) m (r0 / &2)`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
    EXISTS_TAC `schz_cyl (ph1:real^2->real^2) M (r1 / &2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCHZ_CYL_MONO THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x. x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\ M - eps < x$3
             ==> x IN schz_cyl (ph1:real^2->real^2) M (r1 / &2)`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

let SCHZ_MODEL_CHART = prove
 (`!g g':real^3->real^3.
     sch_neck g g' /\ sch_morse g /\ sch_saddles g = {}
     ==> ?(Theta:real^3->real^3) U (cen:real^3) rho.
           open U /\ &0 < rho /\ cball(cen,rho) SUBSET U /\ smooth_map_on U Theta /\
           (!x y. x IN U /\ y IN U /\ Theta x = Theta y ==> x = y) /\
           (!x. x IN U ==> ~(det(matrix(frechet_derivative Theta (at x))) = &0)) /\
           IMAGE Theta (sphere(cen,rho)) SUBSET IMAGE g (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCHZ_TDATA_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Psi0:real^1->real^3->real^3` (X_CHOOSE_THEN `zA:real`
    (X_CHOOSE_THEN `zB:real` (X_CHOOSE_THEN `m:real` (X_CHOOSE_THEN `r0:real`
    (X_CHOOSE_THEN `ph0:real^2->real^2` (X_CHOOSE_THEN `ph0':real^2->real^2`
    (X_CHOOSE_THEN `z0:real` (X_CHOOSE_THEN `M:real` (X_CHOOSE_THEN `r1:real`
    (X_CHOOSE_THEN `ph1:real^2->real^2` (X_CHOOSE_THEN `ph1':real^2->real^2`
    (X_CHOOSE_THEN `b1:real` (X_CHOOSE_THEN `b2:real` ASSUME_TAC)))))))))))))) THEN
  SUBGOAL_THEN `compact(IMAGE (g:real^3->real^3) (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP SCHZ_SURFACE_FACTS (ASSUME `sch_neck (g:real^3->real^3) g'`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`;
                 `Psi0:real^1->real^3->real^3`; `zA:real`; `zB:real`;
                 `m:real`; `r0:real`; `ph0:real^2->real^2`; `ph0':real^2->real^2`; `z0:real`;
                 `M:real`; `r1:real`; `ph1:real^2->real^2`; `ph1':real^2->real^2`;
                 `b1:real`; `b2:real`; `(zA + z0) / &2`; `(b2 + zB) / &2`]
    SCHZ_NDATA_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SCHZ_TD_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Psi:real^1->real^3->real^3` (X_CHOOSE_THEN `kap:real`
    (MP_TAC o MATCH_MP SCHZ_MODEL_FROM_ND))) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The headline.  A model chart Theta of a round ball whose                  *)
(* boundary sphere goes into S (SCHZ_MODEL_CHART) gives the ball chart      *)
(* (SCHZ_BOUNDS_FROM_CHART), hence SCH_BASE0 |- SCH_BASE0_STATEMENT.         *)
(* ------------------------------------------------------------------------- *)

let SCH_BASE0 = prove
 (`SCH_BASE0_STATEMENT`,
  REWRITE_TAC[SCH_BASE0_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `g':real^3->real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCHZ_MODEL_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Theta:real^3->real^3` (X_CHOOSE_THEN `U:real^3->bool`
    (X_CHOOSE_THEN `cen:real^3` (X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC)))) THEN
  MATCH_MP_TAC SCHZ_BOUNDS_FROM_CHART THEN
  MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `Theta:real^3->real^3`; `U:real^3->bool`;
                        `cen:real^3`; `rho:real`] THEN
  ASM_REWRITE_TAC[]);;

