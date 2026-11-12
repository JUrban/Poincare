(* ========================================================================= *)
(* pc_moi_fnd_plst: foundations of the Moise PL core, basic facts on PL      *)
(* solid tori. Main theorem PL_SOLID_TORUS_BASIC (the statement term         *)
(* MOI_FND_PL_SOLID_TORUS_BASIC of pc_moi_fnd_stmt): a PL solid torus (PL    *)
(* image of the square annulus A times an interval I) is a solid torus with  *)
(* a PL 1-sphere spine, and in real^3 its frontier is PL homeomorphic to     *)
(* pl_torus_model.                                                           *)
(* Route: an explicit PL homeomorphism psi of A onto (boundary of the unit *)
(* square) times [1,2], affine on eight triangles, with the infinity norm  *)
(* as second coordinate; then A x I is PL homeomorphic to the boundary of   *)
(* the unit square times the unit square, the frontier of A x I going onto *)
(* pl_torus_model; the spine is the image of the core circle; in real^3    *)
(* the frontier of the image is the image of the frontier (invariance of   *)
(* domain).                                                                  *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_h1.ml";;
needs "src/pc_moi_fnd_m3a.ml";;
needs "src/pc_moi_ptri.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The square annulus A, the boundary                                       *)
(* sq of the unit square, and the map psi of A onto sq x [1,2]: on the      *)
(* right quarter (abs x2 <= x1) psi x = ((1, w x1 x2), x1) with             *)
(* w a b = max (b - a + 1) ((a + b) / 2 - 1), which is affine on the two    *)
(* triangles of the quarter cut by the diagonal from (1,-1) to (2,2); the  *)
(* other quarters are the rotations of this one.  Here: coordinates, the    *)
(* quarter formulas, psi maps A into sq x [1,2], injectively and onto.     *)
(* ========================================================================= *)

let moi_fps_ann = new_definition
 `moi_fps_ann = interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                interval(--vector[&1;&1]:real^2,vector[&1;&1])`;;

let moi_fps_sq = new_definition
 `moi_fps_sq = relative_frontier(interval[--vec 1:real^2,vec 1])`;;

let moi_fps_w = new_definition
 `moi_fps_w (a:real) (b:real) = max (b - a + &1) ((a + b) / &2 - &1)`;;

let moi_fps_pr = new_definition
 `moi_fps_pr (x:real^2) =
    pastecart (vector[&1; moi_fps_w (x$1) (x$2)]:real^2) (lift(x$1))`;;

let moi_fps_pt = new_definition
 `moi_fps_pt (x:real^2) =
    pastecart (vector[--(moi_fps_w (x$2) (--(x$1))); &1]:real^2) (lift(x$2))`;;

let moi_fps_pl = new_definition
 `moi_fps_pl (x:real^2) =
    pastecart (vector[-- &1; --(moi_fps_w (--(x$1)) (--(x$2)))]:real^2) (lift(--(x$1)))`;;

let moi_fps_pb = new_definition
 `moi_fps_pb (x:real^2) =
    pastecart (vector[moi_fps_w (--(x$2)) (x$1); -- &1]:real^2) (lift(--(x$2)))`;;

let moi_fps_psi = new_definition
 `moi_fps_psi (x:real^2) =
    if abs(x$2) <= x$1 then moi_fps_pr x
    else if abs(x$1) <= x$2 then moi_fps_pt x
    else if abs(x$2) <= --(x$1) then moi_fps_pl x
    else moi_fps_pb x`;;

let MOI_FPS_VEC1_2 = prove
 (`vec 1:real^2 = vector[&1;&1]`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT; VECTOR_2]);;

let MOI_FPS_ANN = prove
 (`!x:real^2. x IN moi_fps_ann <=>
              &1 <= max (abs(x$1)) (abs(x$2)) /\ max (abs(x$1)) (abs(x$2)) <= &2`,
  REWRITE_TAC[moi_fps_ann; MOI_FH1_SQUARE_ANNULUS_INFNORM; INFNORM_2]);;

let MOI_FPS_SQ = prove
 (`!x:real^2. x IN moi_fps_sq <=> max (abs(x$1)) (abs(x$2)) = &1`,
  GEN_TAC THEN REWRITE_TAC[moi_fps_sq; MOI_FPS_VEC1_2] THEN
  SIMP_TAC[MOI_FH1_SQUARE_FRONTIER_INFNORM; REAL_LT_01; INFNORM_2]);;

(* psi agrees with the quarter formula on each closed quarter of A. *)

let MOI_FPS_PSI_PIECES = prove
 (`!x:real^2.
     x IN moi_fps_ann
     ==> (abs(x$2) <= x$1 ==> moi_fps_psi x = moi_fps_pr x) /\
         (abs(x$1) <= x$2 ==> moi_fps_psi x = moi_fps_pt x) /\
         (abs(x$2) <= --(x$1) ==> moi_fps_psi x = moi_fps_pl x) /\
         (abs(x$1) <= --(x$2) ==> moi_fps_psi x = moi_fps_pb x)`,
  GEN_TAC THEN REWRITE_TAC[MOI_FPS_ANN; moi_fps_psi] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[moi_fps_pr; moi_fps_pt; moi_fps_pl; moi_fps_pb; PASTECART_INJ; LIFT_EQ] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; moi_fps_w] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_FPS_PSI_IN = prove
 (`!x:real^2.
     x IN moi_fps_ann ==> moi_fps_psi x IN moi_fps_sq PCROSS interval[lift(&1),lift(&2)]`,
  GEN_TAC THEN REWRITE_TAC[MOI_FPS_ANN; moi_fps_psi] THEN STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[moi_fps_pr; moi_fps_pt; moi_fps_pl; moi_fps_pb; PASTECART_IN_PCROSS;
              MOI_FPS_SQ; VECTOR_2; IN_INTERVAL_1; LIFT_DROP; moi_fps_w] THEN
  ASM_REAL_ARITH_TAC);;

let SPDR11_ANN_CASES = prove
 (`!a b. &1 <= max (abs a) (abs b) /\ max (abs a) (abs b) <= &2
         ==> (abs b <= a /\ --a <= b /\ b <= a /\ &1 <= a /\ a <= &2) \/
             (abs a <= b /\ --b <= a /\ a <= b /\ &1 <= b /\ b <= &2) \/
             (abs b <= --a /\ a <= b /\ b <= --a /\ &1 <= --a /\ --a <= &2) \/
             (abs a <= --b /\ b <= a /\ a <= --b /\ &1 <= --b /\ --b <= &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs b <= a \/ abs a <= b \/ abs b <= --a \/ abs a <= --b`
  STRIP_ASSUME_TAC THENL
   [REAL_ARITH_TAC;
    DISJ1_TAC THEN ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN DISJ1_TAC THEN ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN ASM_REAL_ARITH_TAC]);;

let SPDR11_PSI_CASES = prove
 (`!x:real^2.
     x IN moi_fps_ann
     ==> (moi_fps_psi x = moi_fps_pr x /\
          --(x$1) <= x$2 /\ x$2 <= x$1 /\ &1 <= x$1 /\ x$1 <= &2) \/
         (moi_fps_psi x = moi_fps_pt x /\
          --(x$2) <= x$1 /\ x$1 <= x$2 /\ &1 <= x$2 /\ x$2 <= &2) \/
         (moi_fps_psi x = moi_fps_pl x /\
          x$1 <= x$2 /\ x$2 <= --(x$1) /\ &1 <= --(x$1) /\ --(x$1) <= &2) \/
         (moi_fps_psi x = moi_fps_pb x /\
          x$2 <= x$1 /\ x$1 <= --(x$2) /\ &1 <= --(x$2) /\ --(x$2) <= &2)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP MOI_FPS_PSI_PIECES (ASSUME `(x:real^2) IN moi_fps_ann`)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SPDR11_ANN_CASES o REWRITE_RULE[MOI_FPS_ANN]) THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let MOI_FPS_PSI_INJ = prove
 (`!x y:real^2.
     x IN moi_fps_ann /\ y IN moi_fps_ann /\ moi_fps_psi x = moi_fps_psi y ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2(CONJUNCT2 th)) THEN
    MP_TAC(MATCH_MP SPDR11_PSI_CASES (CONJUNCT1(CONJUNCT2 th))) THEN
    MP_TAC(MATCH_MP SPDR11_PSI_CASES (CONJUNCT1 th))) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[moi_fps_pr; moi_fps_pt; moi_fps_pl; moi_fps_pb; PASTECART_INJ; LIFT_EQ] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; moi_fps_w] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_FPS_PSI_ONTO = prove
 (`!z. z IN moi_fps_sq PCROSS interval[lift(&1),lift(&2)]
       ==> ?x:real^2. x IN moi_fps_ann /\ moi_fps_psi x = z`,
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; MOI_FPS_SQ; IN_INTERVAL_1; LIFT_DROP] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `t:real^1`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^2)$1 = &1 \/ u$2 = &1 \/ u$1 = -- &1 \/ u$2 = -- &1` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `vector[drop t; min ((u:real^2)$2 + drop t - &1)
                                   (&2 * u$2 + &2 - drop t)]:real^2` THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[MOI_FPS_ANN; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP MOI_FPS_PSI_PIECES)] THEN
    ANTS_TAC THENL [REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC];
    EXISTS_TAC `vector[--(min (--((u:real^2)$1) + drop t - &1)
                              (&2 * --(u$1) + &2 - drop t)); drop t]:real^2` THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[MOI_FPS_ANN; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP MOI_FPS_PSI_PIECES)] THEN
    ANTS_TAC THENL [REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC];
    EXISTS_TAC `vector[--(drop t); --(min (--((u:real^2)$2) + drop t - &1)
                                         (&2 * --(u$2) + &2 - drop t))]:real^2` THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[MOI_FPS_ANN; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o MATCH_MP MOI_FPS_PSI_PIECES)] THEN
    ANTS_TAC THENL [REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC];
    EXISTS_TAC `vector[min ((u:real^2)$1 + drop t - &1) (&2 * u$1 + &2 - drop t);
                       --(drop t)]:real^2` THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[MOI_FPS_ANN; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o MATCH_MP MOI_FPS_PSI_PIECES)] THEN
    ANTS_TAC THENL [REWRITE_TAC[VECTOR_2] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC]] THEN
  REWRITE_TAC[moi_fps_pr; moi_fps_pt; moi_fps_pl; moi_fps_pb; PASTECART_INJ; VECTOR_2;
              REAL_NEG_NEG; LIFT_DROP] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; moi_fps_w] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* psi is PL on A (the quarter formulas                                    *)
(* are PL on the plane by MOI_PTR_PL_LIFT_MAX; the four closed quarters are *)
(* polytopes; PL_MAP_ON_UNION), so it is a PL homeomorphism of A onto      *)
(* sq x [1,2] (HOMEOMORPHISM_COMPACT, HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM).  *)
(* ========================================================================= *)

let MOI_FPS_LP_UNIV2 = prove
 (`locally_polyhedral (:real^2)`,
  SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]);;

let MOI_FPS_PL_AFF2 = prove
 (`!a b c. pl_map_on (:real^2) (\x. lift(a * x$1 + b * x$2 + c))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. lift(a * x$1 + b * x$2)`; `lift c`]
                PL_MAP_ON_AFFINE) THEN
  REWRITE_TAC[MOI_FPS_LP_UNIV2] THEN ANTS_TAC THENL
   [REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; GSYM LIFT_ADD;
                GSYM LIFT_CMUL; LIFT_EQ] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] PL_MAP_ON_EQ) THEN
    REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ] THEN REAL_ARITH_TAC]);;

let MOI_FPS_PL_W2 = prove
 (`!a1 b1 c1 a2 b2 c2.
     pl_map_on (:real^2)
       (\x. lift(moi_fps_w (a1 * x$1 + b1 * x$2 + c1) (a2 * x$1 + b2 * x$2 + c2)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fps_w] THEN
  MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`a2 - a1`; `b2 - b1`; `c2 - c1 + &1`] MOI_FPS_PL_AFF2);
    MP_TAC(SPECL [`(a1 + a2) / &2`; `(b1 + b2) / &2`; `(c1 + c2) / &2 - &1`]
                 MOI_FPS_PL_AFF2)] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] PL_MAP_ON_EQ) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_EQ] THEN REAL_ARITH_TAC);;

let MOI_FPS_PL_VEC2 = prove
 (`!f g. pl_map_on (:real^2) (\x. lift(f x)) /\ pl_map_on (:real^2) (\x. lift(g x))
         ==> pl_map_on (:real^2) (\x. vector[f x; g x]:real^2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_map_on (:real^2) ((\z:real^(1,1)finite_sum. vector[drop(fstcart z); drop(sndcart z)]:real^2) o
                         (\x. pastecart (lift(f x)) (lift(g x))))`
  MP_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^(1,1)finite_sum)` THEN
    ASM_SIMP_TAC[PL_MAP_ON_PASTECART; SUBSET_UNIV] THEN
    MATCH_MP_TAC MOI_PTR_PL_MAP_ON_LINEAR THEN
    SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                DROP_ADD; DROP_CMUL];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] PL_MAP_ON_EQ) THEN
    REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]]);;

let MOI_FPS_AFF_TAC a b c =
  MP_TAC(SPECL [a; b; c] MOI_FPS_PL_AFF2) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] PL_MAP_ON_EQ) THEN
  REWRITE_TAC[IN_UNIV; LIFT_EQ] THEN REAL_ARITH_TAC;;

let MOI_FPS_W_TAC l =
  MP_TAC(SPECL l MOI_FPS_PL_W2) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] PL_MAP_ON_EQ) THEN
  REWRITE_TAC[IN_UNIV; LIFT_EQ; moi_fps_w] THEN REAL_ARITH_TAC;;

let MOI_FPS_NW_TAC l =
  MP_TAC(SPEC `-- &1` (MATCH_MP MOI_PTR_PL_LIFT_CMUL (SPECL l MOI_FPS_PL_W2))) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] PL_MAP_ON_EQ) THEN
  REWRITE_TAC[IN_UNIV; LIFT_EQ; moi_fps_w] THEN REAL_ARITH_TAC;;

let MOI_FPS_PR_PL = prove
 (`pl_map_on (:real^2) moi_fps_pr`,
  SUBGOAL_THEN
   `moi_fps_pr =
    (\x:real^2. pastecart (vector[&1; moi_fps_w (x$1) (x$2)]:real^2) (lift(x$1)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_fps_pr]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_PASTECART THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FPS_PL_VEC2 THEN CONJ_TAC THENL
     [MOI_FPS_AFF_TAC `&0` `&0` `&1`;
      MOI_FPS_W_TAC [`&1`; `&0`; `&0`; `&0`; `&1`; `&0`]];
    MOI_FPS_AFF_TAC `&1` `&0` `&0`]);;

let MOI_FPS_PT_PL = prove
 (`pl_map_on (:real^2) moi_fps_pt`,
  SUBGOAL_THEN
   `moi_fps_pt =
    (\x:real^2. pastecart (vector[--(moi_fps_w (x$2) (--(x$1))); &1]:real^2) (lift(x$2)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_fps_pt]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_PASTECART THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FPS_PL_VEC2 THEN CONJ_TAC THENL
     [MOI_FPS_NW_TAC [`&0`; `&1`; `&0`; `-- &1`; `&0`; `&0`];
      MOI_FPS_AFF_TAC `&0` `&0` `&1`];
    MOI_FPS_AFF_TAC `&0` `&1` `&0`]);;

let MOI_FPS_PL_PL = prove
 (`pl_map_on (:real^2) moi_fps_pl`,
  SUBGOAL_THEN
   `moi_fps_pl =
    (\x:real^2. pastecart (vector[-- &1; --(moi_fps_w (--(x$1)) (--(x$2)))]:real^2)
                          (lift(--(x$1))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_fps_pl]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_PASTECART THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FPS_PL_VEC2 THEN CONJ_TAC THENL
     [MOI_FPS_AFF_TAC `&0` `&0` `-- &1`;
      MOI_FPS_NW_TAC [`-- &1`; `&0`; `&0`; `&0`; `-- &1`; `&0`]];
    MOI_FPS_AFF_TAC `-- &1` `&0` `&0`]);;

let MOI_FPS_PB_PL = prove
 (`pl_map_on (:real^2) moi_fps_pb`,
  SUBGOAL_THEN
   `moi_fps_pb =
    (\x:real^2. pastecart (vector[moi_fps_w (--(x$2)) (x$1); -- &1]:real^2) (lift(--(x$2))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_fps_pb]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_PASTECART THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FPS_PL_VEC2 THEN CONJ_TAC THENL
     [MOI_FPS_W_TAC [`&0`; `-- &1`; `&0`; `&1`; `&0`; `&0`];
      MOI_FPS_AFF_TAC `&0` `&0` `-- &1`];
    MOI_FPS_AFF_TAC `&0` `-- &1` `&0`]);;

(* The four closed quarters of A are polytopes cut out of the square of side *)
(* 4 by three half-planes each; psi is PL on each and hence on A.            *)

let MOI_FPS_POLY3 = prove
 (`!a b c d e f.
     polytope(interval[--vector[&2;&2]:real^2,vector[&2;&2]] INTER
              {x:real^2 | a dot x <= b} INTER {x:real^2 | c dot x <= d} INTER
              {x:real^2 | e dot x <= f})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
  REWRITE_TAC[POLYTOPE_INTERVAL] THEN
  REPEAT(MATCH_MP_TAC POLYHEDRON_INTER THEN CONJ_TAC) THEN
  REWRITE_TAC[POLYHEDRON_HALFSPACE_LE]);;

let MOI_FPS_PIECE_PL = prove
 (`!a b c d e f (q:real^2->real^(2,1)finite_sum).
     pl_map_on (:real^2) q /\
     (!x. x IN interval[--vector[&2;&2],vector[&2;&2]] /\
          a dot x <= b /\ c dot x <= d /\ e dot x <= f
          ==> moi_fps_psi x = q x)
     ==> pl_map_on (interval[--vector[&2;&2]:real^2,vector[&2;&2]] INTER
                    {x:real^2 | a dot x <= b} INTER {x:real^2 | c dot x <= d} INTER
                    {x:real^2 | e dot x <= f})
                   moi_fps_psi`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `q:real^2->real^(2,1)finite_sum` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; LOCALLY_POLYHEDRAL_POLYTOPE; MOI_FPS_POLY3]]);;

let MOI_FPS_PL_UNION_CLOSED = prove
 (`!(s:real^M->bool) t (f:real^M->real^N).
     pl_map_on s f /\ pl_map_on t f /\ closed s /\ closed t
     ==> pl_map_on (s UNION t) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_UNION THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC CLOSED_SUBSET THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_FPS_ANN_SPLIT = prove
 (`moi_fps_ann =
   ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] INTER
     {x:real^2 | vector[-- &1;&0] dot x <= -- &1} INTER
     {x:real^2 | vector[-- &1;&1] dot x <= &0} INTER
     {x:real^2 | vector[-- &1;-- &1] dot x <= &0}) UNION
    (interval[--vector[&2;&2]:real^2,vector[&2;&2]] INTER
     {x:real^2 | vector[&0;-- &1] dot x <= -- &1} INTER
     {x:real^2 | vector[&1;-- &1] dot x <= &0} INTER
     {x:real^2 | vector[-- &1;-- &1] dot x <= &0})) UNION
   ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] INTER
     {x:real^2 | vector[&1;&0] dot x <= -- &1} INTER
     {x:real^2 | vector[&1;&1] dot x <= &0} INTER
     {x:real^2 | vector[&1;-- &1] dot x <= &0}) UNION
    (interval[--vector[&2;&2]:real^2,vector[&2;&2]] INTER
     {x:real^2 | vector[&0;&1] dot x <= -- &1} INTER
     {x:real^2 | vector[&1;&1] dot x <= &0} INTER
     {x:real^2 | vector[-- &1;&1] dot x <= &0}))`,
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_ELIM_THM; MOI_FPS_ANN; IN_INTERVAL;
              DIMINDEX_2; FORALL_2; DOT_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP SPDR11_ANN_CASES) THEN STRIP_TAC THENL
     [DISJ1_TAC THEN DISJ1_TAC; DISJ1_TAC THEN DISJ2_TAC;
      DISJ2_TAC THEN DISJ1_TAC; DISJ2_TAC THEN DISJ2_TAC] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN ASM_REAL_ARITH_TAC]);;

let MOI_FPS_LEAF_TAC q qth sel =
  MATCH_MP_TAC MOI_FPS_PIECE_PL THEN EXISTS_TAC q THEN REWRITE_TAC[qth] THEN
  X_GEN_TAC `x:real^2` THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; DOT_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `x:real^2` MOI_FPS_PSI_PIECES) THEN
  REWRITE_TAC[MOI_FPS_ANN] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o sel) THEN ASM_REAL_ARITH_TAC;;

let MOI_FPS_PSI_PL = prove
 (`pl_map_on moi_fps_ann moi_fps_psi`,
  ONCE_REWRITE_TAC[MOI_FPS_ANN_SPLIT] THEN
  REPEAT(MATCH_MP_TAC MOI_FPS_PL_UNION_CLOSED THEN
         SIMP_TAC[CLOSED_UNION; POLYTOPE_IMP_CLOSED; MOI_FPS_POLY3] THEN CONJ_TAC) THENL
   [MOI_FPS_LEAF_TAC `moi_fps_pr` MOI_FPS_PR_PL CONJUNCT1;
    MOI_FPS_LEAF_TAC `moi_fps_pt` MOI_FPS_PT_PL (CONJUNCT1 o CONJUNCT2);
    MOI_FPS_LEAF_TAC `moi_fps_pl` MOI_FPS_PL_PL (CONJUNCT1 o CONJUNCT2 o CONJUNCT2);
    MOI_FPS_LEAF_TAC `moi_fps_pb` MOI_FPS_PB_PL (CONJUNCT2 o CONJUNCT2 o CONJUNCT2)]);;

let MOI_FPS_PSI_PLH = prove
 (`?phi. pl_homeomorphism (moi_fps_ann,moi_fps_sq PCROSS interval[lift(&1),lift(&2)])
                          (moi_fps_psi,phi)`,
  MP_TAC(ISPECL [`moi_fps_ann`; `moi_fps_psi`;
                 `moi_fps_sq PCROSS interval[lift(&1),lift(&2)]`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[moi_fps_ann] THEN MATCH_MP_TAC COMPACT_DIFF THEN
      REWRITE_TAC[COMPACT_INTERVAL; OPEN_INTERVAL];
      MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN REWRITE_TAC[MOI_FPS_PSI_PL];
      REWRITE_TAC[EXTENSION; IN_IMAGE] THEN MESON_TAC[MOI_FPS_PSI_IN; MOI_FPS_PSI_ONTO];
      MATCH_ACCEPT_TAC MOI_FPS_PSI_INJ];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `phi:real^(2,1)finite_sum->real^2` THEN
    DISCH_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
    ASM_REWRITE_TAC[MOI_FPS_PSI_PL]]);;

(* ========================================================================= *)
(* The model M = A x [-1,1] and the map                                     *)
(* theta of M onto sq x Q (Q the square [-1,1]^2): theta (x,t) =            *)
(* (u, (2 r - 3, t)) where psi x = (u,r).  theta is a PL homeomorphism and  *)
(* maps the frontier of M (in real^3) onto sq x sq, the PL torus model.     *)
(* ========================================================================= *)

let moi_fps_m = new_definition
 `moi_fps_m = moi_fps_ann PCROSS interval[--vec 1:real^1,vec 1]`;;

let moi_fps_th = new_definition
 `moi_fps_th (z:real^(2,1)finite_sum) =
    pastecart (fstcart(moi_fps_psi(fstcart z)))
              (vector[&2 * drop(sndcart(moi_fps_psi(fstcart z))) - &3;
                      drop(sndcart z)]:real^2)`;;

let MOI_FPS_VECTOR2_EQ = prove
 (`!a b c d. vector[a;b]:real^2 = vector[c;d] <=> a = c /\ b = d`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

(* Finite unions of polytopes are closed under products. *)

let MOI_FPS_PL_POLYHEDRON_PCROSS = prove
 (`!(s:real^M->bool) (t:real^N->bool).
     pl_polyhedron s /\ pl_polyhedron t ==> pl_polyhedron (s PCROSS t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `c:(real^M->bool)->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `{(k:real^M->bool) PCROSS (l:real^N->bool) | k IN c /\ l IN d}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[PCROSS_UNIONS_UNIONS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[POLYTOPE_PCROSS]]);;

let MOI_FPS_ANN_PL_POLYHEDRON = prove
 (`pl_polyhedron moi_fps_ann`,
  ONCE_REWRITE_TAC[MOI_FPS_ANN_SPLIT] THEN
  REPEAT(MATCH_MP_TAC PL_POLYHEDRON_UNION THEN CONJ_TAC) THEN
  MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[MOI_FPS_POLY3]);;

let MOI_FPS_M_PL_POLYHEDRON = prove
 (`pl_polyhedron moi_fps_m`,
  REWRITE_TAC[moi_fps_m] THEN MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN
  SIMP_TAC[MOI_FPS_ANN_PL_POLYHEDRON; POLYTOPE_IMP_PL_POLYHEDRON; POLYTOPE_INTERVAL]);;

let MOI_FPS_SQ_PL_POLYHEDRON = prove
 (`pl_polyhedron moi_fps_sq`,
  REWRITE_TAC[moi_fps_sq] THEN MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
  REWRITE_TAC[POLYTOPE_INTERVAL]);;

let MOI_FPS_M_COMPACT = prove
 (`compact moi_fps_m`,
  REWRITE_TAC[moi_fps_m; moi_fps_ann] THEN MATCH_MP_TAC COMPACT_PCROSS THEN
  SIMP_TAC[COMPACT_DIFF; COMPACT_INTERVAL; OPEN_INTERVAL]);;

(* The two components of psi: a point of sq, and the square norm of x. *)

let MOI_FPS_PSI_COMPONENTS = prove
 (`!x:real^2.
     x IN moi_fps_ann
     ==> fstcart(moi_fps_psi x) IN moi_fps_sq /\
         drop(sndcart(moi_fps_psi x)) = max (abs(x$1)) (abs(x$2))`,
  GEN_TAC THEN REWRITE_TAC[MOI_FPS_ANN; MOI_FPS_SQ; moi_fps_psi] THEN STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[moi_fps_pr; moi_fps_pt; moi_fps_pl; moi_fps_pb; FSTCART_PASTECART;
              SNDCART_PASTECART; LIFT_DROP; VECTOR_2; moi_fps_w] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_FPS_TH_IN = prove
 (`!z. z IN moi_fps_m ==> moi_fps_th z IN moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1]`,
  REWRITE_TAC[moi_fps_m; FORALL_PASTECART; PASTECART_IN_PCROSS; moi_fps_th;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `t:real^1`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FPS_PSI_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^2) IN moi_fps_ann` THEN
  UNDISCH_TAC `(t:real^1) IN interval[--vec 1,vec 1]` THEN
  REWRITE_TAC[MOI_FPS_ANN; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT;
              VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_FPS_TH_INJ = prove
 (`!z w. z IN moi_fps_m /\ w IN moi_fps_m /\ moi_fps_th z = moi_fps_th w ==> z = w`,
  REWRITE_TAC[moi_fps_m; FORALL_PASTECART; PASTECART_IN_PCROSS; moi_fps_th;
              FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_INJ; MOI_FPS_VECTOR2_EQ] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `t:real^1`; `y:real^2`; `r:real^1`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_fps_psi x = moi_fps_psi y` ASSUME_TAC THENL
   [REWRITE_TAC[PASTECART_EQ] THEN ASM_REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[GSYM DROP_EQ] THEN ASM_MESON_TAC[MOI_FPS_PSI_INJ]]);;

let MOI_FPS_TH_ONTO = prove
 (`!w. w IN moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1]
       ==> ?z. z IN moi_fps_m /\ moi_fps_th z = w`,
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `pastecart (u:real^2) (lift(((v:real^2)$1 + &3) / &2))` MOI_FPS_PSI_ONTO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    UNDISCH_TAC `(v:real^2) IN interval[--vec 1,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `pastecart (x:real^2) (lift((v:real^2)$2))` THEN
  ASM_REWRITE_TAC[moi_fps_m; PASTECART_IN_PCROSS; moi_fps_th; FSTCART_PASTECART;
                  SNDCART_PASTECART; LIFT_DROP; PASTECART_INJ] THEN
  UNDISCH_TAC `(v:real^2) IN interval[--vec 1,vec 1]` THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_NEG; DROP_VEC] THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT;
              VEC_COMPONENT] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC);;

(* theta is PL: an affine map after the map (x,t) to (psi x, t). *)

let MOI_FPS_TH_OUTER_PL = prove
 (`pl_map_on (:real^((2,1)finite_sum,1)finite_sum)
     (\w. pastecart (fstcart(fstcart w))
                    (vector[&2 * drop(sndcart(fstcart w)) - &3; drop(sndcart w)]:real^2))`,
  MP_TAC(ISPECL
   [`(:real^((2,1)finite_sum,1)finite_sum)`;
    `\w:real^((2,1)finite_sum,1)finite_sum.
        pastecart (fstcart(fstcart w))
                  (vector[&2 * drop(sndcart(fstcart w)); drop(sndcart w)]:real^2)`;
    `pastecart (vec 0:real^2) (vector[-- &3; &0]:real^2)`] PL_MAP_ON_AFFINE) THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN ANTS_TAC THENL
   [REWRITE_TAC[linear; PASTECART_ADD; GSYM PASTECART_CMUL; FSTCART_ADD; SNDCART_ADD;
                FSTCART_CMUL; SNDCART_CMUL; DROP_ADD; DROP_CMUL; PASTECART_INJ] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] PL_MAP_ON_EQ) THEN
    REWRITE_TAC[IN_UNIV; PASTECART_ADD; VECTOR_ADD_RID; PASTECART_INJ] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let MOI_FPS_TH_PL = prove
 (`pl_map_on moi_fps_m moi_fps_th`,
  SUBGOAL_THEN `locally_polyhedral moi_fps_m` ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    REWRITE_TAC[MOI_FPS_M_PL_POLYHEDRON]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fps_th =
    (\w:real^((2,1)finite_sum,1)finite_sum.
       pastecart (fstcart(fstcart w))
                 (vector[&2 * drop(sndcart(fstcart w)) - &3; drop(sndcart w)]:real^2)) o
    (\z:real^(2,1)finite_sum. pastecart ((moi_fps_psi o fstcart) z) (sndcart z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; moi_fps_th; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
  EXISTS_TAC `(:real^((2,1)finite_sum,1)finite_sum)` THEN
  REWRITE_TAC[SUBSET_UNIV; MOI_FPS_TH_OUTER_PL] THEN
  MATCH_MP_TAC PL_MAP_ON_PASTECART THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `moi_fps_ann` THEN
    REWRITE_TAC[MOI_FPS_PSI_PL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PTR_PL_MAP_ON_LINEAR THEN ASM_REWRITE_TAC[LINEAR_FSTCART];
      REWRITE_TAC[moi_fps_m; SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART;
                  PASTECART_IN_PCROSS; FSTCART_PASTECART] THEN
      SIMP_TAC[]];
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC MOI_PTR_PL_MAP_ON_LINEAR THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART]]);;

let MOI_FPS_TH_PLH = prove
 (`?th'. pl_homeomorphism (moi_fps_m,moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1])
                          (moi_fps_th,th')`,
  MP_TAC(ISPECL [`moi_fps_m`; `moi_fps_th`;
                 `moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1]`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_FPS_M_COMPACT];
      MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN REWRITE_TAC[MOI_FPS_TH_PL];
      REWRITE_TAC[EXTENSION; IN_IMAGE] THEN MESON_TAC[MOI_FPS_TH_IN; MOI_FPS_TH_ONTO];
      MATCH_ACCEPT_TAC MOI_FPS_TH_INJ];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `th':real^(2,2)finite_sum->real^(2,1)finite_sum` THEN
    DISCH_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
    ASM_REWRITE_TAC[MOI_FPS_TH_PL]]);;

(* The frontier of M in real^3 and its image sq x sq. *)

let MOI_FPS_ANN_INTERIOR = prove
 (`!x:real^2. x IN interior moi_fps_ann <=>
              &1 < max (abs(x$1)) (abs(x$2)) /\ max (abs(x$1)) (abs(x$2)) < &2`,
  GEN_TAC THEN REWRITE_TAC[moi_fps_ann] THEN
  ONCE_REWRITE_TAC[SET_RULE `(s:real^2->bool) DIFF t = s INTER (UNIV DIFF t)`] THEN
  REWRITE_TAC[INTERIOR_INTER; INTERIOR_COMPLEMENT; INTERIOR_CLOSED_INTERVAL] THEN
  SUBGOAL_THEN
   `closure(interval(--vector[&1;&1]:real^2,vector[&1;&1])) =
    interval[--vector[&1;&1],vector[&1;&1]]`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
    REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VECTOR_2;
                VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_FPS_M_FRONTIER = prove
 (`!x:real^2 t:real^1.
     pastecart x t IN frontier moi_fps_m <=>
     &1 <= max (abs(x$1)) (abs(x$2)) /\ max (abs(x$1)) (abs(x$2)) <= &2 /\
     abs(drop t) <= &1 /\
     (max (abs(x$1)) (abs(x$2)) = &1 \/ max (abs(x$1)) (abs(x$2)) = &2 \/
      abs(drop t) = &1)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED; MOI_FPS_M_COMPACT] THEN
  REWRITE_TAC[moi_fps_m; INTERIOR_PCROSS; IN_DIFF; PASTECART_IN_PCROSS; MOI_FPS_ANN;
              MOI_FPS_ANN_INTERIOR; INTERIOR_CLOSED_INTERVAL; IN_INTERVAL_1; DROP_NEG;
              DROP_VEC] THEN
  REAL_ARITH_TAC);;

let MOI_FPS_TH_FRONTIER = prove
 (`IMAGE moi_fps_th (frontier moi_fps_m) = moi_fps_sq PCROSS moi_fps_sq`,
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_IMAGE;
              EXISTS_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `t:real^1`] THEN
    REWRITE_TAC[MOI_FPS_M_FRONTIER; moi_fps_th; FSTCART_PASTECART; SNDCART_PASTECART;
                PASTECART_INJ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^2) IN moi_fps_ann` ASSUME_TAC THENL
     [REWRITE_TAC[MOI_FPS_ANN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FPS_PSI_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[MOI_FPS_SQ; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    MP_TAC(SPEC `pastecart (u:real^2) (lift(((v:real^2)$1 + &3) / &2))`
                MOI_FPS_PSI_ONTO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      UNDISCH_TAC `(v:real^2) IN moi_fps_sq` THEN REWRITE_TAC[MOI_FPS_SQ] THEN
      REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `max (abs((x:real^2)$1)) (abs(x$2)) = ((v:real^2)$1 + &3) / &2`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP MOI_FPS_PSI_COMPONENTS) THEN
      ASM_REWRITE_TAC[SNDCART_PASTECART; LIFT_DROP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`x:real^2`; `lift((v:real^2)$2)`] THEN
    REWRITE_TAC[MOI_FPS_M_FRONTIER; moi_fps_th; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP] THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; PASTECART_INJ] THEN
    UNDISCH_TAC `(v:real^2) IN moi_fps_sq` THEN
    REWRITE_TAC[MOI_FPS_SQ; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Tools for the main theorem. Products of homeomorphisms with the factors   *)
(* exchanged; restriction of a PL                                            *)
(* homeomorphism to a locally polyhedral subset; a homeomorphism of closed  *)
(* sets in spaces of equal dimension maps frontier onto frontier            *)
(* (invariance of domain); the square sq is a PL 1-sphere; the disc and the *)
(* square Q are homeomorphic with the centre of Q coming from the open disc; *)
(* the PL 1-sphere sq x 0 inside sq x Q; the dimension bound 3 <= N.        *)
(* ========================================================================= *)

let MOI_FPS_HOMEOMORPHISM_PCROSS_SWAP = prove
 (`!(s:real^M->bool) (s':real^P->bool) (t:real^N->bool) (t':real^Q->bool)
    f f' g g'.
     homeomorphism (s,s') (f,f') /\ homeomorphism (t,t') (g,g')
     ==> homeomorphism (s PCROSS t,t' PCROSS s')
           ((\z. pastecart (g(sndcart z)) (f(fstcart z))),
            (\w. pastecart (f'(sndcart w)) (g'(fstcart w))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHISM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
               PASTECART_IN_PCROSS] THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
  CONJ_TAC THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_FSTCART; LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS; SUBSET] THEN
  SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART]);;

let MOI_FPS_PLH_RESTRICT = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g s'.
     pl_homeomorphism (s,t) (f,g) /\ s' SUBSET s /\ locally_polyhedral s'
     ==> pl_homeomorphism (s',IMAGE f s') (f,g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FPS_HOMEOMORPHISM_FRONTIER = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g.
     dimindex(:M) = dimindex(:N) /\ homeomorphism (s,t) (f,g) /\
     closed s /\ closed t
     ==> IMAGE f (frontier s) = frontier t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `!x. x IN interior s ==> (f:real^M->real^N) x IN interior t`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`]
                  CONTINUOUS_IMAGE_SUBSET_INTERIOR) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN interior t ==> (g:real^N->real^M) y IN interior s`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^N->real^M`; `t:real^N->bool`]
                  CONTINUOUS_IMAGE_SUBSET_INTERIOR) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^M->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `t:real^N->bool` INTERIOR_SUBSET) THEN
  REWRITE_TAC[SUBSET] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `y:real^N` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^M->real^N) s = t` THEN
      UNDISCH_TAC `(x:real^M) IN s` THEN SET_TAC[];
      ASM_MESON_TAC[]];
    STRIP_TAC THEN EXISTS_TAC `(g:real^N->real^M) y` THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^N->real^M) t = s` THEN
      UNDISCH_TAC `(y:real^N) IN t` THEN SET_TAC[];
      ASM_MESON_TAC[]]]);;

let MOI_FPS_SQ_INFNORM = prove
 (`!x:real^2. x IN moi_fps_sq <=> infnorm x = &1`,
  REWRITE_TAC[MOI_FPS_SQ; INFNORM_2]);;

let MOI_FPS_SQ_PL_SPHERE = prove
 (`pl_sphere 1 moi_fps_sq`,
  MP_TAC(ISPEC `moi_fps_sq` MOI_CMB_STAR_SHAPED_PL_SPHERE_0) THEN
  REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[MOI_FPS_SQ_PL_POLYHEDRON; MOI_FPS_SQ_INFNORM; INFNORM_0; INFNORM_MUL] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `u:real^2` THEN REWRITE_TAC[GSYM INFNORM_POS_LT] THEN DISCH_TAC THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `inv(infnorm(u:real^2))` THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    MAP_EVERY X_GEN_TAC [`r:real`; `r':real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs r = r /\ abs r' = r'` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`r:real`; `r':real`; `infnorm(u:real^2)`] REAL_EQ_MUL_RCANCEL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN ASM_MESON_TAC[]]);;

let MOI_FPS_DISC_SQUARE = prove
 (`?a a'. homeomorphism (cball(vec 0:real^2,&1),interval[--vec 1:real^2,vec 1]) (a,a') /\
          a'(vec 0) IN ball(vec 0:real^2,&1)`,
  MP_TAC(ISPECL [`interval[--vec 1:real^2,vec 1]`; `vec 0:real^2`; `&1`]
                HOMEOMORPHIC_CONVEX_COMPACT_CBALL) THEN
  REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL; REAL_LT_01; INTERIOR_CLOSED_INTERVAL;
              INTERVAL_NE_EMPTY] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^2->real^2` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a':real^2->real^2` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPECL [`a':real^2->real^2`; `interval[--vec 1:real^2,vec 1]`]
                CONTINUOUS_IMAGE_SUBSET_INTERIOR) THEN
  ASM_REWRITE_TAC[LE_REFL; INTERIOR_CBALL; INTERIOR_CLOSED_INTERVAL] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC);;

let MOI_FPS_SQ_COMPACT = prove
 (`compact moi_fps_sq`,
  REWRITE_TAC[moi_fps_sq] THEN MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN
  REWRITE_TAC[BOUNDED_INTERVAL]);;

let MOI_FPS_SQ_SLICE_PLH = prove
 (`?e'. pl_homeomorphism (moi_fps_sq,moi_fps_sq PCROSS {vec 0:real^2})
                         ((\u. pastecart u (vec 0)),e')`,
  MP_TAC(ISPECL [`moi_fps_sq`; `(\u:real^2. pastecart u (vec 0:real^2))`;
                 `moi_fps_sq PCROSS {vec 0:real^2}`] HOMEOMORPHISM_COMPACT) THEN
  SUBGOAL_THEN `pl_map_on moi_fps_sq (\u:real^2. pastecart u (vec 0:real^2))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_PASTECART THEN
    SUBGOAL_THEN `locally_polyhedral moi_fps_sq` ASSUME_TAC THENL
     [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      REWRITE_TAC[MOI_FPS_SQ_PL_POLYHEDRON]; ALL_TAC] THEN
    ASM_SIMP_TAC[PL_MAP_ON_CONST] THEN MATCH_MP_TAC MOI_PTR_PL_MAP_ON_LINEAR THEN
    ASM_REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_FPS_SQ_COMPACT];
      MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING;
                  PASTECART_INJ] THEN MESON_TAC[];
      REWRITE_TAC[PASTECART_INJ] THEN MESON_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e':real^(2,2)finite_sum->real^2` THEN
    DISCH_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FPS_SPINE_PL_SPHERE = prove
 (`!(s:real^N->bool) h k.
     pl_homeomorphism (moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1],s) (h,k) /\
     2 <= dimindex(:N)
     ==> pl_sphere 1 (IMAGE h (moi_fps_sq PCROSS {vec 0:real^2}))`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `e':real^(2,2)finite_sum->real^2` MOI_FPS_SQ_SLICE_PLH THEN
  SUBGOAL_THEN
   `pl_homeomorphism (moi_fps_sq PCROSS {vec 0:real^2},
                      IMAGE (h:real^(2,2)finite_sum->real^N)
                            (moi_fps_sq PCROSS {vec 0:real^2})) (h,k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FPS_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1]`;
                          `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; SING_SUBSET] THEN
      REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN
      SIMP_TAC[MOI_FPS_SQ_PL_POLYHEDRON; POLYTOPE_IMP_PL_POLYHEDRON; POLYTOPE_SING]];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `moi_fps_sq` MOI_FM3_PL_SPHERE_TRANSFER) THEN
  MAP_EVERY EXISTS_TAC
   [`(h:real^(2,2)finite_sum->real^N) o (\u:real^2. pastecart u (vec 0:real^2))`;
    `(e':real^(2,2)finite_sum->real^2) o (k:real^N->real^(2,2)finite_sum)`] THEN
  ASM_REWRITE_TAC[MOI_FPS_SQ_PL_SPHERE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `moi_fps_sq PCROSS {vec 0:real^2}` THEN ASM_REWRITE_TAC[];
    ASM_ARITH_TAC]);;

let MOI_FPS_DIM_GE3 = prove
 (`!(s:real^N->bool) (f:real^(2,1)finite_sum->real^N) g.
     homeomorphism (moi_fps_m,s) (f,g) ==> 3 <= dimindex(:N)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPECL [`f:real^(2,1)finite_sum->real^N`; `interior moi_fps_m`]
                INVARIANCE_OF_DIMENSION) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_2; DIMINDEX_1; OPEN_INTERIOR] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPEC `moi_fps_m` INTERIOR_SUBSET) THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `pastecart (vector[&3 / &2; &0]:real^2) (vec 0:real^1)` THEN
    REWRITE_TAC[moi_fps_m; INTERIOR_PCROSS; PASTECART_IN_PCROSS; MOI_FPS_ANN_INTERIOR;
                INTERIOR_CLOSED_INTERVAL; IN_INTERVAL_1; VECTOR_2; DROP_NEG; DROP_VEC] THEN
    REAL_ARITH_TAC;
    ASM SET_TAC[]]);;

(* ========================================================================= *)
(* The main theorem PL_SOLID_TORUS_BASIC.                                   *)
(* For a PL solid torus s with f : M to s, the map h = f o theta^-1 is a PL *)
(* homeomorphism of sq x Q onto s carrying sq x sq onto f(frontier M).      *)
(* (1) s is a solid torus and J = h(sq x 0) is a spine and a PL 1-sphere:   *)
(* precompose h with the disc-square and circle-square homeomorphisms; the  *)
(* point p = a'(0) lies in the open disc.  (2) In real^3, invariance of     *)
(* domain gives frontier s = f(frontier M) = h(sq x sq), so h restricts to  *)
(* a PL homeomorphism of the torus model onto frontier s.                   *)
(* ========================================================================= *)

let MOI_FPS_PL_SOLID_TORUS_ALT = prove
 (`!s:real^N->bool.
     pl_solid_torus s <=> ?f g. pl_homeomorphism (moi_fps_m,s) (f,g)`,
  REWRITE_TAC[pl_solid_torus; moi_fps_m; moi_fps_ann]);;

let MOI_FPS_CORE = prove
 (`!(s:real^N->bool) f g.
     pl_homeomorphism (moi_fps_m,s) (f,g)
     ==> ?h k. pl_homeomorphism
                 (moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1],s) (h,k) /\
               IMAGE h (moi_fps_sq PCROSS moi_fps_sq) = IMAGE f (frontier moi_fps_m)`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `th':real^(2,2)finite_sum->real^(2,1)finite_sum` MOI_FPS_TH_PLH THEN
  EXISTS_TAC `(f:real^(2,1)finite_sum->real^N) o
              (th':real^(2,2)finite_sum->real^(2,1)finite_sum)` THEN
  EXISTS_TAC `moi_fps_th o (g:real^N->real^(2,1)finite_sum)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_fps_m` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o; GSYM MOI_FPS_TH_FRONTIER] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `frontier moi_fps_m SUBSET moi_fps_m` MP_TAC THENL
   [SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED; MOI_FPS_M_COMPACT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> can (find_term ((=)
      `th':real^(2,2)finite_sum->real^(2,1)finite_sum`)) (concl th))) THEN
  REWRITE_TAC[homeomorphism] THEN SET_TAC[]);;

let MOI_FPS_SPINE_IMAGE = prove
 (`!(a:real^2->real^2) a' (b:real^2->real^2) b'.
     homeomorphism (cball(vec 0:real^2,&1),interval[--vec 1:real^2,vec 1]) (a,a') /\
     homeomorphism (sphere(vec 0:real^2,&1),moi_fps_sq) (b,b')
     ==> IMAGE (\z. pastecart (b(sndcart z)) (a(fstcart z)))
               ({a'(vec 0)} PCROSS sphere(vec 0:real^2,&1)) =
         moi_fps_sq PCROSS {vec 0:real^2}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                               GEN_REWRITE_RULE I [homeomorphism])
                              (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism])) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^2` o CONJUNCT1) THEN
  REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING; IN_IMAGE;
              EXISTS_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_INJ] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)
                               (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (b:real^2->real^2) (sphere(vec 0,&1)) = moi_fps_sq` THEN
    UNDISCH_TAC `(y:real^2) IN sphere(vec 0,&1)` THEN SET_TAC[];
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(a':real^2->real^2)(vec 0)`; `(b':real^2->real^2) u`] THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `IMAGE (b':real^2->real^2) moi_fps_sq = sphere(vec 0,&1)` THEN
    UNDISCH_TAC `(u:real^2) IN moi_fps_sq` THEN SET_TAC[]]);;

let PL_SOLID_TORUS_BASIC = prove
 (MOI_FND_PL_SOLID_TORUS_BASIC,
  CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[MOI_FPS_PL_SOLID_TORUS_ALT] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^(2,1)finite_sum->real^N`
      (X_CHOOSE_TAC `g:real^N->real^(2,1)finite_sum`)) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `h:real^(2,2)finite_sum->real^N`
      (X_CHOOSE_THEN `k:real^N->real^(2,2)finite_sum` STRIP_ASSUME_TAC) o
      MATCH_MP MOI_FPS_CORE) THEN
    SUBGOAL_THEN `3 <= dimindex(:N)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FPS_DIM_GE3 THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `f:real^(2,1)finite_sum->real^N`;
                            `g:real^N->real^(2,1)finite_sum`] THEN
      ASM_MESON_TAC[pl_homeomorphism];
      ALL_TAC] THEN
    X_CHOOSE_THEN `a:real^2->real^2` (X_CHOOSE_THEN `a':real^2->real^2` STRIP_ASSUME_TAC)
      MOI_FPS_DISC_SQUARE THEN
    SUBGOAL_THEN `?b b'. homeomorphism (sphere(vec 0:real^2,&1),moi_fps_sq) (b,b')`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM homeomorphic] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
      REWRITE_TAC[moi_fps_sq; MOI_FPS_VEC1_2] THEN
      MATCH_MP_TAC MOI_FH1_SQUARE_FRONTIER_CIRCLE THEN REWRITE_TAC[REAL_LT_01];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `interval[--vec 1:real^2,vec 1]`;
                   `sphere(vec 0:real^2,&1)`; `moi_fps_sq`;
                   `a:real^2->real^2`; `a':real^2->real^2`;
                   `b:real^2->real^2`; `b':real^2->real^2`]
                  MOI_FPS_HOMEOMORPHISM_PCROSS_SWAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `homeomorphism (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1),s)
        ((h:real^(2,2)finite_sum->real^N) o
         (\z. pastecart ((b:real^2->real^2)(sndcart z)) ((a:real^2->real^2)(fstcart z))),
         (\w. pastecart ((a':real^2->real^2)(sndcart w)) ((b':real^2->real^2)(fstcart w))) o
         (k:real^N->real^(2,2)finite_sum))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1]` THEN
      ASM_MESON_TAC[pl_homeomorphism];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[solid_torus] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
      REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC
       [`(h:real^(2,2)finite_sum->real^N) o
         (\z. pastecart ((b:real^2->real^2)(sndcart z)) ((a:real^2->real^2)(fstcart z)))`;
        `(\w. pastecart ((a':real^2->real^2)(sndcart w)) ((b':real^2->real^2)(fstcart w))) o
         (k:real^N->real^(2,2)finite_sum)`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `IMAGE (h:real^(2,2)finite_sum->real^N) (moi_fps_sq PCROSS {vec 0:real^2})` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[spine] THEN
      MAP_EVERY EXISTS_TAC
       [`(h:real^(2,2)finite_sum->real^N) o
         (\z. pastecart ((b:real^2->real^2)(sndcart z)) ((a:real^2->real^2)(fstcart z)))`;
        `(\w. pastecart ((a':real^2->real^2)(sndcart w)) ((b':real^2->real^2)(fstcart w))) o
         (k:real^N->real^(2,2)finite_sum)`;
        `(a':real^2->real^2)(vec 0)`] THEN
      ASM_REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC MOI_FPS_SPINE_IMAGE THEN EXISTS_TAC `b':real^2->real^2` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FPS_SPINE_PL_SPHERE THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `k:real^N->real^(2,2)finite_sum`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    X_GEN_TAC `s:real^3->bool` THEN REWRITE_TAC[MOI_FPS_PL_SOLID_TORUS_ALT] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^(2,1)finite_sum->real^3`
      (X_CHOOSE_TAC `g:real^3->real^(2,1)finite_sum`)) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `h:real^(2,2)finite_sum->real^3`
      (X_CHOOSE_THEN `k:real^3->real^(2,2)finite_sum` STRIP_ASSUME_TAC) o
      MATCH_MP MOI_FPS_CORE) THEN
    MAP_EVERY EXISTS_TAC [`h:real^(2,2)finite_sum->real^3`; `k:real^3->real^(2,2)finite_sum`] THEN
    SUBGOAL_THEN `homeomorphism (moi_fps_m,s) (f:real^(2,1)finite_sum->real^3,g)`
    ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
    SUBGOAL_THEN
     `frontier s = IMAGE (h:real^(2,2)finite_sum->real^3) (moi_fps_sq PCROSS moi_fps_sq)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC MOI_FPS_HOMEOMORPHISM_FRONTIER THEN
      EXISTS_TAC `g:real^3->real^(2,1)finite_sum` THEN
      ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_2; DIMINDEX_1; DIMINDEX_3] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      CONJ_TAC THENL [SIMP_TAC[COMPACT_IMP_CLOSED; MOI_FPS_M_COMPACT]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      SUBGOAL_THEN `s = IMAGE (f:real^(2,1)finite_sum->real^3) moi_fps_m` SUBST1_TAC THENL
       [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[MOI_FPS_M_COMPACT] THEN
      ASM_MESON_TAC[homeomorphism];
      ALL_TAC] THEN
    REWRITE_TAC[pl_torus_model; GSYM moi_fps_sq] THEN
    MATCH_MP_TAC MOI_FPS_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`moi_fps_sq PCROSS interval[--vec 1:real^2,vec 1]`;
                          `s:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET; MOI_FPS_SQ; IN_INTERVAL; DIMINDEX_2; FORALL_2;
                  VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN
      REWRITE_TAC[MOI_FPS_SQ_PL_POLYHEDRON]]]);;

