(* ========================================================================= *)
(* Unit pc_smt_listed: a simply connected listed piece is S^3.               *)
(* RFS_LISTED_SC_S3 proves RFS_LISTED_SC_S3_STATEMENT of pc_rfs_top.  The    *)
(* cases of rfs_listed_piece: S^3 (immediate); space forms                   *)
(* (KILLING_HOPF_COMPONENT of pc_geo_kh); S^2-bundles over S^1 (impossible:  *)
(* the fibre sphere separates by SMT_SC_SPHERE_SEP of pc_smt_sep, but its    *)
(* complement is the connected image of an annulus); twisted charts          *)
(* (impossible: the map collapsing everything off the twisted core to one    *)
(* point of RP^3 lifts to S^3 since the piece is simply connected, and on    *)
(* the one-sided RP^2 the lift would be a continuous choice of one of the    *)
(* two preimages of each point, which the antipodal identification forbids). *)
(* RP^(N-1) is modelled as the image of the unit sphere of real^N under      *)
(* x |-> (u |-> (x dot u) x) in the product topology on real^N -> real^N;    *)
(* it is 2-sheeted covered by the sphere (SMT_RP_COVERING, from              *)
(* COMPACT_LOCAL_HOMEOMORPHISM_IMP_COVERING_MAP of pc_top_cover).  Further   *)
(* results: SMT_RP_COVERING, SMT_TWISTED_NOT_SC, SMT_S2_BUNDLE_NOT_SC.       *)
(* ========================================================================= *)

needs "src/pc_rfs_top.ml";;
needs "src/pc_geo_kh.ml";;
needs "src/pc_smt_sep.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The projective space model and its 2-sheeted covering by                 *)
(* the unit sphere.                                                          *)
(* ========================================================================= *)

let smt_rp_map = new_definition
 `smt_rp_map (x:real^N) = \u:real^N. (x dot u) % x`;;

let smt_rp_space = new_definition
 `smt_rp_space =
    subtopology (product_topology (:real^N) (\u:real^N. (euclidean:(real^N)topology)))
                (IMAGE (smt_rp_map:real^N->real^N->real^N) (sphere(vec 0:real^N,&1)))`;;

let SMTL_RP_MAP_NEG = prove
 (`!x:real^N. smt_rp_map(--x) = smt_rp_map x`,
  REWRITE_TAC[smt_rp_map; FUN_EQ_THM; DOT_LNEG; VECTOR_MUL_LNEG; VECTOR_MUL_RNEG;
              VECTOR_NEG_NEG]);;

let SMTL_RP_MAP_EQ = prove
 (`!x y:real^N.
        norm x = &1 /\ norm y = &1
        ==> (smt_rp_map x = smt_rp_map y <=> y = x \/ y = --x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[SMTL_RP_MAP_NEG]] THEN
  DISCH_THEN(MP_TAC o C AP_THM `x:real^N`) THEN REWRITE_TAC[smt_rp_map] THEN
  SUBGOAL_THEN `(x:real^N) dot x = &1` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_EQ_1]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs((y:real^N) dot x) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) = (y dot x) % y` THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:real^N->real`) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP
    (REAL_ARITH `abs t = &1 ==> t = &1 \/ t = -- &1`)) THEN
  UNDISCH_TAC `(x:real^N) = (y dot x) % y` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LNEG; VECTOR_NEG_NEG]);;

let SMTL_RP_TOPSPACE = prove
 (`topspace (smt_rp_space:(real^N->real^N)topology) =
   IMAGE smt_rp_map (sphere(vec 0:real^N,&1))`,
  REWRITE_TAC[smt_rp_space; TOPSPACE_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY] THEN
  MATCH_MP_TAC(SET_RULE `!s t:(real^N->real^N)->bool. s = UNIV ==> s INTER t = t`) THEN
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_CARTESIAN_PRODUCT; EXTENSIONAL_UNIV; o_THM;
              TOPSPACE_EUCLIDEAN]);;

let SMTL_RP_CONTINUOUS = prove
 (`continuous_map (subtopology euclidean (sphere(vec 0:real^N,&1)),smt_rp_space)
                  smt_rp_map`,
  REWRITE_TAC[smt_rp_space; CONTINUOUS_MAP_IN_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET_REFL] THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV; smt_rp_map] THEN
  X_GEN_TAC `u:real^N` THEN REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[CONTINUOUS_ON_LIFT_DOT]);;

let SMTL_RP_EVAL_CONTINUOUS = prove
 (`!x0:real^N.
        continuous_map (smt_rp_space,euclidean) (\b:real^N->real^N. b x0)`,
  GEN_TAC THEN REWRITE_TAC[smt_rp_space] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  MP_TAC(ISPECL [`\u:real^N. (euclidean:(real^N)topology)`; `(:real^N)`; `x0:real^N`]
                CONTINUOUS_MAP_PRODUCT_PROJECTION) THEN
  REWRITE_TAC[IN_UNIV]);;

(* The local inverse b |-> b x0 / sqrt(x0 dot b x0) on the image of x. *)

let SMTL_RP_INV_FORM = prove
 (`!x x0:real^N.
        ~(x dot x0 = &0)
        ==> &0 < x0 dot smt_rp_map x x0 /\
            inv(sqrt(x0 dot smt_rp_map x x0)) % smt_rp_map x x0 =
            (if &0 < x dot x0 then x else --x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[smt_rp_map; DOT_RMUL] THEN
  SUBGOAL_THEN `(x dot x0) * ((x0:real^N) dot x) = (x dot x0) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC DOT_SYM;
    ALL_TAC] THEN
  REWRITE_TAC[POW_2_SQRT_ABS; VECTOR_MUL_ASSOC] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_POW_2]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`; REAL_MUL_LINV; VECTOR_MUL_LID];
    SUBGOAL_THEN `abs(x dot x0) = --((x:real^N) dot x0)` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_NEG; REAL_MUL_LNEG; VECTOR_MUL_LNEG] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID]]);;

let SMTL_RP_DOT_NZ = prove
 (`!x x0:real^N. &0 < x0 dot smt_rp_map x x0 ==> ~(x dot x0 = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smt_rp_map; DOT_RMUL] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN SIMP_TAC[REAL_MUL_LZERO; REAL_LT_REFL]);;

(* Homeomorphisms between subspaces from maps with inverses on them. *)

let SMTL_HOMEOMORPHIC_MAPS_SUBTOPOLOGIES = prove
 (`!X Y (f:A->B) g U V.
        continuous_map (X,Y) f /\ continuous_map (subtopology Y V,X) g /\
        U SUBSET topspace X /\ V SUBSET topspace Y /\
        (!x. x IN U ==> f x IN V /\ g(f x) = x) /\
        (!y. y IN V ==> g y IN U /\ f(g y) = y)
        ==> homeomorphic_maps (subtopology X U,subtopology Y V) (f,g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[homeomorphic_maps; CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN ASM SET_TAC[]);;

let SMTL_RP_LOCAL_HOMEO = prove
 (`local_homeomorphism_map
     (subtopology euclidean (sphere(vec 0:real^N,&1)),smt_rp_space) smt_rp_map`,
  REWRITE_TAC[local_homeomorphism_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  X_GEN_TAC `x0:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open {z:real^N | &0 < x0 dot z} /\ open {x:real^N | &0 < x dot x0}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x0:real^N`; `&0`] OPEN_HALFSPACE_GT) THEN
    MATCH_MP_TAC(TAUT `(a <=> b) /\ (a <=> c) ==> a ==> b /\ c`) THEN
    CONJ_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; real_gt] THEN MESON_TAC[DOT_SYM];
    ALL_TAC] THEN
  ABBREV_TAC
   `V0 = {b:real^N->real^N | b IN IMAGE smt_rp_map (sphere(vec 0:real^N,&1)) /\
                             &0 < x0 dot b x0}` THEN
  SUBGOAL_THEN `open_in (smt_rp_space:(real^N->real^N)topology) V0` ASSUME_TAC THENL
   [EXPAND_TAC "V0" THEN REWRITE_TAC[GSYM SMTL_RP_TOPSPACE] THEN
    MP_TAC(ISPECL [`\b:real^N->real^N. b x0`; `smt_rp_space:(real^N->real^N)topology`;
                   `euclidean:(real^N)topology`; `{z:real^N | &0 < x0 dot z}`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[SMTL_RP_EVAL_CONTINUOUS; GSYM OPEN_IN; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN sphere(vec 0,&1) /\ &0 < x dot x0
               ==> smt_rp_map x IN V0 /\
                   inv(sqrt(x0 dot smt_rp_map x x0)) % smt_rp_map x x0 = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`x:real^N`; `x0:real^N`] SMTL_RP_INV_FORM) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "V0" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. b IN V0
        ==> inv(sqrt(x0 dot b x0)) % b x0 IN
              sphere(vec 0:real^N,&1) INTER {x:real^N | &0 < x dot x0} /\
            smt_rp_map(inv(sqrt(x0 dot b x0)) % b x0) = b`
  ASSUME_TAC THENL
   [EXPAND_TAC "V0" THEN REWRITE_TAC[IN_ELIM_THM; IMP_CONJ; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^N`; `x0:real^N`] SMTL_RP_DOT_NZ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^N`; `x0:real^N`] SMTL_RP_INV_FORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o last o CONJUNCTS) THEN
    UNDISCH_TAC `(x:real^N) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; IN_INTER; IN_ELIM_THM] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[NORM_NEG; DOT_LNEG; SMTL_RP_MAP_NEG] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology smt_rp_space V0,
                    subtopology euclidean (sphere(vec 0:real^N,&1)))
                   (\b:real^N->real^N. inv(sqrt(x0 dot b x0)) % b x0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      ASM SET_TAC[]] THEN
    SUBGOAL_THEN
     `(\b:real^N->real^N. inv(sqrt(x0 dot b x0)) % b x0) =
      (\z. inv(sqrt(x0 dot z)) % z) o (\b. b x0)` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean {z:real^N | &0 < x0 dot z}` THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
        REWRITE_TAC[SMTL_RP_EVAL_CONTINUOUS];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
        EXPAND_TAC "V0" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
      SUBGOAL_THEN
       `lift o (\z:real^N. inv(sqrt(x0 dot z))) = (lift o inv o (\z. sqrt(x0 dot z)))`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_INV THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN
        REWRITE_TAC[CONTINUOUS_ON_LIFT_DOT];
        REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_IMP_NZ]]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`sphere(vec 0:real^N,&1) INTER {x:real^N | &0 < x dot x0}`;
    `V0:(real^N->real^N)->bool`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    UNDISCH_TAC `(x0:real^N) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1] THEN REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
    EXISTS_TAC `\b:real^N->real^N. inv(sqrt(x0 dot b x0)) % b x0` THEN
    MATCH_MP_TAC SMTL_HOMEOMORPHIC_MAPS_SUBTOPOLOGIES THEN
    ASM_REWRITE_TAC[SMTL_RP_CONTINUOUS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                    SMTL_RP_TOPSPACE; INTER_SUBSET] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "V0" THEN SET_TAC[];
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[]]]);;

let SMT_RP_COVERING = prove
 (`covering_map (subtopology euclidean (sphere(vec 0:real^N,&1)),smt_rp_space)
                smt_rp_map`,
  MATCH_MP_TAC COMPACT_LOCAL_HOMEOMORPHISM_IMP_COVERING_MAP THEN
  REWRITE_TAC[SMTL_RP_CONTINUOUS; SMTL_RP_LOCAL_HOMEO; SMTL_RP_TOPSPACE;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE];
    MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
    REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
    REWRITE_TAC[smt_rp_space] THEN MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
    REWRITE_TAC[HAUSDORFF_SPACE_PRODUCT_TOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN]]);;

(* ========================================================================= *)
(* The map Phi from the punctured space to S^3 in                            *)
(* real^(3,1)finite_sum: Phi(y) = (sqrt(1 - s^2) y / |y|, --s) with the      *)
(* clamp s = smt_twc_s |y| of 2/3 (|y| - 1/|y|) to [-1,1].  Phi is odd under *)
(* the twist, equals the pole (0,1) for |y| <= 1/2 and its negative for       *)
(* |y| >= 2, and is (y,0) on the unit sphere.                                 *)
(* ========================================================================= *)

let smt_twc_s = new_definition
 `smt_twc_s (r:real) =
    inv(&2) * (abs(&2 / &3 * (r - inv r) + &1) - abs(&2 / &3 * (r - inv r) - &1))`;;

let smt_twc_phi = new_definition
 `smt_twc_phi (y:real^3) =
    pastecart (sqrt(&1 - smt_twc_s(norm y) pow 2) / norm y % y)
              (lift(--(smt_twc_s(norm y)))):real^(3,1)finite_sum`;;

let SMTL_TWC_S_BOUNDS = prove
 (`!r. -- &1 <= smt_twc_s r /\ smt_twc_s r <= &1`,
  REWRITE_TAC[smt_twc_s] THEN REAL_ARITH_TAC);;

let SMTL_TWC_S_INV = prove
 (`!r. &0 < r ==> smt_twc_s(inv r) = --(smt_twc_s r)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[smt_twc_s; REAL_INV_INV] THEN
  REWRITE_TAC[REAL_ARITH `&2 / &3 * (inv r - r) = --(&2 / &3 * (r - inv r))`] THEN
  REAL_ARITH_TAC);;

let SMTL_TWC_S_LOW = prove
 (`!r. &0 < r /\ r <= &1 / &2 ==> smt_twc_s r = -- &1`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= inv r` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(&1 / &2) <= inv r` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[smt_twc_s] THEN ASM_REAL_ARITH_TAC);;

let SMTL_TWC_S_HIGH = prove
 (`!r. &2 <= r ==> smt_twc_s r = &1`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= inv r /\ inv r <= &1 / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `inv r <= inv(&2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[smt_twc_s] THEN ASM_REAL_ARITH_TAC);;

let SMTL_TWC_S_ONE = prove
 (`smt_twc_s(&1) = &0`,
  REWRITE_TAC[smt_twc_s; REAL_INV_1] THEN REAL_ARITH_TAC);;

let SMTL_TWC_PHI_NORM = prove
 (`!y:real^3. ~(y = vec 0) ==> norm(smt_twc_phi y) = &1`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPEC `norm(y:real^3)` SMTL_TWC_S_BOUNDS) THEN
  REWRITE_TAC[smt_twc_phi] THEN
  SPEC_TAC(`smt_twc_s(norm(y:real^3))`,`s:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &1 - s pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUB_LE] THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(sqrt(&1 - s pow 2) / norm y % (y:real^3)) = sqrt(&1 - s pow 2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[NORM_PASTECART; NORM_LIFT; REAL_ABS_NEG; REAL_POW2_ABS] THEN
  ASM_SIMP_TAC[SQRT_POW_2] THEN
  REWRITE_TAC[REAL_ARITH `(&1 - s pow 2) + s pow 2 = &1`; SQRT_1]);;

let SMTL_TWIST_NORM = prove
 (`!y:real^3. ~(y = vec 0) ==> norm(rfs_twist y) = inv(norm y)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[rfs_twist; NORM_NEG; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; CONV_TAC REAL_FIELD]);;

let SMTL_TWC_PHI_TWIST = prove
 (`!y:real^3. ~(y = vec 0) ==> smt_twc_phi(rfs_twist y) = --(smt_twc_phi y)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[smt_twc_phi; SMTL_TWIST_NORM; SMTL_TWC_S_INV; GSYM PASTECART_NEG] THEN
  REWRITE_TAC[PASTECART_INJ; REAL_RING `(--x:real) pow 2 = x pow 2`] THEN
  REWRITE_TAC[LIFT_NEG; VECTOR_NEG_NEG; REAL_NEG_NEG] THEN
  SPEC_TAC(`sqrt(&1 - smt_twc_s(norm(y:real^3)) pow 2)`,`c:real`) THEN
  GEN_TAC THEN REWRITE_TAC[rfs_twist; VECTOR_MUL_RNEG; VECTOR_MUL_ASSOC] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD);;

let SMTL_TWC_PHI_LOW = prove
 (`!y:real^3. ~(y = vec 0) /\ norm y <= &1 / &2
              ==> smt_twc_phi y = pastecart (vec 0) (lift(&1))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[smt_twc_phi; SMTL_TWC_S_LOW] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[SQRT_0; real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO]);;

let SMTL_TWC_PHI_HIGH = prove
 (`!y:real^3. &2 <= norm y
              ==> smt_twc_phi y = --(pastecart (vec 0) (lift(&1)))`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[smt_twc_phi; SMTL_TWC_S_HIGH; GSYM PASTECART_NEG; VECTOR_NEG_0; LIFT_NEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[SQRT_0; real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO]);;

let SMTL_TWC_PHI_EQUATOR = prove
 (`!y:real^3. norm y = &1 ==> smt_twc_phi y = pastecart y (vec 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[smt_twc_phi; SMTL_TWC_S_ONE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[SQRT_1; REAL_DIV_1; VECTOR_MUL_LID; REAL_NEG_0; LIFT_NUM]);;

let SMTL_TWC_S_CONT = prove
 (`continuous_map (subtopology euclidean {y:real^3 | ~(y = vec 0)},euclideanreal)
                  (\y. smt_twc_s(norm y))`,
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean {y:real^3 | ~(y = vec 0)},euclideanreal)
                   (norm:real^3->real) /\
    continuous_map (subtopology euclidean {y:real^3 | ~(y = vec 0)},euclideanreal)
                   (\y. inv(norm y))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN] THEN
      REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM];
      DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_INV THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_ELIM_THM; NORM_EQ_0]];
    ALL_TAC] THEN
  REWRITE_TAC[smt_twc_s] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN
  (MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD ORELSE MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB) THEN
  REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN ASM_REWRITE_TAC[]);;

let SMTL_TWC_PHI_CONT = prove
 (`smt_twc_phi continuous_on {y:real^3 | ~(y = vec 0)}`,
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean {y:real^3 | ~(y = vec 0)},euclideanreal)
                   (\y. sqrt(&1 - smt_twc_s(norm y) pow 2) / norm y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_DIV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_SQRT THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_POW THEN REWRITE_TAC[SMTL_TWC_S_CONT];
      REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN] THEN
      REWRITE_TAC[ETA_AX; CONTINUOUS_ON_LIFT_NORM];
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_ELIM_THM; NORM_EQ_0]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[smt_twc_phi] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    UNDISCH_TAC
     `continuous_map (subtopology euclidean {y:real^3 | ~(y = vec 0)},euclideanreal)
                     (\y. sqrt(&1 - smt_twc_s(norm y) pow 2) / norm y)` THEN
    REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN];
    REWRITE_TAC[LIFT_NEG] THEN MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
    MP_TAC SMTL_TWC_S_CONT THEN
    REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF]]);;

(* ========================================================================= *)
(* Twisted charts as 2-to-1 local parametrizations, and the                  *)
(* collapse map to the projective model: q o Phi through the chart on the    *)
(* twisted neighbourhood, the class of the pole elsewhere.                   *)
(* ========================================================================= *)

let SMTL_TWIST_ANNULUS = prove
 (`!y:real^3. y IN annulus (&1 / &4) (&4)
              ==> ~(y = vec 0) /\ rfs_twist y IN annulus (&1 / &4) (&4)`,
  GEN_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SMTL_TWIST_NORM] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `inv(&4) < inv(norm(y:real^3))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
    SUBGOAL_THEN `inv(norm(y:real^3)) < inv(&1 / &4)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]]);;

let SMTL_TWC_FACTS = prove
 (`!top atlas (p:real^3->A).
        rfs_twisted_chart top atlas p
        ==> (!y. y IN annulus (&1 / &4) (&4) ==> p y IN topspace top) /\
            continuous_map (subtopology euclidean (annulus (&1 / &4) (&4)),top) p /\
            (!y. y IN annulus (&1 / &4) (&4)
                 ==> rfs_twist y IN annulus (&1 / &4) (&4) /\ p(rfs_twist y) = p y) /\
            (!y z. y IN annulus (&1 / &4) (&4) /\ z IN annulus (&1 / &4) (&4) /\
                   p y = p z
                   ==> z = y \/ z = rfs_twist y) /\
            (!y. y IN annulus (&1 / &4) (&4)
                 ==> ?r q. &0 < r /\ ball(y,r) SUBSET annulus (&1 / &4) (&4) /\
                           open_in top (IMAGE p (ball(y,r))) /\
                           continuous_map (subtopology top (IMAGE p (ball(y,r))),
                                           euclidean) q /\
                           (!z. z IN ball(y,r) ==> q(p z) = z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_twisted_chart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (LABEL_TAC "loc")) THEN
  SUBGOAL_THEN
   `!y. y IN annulus (&1 / &4) (&4)
        ==> ?r q. &0 < r /\ ball(y,r) SUBSET annulus (&1 / &4) (&4) /\
                  open_in top (IMAGE (p:real^3->A) (ball(y,r))) /\
                  continuous_map (subtopology euclidean (ball(y,r)),top) p /\
                  continuous_map (subtopology top (IMAGE p (ball(y,r))),euclidean) q /\
                  (!z. z IN ball(y,r) ==> q(p z) = z)`
  (LABEL_TAC "par") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:A->real^3` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `q:A->real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN annulus (&1 / &4) (&4) ==> (p:real^3->A) y IN topspace top`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "par" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `q:A->real^3` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `continuous_map (subtopology euclidean (ball(y:real^3,r)),top) (p:real^3->A)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "par" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `q:A->real^3` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `ball(y:real^3,r)` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_ANNULUS; OPEN_BALL; CENTRE_IN_BALL] THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[SET_RULE `(s:real^3->bool) SUBSET t ==> t INTER s = s`];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SMTL_TWIST_ANNULUS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    USE_THEN "id" (MP_TAC o SPECL [`y:real^3`; `rfs_twist y`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN
    USE_THEN "id" (MP_TAC o SPECL [`y:real^3`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "par" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]]]);;

(* The collapse map. *)

let smt_twc_collapse = new_definition
 `smt_twc_collapse (p:real^3->A) (x:A) =
    if x IN IMAGE p (annulus (&1 / &4) (&4))
    then smt_rp_map(smt_twc_phi(@y. y IN annulus (&1 / &4) (&4) /\ p y = x))
    else smt_rp_map(pastecart (vec 0:real^3) (lift(&1)))`;;

let SMTL_COLLAPSE_AT = prove
 (`!top atlas (p:real^3->A) y.
        rfs_twisted_chart top atlas p /\ y IN annulus (&1 / &4) (&4)
        ==> smt_twc_collapse p (p y) = smt_rp_map(smt_twc_phi y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SMTL_TWC_FACTS) THEN
  REWRITE_TAC[smt_twc_collapse] THEN
  SUBGOAL_THEN `(p:real^3->A) y IN IMAGE p (annulus (&1 / &4) (&4))`
    (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `y' = @y'. y' IN annulus (&1 / &4) (&4) /\ (p:real^3->A) y' = p y` THEN
  SUBGOAL_THEN `y' IN annulus (&1 / &4) (&4) /\ (p:real^3->A) y' = p y`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y'" THEN CONV_TAC SELECT_CONV THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `y':real^3 = y \/ y' = rfs_twist y` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SMTL_TWIST_ANNULUS o
      check (fun th -> concl th = `(y:real^3) IN annulus (&1 / &4) (&4)`)) THEN
    ASM_SIMP_TAC[SMTL_TWC_PHI_TWIST; SMTL_RP_MAP_NEG]]);;

let SMTL_COLLAPSE_POLE = prove
 (`!top atlas (p:real^3->A) x.
        rfs_twisted_chart top atlas p /\
        ~(x IN IMAGE p {y | &1 / &2 <= norm y /\ norm y <= &2})
        ==> smt_twc_collapse p x = smt_rp_map(pastecart (vec 0:real^3) (lift(&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:A) IN IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))` THENL
   [ALL_TAC; ASM_REWRITE_TAC[smt_twc_collapse]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
    REWRITE_RULE[IN_IMAGE]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `p:real^3->A`; `y:real^3`] SMTL_COLLAPSE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0) /\ (norm y < &1 / &2 \/ &2 < norm y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[SMTL_TWIST_ANNULUS];
      ASM_CASES_TAC `norm(y:real^3) < &1 / &2 \/ &2 < norm y` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((p:real^3->A) y IN IMAGE p {y | &1 / &2 <= norm y /\ norm y <= &2})` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC];
    ASM_SIMP_TAC[SMTL_TWC_PHI_LOW; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[SMTL_TWC_PHI_HIGH; REAL_LT_IMP_LE; SMTL_RP_MAP_NEG]]);;

let SMTL_CORE_CLOSED = prove
 (`!top atlas (p:real^3->A).
        hausdorff_space top /\ rfs_twisted_chart top atlas p
        ==> closed_in top (IMAGE p {y | &1 / &2 <= norm y /\ norm y <= &2}) /\
            IMAGE p {y | &1 / &2 <= norm y /\ norm y <= &2} SUBSET
            IMAGE p (annulus (&1 / &4) (&4))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SMTL_TWC_FACTS) THEN
  SUBGOAL_THEN
   `{y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} SUBSET annulus (&1 / &4) (&4)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean (annulus (&1 / &4) (&4):real^3->bool)` THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
  SUBGOAL_THEN
   `{y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} =
    cball(vec 0,&2) DIFF ball(vec 0,&1 / &2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]]);;

let SMTL_COLLAPSE_CONT = prove
 (`!top atlas (p:real^3->A).
        hausdorff_space top /\ rfs_twisted_chart top atlas p
        ==> continuous_map (top,smt_rp_space) (smt_twc_collapse p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SMTL_TWC_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lin"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `p:real^3->A`] SMTL_CORE_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:A) IN IMAGE (p:real^3->A) {y | &1 / &2 <= norm y /\ norm y <= &2}` THENL
   [SUBGOAL_THEN `(x:A) IN IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    USE_THEN "lin" (MP_TAC o SPEC `y0:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `q:A->real^3` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `IMAGE (p:real^3->A) (ball(y0,r))` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `smt_rp_map o smt_twc_phi o (q:A->real^3)` THEN CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      X_GEN_TAC `x':A` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
        REWRITE_RULE[IN_IMAGE]) THEN
      REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SMTL_COLLAPSE_AT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^(3,1)finite_sum,&1))` THEN
    REWRITE_TAC[SMTL_RP_CONTINUOUS] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (ball(y0:real^3,r))` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
      X_GEN_TAC `x':A` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
        REWRITE_RULE[IN_IMAGE]) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN REWRITE_TAC[SMTL_TWC_PHI_CONT] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET; SMTL_TWIST_ANNULUS];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN
        ASM_MESON_TAC[SUBSET; SMTL_TWIST_ANNULUS; SMTL_TWC_PHI_NORM]]];
    EXISTS_TAC `topspace top DIFF IMAGE (p:real^3->A) {y | &1 / &2 <= norm y /\ norm y <= &2}` THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE; IN_DIFF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `\x:A. smt_rp_map(pastecart (vec 0:real^3) (lift(&1)))` THEN CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_DIFF] THEN
      X_GEN_TAC `z:A` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SMTL_COLLAPSE_POLE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[CONTINUOUS_MAP_CONST; SMTL_RP_TOPSPACE] THEN DISJ2_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_PASTECART; NORM_0; NORM_LIFT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[SQRT_1]]]);;

(* ========================================================================= *)
(* A simply connected (Hausdorff smooth) manifold has no                     *)
(* twisted chart.  The collapse map lifts to S^3 through the covering of the *)
(* projective model; by uniqueness of lifts on the connected unit sphere the *)
(* lift is y |-> (y,0) there, but p(--e1) = p(e1).                           *)
(* ========================================================================= *)

let SMTL_TWIST_UNIT = prove
 (`!y:real^3. norm y = &1 ==> rfs_twist y = --y`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[rfs_twist; REAL_POW_ONE; REAL_INV_1; VECTOR_MUL_LID]);;

let SMT_TWISTED_NOT_SC = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        simply_connected_space top /\ rfs_has_twisted top atlas
        ==> F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_has_twisted] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `p:real^3->A`)))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SMTL_TWC_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "top") (CONJUNCTS_THEN2 (LABEL_TAC "cont")
    (CONJUNCTS_THEN2 (LABEL_TAC "tw") (K ALL_TAC)))) THEN
  ABBREV_TAC `e1 = basis 1:real^3` THEN
  SUBGOAL_THEN `norm(e1:real^3) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &4) (&4) /\
    (e1:real^3) IN sphere(vec 0,&1) /\ --e1 IN sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[annulus; SUBSET; IN_ELIM_THM; IN_SPHERE_0; NORM_NEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `locally_path_connected_space (top:A topology)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEO_MANIFOLD_LOCALLY_PATH_CONNECTED]; ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (top,smt_rp_space) (smt_twc_collapse (p:real^3->A))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMTL_COLLAPSE_CONT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN sphere(vec 0:real^3,&1)
        ==> smt_twc_collapse (p:real^3->A) (p y) = smt_rp_map(pastecart y (vec 0:real^1))`
  (LABEL_TAC "eq") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `p:real^3->A`; `y:real^3`] SMTL_COLLAPSE_AT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SMTL_TWC_PHI_EQUATOR THEN
    ASM_MESON_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3->A) e1 IN topspace top` ASSUME_TAC THENL
   [USE_THEN "top" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (e1:real^3) (vec 0:real^1) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_SPHERE_0; NORM_PASTECART; NORM_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[SQRT_1];
    ALL_TAC] THEN
  (* the lift of the collapse map *)
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^(3,1)finite_sum,&1))`;
                 `smt_rp_space:(real^(3,1)finite_sum->real^(3,1)finite_sum)topology`;
                 `smt_rp_map:real^(3,1)finite_sum->real^(3,1)finite_sum->real^(3,1)finite_sum`;
                 `top:A topology`; `smt_twc_collapse (p:real^3->A)`;
                 `(p:real^3->A) e1`; `pastecart (e1:real^3) (vec 0:real^1)`]
                COVERING_MAP_LIFT_STRONG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SMT_RP_COVERING; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    CONV_TAC SYM_CONV THEN USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A->real^(3,1)finite_sum` STRIP_ASSUME_TAC) THEN
  (* uniqueness of lifts on the unit sphere *)
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^(3,1)finite_sum,&1))`;
                 `smt_rp_space:(real^(3,1)finite_sum->real^(3,1)finite_sum)topology`;
                 `smt_rp_map:real^(3,1)finite_sum->real^(3,1)finite_sum->real^(3,1)finite_sum`;
                 `subtopology euclidean (sphere(vec 0:real^3,&1))`;
                 `(k:A->real^(3,1)finite_sum) o (p:real^3->A)`;
                 `\y:real^3. pastecart y (vec 0:real^1)`; `e1:real^3`]
                COVERING_MAP_LIFT_UNIQUE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SMT_RP_COVERING; CONNECTED_SPACE_EUCLIDEAN_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_SPHERE THEN REWRITE_TAC[DIMINDEX_3; ARITH];
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `subtopology euclidean (sphere(vec 0:real^3,&1)) =
        subtopology (subtopology euclidean (annulus (&1 / &4) (&4))) (sphere(vec 0,&1))`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[SUBTOPOLOGY_SUBTOPOLOGY;
                     SET_RULE `(s:real^3->bool) SUBSET t ==> t INTER s = s`];
        MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; NORM_PASTECART; NORM_0] THEN
        X_GEN_TAC `y:real^3` THEN DISCH_THEN SUBST1_TAC THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[SQRT_1]];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(p:real^3->A) y IN topspace top` ASSUME_TAC THENL
       [USE_THEN "top" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `--e1:real^3`) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM] THEN
  SUBGOAL_THEN `(p:real^3->A)(--e1) = p e1` SUBST1_TAC THENL
   [ASM_MESON_TAC[SMTL_TWIST_UNIT; SUBSET; IN_SPHERE_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[PASTECART_INJ] THEN
  DISCH_TAC THEN UNDISCH_TAC `norm(e1:real^3) = &1` THEN
  SUBGOAL_THEN `e1:real^3 = vec 0` SUBST1_TAC THENL
   [UNDISCH_TAC `(e1:real^3) = --e1` THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* A connected simply connected manifold is no S^2-bundle over               *)
(* S^1 in the sense of rfs_s2_bundle: the central sphere of the neck chart   *)
(* separates (SMT_SC_SPHERE_SEP), but its complement is the connected image  *)
(* of the annulus.                                                           *)
(* ========================================================================= *)

let SMT_S2_BUNDLE_NOT_SC = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        connected_space top /\ simply_connected_space top /\
        rfs_s2_bundle top atlas
        ==> F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_s2_bundle] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `e:real^3->A` (X_CHOOSE_THEN `E:real^3->A`
      (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
        STRIP_ASSUME_TAC)))))))) THEN
  MP_TAC(ISPEC `(:A)` SMT_SC_SPHERE_SEP) THEN
  REWRITE_TAC[APX_SC_SPHERE_SEP_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `U:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `connected_components_of top = {topspace top:A->bool}` ASSUME_TAC THENL
     [REWRITE_TAC[CONNECTED_COMPONENTS_OF_EQ_SING] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] NONEMPTY_CONNECTED_COMPONENTS_OF) THEN
      MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] CONNECTED_COMPONENTS_OF_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `U:A->bool = topspace top` SUBST1_TAC THENL
     [ASM_MESON_TAC[IN_SING]; ALL_TAC] THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_TOPSPACE];
    ALL_TAC] THEN
  REWRITE_TAC[apx_sphere_sep; apx_separates] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real^3->A`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `connected_component_of (subtopology top (IMAGE (E:real^3->A) (annulus (&1) (&4))))
      (e(&3 / &4 % basis 1:real^3)) (e(&4 / &3 % basis 1))`
  MP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[connected_component_of] THEN
  EXISTS_TAC `IMAGE (E:real^3->A) (annulus (&1) (&4))` THEN
  ASM_REWRITE_TAC[CONNECTED_IN_ABSOLUTE] THEN
  MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
  EXISTS_TAC `subtopology euclidean (annulus (&1) (&4):real^3->bool)` THEN
  REWRITE_TAC[CONNECTED_IN_ABSOLUTE; CONNECTED_IN_EUCLIDEAN] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    DISCH_THEN(X_CHOOSE_THEN `E':A->real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `&4`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_RZERO; annulus]]);;

(* ========================================================================= *)
(* The main theorem RFS_LISTED_SC_S3.                                        *)
(* ========================================================================= *)

let RFS_LISTED_SC_S3 = prove
 (`!u:A->bool. RFS_LISTED_SC_S3_STATEMENT u`,
  REWRITE_TAC[RFS_LISTED_SC_S3_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `U:A->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE THEN
    ASM_MESON_TAC[GEO_MANIFOLD_LOCALLY_PATH_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology top U)
      (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (subtopology top (U:A->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY]; ALL_TAC] THEN
  SUBGOAL_THEN `connected_space (subtopology top (U:A->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_SPACE_SUBTOPOLOGY THEN
    MATCH_MP_TAC CONNECTED_IN_CONNECTED_COMPONENTS_OF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_listed_piece]) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC (DISJ_CASES_THEN2 ASSUME_TAC
    (DISJ_CASES_THEN2 ASSUME_TAC ASSUME_TAC))) THENL
   [MATCH_MP_TAC KILLING_HOPF_COMPONENT THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_space_form]) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT2);
    MP_TAC(ISPECL [`subtopology top (U:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U`]
                  SMT_S2_BUNDLE_NOT_SC) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`subtopology top (U:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) U`]
                  SMT_TWISTED_NOT_SC) THEN
    ASM_REWRITE_TAC[]]);;

