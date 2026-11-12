(* ========================================================================= *)
(* pc_moi_s31_carrier: the carrier of 31.4 (Moise pp.221-222), DG's         *)
(* asymmetric form.  Main theorem CARRIER : |- MOI_S31_CARRIER (statement   *)
(* of pc_moi_s3032_stmt.ml).  A thin PL core of sb, whose H_1 maps          *)
(* isomorphically onto H_1(sb), is cut along frontier sa by MV_POLY.        *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_fnd_h1.ml";;
needs "src/pc_moi_s34_h1.ml";;
needs "src/pc_moi_s34_torus.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_fnd_plst.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: the model solid torus S0 (square annulus 1 <= infnorm <= 2       *)
(* times [-1,1]) and its cores S_e (1 + e <= infnorm <= 2 - e, |t| <= 1-e). *)
(* ------------------------------------------------------------------------- *)

let moi_s3cr_s0 = new_definition
 `moi_s3cr_s0 = (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                 interval(--vector[&1;&1]:real^2,vector[&1;&1])) PCROSS
                interval[--vec 1:real^1,vec 1]`;;

let moi_s3cr_core = new_definition
 `moi_s3cr_core e =
    {u:real^2 | &1 + e <= infnorm u /\ infnorm u <= &2 - e} PCROSS
    interval[--lift(&1 - e),lift(&1 - e)]`;;

let MOI_S3CR_IN_S0 = prove
 (`!(u:real^2) (t:real^1).
     pastecart u t IN moi_s3cr_s0 <=>
     &1 <= infnorm u /\ infnorm u <= &2 /\ abs(drop t) <= &1`,
  REWRITE_TAC[moi_s3cr_s0; PASTECART_IN_PCROSS; MOI_FH1_SQUARE_ANNULUS_INFNORM;
              IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
  REAL_ARITH_TAC);;

let MOI_S3CR_IN_CORE = prove
 (`!e (u:real^2) (t:real^1).
     pastecart u t IN moi_s3cr_core e <=>
     &1 + e <= infnorm u /\ infnorm u <= &2 - e /\ abs(drop t) <= &1 - e`,
  REWRITE_TAC[moi_s3cr_core; PASTECART_IN_PCROSS; IN_ELIM_THM; IN_INTERVAL_1;
              DROP_NEG; LIFT_DROP] THEN
  REAL_ARITH_TAC);;

let MOI_S3CR_IN_INTERIOR_S0 = prove
 (`!(u:real^2) (t:real^1).
     pastecart u t IN interior moi_s3cr_s0 <=>
     &1 < infnorm u /\ infnorm u < &2 /\ abs(drop t) < &1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s3cr_s0; INTERIOR_PCROSS; PASTECART_IN_PCROSS; INTERIOR_DIFF;
              INTERIOR_CLOSED_INTERVAL] THEN
  SUBGOAL_THEN `closure(interval(--vector[&1;&1]:real^2,vector[&1;&1])) =
                interval[--vector[&1;&1],vector[&1;&1]]` SUBST1_TAC THENL
   [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
    REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VECTOR_2;
                VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_INTERVAL; IN_INTERVAL_1; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_NEG_COMPONENT; INFNORM_2; DROP_NEG; DROP_VEC] THEN
  REAL_ARITH_TAC);;

let MOI_S3CR_ANN_POLYHEDRON = prove
 (`!e. &0 <= e /\ e <= inv(&2)
       ==> pl_polyhedron {u:real^2 | &1 + e <= infnorm u /\ infnorm u <= &2 - e}`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC
   `{interval[vector[--(&2 - e); --(&2 - e)]:real^2,vector[--(&1 + e); &2 - e]],
     interval[vector[&1 + e; --(&2 - e)]:real^2,vector[&2 - e; &2 - e]],
     interval[vector[--(&2 - e); --(&2 - e)]:real^2,vector[&2 - e; --(&1 + e)]],
     interval[vector[--(&2 - e); &1 + e]:real^2,vector[&2 - e; &2 - e]]}` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
              POLYTOPE_INTERVAL] THEN
  REWRITE_TAC[UNIONS_INSERT; UNIONS_0; UNION_EMPTY; EXTENSION; IN_UNION; IN_ELIM_THM;
              IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; INFNORM_2] THEN
  GEN_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S3CR_CORE_POLYHEDRON = prove
 (`!e. &0 <= e /\ e <= inv(&2) ==> pl_polyhedron (moi_s3cr_core e)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3cr_core] THEN
  MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN
  ASM_SIMP_TAC[MOI_S3CR_ANN_POLYHEDRON; POLYTOPE_IMP_PL_POLYHEDRON; POLYTOPE_INTERVAL]);;

let MOI_S3CR_S0_POLYHEDRON = prove
 (`pl_polyhedron moi_s3cr_s0`,
  SUBGOAL_THEN `moi_s3cr_s0 = moi_s3cr_core (&0)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PASTECART; MOI_S3CR_IN_S0; MOI_S3CR_IN_CORE] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC MOI_S3CR_CORE_POLYHEDRON THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let MOI_S3CR_CORE_SUBSET = prove
 (`!e. &0 <= e ==> moi_s3cr_core e SUBSET moi_s3cr_s0`,
  REWRITE_TAC[SUBSET; FORALL_PASTECART; MOI_S3CR_IN_CORE; MOI_S3CR_IN_S0] THEN
  REAL_ARITH_TAC);;

let MOI_S3CR_CORE_SUBSET_INTERIOR = prove
 (`!e. &0 < e ==> moi_s3cr_core e SUBSET interior moi_s3cr_s0`,
  REWRITE_TAC[SUBSET; FORALL_PASTECART; MOI_S3CR_IN_CORE; MOI_S3CR_IN_INTERIOR_S0] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part 2: a compact subset of the interior of S0 lies in some core;        *)
(* a homeomorphism of S0 onto s maps interiors to interiors (invariance of  *)
(* domain).                                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CR_PSI_CONTINUOUS = prove
 (`!s:real^(2,1)finite_sum->bool.
     (lift o (\p. max (&2 * abs(infnorm(fstcart p) - &3 / &2))
                      (abs(drop(sndcart p))))) continuous_on s`,
  GEN_TAC THEN REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_MAX_1 THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN REWRITE_TAC[LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    SUBGOAL_THEN `(\p:real^(2,1)finite_sum. lift(infnorm(fstcart p))) =
                  (lift o infnorm) o fstcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[CONTINUOUS_AT_LIFT_INFNORM];
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]]);;

let MOI_S3CR_COMPACT_IN_CORE = prove
 (`!k. compact k /\ k SUBSET interior moi_s3cr_s0
       ==> ?e. &0 < e /\ e <= inv(&2) /\ k SUBSET moi_s3cr_core e`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k:real^(2,1)finite_sum->bool = {}` THENL
   [EXISTS_TAC `inv(&2)` THEN ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p:real^(2,1)finite_sum. max (&2 * abs(infnorm(fstcart p) - &3 / &2))
                                               (abs(drop(sndcart p)))`;
                 `k:real^(2,1)finite_sum->bool`] CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[MOI_S3CR_PSI_CONTINUOUS] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^(2,1)finite_sum` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `m = max (&2 * abs(infnorm(fstcart p0) - &3 / &2))
                      (abs(drop(sndcart(p0:real^(2,1)finite_sum))))` THEN
  SUBGOAL_THEN `&0 <= m /\ m < &1` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`fstcart(p0:real^(2,1)finite_sum)`; `sndcart(p0:real^(2,1)finite_sum)`]
      MOI_S3CR_IN_INTERIOR_S0) THEN
    REWRITE_TAC[PASTECART_FST_SND] THEN
    SUBGOAL_THEN `(p0:real^(2,1)finite_sum) IN interior moi_s3cr_s0`
      (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "m" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(&1 - m) / &2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_PASTECART; MOI_S3CR_IN_CORE] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `t:real^1`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (u:real^2) (t:real^1)` o check (fun th ->
    is_forall(concl th))) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3CR_INTERIORS = prove
 (`!(s:real^3->bool) f g.
     homeomorphism (moi_s3cr_s0,s) (f,g)
     ==> IMAGE f (interior moi_s3cr_s0) SUBSET interior s /\
         IMAGE g (interior s) SUBSET interior moi_s3cr_s0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `dim(:real^3) <= dim(:real^(2,1)finite_sum) /\
                dim(:real^(2,1)finite_sum) <= dim(:real^3)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[DIM_UNIV; DIMINDEX_3; DIMINDEX_FINITE_SUM; DIMINDEX_2; DIMINDEX_1] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `moi_s3cr_s0` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`f:real^(2,1)finite_sum->real^3`; `(:real^(2,1)finite_sum)`;
                   `(:real^3)`; `interior moi_s3cr_s0`] INVARIANCE_OF_DOMAIN_SUBSPACES) THEN
    ASM_REWRITE_TAC[SUBSPACE_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV; GSYM OPEN_IN;
                    OPEN_INTERIOR] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_s3cr_s0` THEN ASM_REWRITE_TAC[INTERIOR_SUBSET];
      MP_TAC(ISPEC `moi_s3cr_s0` INTERIOR_SUBSET) THEN ASM SET_TAC[]];
    MP_TAC(ISPEC `s:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`g:real^3->real^(2,1)finite_sum`; `(:real^3)`;
                   `(:real^(2,1)finite_sum)`; `interior s:real^3->bool`]
      INVARIANCE_OF_DOMAIN_SUBSPACES) THEN
    ASM_REWRITE_TAC[SUBSPACE_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV; GSYM OPEN_IN;
                    OPEN_INTERIOR] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[INTERIOR_SUBSET];
      MP_TAC(ISPEC `s:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: the straight-line retraction of S0 onto a core and the           *)
(* resulting isomorphism H_1(core image) -> H_1(s).                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CR_N1_CONTINUOUS = prove
 (`!s:real^(2,1)finite_sum->bool. (\p. lift(infnorm(fstcart p))) continuous_on s`,
  GEN_TAC THEN
  SUBGOAL_THEN `(\p:real^(2,1)finite_sum. lift(infnorm(fstcart p))) =
                (lift o infnorm) o fstcart` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[CONTINUOUS_AT_LIFT_INFNORM]);;

let MOI_S3CR_N2_CONTINUOUS = prove
 (`!s:real^(2,1)finite_sum->bool. (\p. lift(drop(sndcart p))) continuous_on s`,
  GEN_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `(\p:real^(2,1)finite_sum. sndcart p) = sndcart` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]);;

let MOI_S3CR_RETRACT = prove
 (`!e. &0 <= e /\ e <= inv(&2)
       ==> ?r. r continuous_on moi_s3cr_s0 /\
               IMAGE r moi_s3cr_s0 SUBSET moi_s3cr_core e /\
               (!x. x IN moi_s3cr_core e ==> r x = x) /\
               (!x. x IN moi_s3cr_s0 ==> segment[x,r x] SUBSET moi_s3cr_s0)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC
   `\p:real^(2,1)finite_sum.
      pastecart ((max (&1 + e) (min (&2 - e) (infnorm(fstcart p))) *
                  inv(infnorm(fstcart p))) % fstcart p)
                (lift(max (--(&1 - e)) (min (&1 - e) (drop(sndcart p)))))` THEN
  SUBGOAL_THEN `!x:real^(2,1)finite_sum. x IN moi_s3cr_s0 ==> &1 <= infnorm(fstcart x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; MOI_S3CR_IN_S0; FSTCART_PASTECART] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
      REWRITE_TAC[o_DEF; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_MAX_1 THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_MIN_1 THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST; MOI_S3CR_N1_CONTINUOUS];
        MP_TAC(ISPECL [`\p:real^(2,1)finite_sum. infnorm(fstcart p)`; `moi_s3cr_s0`]
          CONTINUOUS_ON_INV) THEN
        REWRITE_TAC[o_DEF; MOI_S3CR_N1_CONTINUOUS] THEN DISCH_THEN MATCH_MP_TAC THEN
        X_GEN_TAC `x:real^(2,1)finite_sum` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^(2,1)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC];
      MATCH_MP_TAC CONTINUOUS_ON_MAX_1 THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MIN_1 THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; MOI_S3CR_N2_CONTINUOUS]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; MOI_S3CR_IN_S0;
                MOI_S3CR_IN_CORE; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`u:real^2`; `t:real^1`] THEN STRIP_TAC THEN
    REWRITE_TAC[INFNORM_MUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_INFNORM] THEN
    SUBGOAL_THEN `abs(max (&1 + e) (min (&2 - e) (infnorm(u:real^2)))) =
                  max (&1 + e) (min (&2 - e) (infnorm u))` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(max (&1 + e) (min (&2 - e) (infnorm(u:real^2))) * inv(infnorm u)) *
                  infnorm u = max (&1 + e) (min (&2 - e) (infnorm u))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN `~(infnorm(u:real^2) = &0)` (fun th ->
        SIMP_TAC[th; REAL_MUL_LINV; REAL_MUL_RID]) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[FORALL_PASTECART; MOI_S3CR_IN_CORE; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`u:real^2`; `t:real^1`] THEN STRIP_TAC THEN
    REWRITE_TAC[PASTECART_INJ] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `max (&1 + e) (min (&2 - e) (infnorm(u:real^2))) = infnorm u`
        SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(infnorm(u:real^2) = &0)` (fun th ->
        SIMP_TAC[th; REAL_MUL_RINV; VECTOR_MUL_LID]) THEN
      ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM LIFT_DROP] THEN AP_TERM_TAC THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[FORALL_PASTECART; MOI_S3CR_IN_S0; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`u:real^2`; `t:real^1`] THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; IN_SEGMENT] THEN X_GEN_TAC `y:real^(2,1)finite_sum` THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[GSYM PASTECART_CMUL; PASTECART_ADD; MOI_S3CR_IN_S0] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FH1_INFNORM_SEGMENT THEN
      MAP_EVERY EXISTS_TAC
       [`u:real^2`; `max (&1 + e) (min (&2 - e) (infnorm(u:real^2)))`] THEN
      ASM_REWRITE_TAC[IN_SEGMENT] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXISTS_TAC `l:real` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
      MATCH_MP_TAC(REAL_ARITH `--a <= x /\ x <= a ==> abs x <= a`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `(&1 - l) * --(drop t) + l * --y <= &1 ==>
                                 --(&1) <= (&1 - l) * drop t + l * y`) THEN
        MATCH_MP_TAC REAL_CONVEX_BOUND_LE;
        MATCH_MP_TAC REAL_CONVEX_BOUND_LE] THEN
      ASM_REAL_ARITH_TAC]]);;

let MOI_S3CR_CORE_ISO = prove
 (`!(s:real^3->bool) f g e.
     homeomorphism (moi_s3cr_s0,s) (f,g) /\ &0 <= e /\ e <= inv(&2)
     ==> group_isomorphism
           (homology_group(&1,subtopology euclidean (IMAGE f (moi_s3cr_core e))),
            homology_group(&1,subtopology euclidean s))
           (hom_induced (&1) (subtopology euclidean (IMAGE f (moi_s3cr_core e)),{})
                             (subtopology euclidean s,{}) (\x. x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e:real` MOI_S3CR_RETRACT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^(2,1)finite_sum->real^(2,1)finite_sum`
    STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_FH1_H1_DEFORM_ISO THEN
  MAP_EVERY EXISTS_TAC [`moi_s3cr_s0`; `g:real^3->real^(2,1)finite_sum`;
                        `r:real^(2,1)finite_sum->real^(2,1)finite_sum`] THEN
  ASM_SIMP_TAC[MOI_S3CR_CORE_SUBSET]);;

let MOI_S3CR_INCL_COMPOSE = prove
 (`!(x:real^N->bool) y z c.
     x SUBSET y /\ y SUBSET z
     ==> hom_induced (&1) (subtopology euclidean x,{}) (subtopology euclidean z,{})
                     (\x. x) c =
         hom_induced (&1) (subtopology euclidean y,{}) (subtopology euclidean z,{})
                     (\x. x)
           (hom_induced (&1) (subtopology euclidean x,{}) (subtopology euclidean y,{})
                        (\x. x) c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `hom_induced (&1) (subtopology euclidean x,{}) (subtopology euclidean z,{})
                (\x:real^N. x) =
    hom_induced (&1) (subtopology euclidean y,{}) (subtopology euclidean z,{}) (\x. x) o
    hom_induced (&1) (subtopology euclidean x,{}) (subtopology euclidean y,{}) (\x. x)`
  (fun th -> REWRITE_TAC[th; o_THM]) THENL
   [ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^N. x) = (\x. x) o (\x. x)` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC HOM_INDUCED_COMPOSE_EMPTY THEN
  ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION]);;

let MOI_S3CR_CARRIES_ISO = prove
 (`!(j:real^N->bool) m s.
     j SUBSET m /\ m SUBSET s /\ carries_h1 j s /\
     group_isomorphism (homology_group(&1,subtopology euclidean m),
                        homology_group(&1,subtopology euclidean s))
       (hom_induced (&1) (subtopology euclidean m,{}) (subtopology euclidean s,{}) (\x. x))
     ==> carries_h1 j m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[carries_h1; GROUP_ISOMORPHISM; group_image] THEN
  STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (j:real^N->bool)`;
                   `subtopology euclidean (m:real^N->bool)`; `\x:real^N. x`]
      GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
    SIMP_TAC[group_homomorphism];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `w:((num->real)->real^N)frag->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `hom_induced (&1) (subtopology euclidean m,{}) (subtopology euclidean s,{})
                (\x:real^N. x) w IN
    group_carrier(homology_group(&1,subtopology euclidean s))` MP_TAC THENL
   [MATCH_MP_TAC MOI_S4J_HOM_IN THEN
    EXISTS_TAC `homology_group(&1,subtopology euclidean (m:real^N->bool))` THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) o
    check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `j:real^N->bool`)) (lhs(concl th)))) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:((num->real)->real^N)frag->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:((num->real)->real^N)frag->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4J_HOM_IN THEN
    EXISTS_TAC `homology_group(&1,subtopology euclidean (j:real^N->bool))` THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ASM_MESON_TAC[MOI_S3CR_INCL_COMPOSE]]);;

(* ------------------------------------------------------------------------- *)
(* Part 4: cutting a polyhedron p along a closed polyhedron s.  With a       *)
(* triangulation of p having p INTER s as a subcomplex, the union b of the   *)
(* closed simplices outside the subcomplex is a polyhedron, (p INTER s)      *)
(* UNION b = p, and (p INTER s) INTER b misses the interior of s.            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CR_PIECES = prove
 (`!(p:real^N->bool) s.
     pl_polyhedron p /\ pl_polyhedron s /\ closed s
     ==> ?b. pl_polyhedron b /\ (p INTER s) UNION b = p /\
             (p INTER s) INTER b SUBSET p DIFF interior s /\
             p DIFF s SUBSET b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (p INTER s:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PL_POLYHEDRON_INTER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^N->bool`; `p INTER s:real^N->bool`] MOI_S4J_PAIR_TRIANGULATION) THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool`
    (X_CHOOSE_THEN `l:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `UNIONS (t DIFF l):real^N->bool` THEN
  UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) t` THEN
  REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
  UNDISCH_TAC `simplicial_complex (t:(real^N->bool)->bool)` THEN
  REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4J_PL_POLYHEDRON_UNIONS THEN ASM_SIMP_TAC[FINITE_DIFF; IN_DIFF] THEN
    X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    MAP_EVERY UNDISCH_TAC
     [`UNIONS t = (p:real^N->bool)`; `UNIONS l = (p INTER s:real^N->bool)`;
      `(l:(real^N->bool)->bool) SUBSET t`] THEN
    SET_TAC[];
    ALL_TAC;
    MAP_EVERY UNDISCH_TAC
     [`UNIONS t = (p:real^N->bool)`; `UNIONS l = (p INTER s:real^N->bool)`] THEN
    SET_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_DIFF] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (X_CHOOSE_THEN `sg:real^N->bool` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?n. n simplex (sg:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (sg:real^N->bool) /\ closed sg` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `~(interior s INTER relative_interior (sg:real^N->bool) = {})`
  (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC o
   REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THENL
   [MP_TAC(ISPECL [`interior s:real^N->bool`; `relative_interior(sg:real^N->bool)`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN
    UNDISCH_TAC `(x:real^N) IN interior s` THEN UNDISCH_TAC `(x:real^N) IN sg` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS l` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN
    MP_TAC(ISPEC `sg:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `UNIONS t = (p:real^N->bool)` THEN
    UNDISCH_TAC `(sg:real^N->bool) IN t` THEN
    UNDISCH_TAC `(y:real^N) IN interior s` THEN
    UNDISCH_TAC `(y:real^N) IN relative_interior sg` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(tau:real^N->bool) IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((sg:real^N->bool) INTER tau) face_of sg /\ (sg INTER tau) face_of tau`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(sg:real^N->bool) INTER tau = sg` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(sg:real^N->bool) INTER tau`; `sg:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN relative_interior sg` THEN
    UNDISCH_TAC `(y:real^N) IN tau` THEN
    MP_TAC(ISPEC `sg:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~((sg:real^N->bool) IN l)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(ASSUME `!s f:real^N->bool. s IN l /\ f face_of s ==> f IN l`) THEN
  EXISTS_TAC `tau:real^N->bool` THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 5: the Mayer-Vietoris step.  If zm SUBSET a SUBSET s carries          *)
(* H_1(s) and zo SUBSET b carries H_1(a UNION b), then a INTER b carries      *)
(* H_1(s) (MV_POLY for the polyhedra a, b).                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CR_MV_CARRIES = prove
 (mk_imp(moi_n3 MOI_S31_MV_POLY,
  `!(a:real^3->bool) b zm zo s.
     pl_polyhedron a /\ pl_polyhedron b /\
     zm SUBSET a /\ a SUBSET s /\ zo SUBSET b /\
     carries_h1 zm s /\ carries_h1 zo (a UNION b)
     ==> carries_h1 (a INTER b) s`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[carries_h1; group_image] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (a INTER b:real^3->bool)`;
                   `subtopology euclidean (s:real^3->bool)`; `\x:real^3. x`]
      GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
    SIMP_TAC[group_homomorphism];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `c0:((num->real)->real^3)frag->bool` THEN
  DISCH_TAC THEN
  UNDISCH_TAC `carries_h1 (zm:real^3->bool) s` THEN
  REWRITE_TAC[carries_h1; group_image] THEN
  DISCH_THEN(MP_TAC o SPEC `c0:((num->real)->real^3)frag->bool` o
             GEN_REWRITE_RULE I [EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `be:((num->real)->real^3)frag->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `x0 = hom_induced (&1) (subtopology euclidean zm,{})
                               (subtopology euclidean a,{}) (\x:real^3. x) be` THEN
  SUBGOAL_THEN `x0 IN group_carrier(homology_group(&1,subtopology euclidean (a:real^3->bool)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN MATCH_MP_TAC MOI_S4J_HOM_IN THEN
    EXISTS_TAC `homology_group(&1,subtopology euclidean (zm:real^3->bool))` THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ALL_TAC] THEN
  ABBREV_TAC `w = hom_induced (&1) (subtopology euclidean a,{})
                              (subtopology euclidean (a UNION b),{}) (\x:real^3. x) x0` THEN
  SUBGOAL_THEN `w IN group_carrier(homology_group(&1,subtopology euclidean
                                     (a UNION b:real^3->bool)))` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC MOI_S4J_HOM_IN THEN
    EXISTS_TAC `homology_group(&1,subtopology euclidean (a:real^3->bool))` THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ALL_TAC] THEN
  UNDISCH_TAC `carries_h1 (zo:real^3->bool) (a UNION b)` THEN
  REWRITE_TAC[carries_h1; group_image] THEN
  DISCH_THEN(MP_TAC o SPEC `w:((num->real)->real^3)frag->bool` o
             GEN_REWRITE_RULE I [EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `de:((num->real)->real^3)frag->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `y0 = hom_induced (&1) (subtopology euclidean zo,{})
                               (subtopology euclidean b,{}) (\x:real^3. x) de` THEN
  SUBGOAL_THEN `y0 IN group_carrier(homology_group(&1,subtopology euclidean (b:real^3->bool)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN MATCH_MP_TAC MOI_S4J_HOM_IN THEN
    EXISTS_TAC `homology_group(&1,subtopology euclidean (zo:real^3->bool))` THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hom_induced (&1) (subtopology euclidean b,{}) (subtopology euclidean (a UNION b),{})
                (\x:real^3. x) y0 = w` ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN
    MP_TAC(ISPECL [`zo:real^3->bool`; `b:real^3->bool`; `a UNION b:real^3->bool`;
                   `de:((num->real)->real^3)frag->bool`] MOI_S3CR_INCL_COMPOSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    FIRST_X_ASSUM(ACCEPT_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `w:((num->real)->real^3)frag->bool`));
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3->bool`; `b:real^3->bool`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `pl_polyhedron:(real^3->bool)->bool`))
    (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x0:((num->real)->real^3)frag->bool`;
                             `y0:((num->real)->real^3)frag->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:((num->real)->real^3)frag->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:((num->real)->real^3)frag->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`a INTER b:real^3->bool`; `a:real^3->bool`; `s:real^3->bool`;
                 `z:((num->real)->real^3)frag->bool`] MOI_S3CR_INCL_COMPOSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[INTER_SUBSET]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "x0" THEN
  MP_TAC(ISPECL [`zm:real^3->bool`; `a:real^3->bool`; `s:real^3->bool`;
                 `be:((num->real)->real^3)frag->bool`] MOI_S3CR_INCL_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 6: facts about PL solid tori and the theorem CARRIER.                *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CR_S0_PATH_CONNECTED = prove
 (`path_connected moi_s3cr_s0`,
  SUBGOAL_THEN
   `moi_s3cr_s0 =
    (((interval[vector[--(&2); --(&2)]:real^2,vector[--(&1); &2]] UNION
       interval[vector[--(&2); --(&2)]:real^2,vector[&2; --(&1)]]) UNION
      interval[vector[&1; --(&2)]:real^2,vector[&2; &2]]) UNION
     interval[vector[--(&2); &1]:real^2,vector[&2; &2]]) PCROSS
    interval[--vec 1:real^1,vec 1]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PASTECART; MOI_S3CR_IN_S0; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[IN_UNION; IN_INTERVAL; IN_INTERVAL_1; DIMINDEX_2; FORALL_2; VECTOR_2;
                INFNORM_2; DROP_NEG; DROP_VEC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PATH_CONNECTED_PCROSS THEN
  SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; CONVEX_INTERVAL] THEN
  REPEAT(MATCH_MP_TAC PATH_CONNECTED_UNION THEN
         SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; CONVEX_INTERVAL] THEN
         TRY CONJ_TAC) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THENL
   [EXISTS_TAC `vector[--(&2); --(&2)]:real^2`;
    EXISTS_TAC `vector[&2; --(&2)]:real^2`;
    EXISTS_TAC `vector[--(&2); &2]:real^2`] THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC);;

let MOI_S3CR_SOLID_TORUS_FACTS = prove
 (`!s:real^N->bool.
     pl_solid_torus s
     ==> ?f g. pl_homeomorphism (moi_s3cr_s0,s) (f,g) /\
               pl_polyhedron s /\ path_connected s /\ compact s`,
  GEN_TAC THEN REWRITE_TAC[pl_solid_torus; GSYM moi_s3cr_s0] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^(2,1)finite_sum->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^(2,1)finite_sum` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_comb(lhs(concl th)) && fst(dest_const(fst(strip_comb(lhs(concl th))))) = "IMAGE" &&
    can (find_term ((=) `moi_s3cr_s0`)) (lhs(concl th)))) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[MOI_S3CR_S0_POLYHEDRON];
    MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[MOI_S3CR_S0_PATH_CONNECTED];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[MOI_S3CR_S0_POLYHEDRON; PL_POLYHEDRON_IMP_COMPACT]]);;

let CARRIER = prove
 (MOI_S31_CARRIER,
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`sa:real^3->bool`; `sb:real^3->bool`; `zm:real^3->bool`;
                       `zo:real^3->bool`; `gg:real^3->bool`] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  (* the two solid tori *)
  MP_TAC(ISPEC `sb:real^3->bool` MOI_S3CR_SOLID_TORUS_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(2,1)finite_sum->real^3`
    (X_CHOOSE_THEN `g:real^3->real^(2,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `sa:real^3->bool` MOI_S3CR_SOLID_TORUS_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^(2,1)finite_sum->real^3`
    (X_CHOOSE_THEN `g':real^3->real^(2,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `homeomorphism (moi_s3cr_s0,sb) (f:real^(2,1)finite_sum->real^3,g) /\
                pl_map_on moi_s3cr_s0 f` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sb:real^3->bool`; `f:real^(2,1)finite_sum->real^3`;
                 `g:real^3->real^(2,1)finite_sum`] MOI_S3CR_INTERIORS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (zm:real^3->bool) /\ compact (zo:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_SPHERE]; ALL_TAC] THEN
  (* the core of sb *)
  MP_TAC(ISPEC `IMAGE (g:real^3->real^(2,1)finite_sum) (zm UNION zo)`
    MOI_S3CR_COMPACT_IN_CORE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[COMPACT_UNION] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sb:real^3->bool` THEN
      UNDISCH_TAC `homeomorphism (moi_s3cr_s0,sb) (f:real^(2,1)finite_sum->real^3,g)` THEN
      REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `sb:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (g:real^3->real^(2,1)finite_sum) (interior sb)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `B = IMAGE (f:real^(2,1)finite_sum->real^3) (moi_s3cr_core e)` THEN
  SUBGOAL_THEN `pl_polyhedron (B:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_SIMP_TAC[MOI_S3CR_CORE_POLYHEDRON; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_s3cr_s0` THEN
    ASM_SIMP_TAC[MOI_S3CR_CORE_SUBSET; REAL_LT_IMP_LE; LOCALLY_POLYHEDRAL_PL_POLYHEDRON;
                 MOI_S3CR_CORE_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN `zm UNION zo SUBSET (B:real^3->bool) /\ B SUBSET interior sb`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (moi_s3cr_s0,sb) (f:real^(2,1)finite_sum->real^3,g)` THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN EXPAND_TAC "B" THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      EXISTS_TAC `(g:real^3->real^(2,1)finite_sum) y` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        MP_TAC(ISPEC `sb:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
        UNDISCH_TAC `IMAGE (g:real^3->real^(2,1)finite_sum) (zm UNION zo) SUBSET
                     moi_s3cr_core e` THEN ASM SET_TAC[]];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (f:real^(2,1)finite_sum->real^3) (interior moi_s3cr_s0)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_SIMP_TAC[MOI_S3CR_CORE_SUBSET_INTERIOR];
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B:real^3->bool) SUBSET sb` ASSUME_TAC THENL
   [MP_TAC(ISPEC `sb:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  (* H_1 of the core *)
  SUBGOAL_THEN `carries_h1 (zo:real^3->bool) B` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3CR_CARRIES_ISO THEN EXISTS_TAC `sb:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOOPS_CARRIED_IMP_CARRIES_H1 THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `sb:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      EXPAND_TAC "B" THEN MATCH_MP_TAC MOI_S3CR_CORE_ISO THEN
      EXISTS_TAC `g:real^3->real^(2,1)finite_sum` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `carries_h1 (zm:real^3->bool) sa` ASSUME_TAC THENL
   [MATCH_MP_TAC LOOPS_CARRIED_IMP_CARRIES_H1 THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `sa:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the pieces *)
  MP_TAC(ISPECL [`B:real^3->bool`; `sa:real^3->bool`] MOI_S3CR_PIECES) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`B INTER sa:real^3->bool`; `b:real^3->bool`; `zm:real^3->bool`;
                `zo:real^3->bool`; `sa:real^3->bool`]
    (MP MOI_S3CR_MV_CARRIES (ASSUME (moi_n3 MOI_S31_MV_POLY)))) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PL_POLYHEDRON_INTER; INTER_SUBSET] THEN
    MP_TAC(ISPEC `sa:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `zm UNION zo SUBSET (B:real^3->bool)` THEN
    UNDISCH_TAC `zm SUBSET interior sa INTER interior (sb:real^3->bool)` THEN
    UNDISCH_TAC `zo SUBSET interior sb DIFF (sa:real^3->bool)` THEN
    UNDISCH_TAC `(B:real^3->bool) DIFF sa SUBSET b` THEN SET_TAC[];
    DISCH_TAC] THEN
  (* the carrier *)
  SUBGOAL_THEN `DISJOINT ((B INTER sa) INTER b) (frontier sb:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `sb:real^3->bool` FRONTIER_SUBSET_CLOSED) THEN
    REWRITE_TAC[frontier] THEN UNDISCH_TAC `(B:real^3->bool) SUBSET interior sb` THEN
    SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(B INTER sa) INTER b:real^3->bool` THEN
  ASM_SIMP_TAC[PL_POLYHEDRON_INTER] THEN
  SUBGOAL_THEN `frontier sa = sa DIFF interior (sa:real^3->bool)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(B INTER sa) INTER b SUBSET B DIFF interior (sa:real^3->bool)`;
    `DISJOINT ((B INTER sa) INTER b) (frontier sb:real^3->bool)`;
    `(gg:real^3->bool) SUBSET frontier sb`] THEN
  SET_TAC[]);;

