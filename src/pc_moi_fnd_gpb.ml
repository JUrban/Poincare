(* ========================================================================= *)
(* pc_moi_fnd_gpb: general position of surfaces in real^3 and of curves in  *)
(* surfaces (Moise GTM 47, 28.2 p.202 and the uses on pp.221, 231, 240).    *)
(* Main theorems (terms of pc_moi_fnd_stmt.ml):                              *)
(*   GENERAL_POSITION_SURFACES_3   = MOI_FND_GP_SURFACES_3                   *)
(*   GENERAL_POSITION_CURVES_2     = MOI_FND_GP_CURVES_2                     *)
(*                                                                           *)
(* Route for SURFACES_3 (as DG GeneralPosition.lean:447): a PL cutoff phi   *)
(* with Lipschitz constant 1/r, equal to 1 on UNIONS s and supported in a   *)
(* compact subset of w, and a generic small vector d give the PLH           *)
(* x |-> x + phi(x) d of real^3 (it maps each line parallel to d onto       *)
(* itself), which translates UNIONS s by d.  A generic translate is in      *)
(* affine general position with the finitely many simplices of t near it;  *)
(* at a common point the carriers are two triangles (two transverse planes) *)
(* or an edge and a triangle (a wedge of two half planes or a plane against *)
(* a transverse plane), and explicit PL charts (affine maps and the map     *)
(* (X,Y,Z) |-> (min X Y,Z,X - Y)) give pl_crossing_at.                      *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_gpa.ml";;
needs "src/pc_moi_fnd_m3a.ml";;
needs "src/pc_moi_ptri.ml";;
needs "src/pc_moi_fnd_surfa.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A. A PL cutoff with Lipschitz constant 1/r (maxima of cube bumps built   *)
(* from infnorm), and the push x |-> x + phi(x) d, a PLH of real^3 when     *)
(* norm d < r.                                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_INFNORM_3 = prove
 (`!x:real^3. infnorm x = max (abs(x$1)) (max (abs(x$2)) (abs(x$3)))`,
  GEN_TAC THEN
  REWRITE_TAC[infnorm; INFNORM_SET_IMAGE; DIMINDEX_3] THEN
  REWRITE_TAC[NUMSEG_CONV `1..3`; IMAGE_CLAUSES] THEN
  SIMP_TAC[SUP_INSERT_FINITE; FINITE_INSERT; FINITE_EMPTY; NOT_INSERT_EMPTY]);;

let MOI_FGB_PL_INFNORM = prove
 (`!c:real^3. pl_map_on (:real^3) (\x. lift(infnorm(x - c)))`,
  GEN_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `\x:real^3. lift(max (max (x$1 - (c:real^3)$1) (c$1 - x$1))
                              (max (max (x$2 - c$2) (c$2 - x$2))
                                   (max (x$3 - c$3) (c$3 - x$3))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIV; MOI_FGB_INFNORM_3; VECTOR_SUB_COMPONENT; LIFT_EQ] THEN
    REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN CONJ_TAC) THEN
    SIMP_TAC[MOI_PTR_PL_LIFT_COORD; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]]);;

let MOI_FGB_BETA_PL = prove
 (`!(c:real^3) r.
     pl_map_on (:real^3)
       (\x. lift(min (&1) (max (&0) (&2 - infnorm(x - c) / r))))`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MOI_PTR_PL_LIFT_MIN THEN
  SIMP_TAC[MOI_PTR_PL_LIFT_CONST; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
  MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN
  SIMP_TAC[MOI_PTR_PL_LIFT_CONST; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `\x:real^3. lift(&2) + lift(--(inv r) * infnorm(x - c))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIV; GSYM LIFT_ADD; LIFT_EQ; real_div] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC PL_MAP_ON_ADD THEN
    SIMP_TAC[MOI_PTR_PL_LIFT_CONST; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
    MATCH_MP_TAC MOI_PTR_PL_LIFT_CMUL THEN REWRITE_TAC[MOI_FGB_PL_INFNORM]]);;

let MOI_FGB_BETA_LIPSCHITZ = prove
 (`!(c:real^N) r x y.
     &0 < r
     ==> abs(min (&1) (max (&0) (&2 - infnorm(x - c) / r)) -
             min (&1) (max (&0) (&2 - infnorm(y - c) / r)))
         <= norm(x - y) / r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(infnorm(x - c) - infnorm(y - c:real^N)) <= norm(x - y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `infnorm((x - c) - (y - c:real^N))` THEN
    REWRITE_TAC[REAL_ABS_SUB_INFNORM] THEN
    REWRITE_TAC[VECTOR_ARITH `(x - c) - (y - c):real^N = x - y`;
                INFNORM_LE_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(infnorm(x - c) / r - infnorm(y - c:real^N) / r) <= norm(x - y) / r`
  MP_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < r ==> abs r = r`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let MOI_FGB_BUMP_FINITE = prove
 (`!C:real^3->bool r.
     FINITE C /\ &0 < r
     ==> ?phi:real^3->real.
           pl_map_on (:real^3) (\x. lift(phi x)) /\
           (!x. &0 <= phi x /\ phi x <= &1) /\
           (!x y. abs(phi x - phi y) <= norm(x - y) / r) /\
           (!c x. c IN C /\ norm(x - c) <= r ==> phi x = &1) /\
           (!x. (!c. c IN C ==> &4 * r <= norm(x - c)) ==> phi x = &0)`,
  GEN_TAC THEN X_GEN_TAC `r:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  SPEC_TAC(`C:real^3->bool`,`C:real^3->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `\x:real^3. &0` THEN
    SIMP_TAC[MOI_PTR_PL_LIFT_CONST; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
    REWRITE_TAC[NOT_IN_EMPTY; REAL_POS; REAL_SUB_REFL; REAL_ABS_0] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c0:real^3`; `C:real^3->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "b") (CONJUNCTS_THEN2 (LABEL_TAC "l")
    (CONJUNCTS_THEN2 (LABEL_TAC "one") (LABEL_TAC "zero")))))) THEN
  EXISTS_TAC `\x:real^3. max (min (&1) (max (&0) (&2 - infnorm(x - c0) / r)))
                             (phi x)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN ASM_REWRITE_TAC[MOI_FGB_BETA_PL];
    GEN_TAC THEN REMOVE_THEN "b" (MP_TAC o SPEC `x:real^3`) THEN
    REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    MP_TAC(ISPECL [`c0:real^3`; `r:real`; `x:real^3`; `y:real^3`]
      MOI_FGB_BETA_LIPSCHITZ) THEN
    REMOVE_THEN "l" (MP_TAC o SPECL [`x:real^3`; `y:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`c:real^3`; `x:real^3`] THEN
    REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `infnorm(x - c0:real^3) / r <= &1` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x - c0:real^3)` THEN
        ASM_REWRITE_TAC[INFNORM_LE_NORM];
        REMOVE_THEN "b" (MP_TAC o SPEC `x:real^3`) THEN REAL_ARITH_TAC];
      REMOVE_THEN "one" (MP_TAC o SPECL [`c:real^3`; `x:real^3`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INSERT] THEN DISCH_TAC THEN
    REMOVE_THEN "zero" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `&2 <= infnorm(x - c0:real^3) / r` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      SUBGOAL_THEN `&4 * r <= norm(x - c0:real^3)` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPEC `x - c0:real^3` NORM_LE_INFNORM) THEN
      REWRITE_TAC[DIMINDEX_3] THEN
      SUBGOAL_THEN `sqrt(&3) <= &2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPEC `x - c0:real^3` INFNORM_POS_LE) THEN
      MP_TAC(SPEC `&3` SQRT_POS_LE) THEN REWRITE_TAC[REAL_POS] THEN
      REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `sqrt(&3) * infnorm(x - c0:real^3) <= &2 * infnorm(x - c0)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let MOI_FGB_CUTOFF = prove
 (`!K w:real^3->bool.
     compact K /\ open w /\ K SUBSET w
     ==> ?phi r k.
           &0 < r /\ pl_map_on (:real^3) (\x. lift(phi x)) /\
           (!x. &0 <= phi x /\ phi x <= &1) /\
           (!x y. abs(phi x - phi y) <= norm(x - y) / r) /\
           (!x. x IN K ==> phi x = &1) /\
           compact k /\ k SUBSET w /\ (!x. ~(x IN k) ==> phi x = &0) /\
           (!x y. x IN K /\ dist(x,y) <= r ==> y IN k)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `K:real^3->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`\x:real^3. &0`; `&1`; `{}:real^3->bool`] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; COMPACT_EMPTY; EMPTY_SUBSET] THEN
    SIMP_TAC[MOI_PTR_PL_LIFT_CONST; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
    REWRITE_TAC[REAL_POS; REAL_SUB_REFL; REAL_ABS_0; REAL_DIV_1; NORM_POS_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real^3->bool`; `(:real^3) DIFF w`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "sep"))) THEN
  MP_TAC(ISPEC `K:real^3->bool` COMPACT_IMP_TOTALLY_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `dl / &5`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`C:real^3->bool`; `dl / &5`] MOI_FGB_BUMP_FINITE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "one") (LABEL_TAC "zero")))))) THEN
  SUBGOAL_THEN
   `!x:real^3. x IN K ==> ?c. c IN C /\ dist(c,x) < dl / &5`
  (LABEL_TAC "cov") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC
     `K SUBSET UNIONS (IMAGE (\x:real^3. ball(x,dl / &5)) C)` THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM; IN_BALL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`phi:real^3->real`; `dl / &5`;
    `UNIONS (IMAGE (\c:real^3. cball(c,&4 * dl / &5)) C)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    REMOVE_THEN "cov" (MP_TAC o SPEC `x:real^3`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "one" MATCH_MP_TAC THEN EXISTS_TAC `c:real^3` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    REWRITE_TAC[GSYM dist] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; COMPACT_CBALL];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; SUBSET; IN_CBALL] THEN
    X_GEN_TAC `c:real^3` THEN DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(c:real^3) IN K` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(y:real^3) IN w` THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "sep" (MP_TAC o SPECL [`c:real^3`; `y:real^3`]) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; IN_CBALL; NOT_EXISTS_THM] THEN
    DISCH_TAC THEN REMOVE_THEN "zero" MATCH_MP_TAC THEN
    X_GEN_TAC `c:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^3`) THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[GSYM dist] THEN
    REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "cov" (MP_TAC o SPEC `x:real^3`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; IN_CBALL] THEN
    EXISTS_TAC `c:real^3` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:real^3`; `x:real^3`; `y:real^3`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC]);;

(* Each line parallel to d is mapped into itself; along it the push is a  *)
(* continuous function of the parameter.                                    *)

let MOI_FGB_LINE_CONT = prove
 (`!(phi:real^N->real) r (d:real^N) y.
     &0 < r /\ (!x y. abs(phi x - phi y) <= norm(x - y) / r)
     ==> (\u:real^1. lift(drop u - phi(y - drop u % d))) continuous_on
         (:real^1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIPSCHITZ_IMP_CONTINUOUS_ON THEN
  EXISTS_TAC `&1 + norm(d:real^N) / r` THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y - drop u % d:real^N`;
                                `y - drop v % d:real^N`]) THEN
  REWRITE_TAC[VECTOR_ARITH
   `(y - a % d) - (y - b % d):real^N = (b - a) % d`] THEN
  REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN
   `(abs(drop v - drop u) * norm(d:real^N)) / r =
    abs(drop u - drop v) * (norm d / r)`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_ABS_SUB] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let MOI_FGB_PUSH = prove
 (`!(phi:real^N->real) r (d:real^N).
     &0 < r /\ norm d < r /\
     pl_map_on (:real^N) (\x. lift(phi x)) /\
     (!x. &0 <= phi x /\ phi x <= &1) /\
     (!x y. abs(phi x - phi y) <= norm(x - y) / r)
     ==> ?g. pl_homeomorphism ((:real^N),(:real^N)) ((\x. x + phi x % d),g)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "b")
    (LABEL_TAC "l"))))) THEN
  SUBGOAL_THEN `&0 <= norm(d:real^N) / r /\ norm(d:real^N) / r < &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_LT_IMP_LE;
                 REAL_LT_LDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  ABBREV_TAC `q = norm(d:real^N) / r` THEN
  SUBGOAL_THEN
   `!x y:real^N. abs(phi x - phi y) * norm(d:real^N) <= q * norm(x - y)`
  (LABEL_TAC "l2") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "q" THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(norm(x - y:real^N) / r) * norm(d:real^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN
      USE_THEN "l" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[NORM_POS_LE];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^N. (&1 - q) * norm(x - y) <=
                 norm((x + phi x % d) - (y + phi y % d))`
  (LABEL_TAC "key") THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[VECTOR_ARITH
     `(x + a % d) - (y + b % d):real^N = (x - y) + (a - b) % d`] THEN
    USE_THEN "l2" (MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
    MP_TAC(ISPECL [`x - y:real^N`; `(phi(x:real^N) - phi y) % (d:real^N)`]
      (NORM_ARITH `!a b:real^N. norm(a) <= norm(a + b) + norm(b)`)) THEN
    REWRITE_TAC[NORM_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^N. x + phi x % d = y + phi y % d ==> x = y`
  (LABEL_TAC "inj") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(fun th ->
      USE_THEN "key" (MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
      REWRITE_TAC[th; VECTOR_SUB_REFL; NORM_0]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `norm(x - y:real^N) = &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
      REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&1 - q` THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. ?x. x + phi x % d = y` MP_TAC THENL
   [X_GEN_TAC `y:real^N` THEN
    MP_TAC(ISPECL
     [`\u:real^1. lift(drop u - phi(y - drop u % d:real^N))`;
      `vec 0:real^1`; `vec 1:real^1`; `&0`; `1`]
     IVT_INCREASING_COMPONENT_1) THEN
    REWRITE_TAC[DIMINDEX_1; LE_REFL; DROP_VEC; REAL_POS] THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP; VECTOR_MUL_LZERO; VECTOR_SUB_RZERO;
                VECTOR_MUL_LID] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`phi:real^N->real`; `r:real`; `d:real^N`; `y:real^N`]
          MOI_FGB_LINE_CONT) THEN
        ASM_REWRITE_TAC[] THEN
        SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
        USE_THEN "b" (MP_TAC o SPEC `y:real^N`) THEN
        USE_THEN "b" (MP_TAC o SPEC `y - d:real^N`) THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y - drop u % d:real^N` THEN
    UNDISCH_TAC `drop u - phi (y - drop u % d:real^N) = &0` THEN
    REWRITE_TAC[REAL_SUB_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` (LABEL_TAC "g")) THEN
  EXISTS_TAC `g:real^N->real^N` THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism; IN_UNIV] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN USE_THEN "inj" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC LIPSCHITZ_IMP_CONTINUOUS_ON THEN
      EXISTS_TAC `&1 + q` THEN REWRITE_TAC[IN_UNIV] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(x + a % d) - (y + b % d):real^N = (x - y) + (a - b) % d`] THEN
      USE_THEN "l2" (MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
      MP_TAC(ISPECL [`x - y:real^N`; `(phi(x:real^N) - phi y) % (d:real^N)`]
        NORM_TRIANGLE) THEN
      REWRITE_TAC[NORM_MUL] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
      X_GEN_TAC `x:real^N` THEN
      EXISTS_TAC `x + phi x % d:real^N` THEN
      USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LIPSCHITZ_IMP_CONTINUOUS_ON THEN
      EXISTS_TAC `inv(&1 - q)` THEN REWRITE_TAC[IN_UNIV] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
      USE_THEN "key" (MP_TAC o SPECL [`(g:real^N->real^N) x`;
                                       `(g:real^N->real^N) y`]) THEN
      USE_THEN "g" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC PL_MAP_ON_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
      SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV];
      SUBGOAL_THEN
       `(\x:real^N. phi x % (d:real^N)) =
        (\u:real^1. drop u % d) o (\x. lift(phi x))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN
      MP_TAC(ISPECL [`(:real^1)`; `\u:real^1. drop u % (d:real^N)`;
                     `vec 0:real^N`] PL_MAP_ON_AFFINE) THEN
      REWRITE_TAC[VECTOR_ADD_RID; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
      SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
      MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID]]]);;

(* ------------------------------------------------------------------------- *)
(* B. Generic translates.  A translate d + A of a set A of real^3 is in      *)
(* affine general position with B unless d lies in the affine set of       *)
(* differences of the two affine hulls, and that set is all of real^3 only  *)
(* when every translate is in general position.  Finitely many simplices    *)
(* of a locally finite complex closed in w meet a compact subset of w.      *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_GP_TRANSLATE = prove
 (`!(A:real^3->bool) B d.
     ~(d IN {b - a | b IN affine hull B /\ a IN affine hull A}) \/
     {b - a | b IN affine hull B /\ a IN affine hull A} = (:real^3)
     ==> affine_gp_3 (IMAGE (\x. d + x) A) B`,
  REPEAT GEN_TAC THEN REWRITE_TAC[affine_gp_3] THEN
  ASM_CASES_TAC `DISJOINT (IMAGE (\x:real^3. d + x) A) B` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~DISJOINT (IMAGE (\x:real^3. d + x) A) B` THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `a0:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  STRIP_TAC THENL
   [UNDISCH_TAC
     `~((d:real^3) IN {b - a | b IN affine hull B /\ a IN affine hull A})` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MAP_EVERY EXISTS_TAC [`p:real^3`; `a0:real^3`] THEN
    ASM_SIMP_TAC[HULL_INC] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `affine hull (IMAGE (\x:real^3. d + x) A UNION B) = (:real^3)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIV] THEN X_GEN_TAC `z:real^3` THEN
    SUBGOAL_THEN
     `(z - p + d:real^3) IN {b - a | b IN affine hull B /\ a IN affine hull A}`
    MP_TAC THENL [ASM_REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^3` (X_CHOOSE_THEN `a:real^3`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `z:real^3 = p + &1 % (b - (d + a))` SUBST1_TAC THENL
     [UNDISCH_TAC `z - p + d:real^3 = b - a` THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
    REWRITE_TAC[AFFINE_AFFINE_HULL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!s t. (x:real^3) IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `affine hull B:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!s t. (x:real^3) IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `affine hull (IMAGE (\x:real^3. d + x) A)` THEN CONJ_TAC THENL
       [REWRITE_TAC[AFFINE_HULL_TRANSLATION] THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a:real^3` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(affine hull (IMAGE (\x:real^3. d + x) A) INTER affine hull B = {})`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `p:real^3` THEN CONJ_TAC THEN MATCH_MP_TAC HULL_INC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a0:real^3` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\x:real^3. d + x) A`; `B:real^3->bool`]
    MOI_FGP_AFF_DIM_HULLS_UNION) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `affine hull (IMAGE (\x:real^3. d + x) A UNION B) = (:real^3)` THEN
  REWRITE_TAC[GSYM MOI_FGP_AFF_DIM_3_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[AFF_DIM_TRANSLATION_EQ] THEN
  MP_TAC(ISPEC
   `affine hull (IMAGE (\x:real^3. d + x) A) INTER affine hull B`
   AFF_DIM_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_FGB_GENERIC_TRANSLATE = prove
 (`!(s:(real^3->bool)->bool) (t:(real^3->bool)->bool) e.
     FINITE s /\ FINITE t /\ &0 < e
     ==> ?d. norm d < e /\
             !A B. A IN s /\ B IN t ==> affine_gp_3 (IMAGE (\x. d + x) A) B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{D | ?A B. A IN s /\ B IN t /\ ~(D = (:real^3)) /\
              D = {b - a | b IN affine hull B /\ a IN affine hull A}}`;
    `(:real^3)`] MOI_FGP_AVOID_AFFINE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `{(\A:real^3->bool B:real^3->bool.
            {b - a | b IN affine hull B /\ a IN affine hull A}) x y |
         x IN s /\ y IN (\x:real^3->bool. (t:(real^3->bool)->bool)) x}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
      REWRITE_TAC[IN_ELIM_THM; AFFINE_HULL_UNIV; SUBSET_UNIV] THEN
      X_GEN_TAC `D:real^3->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `A:real^3->bool` (X_CHOOSE_THEN
        `B:real^3->bool` STRIP_ASSUME_TAC)) THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC AFFINE_DIFFERENCES THEN
        REWRITE_TAC[AFFINE_AFFINE_HULL];
        UNDISCH_TAC `~(D:real^3->bool = (:real^3))` THEN SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `ball(vec 0:real^3,e)`) THEN
  REWRITE_TAC[AFFINE_HULL_UNIV; SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_BALL;
              BALL_EQ_EMPTY] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real^3` THEN CONJ_TAC THENL
   [UNDISCH_TAC `(d:real^3) IN ball(vec 0,e)` THEN
    REWRITE_TAC[IN_BALL_0];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`A:real^3->bool`; `B:real^3->bool`] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FGB_GP_TRANSLATE THEN
  ASM_CASES_TAC
   `{b - a | b IN affine hull B /\ a IN affine hull (A:real^3->bool)} =
    (:real^3)` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`A:real^3->bool`; `B:real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_FGB_LF_FINITE_NEAR = prove
 (`!(t:(real^N->bool)->bool) w k.
     lf_simplicial_complex t /\
     closed_in (subtopology euclidean w) (UNIONS t) /\
     compact k /\ k SUBSET w
     ==> FINITE {B | B IN t /\ ~(B INTER k = {})}`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `closed_in (subtopology euclidean w) (UNIONS t:real^N->bool)` THEN
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `k INTER C:real^N->bool`]
    MOI_FDN_LF_COMPACT_MEETS_FINITE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_INTER_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `B:real^N->bool` THEN
  ASM_CASES_TAC `(B:real^N->bool) IN t` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(B:real^N->bool) SUBSET UNIONS t` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* C. Locally finite combinatorial 2-manifolds (no finiteness assumed): the *)
(* vertex links are finite complexes homeomorphic to a circle with Euler    *)
(* characteristic 0, every simplex has dimension at most 2 and every edge   *)
(* lies in exactly two triangles.  Same proofs as MOI_FSA_CM_LINK, _DIM,    *)
(* _EDGE2 of pc_moi_fnd_surfa (stated there for finite complexes), with the *)
(* locally finite link lemmas MOI_FM3_* of pc_moi_fnd_m3a.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_CM2_LINK = prove
 (`!c (v:real^N).
        combinatorial_manifold 2 c /\ {v} IN c
        ==> simplicial_complex (simplicial_link c v) /\
            ?k:real^N->bool f:real^N->real^N g. &2 simplex k /\
                    homeomorphism (relative_frontier k,
                                   UNIONS (simplicial_link c v)) (f,g) /\
                    complex_euler (simplicial_link c v) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[combinatorial_manifold] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[pl_sphere] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                        `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier (k:real^N->bool)`;
                 `&1 - (-- &1) pow 2`;
                 `simplicial_link c (v:real^N)`; `f:real^N->real^N`;
                 `g:real^N->real^N`] MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FEU_EULER_SIMPLEX_FRONTIER THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_BOUNDED]];
    DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let MOI_FGB_CM2_DIM = prove
 (`!c s:real^N->bool.
        combinatorial_manifold 2 c /\ s IN c ==> aff_dim s <= &2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_FM3_LF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FGB_CM2_LINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`; `s':real^N->bool`]
    MOI_FSA_LK_DIM) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim(convex hull ((v:real^N) INSERT s')) = aff_dim s' + &1` THEN
  UNDISCH_TAC `s:real^N->bool = convex hull (v INSERT s')` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN INT_ARITH_TAC);;

let MOI_FGB_CM2_EDGE2 = prove
 (`!c e:real^N->bool.
        combinatorial_manifold 2 c /\ e IN c /\ aff_dim e = &1
        ==> CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_FM3_LF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(s':real^N->bool) = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `aff_dim(convex hull ((v:real^N) INSERT s')) = aff_dim s' + &1` THEN
    UNDISCH_TAC `e:real^N->bool = convex hull (v INSERT s')` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?u:real^N. s' = {u}` (X_CHOOSE_THEN `u:real^N` SUBST_ALL_TAC)
  THENL
   [REWRITE_TAC[GSYM SIMPLEX_ZERO] THEN
    SUBGOAL_THEN `aff_dim(s':real^N->bool) simplex s'` MP_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_SIMPLEX THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_MESON_TAC[MOI_FM3_LINK_IN];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `{u:real^N}`;
                 `&1:int`; `&2:int`] MOI_FM3_LINK_CARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `e:real^N->bool = convex hull (v INSERT {u})` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SING_SUBSET] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FGB_CM2_LINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC)))) THEN
  MATCH_MP_TAC MOI_FSA_LK_DEG2 THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                        `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* D. Crossing charts.  pl_crossing_at only depends on the two sets near    *)
(* the point; a global PLH f of real^3 with f x = 0 is a crossing chart for *)
(* the preimages of the first two coordinate planes.  Explicit global PLHs: *)
(* injective linear maps (rows of three independent vectors), translations *)
(* and the folding maps (X,Y,Z) |-> (min X Y,Z,X - Y), (Z,min X Y,X - Y).  *)
(* Models: two transverse planes (MOI_FGB_MODEL_P); a wedge of two half     *)
(* planes and a plane through its edge line transverse to it, both orders   *)
(* (MOI_FGB_MODEL_W).                                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_CROSSING_LOCAL = prove
 (`!s t s' t' (x:real^3) v.
     pl_crossing_at s t x /\ open v /\ x IN v /\
     (!y. y IN v ==> (y IN s <=> y IN s')) /\
     (!y. y IN v ==> (y IN t <=> y IN t'))
     ==> pl_crossing_at s' t' x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_crossing_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
     (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC)))
   STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`u INTER v:real^3->bool`; `f:real^3->real^3`;
                        `g:real^3->real^3`] THEN
  UNDISCH_TAC `pl_homeomorphism (u,IMAGE f u) (f:real^3->real^3,g:real^3->real^3)` THEN
  REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. y IN u ==> (g:real^3->real^3)((f:real^3->real^3) y) = y`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (f:real^3->real^3) (u INTER v))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `u:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN
    ASM_SIMP_TAC[OPEN_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `IMAGE (f:real^3->real^3) u`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN SET_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_SIMP_TAC[INTER_SUBSET; LOCALLY_POLYHEDRAL_OPEN; OPEN_INTER];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN] THEN SET_TAC[];
    UNDISCH_TAC
     `IMAGE (f:real^3->real^3) (s INTER u) =
      IMAGE f u INTER {y:real^3 | y$1 = &0}` THEN
    UNDISCH_TAC `!y:real^3. y IN v ==> (y IN s <=> y IN s')` THEN
    UNDISCH_TAC `!y:real^3. y IN u ==> (g:real^3->real^3)((f:real^3->real^3) y) = y` THEN
    SET_TAC[];
    UNDISCH_TAC
     `IMAGE (f:real^3->real^3) (t INTER u) =
      IMAGE f u INTER {y:real^3 | y$2 = &0}` THEN
    UNDISCH_TAC `!y:real^3. y IN v ==> (y IN t <=> y IN t')` THEN
    UNDISCH_TAC `!y:real^3. y IN u ==> (g:real^3->real^3)((f:real^3->real^3) y) = y` THEN
    SET_TAC[]]);;

let MOI_FGB_CROSSING_GLOBAL = prove
 (`!(f:real^3->real^3) g x.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ f x = vec 0
     ==> pl_crossing_at {y | (f y)$1 = &0} {y | (f y)$2 = &0} x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_crossing_at] THEN
  MAP_EVERY EXISTS_TAC [`(:real^3)`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (:real^3) = (:real^3)` ASSUME_TAC
  THENL [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. f((g:real^3->real^3) y) = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism; IN_UNIV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; INTER_UNIV] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  CONJ_TAC THEN X_GEN_TAC `z:real^3` THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `(g:real^3->real^3) z` THEN
  ASM_REWRITE_TAC[]);;

let MOI_FGB_LINEAR_PLH_UNIV = prove
 (`!f:real^N->real^N.
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> ?g. linear g /\ (!x. g(f x) = x) /\ (!y. f(g y) = y) /\
             pl_homeomorphism ((:real^N),(:real^N)) (f,g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^N->real^N) o g = I` ASSUME_TAC THENL
   [ASM_MESON_TAC[LINEAR_INVERSE_LEFT]; ALL_TAC] THEN
  EXISTS_TAC `g:real^N->real^N` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism; IN_UNIV] THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`(:real^N)`; `f:real^N->real^N`; `vec 0:real^N`]
      PL_MAP_ON_AFFINE) THEN
    ASM_SIMP_TAC[VECTOR_ADD_RID; ETA_AX; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]]);;

let MOI_FGB_ROWS_INJ = prove
 (`!n m w:real^3.
     (!a b c. a % n + b % m + c % w = vec 0 ==> a = &0 /\ b = &0 /\ c = &0)
     ==> !z. n dot z = &0 /\ m dot z = &0 /\ w dot z = &0 ==> z = vec 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `M = (vector[n;m;w]:real^3^3)` THEN
  SUBGOAL_THEN `~(det(transp(M:real^3^3)) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~(x:real^3 = vec 0)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(x:real^3)$1`; `(x:real^3)$2`;
                                  `(x:real^3)$3`]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `transp(M:real^3^3) ** x = vec 0` THEN
      EXPAND_TAC "M" THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MATRIX_VECTOR_MUL_COMPONENT;
               DOT_3; TRANSP_COMPONENT; VECTOR_3; VEC_COMPONENT;
               VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; ARITH] THEN
      SIMP_TAC[REAL_MUL_SYM];
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT]];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `M:real^3^3` HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DET_TRANSP]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
  REWRITE_TAC[TAUT `~(~p /\ q) <=> q ==> p`] THEN DISCH_THEN MATCH_MP_TAC THEN
  EXPAND_TAC "M" THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MATRIX_VECTOR_MUL_COMPONENT;
           VECTOR_3; VEC_COMPONENT; ARITH] THEN
  ASM_REWRITE_TAC[]);;

let MOI_FGB_ROWS_PLH = prove
 (`!n m w:real^3.
     (!a b c. a % n + b % m + c % w = vec 0 ==> a = &0 /\ b = &0 /\ c = &0)
     ==> ?g. pl_homeomorphism ((:real^3),(:real^3))
               ((\z. vector[n dot z; m dot z; w dot z]:real^3),g) /\
             linear (\z. vector[n dot z; m dot z; w dot z]:real^3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear (\z:real^3. vector[(n:real^3) dot z; (m:real^3) dot z;
                                          (w:real^3) dot z]:real^3)`
  ASSUME_TAC THENL
   [REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                DOT_RADD; DOT_RMUL];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\z:real^3. vector[(n:real^3) dot z; (m:real^3) dot z;
                                   (w:real^3) dot z]:real^3`
    MOI_FGB_LINEAR_PLH_UNIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3]) THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    MP_TAC(ISPECL [`n:real^3`; `m:real^3`; `w:real^3`] MOI_FGB_ROWS_INJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[DOT_RSUB; REAL_SUB_REFL];
    DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g:real^3->real^3` THEN ASM_REWRITE_TAC[]]);;

let MOI_FGB_THIRD_VECTOR = prove
 (`!n m:real^3.
     (!a b. a % n + b % m = vec 0 ==> a = &0 /\ b = &0)
     ==> ?w. !a b c. a % n + b % m + c % w = vec 0
                     ==> a = &0 /\ b = &0 /\ c = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `span {n:real^3,m}` ORTHOGONAL_TO_SUBSPACE_EXISTS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIM_SPAN; DIMINDEX_3] THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `CARD {n:real^3,m}` THEN
    SIMP_TAC[DIM_LE_CARD; FINITE_INSERT; FINITE_EMPTY] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[NOT_IN_EMPTY] THEN COND_CASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^3` THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `w dot (n:real^3) = &0 /\ w dot (m:real^3) = &0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM orthogonal] THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC SPAN_SUPERSET THEN
    REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `c = &0` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. w dot v`) THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RZERO; REAL_MUL_RZERO;
                    REAL_ADD_LID] THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; DOT_EQ_0];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `a % n + b % m + &0 % w:real^3 = vec 0` THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID]);;

let MOI_FGB_TRANSLATE_PLH = prove
 (`!a:real^N. pl_homeomorphism ((:real^N),(:real^N)) ((\z. z - a),(\z. z + a))`,
  GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism; IN_UNIV] THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID;
             CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
    REPEAT CONJ_TAC THEN TRY (GEN_TAC THEN VECTOR_ARITH_TAC) THEN
    X_GEN_TAC `y:real^N` THENL
     [EXISTS_TAC `y + a:real^N`; EXISTS_TAC `y - a:real^N`] THEN
    VECTOR_ARITH_TAC;
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^N. (\z. z) z + --(a:real^N)` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIV] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
      SIMP_TAC[LINEAR_ID; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]]]);;

let MOI_FGB_PL_SCALE_VECTOR = prove
 (`!s (a:real^N->real) (v:real^M).
     pl_map_on s (\x. lift(a x)) ==> pl_map_on s (\x. a x % v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^N. a x % (v:real^M)) = (\u:real^1. drop u % v) o (\x. lift(a x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^1)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\u:real^1. drop u % (v:real^M)`;
                 `vec 0:real^M`] PL_MAP_ON_AFFINE) THEN
  REWRITE_TAC[VECTOR_ADD_RID; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
  MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID]);;

let MOI_FGB_PL_VECTOR3 = prove
 (`!s (a:real^N->real) b c.
     pl_map_on s (\x. lift(a x)) /\ pl_map_on s (\x. lift(b x)) /\
     pl_map_on s (\x. lift(c x))
     ==> pl_map_on s (\x. vector[a x; b x; c x]:real^3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^N. vector[a x; b x; c x]:real^3) =
    (\x. a x % (basis 1:real^3) + b x % basis 2 + c x % basis 3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC PL_MAP_ON_ADD THEN CONJ_TAC) THEN
  MATCH_MP_TAC MOI_FGB_PL_SCALE_VECTOR THEN ASM_REWRITE_TAC[]);;

let MOI_FGB_PL_LIFT_AFFINE = prove
 (`!(a:real^N) b. pl_map_on (:real^N) (\x. lift(a dot x + b))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. lift(a dot x)`; `lift b`]
    PL_MAP_ON_AFFINE) THEN
  SIMP_TAC[LINEAR_LIFT_DOT; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV; LIFT_ADD]);;

let MOI_FGB_PL_COORDS = prove
 (`(!i. 1 <= i /\ i <= 3 ==> pl_map_on (:real^3) (\x:real^3. lift(x$i))) /\
   pl_map_on (:real^3) (\x:real^3. lift(x$1 - x$2)) /\
   pl_map_on (:real^3) (\x:real^3. lift(min (x$1) (x$2))) /\
   (!i. 1 <= i /\ i <= 3
        ==> pl_map_on (:real^3) (\x:real^3. lift(x$i + max (x$3) (&0))) /\
            pl_map_on (:real^3) (\x:real^3. lift(x$i - min (x$3) (&0))))`,
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 3 ==> pl_map_on (:real^3) (\x:real^3. lift(x$i))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^3. lift((basis i:real^3) dot x + &0)` THEN
    REWRITE_TAC[MOI_FGB_PL_LIFT_AFFINE; IN_UNIV; REAL_ADD_RID] THEN
    ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^3. lift((basis 1 - basis 2:real^3) dot x + &0)` THEN
    REWRITE_TAC[MOI_FGB_PL_LIFT_AFFINE; IN_UNIV; REAL_ADD_RID; DOT_LSUB] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH];
    MATCH_MP_TAC MOI_PTR_PL_LIFT_MIN THEN ASM_SIMP_TAC[ARITH];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC PL_MAP_ON_EQ THENL
     [EXISTS_TAC `\x:real^3. lift(max ((basis i + basis 3:real^3) dot x + &0)
                                     ((basis i:real^3) dot x + &0))`;
      EXISTS_TAC `\x:real^3. lift(max ((basis i - basis 3:real^3) dot x + &0)
                                     ((basis i:real^3) dot x + &0))`] THEN
    SIMP_TAC[MOI_PTR_PL_LIFT_MAX; MOI_FGB_PL_LIFT_AFFINE] THEN
    ASM_SIMP_TAC[IN_UNIV; REAL_ADD_RID; DOT_LADD; DOT_LSUB; DOT_BASIS;
                 DIMINDEX_3; ARITH; LIFT_EQ] THEN
    REAL_ARITH_TAC]);;

let MOI_FGB_FOLD1_PLH = prove
 (`pl_homeomorphism ((:real^3),(:real^3))
     ((\p:real^3. vector[min (p$1) (p$2); p$3; p$1 - p$2]:real^3),
      (\q:real^3. vector[q$1 + max (q$3) (&0); q$1 - min (q$3) (&0);
                         q$2]:real^3))`,
  SUBGOAL_THEN
   `pl_map_on (:real^3)
      (\p:real^3. vector[min (p$1) (p$2); p$3; p$1 - p$2]:real^3) /\
    pl_map_on (:real^3)
      (\q:real^3. vector[q$1 + max (q$3) (&0); q$1 - min (q$3) (&0);
                         q$2]:real^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FGB_PL_VECTOR3 THEN
    SIMP_TAC[MOI_FGB_PL_COORDS; ARITH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN
    EXISTS_TAC `vector[(y:real^3)$1 + max (y$3) (&0); y$1 - min (y$3) (&0);
                       y$2]:real^3` THEN
    SIMP_TAC[VECTOR_3] THEN REAL_ARITH_TAC;
    GEN_TAC THEN REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN
    EXISTS_TAC `vector[min ((y:real^3)$1) (y$2); y$3; y$1 - y$2]:real^3` THEN
    SIMP_TAC[VECTOR_3] THEN REAL_ARITH_TAC]);;

let MOI_FGB_FOLD2_PLH = prove
 (`pl_homeomorphism ((:real^3),(:real^3))
     ((\p:real^3. vector[p$3; min (p$1) (p$2); p$1 - p$2]:real^3),
      (\q:real^3. vector[q$2 + max (q$3) (&0); q$2 - min (q$3) (&0);
                         q$1]:real^3))`,
  SUBGOAL_THEN
   `pl_map_on (:real^3)
      (\p:real^3. vector[p$3; min (p$1) (p$2); p$1 - p$2]:real^3) /\
    pl_map_on (:real^3)
      (\q:real^3. vector[q$2 + max (q$3) (&0); q$2 - min (q$3) (&0);
                         q$1]:real^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FGB_PL_VECTOR3 THEN
    SIMP_TAC[MOI_FGB_PL_COORDS; ARITH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN
    EXISTS_TAC `vector[(y:real^3)$2 + max (y$3) (&0); y$2 - min (y$3) (&0);
                       y$1]:real^3` THEN
    SIMP_TAC[VECTOR_3] THEN REAL_ARITH_TAC;
    GEN_TAC THEN REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN
    EXISTS_TAC `vector[(y:real^3)$3; min (y$1) (y$2); y$1 - y$2]:real^3` THEN
    SIMP_TAC[VECTOR_3] THEN REAL_ARITH_TAC]);;

let MOI_FGB_MODEL_P = prove
 (`!(x:real^3) n m.
     (!a b. a % n + b % m = vec 0 ==> a = &0 /\ b = &0)
     ==> pl_crossing_at {z | n dot (z - x) = &0} {z | m dot (z - x) = &0} x`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `w:real^3` o MATCH_MP MOI_FGB_THIRD_VECTOR) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MOI_FGB_ROWS_PLH) THEN
  MP_TAC(ISPECL
   [`(\z:real^3. vector[(n:real^3) dot z; (m:real^3) dot z;
                        (w:real^3) dot z]:real^3) o (\z:real^3. z - x)`;
    `(\z:real^3. z + x) o (g:real^3->real^3)`; `x:real^3`]
   MOI_FGB_CROSSING_GLOBAL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[MOI_FGB_TRANSLATE_PLH];
      REWRITE_TAC[o_THM; VECTOR_SUB_REFL; DOT_RZERO] THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT]];
    REWRITE_TAC[o_THM; VECTOR_3] THEN DISCH_THEN MATCH_ACCEPT_TAC]);;

let MOI_FGB_MODEL_W = prove
 (`!(x:real^3) n1 n2 m.
     (!a b c. a % n1 + b % n2 + c % m = vec 0 ==> a = &0 /\ b = &0 /\ c = &0)
     ==> pl_crossing_at
           {z | n1 dot (z - x) = &0 /\ &0 <= n2 dot (z - x) \/
                n2 dot (z - x) = &0 /\ &0 <= n1 dot (z - x)}
           {z | m dot (z - x) = &0} x /\
         pl_crossing_at
           {z | m dot (z - x) = &0}
           {z | n1 dot (z - x) = &0 /\ &0 <= n2 dot (z - x) \/
                n2 dot (z - x) = &0 /\ &0 <= n1 dot (z - x)} x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!a b c. a % n2 + b % n1 + c % (m:real^3) = vec 0
            ==> a = &0 /\ b = &0 /\ c = &0`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`b:real`; `a:real`; `c:real`]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `a % n2 + b % n1 + c % m:real^3 = vec 0` THEN
      VECTOR_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MOI_FGB_ROWS_PLH) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`(\p:real^3. vector[min (p$1) (p$2); p$3; p$1 - p$2]:real^3) o
       (\z:real^3. vector[(n2:real^3) dot z; (n1:real^3) dot z;
                          (m:real^3) dot z]:real^3) o (\z:real^3. z - x)`;
      `((\z:real^3. z + x) o (g:real^3->real^3)) o
       (\q:real^3. vector[q$1 + max (q$3) (&0); q$1 - min (q$3) (&0);
                          q$2]:real^3)`; `x:real^3`]
     MOI_FGB_CROSSING_GLOBAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
        REWRITE_TAC[MOI_FGB_FOLD1_PLH] THEN
        MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[MOI_FGB_TRANSLATE_PLH];
        REWRITE_TAC[o_THM; VECTOR_SUB_REFL; DOT_RZERO] THEN
        SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN
        REAL_ARITH_TAC];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM; VECTOR_3] THEN
      GEN_TAC THEN REAL_ARITH_TAC];
    MP_TAC(ISPECL
     [`(\p:real^3. vector[p$3; min (p$1) (p$2); p$1 - p$2]:real^3) o
       (\z:real^3. vector[(n2:real^3) dot z; (n1:real^3) dot z;
                          (m:real^3) dot z]:real^3) o (\z:real^3. z - x)`;
      `((\z:real^3. z + x) o (g:real^3->real^3)) o
       (\q:real^3. vector[q$2 + max (q$3) (&0); q$2 - min (q$3) (&0);
                          q$1]:real^3)`; `x:real^3`]
     MOI_FGB_CROSSING_GLOBAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
        REWRITE_TAC[MOI_FGB_FOLD2_PLH] THEN
        MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[MOI_FGB_TRANSLATE_PLH];
        REWRITE_TAC[o_THM; VECTOR_SUB_REFL; DOT_RZERO] THEN
        SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN
        REAL_ARITH_TAC];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM; VECTOR_3] THEN
      GEN_TAC THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* E. Local form of a triangle near a relative interior point of an edge:  *)
(* a half plane, cut out of the affine hull by any functional v vanishing  *)
(* on the edge direction and positive on the third vertex.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_COEF_BOUND = prove
 (`!(e:real^3) w v.
     ~(e = vec 0) /\ v dot e = &0 /\ ~(v dot w = &0)
     ==> ?K. &0 < K /\ !l g. abs l + abs g <= K * norm(l % e + g % w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x:real^2. x$1 % (e:real^3) + x$2 % w`
    LINEAR_INJECTIVE_BOUNDED_BELOW_POS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REPEAT GEN_TAC THEN VECTOR_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN REWRITE_TAC[] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^2)$2 = (y:real^2)$2` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o AP_TERM `\z:real^3. (v:real^3) dot z`) THEN
        ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_LID] THEN
        ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^2)$1 = (y:real^2)$1` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^2)$1 % (e:real^3) + x$2 % w = (y:real^2)$1 % e + y$2 % w` THEN
        ASM_REWRITE_TAC[VECTOR_ARITH
         `a % e + b % w = c % e + b % w <=> (a - c) % e = vec 0:real^3`] THEN
        ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_SUB_0];
        ASM_SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&2 / B` THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  MAP_EVERY X_GEN_TAC [`l:real`; `g:real`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `vector[l; g]:real^2`) THEN
  REWRITE_TAC[VECTOR_2] THEN
  MP_TAC(ISPECL [`vector[l; g]:real^2`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`vector[l; g]:real^2`; `2`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[VECTOR_2] THEN
  ABBREV_TAC `n2 = norm(vector[l; g]:real^2)` THEN
  ABBREV_TAC `nn = norm(l % e + g % w:real^3)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `n2 <= nn / B` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * n2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_REWRITE_TAC[]);;

let MOI_FGB_HALF_PLANE = prove
 (`!(p:real^3) q a v u.
     ~(p = q) /\ &0 < u /\ u < &1 /\
     v dot (q - p) = &0 /\ &0 < v dot (a - ((&1 - u) % p + u % q))
     ==> ?r. &0 < r /\
             !z. dist((&1 - u) % p + u % q,z) < r
                 ==> (z IN convex hull {p,q,a} <=>
                      z IN affine hull {p,q,a} /\
                      &0 <= v dot (z - ((&1 - u) % p + u % q)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`q - p:real^3`; `a - ((&1 - u) % p + u % q):real^3`;
                 `v:real^3`] MOI_FGB_COEF_BOUND) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "cb"))) THEN
  SUBGOAL_THEN
   `!al be ga. al + be + ga = &1
               ==> (al % p + be % q + ga % a) - ((&1 - u) % p + u % q) =
                   (be - u * (&1 - ga)) % (q - p) +
                   ga % (a - ((&1 - u) % p + u % q:real^3))`
  (LABEL_TAC "dec") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `al = &1 - be - ga` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min u (&1 - u) / (&4 * K)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `al:real` (X_CHOOSE_THEN `be:real`
      (X_CHOOSE_THEN `ga:real` STRIP_ASSUME_TAC))) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`al:real`; `be:real`; `ga:real`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      USE_THEN "dec" (fun th -> ASM_SIMP_TAC[th]) THEN
      ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `K * norm(z - ((&1 - u) % p + u % q:real^3)) < min u (&1 - u) / &4`
  MP_TAC THENL
   [UNDISCH_TAC
     `dist((&1 - u) % p + u % q:real^3,z) < min u (&1 - u) / (&4 * K)` THEN
    REWRITE_TAC[dist] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [NORM_SUB] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < K ==> &0 < &4 * K`;
                 REAL_ARITH `&0 < &4`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `al:real` (X_CHOOSE_THEN `be:real`
      (X_CHOOSE_THEN `ga:real` (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "zdef"))))) ASSUME_TAC) THEN
  SUBGOAL_THEN
   `z - ((&1 - u) % p + u % q) =
    (be - u * (&1 - ga)) % (q - p) + ga % (a - ((&1 - u) % p + u % q:real^3))`
  (LABEL_TAC "zy") THENL
   [USE_THEN "zdef" SUBST1_TAC THEN USE_THEN "dec" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ga` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 <= v dot (z - ((&1 - u) % p + u % q:real^3))` THEN
    USE_THEN "zy" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
    EXISTS_TAC `v dot (a - ((&1 - u) % p + u % q:real^3))` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  USE_THEN "cb" (MP_TAC o SPECL [`be - u * (&1 - ga)`; `ga:real`]) THEN
  USE_THEN "zy" (fun th -> REWRITE_TAC[GSYM th]) THEN DISCH_TAC THEN
  SUBGOAL_THEN `u * ga <= ga /\ (&1 - u) * ga <= ga` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - x) * g ==> x * g <= g`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "zdef" SUBST1_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`al:real`; `be:real`; `ga:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `al = (&1 - u) - (&1 - u) * ga - (be - u * (&1 - ga))`
  SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `be = (be - u * (&1 - ga)) + u - u * ga` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* F. Local forms of a locally finite combinatorial 2-manifold c in real^3. *)
(* An edge A has exactly two triangles conv{p,q,a1}, conv{p,q,a2} meeting   *)
(* in A (MOI_FGB_EDGE_DATA).  Near a relative interior point y of a         *)
(* triangle, UNIONS c is its plane (MOI_FGB_TRI_FORM); near a relative      *)
(* interior point of an edge with direction e it is a plane containing the  *)
(* edge line or a wedge of two half planes along it (MOI_FGB_EDGE_FORM).    *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_EDGE_DATA2 = prove
 (`!c (A:real^N->bool).
     lf_simplicial_complex c /\ A IN c /\ aff_dim A = &1 /\
     CARD {tr | tr IN c /\ aff_dim tr = &2 /\ A SUBSET tr} = 2
     ==> ?p q a1 a2.
           ~(p = q) /\ A = convex hull {p,q} /\
           convex hull {p,q,a1} IN c /\ convex hull {p,q,a2} IN c /\
           ~(a1 = a2) /\ ~(a1 = p) /\ ~(a1 = q) /\ ~(a2 = p) /\ ~(a2 = q) /\
           ~affine_dependent {p,q,a1} /\ ~affine_dependent {p,q,a2} /\
           convex hull {p,q,a1} INTER convex hull {p,q,a2} =
           convex hull {p,q} /\
           (!tr. tr IN c /\ aff_dim tr = &2 /\ A SUBSET tr
                ==> tr = convex hull {p,q,a1} \/ tr = convex hull {p,q,a2})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(A:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(A:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `A:real^N->bool`]
    MOI_FM3_LF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_CSTAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `L = moi_fm3_cstar c (v:real^N)` THEN
  SUBGOAL_THEN `(A:real^N->bool) IN (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `A:real^N->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `{tr | tr IN (c:(real^N->bool)->bool) /\ aff_dim tr = &2 /\ A SUBSET tr} HAS_SIZE 2`
  MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{tr | tr IN (c:(real^N->bool)->bool) /\ (v:real^N) IN tr}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FM3_STAR_FINITE THEN
        REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[]];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real^N->bool` (X_CHOOSE_THEN `T2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!tr:real^N->bool. tr IN (c:(real^N->bool)->bool) /\ aff_dim tr = &2 /\ A SUBSET tr <=> tr = T1 \/ tr = T2`
  (LABEL_TAC "tri") THENL
   [UNDISCH_TAC
     `{tr | tr IN (c:(real^N->bool)->bool) /\ aff_dim tr = &2 /\ A SUBSET tr} = {T1:real^N->bool, T2}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(T1:real^N->bool) IN (c:(real^N->bool)->bool) /\ aff_dim T1 = &2 /\
    (A:real^N->bool) SUBSET T1 /\
    (T2:real^N->bool) IN c /\ aff_dim T2 = &2 /\ A SUBSET T2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(T1:real^N->bool) IN (L:(real^N->bool)->bool) /\ T2 IN L`
  STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `p:real^N`; `q:real^N`;
                 `T1:real^N->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `p:real^N`; `q:real^N`;
                 `T2:real^N->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a2:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(a1:real^N = a2)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(T1:real^N->bool = T2)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`; `a1:real^N`; `a2:real^N`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `{p:real^N,q,a1}`;
                   `{p:real^N,q,a2}`] MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    X_GEN_TAC `tr:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "tri" (MP_TAC o SPEC `tr:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let MOI_FGB_EDGE_DATA = prove
 (`!c (A:real^N->bool).
     combinatorial_manifold 2 c /\ A IN c /\ aff_dim A = &1
     ==> ?p q a1 a2.
           ~(p = q) /\ A = convex hull {p,q} /\
           convex hull {p,q,a1} IN c /\ convex hull {p,q,a2} IN c /\
           ~(a1 = a2) /\ ~(a1 = p) /\ ~(a1 = q) /\ ~(a2 = p) /\ ~(a2 = q) /\
           ~affine_dependent {p,q,a1} /\ ~affine_dependent {p,q,a2} /\
           convex hull {p,q,a1} INTER convex hull {p,q,a2} =
           convex hull {p,q} /\
           (!tr. tr IN c /\ aff_dim tr = &2 /\ A SUBSET tr
                ==> tr = convex hull {p,q,a1} \/ tr = convex hull {p,q,a2})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FGB_EDGE_DATA2 THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold];
    MATCH_MP_TAC MOI_FGB_CM2_EDGE2 THEN ASM_REWRITE_TAC[]]);;

let MOI_FGB_PLANE_NORMAL = prove
 (`!(s:real^3->bool) y.
     aff_dim s = &2 /\ y IN affine hull s
     ==> ?n. ~(n = vec 0) /\ !z. z IN affine hull s <=> n dot (z - y) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` AFF_DIM_EQ_HYPERPLANE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC INT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^3` (X_CHOOSE_THEN `b:real`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `n:real^3` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(y:real^3) IN affine hull s` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; DOT_RSUB] THEN REAL_ARITH_TAC);;

let MOI_FGB_TRI_FORM = prove
 (`!c (A:real^3->bool) y.
     combinatorial_manifold 2 c /\ A IN c /\ aff_dim A = &2 /\
     y IN relative_interior A
     ==> ?r n. &0 < r /\ ~(n = vec 0) /\
               (!z. z IN affine hull A ==> n dot (z - y) = &0) /\
               !z. dist(y,z) < r ==> (z IN UNIONS c <=> n dot (z - y) = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN A` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^3->bool`; `y:real^3`] MOI_FGB_PLANE_NORMAL) THEN
  ASM_SIMP_TAC[HULL_INC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "aff"))) THEN
  SUBGOAL_THEN
   `?r1. &0 < r1 /\ ball(y:real^3,r1) INTER affine hull A SUBSET A`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_RELATIVE_INTERIOR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `y:real^3`] MOI_CMB_STAR_NBHD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "star"))) THEN
  MAP_EVERY EXISTS_TAC [`min r0 r1`; `n:real^3`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "star" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(A:real^3->bool) SUBSET S` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `y:real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(S:real^3->bool) = &2` ASSUME_TAC THENL
     [MATCH_MP_TAC(INT_ARITH `!a:int b. a <= b /\ b <= &2 /\ a = &2 ==> b = &2`) THEN
      EXISTS_TAC `aff_dim(A:real^3->bool)` THEN
      ASM_SIMP_TAC[AFF_DIM_SUBSET] THEN ASM_MESON_TAC[MOI_FGB_CM2_DIM];
      ALL_TAC] THEN
    SUBGOAL_THEN `S:real^3->bool = A` SUBST_ALL_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
      USE_THEN "aff" (fun th -> REWRITE_TAC[GSYM th]) THEN
      MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]];
    DISCH_TAC THEN REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `A:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(y:real^3,r1) INTER affine hull A SUBSET A` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "aff" (fun th -> ASM_REWRITE_TAC[th])]);;

let MOI_FGB_CARD3 = prove
 (`!p q a:real^N. ~(p = q) /\ ~(a = p) /\ ~(a = q) ==> CARD {p,q,a} = 3`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC);;

let MOI_FGB_SAME_PLANE = prove
 (`!p q a1 a2:real^N.
     ~(p = q) /\ ~(a1 = p) /\ ~(a1 = q) /\ ~(a2 = p) /\ ~(a2 = q) /\
     ~affine_dependent {p,q,a1} /\ ~affine_dependent {p,q,a2} /\
     a2 IN affine hull {p,q,a1}
     ==> affine hull {p,q,a2} = affine hull {p,q,a1}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{p:real^N,q,a2}`; `affine hull {p:real^N,q,a1}`]
    AFF_DIM_EQ_AFFINE_HULL) THEN
  REWRITE_TAC[HULL_HULL; AFF_DIM_AFFINE_HULL] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[HULL_INC; IN_INSERT];
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; MOI_FGB_CARD3] THEN
    INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* G. Two triangles conv{p,q,a1}, conv{p,q,a2} meeting in the edge [p,q],  *)
(* near a point y of the open edge: a wedge of two half planes when they   *)
(* are not coplanar (MOI_FGB_WEDGE_CASE), their common plane otherwise     *)
(* (MOI_FGB_COPLANAR_CASE; here the meeting condition forces a1 and a2 to  *)
(* opposite sides of the edge line).                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_EDGE_POINT_IN_HULL = prove
 (`!p q a u:real. ((&1 - u) % p + u % q:real^N) IN affine hull {p,q,a}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`&1 - u`; `u:real`; `&0`] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN REAL_ARITH_TAC);;

let MOI_FGB_TRI_PLANE = prove
 (`!(p:real^3) q a u.
     ~(p = q) /\ ~(a = p) /\ ~(a = q) /\ ~affine_dependent {p,q,a}
     ==> ?n. ~(n = vec 0) /\ n dot (q - p) = &0 /\
             !z. z IN affine hull {p,q,a} <=>
                 n dot (z - ((&1 - u) % p + u % q)) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{p:real^3,q,a}`; `(&1 - u) % p + u % q:real^3`]
    MOI_FGB_PLANE_NORMAL) THEN
  ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; MOI_FGB_CARD3;
               MOI_FGB_EDGE_POINT_IN_HULL] THEN
  ANTS_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `n:real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(p:real^3) IN affine hull {p,q,a} /\ q IN affine hull {p,q,a}`
  MP_TAC THENL [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[DOT_RSUB] THEN REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
  CONV_TAC REAL_RING);;

let MOI_FGB_WEDGE_CASE = prove
 (`!(p:real^3) q a1 a2 u.
     ~(p = q) /\ ~(a1 = p) /\ ~(a1 = q) /\ ~(a2 = p) /\ ~(a2 = q) /\
     ~affine_dependent {p,q,a1} /\ ~affine_dependent {p,q,a2} /\
     &0 < u /\ u < &1 /\ ~(a2 IN affine hull {p,q,a1})
     ==> ?r n1 n2.
           &0 < r /\ n1 dot (q - p) = &0 /\ n2 dot (q - p) = &0 /\
           (!a b. a % n1 + b % n2 = vec 0 ==> a = &0 /\ b = &0) /\
           !z. dist((&1 - u) % p + u % q,z) < r
               ==> (z IN convex hull {p,q,a1} \/ z IN convex hull {p,q,a2} <=>
                    n1 dot (z - ((&1 - u) % p + u % q)) = &0 /\
                    &0 <= n2 dot (z - ((&1 - u) % p + u % q)) \/
                    n2 dot (z - ((&1 - u) % p + u % q)) = &0 /\
                    &0 <= n1 dot (z - ((&1 - u) % p + u % q)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a1:real^3`; `u:real`]
    MOI_FGB_TRI_PLANE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h1")))) THEN
  MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a2:real^3`; `u:real`]
    MOI_FGB_TRI_PLANE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h2")))) THEN
  SUBGOAL_THEN `~((n1:real^3) dot (a2 - ((&1 - u) % p + u % q)) = &0)`
  ASSUME_TAC THENL
   [USE_THEN "h1" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((n2:real^3) dot (a1 - ((&1 - u) % p + u % q)) = &0)`
  ASSUME_TAC THENL
   [USE_THEN "h2" (fun th -> REWRITE_TAC[GSYM th]) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a2:real^3`; `a1:real^3`]
      MOI_FGB_SAME_PLANE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((a2:real^3) IN affine hull {p,q,a1})` THEN
    UNDISCH_TAC `affine hull {p,q,a1} = affine hull {p:real^3,q,a2}` THEN
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC[HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(n2:real^3) dot (a2 - ((&1 - u) % p + u % q)) = &0`
  ASSUME_TAC THENL
   [USE_THEN "h2" (fun th -> REWRITE_TAC[GSYM th]) THEN
    SIMP_TAC[HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  ABBREV_TAC `c1 = (n1:real^3) dot (a2 - ((&1 - u) % p + u % q))` THEN
  ABBREV_TAC `c2 = (n2:real^3) dot (a1 - ((&1 - u) % p + u % q))` THEN
  MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a1:real^3`; `c2 % n2:real^3`;
                 `u:real`] MOI_FGB_HALF_PLANE) THEN
  ASM_REWRITE_TAC[DOT_LMUL; REAL_MUL_RZERO; REAL_LT_SQUARE] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "hp1"))) THEN
  MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a2:real^3`; `c1 % n1:real^3`;
                 `u:real`] MOI_FGB_HALF_PLANE) THEN
  ASM_REWRITE_TAC[DOT_LMUL; REAL_MUL_RZERO; REAL_LT_SQUARE] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "hp2"))) THEN
  MAP_EVERY EXISTS_TAC [`min r1 r2`; `c1 % n1:real^3`; `c2 % n2:real^3`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; DOT_LMUL; REAL_MUL_RZERO] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `a = &0` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM
        `\v:real^3. v dot (a2 - ((&1 - u) % p + u % q))`) THEN
      REWRITE_TAC[DOT_LADD; DOT_LMUL; DOT_LZERO] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_ENTIRE] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 % c1 % n1 + b % c2 % n2:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_MUL_EQ_0];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  USE_THEN "hp1" (MP_TAC o SPEC `z:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "hp2" (MP_TAC o SPEC `z:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "h1" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "h2" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[REAL_ENTIRE] THEN
  ASM_CASES_TAC `(n1:real^3) dot (z - ((&1 - u) % p + u % q)) = &0` THEN
  ASM_CASES_TAC `(n2:real^3) dot (z - ((&1 - u) % p + u % q)) = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]);;

let MOI_FGB_OFF_LINE = prove
 (`!p q a:real^N.
     ~(p = q) /\ ~(a = p) /\ ~(a = q) /\ ~affine_dependent {p,q,a}
     ==> ~(a IN affine hull {p,q})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `a:real^N`] COLLINEAR_3_AFFINE_HULL) THEN
  ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN ASM_MESON_TAC[]);;

let MOI_FGB_LINE_PT = prove
 (`!p q:real^N u k. (&1 - u) % p + u % q + k % (q - p) IN affine hull {p,q}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`&1 - u - k`; `u + k`] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let MOI_FGB_SMALL_STEP = prove
 (`!r N. &0 < r /\ &0 <= N
         ==> &0 < min (&1 / &2) (r / (&2 * (N + &1))) /\
             min (&1 / &2) (r / (&2 * (N + &1))) <= &1 /\
             min (&1 / &2) (r / (&2 * (N + &1))) * N < r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * (N + &1)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r / (&2 * (N + &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `r / (&2 * (N + &1)) * N` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `r / (&2 * (N + &1)) * N = r * (N / (&2 * (N + &1)))`
  SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let MOI_FGB_COPLANAR_CASE = prove
 (`!(p:real^3) q a1 a2 u.
     ~(p = q) /\ ~(a1 = p) /\ ~(a1 = q) /\ ~(a2 = p) /\ ~(a2 = q) /\
     ~affine_dependent {p,q,a1} /\ ~affine_dependent {p,q,a2} /\
     convex hull {p,q,a1} INTER convex hull {p,q,a2} = convex hull {p,q} /\
     &0 < u /\ u < &1 /\ a2 IN affine hull {p,q,a1}
     ==> ?r n. &0 < r /\ ~(n = vec 0) /\ n dot (q - p) = &0 /\
               !z. dist((&1 - u) % p + u % q,z) < r
                   ==> (z IN convex hull {p,q,a1} \/
                        z IN convex hull {p,q,a2} <=>
                        n dot (z - ((&1 - u) % p + u % q)) = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a1:real^3`; `u:real`]
    MOI_FGB_TRI_PLANE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h1")))) THEN
  SUBGOAL_THEN `affine hull {p,q,a2} = affine hull {p:real^3,q,a1}`
  (LABEL_TAC "same") THENL
   [MATCH_MP_TAC MOI_FGB_SAME_PLANE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((q - p:real^3) dot (q - p) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ABBREV_TAC `y:real^3 = (&1 - u) % p + u % q` THEN
  ABBREV_TAC `k = ((a1 - y) dot (q - p)) / ((q - p:real^3) dot (q - p))` THEN
  ABBREV_TAC `m:real^3 = (a1 - y) - k % (q - p)` THEN
  SUBGOAL_THEN `(m:real^3) dot (q - p) = &0` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN GEN_REWRITE_TAC LAND_CONV [DOT_LSUB] THEN
    REWRITE_TAC[DOT_LMUL] THEN EXPAND_TAC "k" THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_SUB_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `a1 - y:real^3 = m + k % (q - p)` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(m:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a1:real^3`] MOI_FGB_OFF_LINE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a1:real^3 = (&1 - u) % p + u % q + k % (q - p)` SUBST1_TAC
    THENL
     [UNDISCH_TAC `a1 - y:real^3 = m + k % (q - p)` THEN
      ASM_REWRITE_TAC[VECTOR_ADD_LID] THEN EXPAND_TAC "y" THEN
      VECTOR_ARITH_TAC;
      REWRITE_TAC[MOI_FGB_LINE_PT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^3) dot (a1 - y) = m dot m` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (m:real^3) dot m` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `a1 - y:real^3 = m + k % (q - p)` THEN DISCH_THEN(K ALL_TAC) THEN
  UNDISCH_TAC `(a2:real^3) IN affine hull {p,q,a1}` THEN
  REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (X_CHOOSE_THEN `t0:real`
    (X_CHOOSE_THEN `w0:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `a2 - y:real^3 = (t0 - u * (&1 - w0)) % (q - p) + w0 % (a1 - y)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `a2:real^3 = s0 % p + t0 % q + w0 % a1` THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "y" THEN
    SUBGOAL_THEN `s0 = &1 - t0 - w0` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `a2:real^3 = s0 % p + t0 % q + w0 % a1` THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `(m:real^3) dot (a2 - y) = w0 * (m dot m)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_LID;
                    REAL_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w0 = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a2:real^3`] MOI_FGB_OFF_LINE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `a2:real^3 = (&1 - u) % p + u % q + (t0 - u * (&1 - w0)) % (q - p)`
    SUBST1_TAC THENL
     [UNDISCH_TAC
       `a2 - y:real^3 = (t0 - u * (&1 - w0)) % (q - p) + w0 % (a1 - y)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN EXPAND_TAC "y" THEN
      VECTOR_ARITH_TAC;
      REWRITE_TAC[MOI_FGB_LINE_PT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN affine hull {p,q}` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN
    MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `u:real`; `&0`] MOI_FGB_LINE_PT) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN convex hull {p,q,a1}` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC IN_CONVEX_SET THEN
    ASM_SIMP_TAC[CONVEX_CONVEX_HULL; REAL_LT_IMP_LE; HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `w0 < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < w0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a2:real^3`; `m:real^3`; `u:real`]
      MOI_FGB_HALF_PLANE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_LID;
                      REAL_ADD_RID] THEN
      ASM_SIMP_TAC[REAL_LT_MUL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "hp2"))) THEN
    ABBREV_TAC `t1 = min (&1 / &2) (r2 / (&2 * (norm(a1 - y:real^3) + &1)))` THEN
    SUBGOAL_THEN `&0 < t1 /\ t1 <= &1 /\ t1 * norm(a1 - y:real^3) < r2`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t1" THEN MATCH_MP_TAC MOI_FGB_SMALL_STEP THEN
      ASM_REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `y + t1 % (a1 - y) IN convex hull {p:real^3,q}` ASSUME_TAC
    THENL
     [UNDISCH_TAC
       `convex hull {p,q,a1} INTER convex hull {p,q,a2} =
        convex hull {p:real^3,q}` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_ARITH
         `y + t % (a - y):real^N = (&1 - t) % y + t % a`] THEN
        MATCH_MP_TAC IN_CONVEX_SET THEN
        ASM_SIMP_TAC[CONVEX_CONVEX_HULL; REAL_LT_IMP_LE; HULL_INC; IN_INSERT];
        USE_THEN "hp2" (MP_TAC o SPEC `y + t1 % (a1 - y):real^3`) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[dist; VECTOR_ARITH `y - (y + a):real^N = --a`; NORM_NEG;
                      NORM_MUL] THEN
          ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`];
          DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC[VECTOR_ARITH `(y + a) - y:real^N = a`; DOT_RMUL] THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `(n:real^3) dot (a1 - y) = &0`
          (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
          USE_THEN "h1" (fun th -> REWRITE_TAC[GSYM th]) THEN
          SIMP_TAC[HULL_INC; IN_INSERT];
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a1:real^3`] MOI_FGB_OFF_LINE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a1:real^3 = y + inv t1 % ((y + t1 % (a1 - y)) - y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `(y + a) - y:real^N = a`; VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `inv t1 * t1 = &1` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
    ASM_REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a1:real^3`; `m:real^3`; `u:real`]
    MOI_FGB_HALF_PLANE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "hp1"))) THEN
  MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a2:real^3`; `--m:real^3`; `u:real`]
    MOI_FGB_HALF_PLANE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DOT_LNEG; REAL_NEG_0] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_LID;
                    REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_ARITH `&0 < --(w * x) <=> &0 < --w * x`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "hp3"))) THEN
  MAP_EVERY EXISTS_TAC [`min r1 r3`; `n:real^3`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  USE_THEN "hp1" (MP_TAC o SPEC `z:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "hp3" (MP_TAC o SPEC `z:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DOT_LNEG] THEN REAL_ARITH_TAC);;

let MOI_FGB_EDGE_FORM = prove
 (`!c (A:real^3->bool) y.
     combinatorial_manifold 2 c /\ A IN c /\ aff_dim A = &1 /\
     y IN relative_interior A
     ==> ?r e. &0 < r /\ ~(e = vec 0) /\
               (!z. z IN affine hull A ==> ?l. z = y + l % e) /\
               ((?n. ~(n = vec 0) /\ n dot e = &0 /\
                     !z. dist(y,z) < r
                         ==> (z IN UNIONS c <=> n dot (z - y) = &0)) \/
                (?n1 n2. n1 dot e = &0 /\ n2 dot e = &0 /\
                         (!a b. a % n1 + b % n2 = vec 0 ==> a = &0 /\ b = &0) /\
                         !z. dist(y,z) < r
                             ==> (z IN UNIONS c <=>
                                  n1 dot (z - y) = &0 /\ &0 <= n2 dot (z - y) \/
                                  n2 dot (z - y) = &0 /\
                                  &0 <= n1 dot (z - y))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN A` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `y:real^3`] MOI_CMB_STAR_NBHD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "star"))) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `A:real^3->bool`]
    MOI_FGB_EDGE_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `q:real^3`
   (X_CHOOSE_THEN `a1:real^3` (X_CHOOSE_THEN `a2:real^3`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN
   `!z. dist(y,z) < r0
        ==> (z IN UNIONS c <=>
             z IN convex hull {p,q,a1} \/ z IN convex hull {p:real^3,q,a2})`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN USE_THEN "star" (MP_TAC o SPEC `z:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(A:real^3->bool) SUBSET S` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
        MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `y:real^3`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `aff_dim(S:real^3->bool) = &1 \/ aff_dim S = &2`
      STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPECL [`A:real^3->bool`; `S:real^3->bool`] AFF_DIM_SUBSET) THEN
        MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `S:real^3->bool`]
          MOI_FGB_CM2_DIM) THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
        SUBGOAL_THEN `A:real^3->bool = S` SUBST_ALL_TAC THENL
         [MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
          EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
          DISJ1_TAC THEN
          UNDISCH_TAC `(z:real^3) IN S` THEN UNDISCH_TAC `S = convex hull {p:real^3,q}` THEN
          DISCH_THEN SUBST1_TAC THEN
          SPEC_TAC(`z:real^3`,`z:real^3`) THEN REWRITE_TAC[GSYM SUBSET] THEN
          MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
        SUBGOAL_THEN `S = convex hull {p,q,a1} \/ S = convex hull {p:real^3,q,a2}`
        STRIP_ASSUME_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          DISJ1_TAC THEN ASM_MESON_TAC[];
          DISJ2_TAC THEN ASM_MESON_TAC[]]];
      REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u. &0 < u /\ u < &1 /\ y = (&1 - u) % p + u % (q:real^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN relative_interior A` THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT;
                    IN_SEGMENT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `y = (&1 - u) % p + u % (q:real^3)` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `!z:real^3. z IN affine hull A
               ==> ?l. z = ((&1 - u) % p + u % q) + l % (q - p)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_HULL_CONVEX_HULL; AFFINE_HULL_2; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `t1:real`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `t1 - u:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s1 = &1 - t1` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(a2:real^3) IN affine hull {p,q,a1}` THENL
   [MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a1:real^3`; `a2:real^3`; `u:real`]
      MOI_FGB_COPLANAR_CASE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `n:real^3`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`min r0 r1`; `q - p:real^3`] THEN
    REWRITE_TAC[REAL_LT_MIN; VECTOR_SUB_EQ] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISJ1_TAC THEN EXISTS_TAC `n:real^3` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a1:real^3`; `a2:real^3`; `u:real`]
      MOI_FGB_WEDGE_CASE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `n1:real^3`
      (X_CHOOSE_THEN `n2:real^3` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`min r0 r1`; `q - p:real^3`] THEN
    REWRITE_TAC[REAL_LT_MIN; VECTOR_SUB_EQ] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`n1:real^3`; `n2:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* H. Assembly of the local analysis: translated local forms, transversality *)
(* consequences of affine general position, and the crossing at each       *)
(* common point of a generic translate of s with t (MOI_FGB_LOCAL_CROSS).   *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_IN_TRANSLATE = prove
 (`!(d:real^N) S z. z IN IMAGE (\y. d + y) S <=> (z - d) IN S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_ARITH `(d + x) - d:real^N = x`];
    DISCH_TAC THEN EXISTS_TAC `z - d:real^N` THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC]);;

let MOI_FGB_DIST_TRANSLATE = prove
 (`!(d:real^N) y z. dist(d + y,z) = dist(y,z - d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dist] THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC);;

let MOI_FGB_TRI_FORM_T = prove
 (`!c (A:real^3->bool) y d.
     combinatorial_manifold 2 c /\ A IN c /\ aff_dim A = &2 /\
     y IN relative_interior A
     ==> ?r n. &0 < r /\ ~(n = vec 0) /\
               (!z. z IN affine hull A ==> n dot (z - y) = &0) /\
               !z. dist(d + y,z) < r
                   ==> (z IN IMAGE (\y. d + y) (UNIONS c) <=>
                        n dot (z - (d + y)) = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `A:real^3->bool`; `y:real^3`]
    MOI_FGB_TRI_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `n:real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `n:real^3`] THEN
  ASM_REWRITE_TAC[MOI_FGB_IN_TRANSLATE; MOI_FGB_DIST_TRANSLATE] THEN
  REWRITE_TAC[VECTOR_ARITH `z - d - y:real^N = z - (d + y)`] THEN
  ASM_MESON_TAC[VECTOR_ARITH `z - d - y:real^N = z - (d + y)`]);;

let MOI_FGB_EDGE_FORM_T = prove
 (`!c (A:real^3->bool) y d.
     combinatorial_manifold 2 c /\ A IN c /\ aff_dim A = &1 /\
     y IN relative_interior A
     ==> ?r e. &0 < r /\ ~(e = vec 0) /\
               (!z. z IN affine hull A ==> ?l. z = y + l % e) /\
               ((?n. ~(n = vec 0) /\ n dot e = &0 /\
                     !z. dist(d + y,z) < r
                         ==> (z IN IMAGE (\y. d + y) (UNIONS c) <=>
                              n dot (z - (d + y)) = &0)) \/
                (?n1 n2. n1 dot e = &0 /\ n2 dot e = &0 /\
                         (!a b. a % n1 + b % n2 = vec 0 ==> a = &0 /\ b = &0) /\
                         !z. dist(d + y,z) < r
                             ==> (z IN IMAGE (\y. d + y) (UNIONS c) <=>
                                  n1 dot (z - (d + y)) = &0 /\
                                  &0 <= n2 dot (z - (d + y)) \/
                                  n2 dot (z - (d + y)) = &0 /\
                                  &0 <= n1 dot (z - (d + y)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `A:real^3->bool`; `y:real^3`]
    MOI_FGB_EDGE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `e:real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `e:real^3`] THEN ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN EXISTS_TAC `n:real^3` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[MOI_FGB_IN_TRANSLATE; MOI_FGB_DIST_TRANSLATE] THEN
    REWRITE_TAC[VECTOR_ARITH `z - (d + y):real^N = (z - d) - y`] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `z - d:real^3`) THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`n1:real^3`; `n2:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[MOI_FGB_IN_TRANSLATE; MOI_FGB_DIST_TRANSLATE] THEN
    REWRITE_TAC[VECTOR_ARITH `z - (d + y):real^N = (z - d) - y`] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `z - d:real^3`) THEN ASM_REWRITE_TAC[]]);;

let MOI_FGB_HULL_IN_PLANE = prove
 (`!S (x:real^3) n.
     ~(n = vec 0) /\ (!z. z IN S ==> n dot (z - x) = &0)
     ==> ~(affine hull S = (:real^3))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `affine hull S SUBSET {z:real^3 | n dot z = n dot x}` MP_TAC
  THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN
    ASM_REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET; IN_UNIV; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x + n:real^3`) THEN
  ASM_REWRITE_TAC[DOT_RADD; REAL_ARITH `a + b = a <=> b = &0`; DOT_EQ_0]);;

let MOI_FGB_TRANSV_PLANES = prove
 (`!X Y (x:real^3) n m.
     ~(n = vec 0) /\ ~(m = vec 0) /\
     (!z. z IN X ==> n dot (z - x) = &0) /\
     (!z. z IN Y ==> m dot (z - x) = &0) /\
     affine hull (X UNION Y) = (:real^3)
     ==> !a b. a % n + b % m = vec 0 ==> a = &0 /\ b = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `b = &0` THENL
   [UNDISCH_TAC `a % n + b % m:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_EQ_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `a = &0` THENL
   [UNDISCH_TAC `a % n + b % m:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_MUL_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN X UNION Y ==> n dot (z - x) = &0`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN
    MP_TAC(ISPECL [`X UNION Y:real^3->bool`; `x:real^3`; `n:real^3`]
      MOI_FGB_HULL_IN_PLANE) THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[IN_UNION] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `m:real^3 = --(a / b) % n` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `a % n + b % m:real^3 = vec 0` THEN
    REWRITE_TAC[VECTOR_ARITH `a % n + b % m = vec 0 <=> b % m = --(a % n):real^N`] THEN
    DISCH_THEN(MP_TAC o AP_TERM `(%) (inv b):real^3->real^3`) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[real_div; VECTOR_MUL_RNEG; VECTOR_MUL_LNEG; VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DOT_LMUL; DOT_LNEG; REAL_MUL_LNEG; REAL_NEG_EQ_0; REAL_ENTIRE] THEN
  ASM_SIMP_TAC[REAL_DIV_EQ_0]);;

let MOI_FGB_TRANSV_LINE = prove
 (`!X Y (x:real^3) e m.
     ~(m = vec 0) /\
     (!z. z IN X ==> ?l. z = x + l % e) /\
     (!z. z IN Y ==> m dot (z - x) = &0) /\
     affine hull (X UNION Y) = (:real^3)
     ==> ~(m dot e = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^3. z IN X UNION Y ==> m dot (z - x) = &0`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN
    MP_TAC(ISPECL [`X UNION Y:real^3->bool`; `x:real^3`; `m:real^3`]
      MOI_FGB_HULL_IN_PLANE) THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[IN_UNION] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN X`)) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `(x + l % e) - x:real^N = l % e`; DOT_RMUL;
                  REAL_MUL_RZERO]);;

let MOI_FGB_INDEP_LINE2 = prove
 (`!n m e:real^3.
     n dot e = &0 /\ ~(m dot e = &0) /\ ~(n = vec 0)
     ==> (!a b. a % n + b % m = vec 0 ==> a = &0 /\ b = &0) /\
         (!a b. a % m + b % n = vec 0 ==> a = &0 /\ b = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b. a % (n:real^3) + b % (m:real^3) = vec 0
                      ==> a = &0 /\ b = &0`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `b = &0` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. v dot e`) THEN
      ASM_REWRITE_TAC[DOT_LADD; DOT_LMUL; DOT_LZERO; REAL_MUL_RZERO;
                      REAL_ADD_LID; REAL_ENTIRE];
      UNDISCH_TAC `a % n + &0 % m:real^3 = vec 0` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_EQ_0]];
    ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN ASM_REWRITE_TAC[]]);;

let MOI_FGB_INDEP_LINE3 = prove
 (`!n1 n2 m e:real^3.
     n1 dot e = &0 /\ n2 dot e = &0 /\
     (!a b. a % n1 + b % n2 = vec 0 ==> a = &0 /\ b = &0) /\
     ~(m dot e = &0)
     ==> !a b c. a % n1 + b % n2 + c % m = vec 0
                 ==> a = &0 /\ b = &0 /\ c = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `c = &0` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. v dot e`) THEN
    ASM_REWRITE_TAC[DOT_LADD; DOT_LMUL; DOT_LZERO; REAL_MUL_RZERO;
                    REAL_ADD_LID; REAL_ENTIRE];
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `a % n1 + b % n2 + &0 % m:real^3 = vec 0` THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID]]);;

let MOI_FGB_CROSS_FROM_MODEL = prove
 (`!S1 S2 M1 M2 (x:real^3) r.
     pl_crossing_at M1 M2 x /\ &0 < r /\
     (!z. dist(x,z) < r ==> (z IN S1 <=> z IN M1)) /\
     (!z. dist(x,z) < r ==> (z IN S2 <=> z IN M2))
     ==> pl_crossing_at S1 S2 x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FGB_CROSSING_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`M1:real^3->bool`; `M2:real^3->bool`;
                        `ball(x:real^3,r)`] THEN
  ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL; IN_BALL; DIST_REFL]);;

let MOI_FGB_CASE22 = prove
 (`!(s:(real^3->bool)->bool) t d y0 A B.
     combinatorial_manifold 2 s /\ combinatorial_manifold 2 t /\
     A IN s /\ B IN t /\ aff_dim A = &2 /\ aff_dim B = &2 /\
     y0 IN relative_interior A /\ (d + y0) IN relative_interior B /\
     affine hull (IMAGE (\y. d + y) A UNION B) = (:real^3)
     ==> pl_crossing_at (IMAGE (\y. d + y) (UNIONS s)) (UNIONS t) (d + y0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(real^3->bool)->bool`; `A:real^3->bool`; `y0:real^3`;
                 `d:real^3`] MOI_FGB_TRI_FORM_T) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rs:real` (X_CHOOSE_THEN `ns:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "as") (LABEL_TAC "ls")))))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `B:real^3->bool`;
                 `d + y0:real^3`] MOI_FGB_TRI_FORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rt:real` (X_CHOOSE_THEN `nt:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "at") (LABEL_TAC "lt")))))) THEN
  MATCH_MP_TAC MOI_FGB_CROSS_FROM_MODEL THEN
  MAP_EVERY EXISTS_TAC
   [`{z:real^3 | ns dot (z - (d + y0)) = &0}`;
    `{z:real^3 | nt dot (z - (d + y0)) = &0}`; `min rs rt`] THEN
  REWRITE_TAC[REAL_LT_MIN; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FGB_MODEL_P THEN
    MATCH_MP_TAC MOI_FGB_TRANSV_PLANES THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (\y:real^3. d + y) A`; `B:real^3->bool`;
                          `d + y0:real^3`] THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THEN
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `(d + w) - (d + y):real^N = w - y`] THEN
      USE_THEN "as" MATCH_MP_TAC THEN ASM_SIMP_TAC[HULL_INC];
      USE_THEN "at" MATCH_MP_TAC THEN ASM_SIMP_TAC[HULL_INC]];
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    USE_THEN "ls" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    USE_THEN "lt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_FGB_CASE21 = prove
 (`!(s:(real^3->bool)->bool) t d y0 A B.
     combinatorial_manifold 2 s /\ combinatorial_manifold 2 t /\
     A IN s /\ B IN t /\ aff_dim A = &2 /\ aff_dim B = &1 /\
     y0 IN relative_interior A /\ (d + y0) IN relative_interior B /\
     affine hull (IMAGE (\y. d + y) A UNION B) = (:real^3)
     ==> pl_crossing_at (IMAGE (\y. d + y) (UNIONS s)) (UNIONS t) (d + y0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(real^3->bool)->bool`; `A:real^3->bool`; `y0:real^3`;
                 `d:real^3`] MOI_FGB_TRI_FORM_T) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rs:real` (X_CHOOSE_THEN `ns:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "as") (LABEL_TAC "ls")))))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `B:real^3->bool`;
                 `d + y0:real^3`] MOI_FGB_EDGE_FORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rt:real` (X_CHOOSE_THEN `e:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "at") MP_TAC))))) THEN
  SUBGOAL_THEN `~((ns:real^3) dot e = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FGB_TRANSV_LINE THEN
    MAP_EVERY EXISTS_TAC [`B:real^3->bool`; `IMAGE (\y:real^3. d + y) A`;
                          `d + y0:real^3`] THEN
    ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
    CONJ_TAC THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THENL
     [USE_THEN "at" MATCH_MP_TAC THEN ASM_SIMP_TAC[HULL_INC];
      REWRITE_TAC[VECTOR_ARITH `(d + w) - (d + y):real^N = w - y`] THEN
      USE_THEN "as" MATCH_MP_TAC THEN ASM_SIMP_TAC[HULL_INC]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC MOI_FGB_CROSS_FROM_MODEL THEN
    MAP_EVERY EXISTS_TAC
     [`{z:real^3 | ns dot (z - (d + y0)) = &0}`;
      `{z:real^3 | n dot (z - (d + y0)) = &0}`; `min rs rt`] THEN
    REWRITE_TAC[REAL_LT_MIN; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FGB_MODEL_P THEN
      MP_TAC(ISPECL [`n:real^3`; `ns:real^3`; `e:real^3`]
        MOI_FGB_INDEP_LINE2) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      USE_THEN "ls" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `rt:real`)) (concl th) &&
        is_forall(concl th))) THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MOI_FGB_CROSS_FROM_MODEL THEN
    MAP_EVERY EXISTS_TAC
     [`{z:real^3 | ns dot (z - (d + y0)) = &0}`;
      `{z:real^3 | n1 dot (z - (d + y0)) = &0 /\
                   &0 <= n2 dot (z - (d + y0)) \/
                   n2 dot (z - (d + y0)) = &0 /\
                   &0 <= n1 dot (z - (d + y0))}`; `min rs rt`] THEN
    REWRITE_TAC[REAL_LT_MIN; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`d + y0:real^3`; `n1:real^3`; `n2:real^3`; `ns:real^3`]
        MOI_FGB_MODEL_W) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC MOI_FGB_INDEP_LINE3 THEN EXISTS_TAC `e:real^3` THEN
        ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      USE_THEN "ls" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `rt:real`)) (concl th) &&
        is_forall(concl th))) THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_FGB_CASE12 = prove
 (`!(s:(real^3->bool)->bool) t d y0 A B.
     combinatorial_manifold 2 s /\ combinatorial_manifold 2 t /\
     A IN s /\ B IN t /\ aff_dim A = &1 /\ aff_dim B = &2 /\
     y0 IN relative_interior A /\ (d + y0) IN relative_interior B /\
     affine hull (IMAGE (\y. d + y) A UNION B) = (:real^3)
     ==> pl_crossing_at (IMAGE (\y. d + y) (UNIONS s)) (UNIONS t) (d + y0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(real^3->bool)->bool`; `A:real^3->bool`; `y0:real^3`;
                 `d:real^3`] MOI_FGB_EDGE_FORM_T) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rs:real` (X_CHOOSE_THEN `e:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "as") MP_TAC))))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `B:real^3->bool`;
                 `d + y0:real^3`] MOI_FGB_TRI_FORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rt:real` (X_CHOOSE_THEN `nt:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "at") (LABEL_TAC "lt")))))) THEN
  SUBGOAL_THEN `~((nt:real^3) dot e = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FGB_TRANSV_LINE THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (\y:real^3. d + y) A`; `B:real^3->bool`;
                          `d + y0:real^3`] THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
    CONJ_TAC THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THENL
     [USE_THEN "as" (MP_TAC o SPEC `w:real^3`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[HULL_INC]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `l:real` SUBST1_TAC) THEN
      EXISTS_TAC `l:real` THEN VECTOR_ARITH_TAC;
      USE_THEN "at" MATCH_MP_TAC THEN ASM_SIMP_TAC[HULL_INC]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC MOI_FGB_CROSS_FROM_MODEL THEN
    MAP_EVERY EXISTS_TAC
     [`{z:real^3 | n dot (z - (d + y0)) = &0}`;
      `{z:real^3 | nt dot (z - (d + y0)) = &0}`; `min rs rt`] THEN
    REWRITE_TAC[REAL_LT_MIN; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FGB_MODEL_P THEN
      MP_TAC(ISPECL [`n:real^3`; `nt:real^3`; `e:real^3`]
        MOI_FGB_INDEP_LINE2) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `rs:real`)) (concl th) &&
        is_forall(concl th))) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      USE_THEN "lt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MOI_FGB_CROSS_FROM_MODEL THEN
    MAP_EVERY EXISTS_TAC
     [`{z:real^3 | n1 dot (z - (d + y0)) = &0 /\
                   &0 <= n2 dot (z - (d + y0)) \/
                   n2 dot (z - (d + y0)) = &0 /\
                   &0 <= n1 dot (z - (d + y0))}`;
      `{z:real^3 | nt dot (z - (d + y0)) = &0}`; `min rs rt`] THEN
    REWRITE_TAC[REAL_LT_MIN; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`d + y0:real^3`; `n1:real^3`; `n2:real^3`; `nt:real^3`]
        MOI_FGB_MODEL_W) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC MOI_FGB_INDEP_LINE3 THEN EXISTS_TAC `e:real^3` THEN
        ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `rs:real`)) (concl th) &&
        is_forall(concl th))) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      USE_THEN "lt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let MOI_FGB_LOCAL_CROSS = prove
 (`!(s:(real^3->bool)->bool) t d x.
     combinatorial_manifold 2 s /\ combinatorial_manifold 2 t /\
     (!A B. A IN s /\ B IN t ==> affine_gp_3 (IMAGE (\y. d + y) A) B) /\
     x IN IMAGE (\y. d + y) (UNIONS s) /\ x IN UNIONS t
     ==> pl_crossing_at (IMAGE (\y. d + y) (UNIONS s)) (UNIONS t) x`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(x:real^3) IN IMAGE (\y. d + y) (UNIONS s)` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `lf_simplicial_complex (s:(real^3->bool)->bool) /\
    lf_simplicial_complex (t:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(real^3->bool)->bool`; `y0:real^3`]
    MOI_FM3_CARRIER_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3->bool` (X_CHOOSE_THEN `v:real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `d + y0:real^3`]
    MOI_FM3_CARRIER_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^3->bool` (X_CHOOSE_THEN `w:real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN A /\ (d + y0:real^3) IN B` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(d + y0:real^3) IN IMAGE (\y. d + y) A INTER B` ASSUME_TAC
  THENL
   [REWRITE_TAC[IN_INTER; IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `y0:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine_gp_3 (IMAGE (\y:real^3. d + y) A) B` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `affine hull (IMAGE (\y:real^3. d + y) A UNION B) = (:real^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FGP_GP_MEET_UNIV THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&3 <= aff_dim (A:real^3->bool) + aff_dim (B:real^3->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `affine_gp_3 (IMAGE (\y:real^3. d + y) A) B` THEN
    REWRITE_TAC[affine_gp_3; AFF_DIM_TRANSLATION_EQ] THEN
    SUBGOAL_THEN `~DISJOINT (IMAGE (\y:real^3. d + y) A) B`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[DISJOINT] THEN ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (A:real^3->bool) <= &2 /\ aff_dim (B:real^3->bool) <= &2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FGB_CM2_DIM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(aff_dim (A:real^3->bool) = &2 /\ aff_dim (B:real^3->bool) = &2) \/
    (aff_dim A = &2 /\ aff_dim B = &1) \/
    (aff_dim A = &1 /\ aff_dim B = &2)`
  STRIP_ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC;
    MATCH_MP_TAC MOI_FGB_CASE22 THEN
    MAP_EVERY EXISTS_TAC [`A:real^3->bool`; `B:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FGB_CASE21 THEN
    MAP_EVERY EXISTS_TAC [`A:real^3->bool`; `B:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FGB_CASE12 THEN
    MAP_EVERY EXISTS_TAC [`A:real^3->bool`; `B:real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* I. GENERAL_POSITION_SURFACES_3.                                           *)
(* ------------------------------------------------------------------------- *)

let GENERAL_POSITION_SURFACES_3 = prove
 (`!(s:(real^3->bool)->bool) (t:(real^3->bool)->bool) w e.
     FINITE s /\ combinatorial_manifold 2 s /\ combinatorial_manifold 2 t /\
     open w /\ UNIONS s SUBSET w /\ UNIONS t SUBSET w /\
     closed_in (subtopology euclidean w) (UNIONS t) /\ &0 < e
     ==> ?f g. pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
               (?k. compact k /\ k SUBSET w /\ !x. ~(x IN k) ==> f x = x) /\
               (!x. dist(f x,x) < e) /\
               !x. x IN IMAGE f (UNIONS s) INTER UNIONS t
                   ==> pl_crossing_at (IMAGE f (UNIONS s)) (UNIONS t) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact(UNIONS s:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_FM3_LF_COMPACT; combinatorial_manifold];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS s:real^3->bool`; `w:real^3->bool`] MOI_FGB_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real` (X_CHOOSE_THEN `r:real`
    (X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `w:real^3->bool`; `k:real^3->bool`]
    MOI_FGB_LF_FINITE_NEAR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[combinatorial_manifold]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`s:(real^3->bool)->bool`;
                 `{B:real^3->bool | B IN t /\ ~(B INTER k = {})}`; `min r e`]
    MOI_FGB_GENERIC_TRANSLATE) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`phi:real^3->real`; `r:real`; `d:real^3`] MOI_FGB_PUSH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^3`) THEN
  MAP_EVERY EXISTS_TAC [`\x:real^3. x + phi x % d`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^3. x + phi x % d) (UNIONS s) = IMAGE (\y. d + y) (UNIONS s)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `k:real^3->bool` THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[dist; VECTOR_ARITH `(x + a) - x:real^N = a`; NORM_MUL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `&0 <= phi(x:real^3)`)) (snd(strip_forall(concl th))))) THEN
    MP_TAC(ISPEC `d:real^3` NORM_POS_LE) THEN
    SUBGOAL_THEN `norm(d:real^3) < e` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * norm(d:real^3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FGB_LOCAL_CROSS THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`A:real^3->bool`; `B:real^3->bool`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `B INTER k:real^3->bool = {}` THENL
     [REWRITE_TAC[affine_gp_3] THEN DISJ1_TAC THEN
      SUBGOAL_THEN `IMAGE (\y:real^3. d + y) A SUBSET k` MP_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `a:real^3` THEN
        DISCH_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `r:real`)) (concl th) &&
          can (find_term ((=) `k:real^3->bool`)) (concl th) &&
          is_forall(concl th))) THEN
        EXISTS_TAC `a:real^3` THEN
        REWRITE_TAC[dist; VECTOR_ARITH `a - (d + a):real^N = --d`; NORM_NEG] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
        UNDISCH_TAC `B INTER k:real^3->bool = {}` THEN SET_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]]]);;

(* ------------------------------------------------------------------------- *)
(* J. Arc links.  A finite complex L whose polyhedron is homeomorphic to a  *)
(* 1-simplex (the link of a boundary vertex of a combinatorial surface) has *)
(* dimension at most 1, every vertex lies in one or two edges, and some     *)
(* vertex lies in exactly one edge: an isolated vertex would be an isolated *)
(* point; a vertex in one edge is a non-cut point, and an arc has exactly   *)
(* two non-cut points (CONNECTED_ARC_IMAGE_DELETE); the Euler               *)
(* characteristic 1 and the handshake count do the rest.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_ARC_DIM = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g s.
     simplicial_complex L /\ &1 simplex k /\ homeomorphism (k,UNIONS L) (f,g) /\
     s IN L
     ==> aff_dim s <= &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS L` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(k:real^N->bool)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN THEN
    EXISTS_TAC `g:real^N->real^N` THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `k:real^N->bool`]
        HULL_SUBSET) THEN
      ASM SET_TAC[];
      ASM_MESON_TAC[SUBSET]];
    ASM_MESON_TAC[AFF_DIM_SIMPLEX; INT_LE_REFL]]);;

let MOI_FGB_SIMPLEX_1_SEGMENT = prove
 (`!k:real^N->bool. &1 simplex k ==> ?a b. ~(a = b) /\ k = segment[a,b]`,
  GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
    UNDISCH_TAC `&(CARD (c:real^N->bool)):int = &1 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
  ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL]);;

let MOI_FGB_ARC_CUT = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g.
     &1 simplex k /\ homeomorphism (k,UNIONS L) (f,g)
     ==> connected (UNIONS L) /\
         ?a b. ~(a = b) /\ k = segment[a,b] /\
               {x | x IN UNIONS L /\ connected (UNIONS L DELETE x)} =
               {f a, f b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_FGB_SIMPLEX_1_SEGMENT) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `arc((f:real^N->real^N) o linepath(a,b))` ASSUME_TAC THENL
   [MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[ARC_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    UNDISCH_TAC `k:real^N->bool = segment[a,b]` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image((f:real^N->real^N) o linepath(a,b)) = UNIONS L` ASSUME_TAC
  THENL
   [REWRITE_TAC[PATH_IMAGE_COMPOSE; PATH_IMAGE_LINEPATH] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONNECTED_ARC_IMAGE]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `(x:real^N) IN UNIONS L` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`(f:real^N->real^N) o linepath(a,b)`; `x:real^N`]
      CONNECTED_ARC_IMAGE_DELETE) THEN
    ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE;
                    PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    UNDISCH_TAC `~((x:real^N) IN UNIONS L)` THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^N) k = UNIONS L` THEN
    ASM_REWRITE_TAC[] THEN
    MESON_TAC[ENDS_IN_SEGMENT; FUN_IN_IMAGE]]);;

let MOI_FGB_ARC_STAR = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g u s.
     simplicial_complex L /\ &1 simplex k /\ homeomorphism (k,UNIONS L) (f,g) /\
     {u} IN L /\ s IN L /\ u IN s
     ==> s = {u} \/ aff_dim s = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`; `f:real^N->real^N`;
                 `g:real^N->real^N`; `s:real^N->bool`] MOI_FGB_ARC_DIM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` (fun th -> REWRITE_TAC[th]) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN ASM_CASES_TAC `aff_dim(s:real^N->bool) = &1` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = &0` MP_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[AFF_DIM_EQ_0] THEN ASM SET_TAC[]);;

let MOI_FGB_ARC_DEG_GE1 = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g u.
     simplicial_complex L /\ &1 simplex k /\ homeomorphism (k,UNIONS L) (f,g) /\
     {u} IN L
     ==> ?e. e IN L /\ aff_dim e = &1 /\ u IN e`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN L /\ u IN s ==> s = {u}` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `f:real^N->real^N`; `g:real^N->real^N`; `u:real^N`;
                   `s:real^N->bool`] MOI_FGB_ARC_STAR) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `u:real^N`] MOI_FSA_LOCAL_STAR) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_FGB_ARC_CUT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `a:real^N`
    (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `{u:real^N}`) THEN
  SUBGOAL_THEN `(u:real^N) IN UNIONS L` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `ball(u:real^N,r)` THEN
      REWRITE_TAC[OPEN_BALL] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; IN_BALL] THEN
      X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
       [DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[DIST_REFL]; ALL_TAC] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `s = {u:real^N}` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[]; ASM SET_TAC[]];
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `{u:real^N}` THEN
      REWRITE_TAC[CLOSED_SING] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(f:real^N->real^N) a = u /\ f b = u` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(a:real^N) IN k /\ b IN k` MP_TAC THENL
     [ASM_REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(a:real^N = b)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a:real^N) IN k /\ b IN k` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_FGB_ARC_LEAF_CUT = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g u e.
     simplicial_complex L /\ &1 simplex k /\ homeomorphism (k,UNIONS L) (f,g) /\
     {u} IN L /\ e IN L /\ aff_dim e = &1 /\ u IN e /\
     (!e'. e' IN L /\ aff_dim e' = &1 /\ u IN e' ==> e' = e)
     ==> connected (UNIONS L DELETE u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?w:real^N. ~(w = u) /\ e = segment[u,w] /\ {w} IN L`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`]
      MOI_FSA_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(u:real^N) IN {v | {v} IN L /\ v IN e}` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
     [EXISTS_TAC `q:real^N` THEN ASM_MESON_TAC[];
      EXISTS_TAC `p:real^N` THEN ASM_MESON_TAC[SEGMENT_SYM]];
    ALL_TAC] THEN
  ABBREV_TAC `L' = {s:real^N->bool | s IN L /\ ~(u IN s)}` THEN
  SUBGOAL_THEN `UNIONS L = UNIONS L' UNION (e:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L'" THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_UNIONS;
                                     IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `(u:real^N) IN s` THENL
       [DISJ2_TAC THEN
        MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                       `f:real^N->real^N`; `g:real^N->real^N`; `u:real^N`;
                       `s:real^N->bool`] MOI_FGB_ARC_STAR) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
         [UNDISCH_TAC `(z:real^N) IN s` THEN ASM_REWRITE_TAC[IN_SING] THEN
          DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[];
          ASM_MESON_TAC[]];
        DISJ1_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]];
      STRIP_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS L' INTER (e:real^N->bool) SUBSET {w}` ASSUME_TAC THENL
   [EXPAND_TAC "L'" THEN REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM;
                                     IN_SING] THEN
    X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool`
      STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(s INTER e:real^N->bool) face_of e` MP_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~((u:real^N) IN c)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(u:real^N) IN s INTER convex hull {u,w}` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `c SUBSET {w:real^N}` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN convex hull c` MP_TAC THENL
     [UNDISCH_TAC `s INTER convex hull {u:real^N,w} = convex hull c` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER] THEN
      ASM_MESON_TAC[SEGMENT_CONVEX_HULL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `c:real^N->bool`; `{w:real^N}`]
      HULL_MONO) THEN
    ASM_REWRITE_TAC[CONVEX_HULL_SING] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN UNIONS L'` ASSUME_TAC THENL
   [EXPAND_TAC "L'" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((u:real^N) IN UNIONS L')` ASSUME_TAC THENL
   [EXPAND_TAC "L'" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(UNIONS L':real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN EXPAND_TAC "L'" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
      REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(e:real^N->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CLOSED_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `connected(UNIONS L':real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `f:real^N->real^N`; `g:real^N->real^N`] MOI_FGB_ARC_CUT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[CONNECTED_CLOSED; CONTRAPOS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN
    STRIP_TAC THEN
    ASM_CASES_TAC `(w:real^N) IN e1` THENL
     [MAP_EVERY EXISTS_TAC [`(e1 INTER UNIONS L') UNION e:real^N->bool`;
                            `e2 INTER UNIONS L':real^N->bool`] THEN
      ASM_SIMP_TAC[CLOSED_UNION; CLOSED_INTER] THEN ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`e1 INTER UNIONS L':real^N->bool`;
                            `(e2 INTER UNIONS L') UNION e:real^N->bool`] THEN
      ASM_SIMP_TAC[CLOSED_UNION; CLOSED_INTER] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS L DELETE (u:real^N) = UNIONS L' UNION (e DELETE u)`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_CONNECTED THEN REWRITE_TAC[CONVEX_SEMIOPEN_SEGMENT];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `w:real^N` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DELETE; ENDS_IN_SEGMENT]]);;

(* As MOI_FSA_LK_CHI (pc_moi_fnd_surfa.ml), which assumes a circle link,     *)
(* but with the dimension bound as a hypothesis.                             *)

let MOI_FGB_CHI_DIM1 = prove
 (`!L:(real^N->bool)->bool.
     simplicial_complex L /\ (!s. s IN L ==> aff_dim s <= &1)
     ==> complex_euler L =
         &(CARD {u | {u} IN L}) - &(CARD {e | e IN L /\ aff_dim e = &1})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN L /\ ~(s = {})} =
    {s | s IN L /\ aff_dim s = &0} UNION {e | e IN L /\ aff_dim e = &1}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
    ASM_CASES_TAC `(s:real^N->bool) IN L` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &1` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THENL
     [CONV_TAC INT_REDUCE_CONV;
      MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT {s:real^N->bool | s IN L /\ aff_dim s = &0}
             {e | e IN L /\ aff_dim e = &1}`
  ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `s:real^N->bool` THEN
    ASM_CASES_TAC `aff_dim(s:real^N->bool) = &0` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION; FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `sum {s:real^N->bool | s IN L /\ aff_dim s = &0}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {s:real^N->bool | s IN L /\ aff_dim s = &0} (\s. &1) /\
    sum {e:real^N->bool | e IN L /\ aff_dim e = &1}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {e:real^N->bool | e IN L /\ aff_dim e = &1} (\s. -- &1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; NUM_OF_INT_OF_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN L /\ aff_dim s = &0} =
    IMAGE (\u:real^N. {u}) {u | {u} IN L}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; AFF_DIM_EQ_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN L}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real^N. {u}`; `{u:real^N | {u} IN L}`] CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RNEG; GSYM real_sub]);;

let MOI_FGB_ARC_DEGREES = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g.
     simplicial_complex L /\ &1 simplex k /\ pl_homeomorphism (k,UNIONS L) (f,g)
     ==> (!u. {u} IN L
              ==> 1 <= CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e} /\
                  CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e} <= 2) /\
         (?u. {u} IN L /\ CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e} = 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (k,UNIONS L) (f:real^N->real^N,g)` ASSUME_TAC
  THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN L ==> aff_dim s <= &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FGB_ARC_DIM THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                          `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Vs = {u:real^N | {u} IN L}` THEN
  ABBREV_TAC `E = CARD {e:real^N->bool | e IN L /\ aff_dim e = &1}` THEN
  ABBREV_TAC `deg = \u:real^N. CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e}` THEN
  SUBGOAL_THEN `FINITE (Vs:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Vs" THEN MATCH_MP_TAC FINITE_IMAGE_INJ THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (Vs:real^N->bool) = E + 1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `L:(real^N->bool)->bool` COMPLEX_EULER_VALUES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INT_ARITH `x:int <= &1 ==> x <= &2`];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[pl_ball] THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                            `g:real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `L:(real^N->bool)->bool` MOI_FGB_CHI_DIM1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ARITH `a - b = &1 <=> a = b + &1`; REAL_OF_NUM_ADD;
                REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `nsum Vs (deg:real^N->num) = 2 * E` ASSUME_TAC THENL
   [EXPAND_TAC "Vs" THEN EXPAND_TAC "deg" THEN EXPAND_TAC "E" THEN
    MATCH_MP_TAC MOI_FSA_LK_HANDSHAKE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N. u IN Vs ==> 1 <= deg u` (LABEL_TAC "ge1") THENL
   [EXPAND_TAC "Vs" THEN EXPAND_TAC "deg" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT; ASSUME `FINITE (L:(real^N->bool)->bool)`] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MATCH_MP_TAC MOI_FGB_ARC_DEG_GE1 THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                          `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Lv = {u:real^N | u IN Vs /\ deg u = 1}` THEN
  SUBGOAL_THEN `CARD (Lv:real^N->bool) <= 2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `f:real^N->real^N`; `g:real^N->real^N`] MOI_FGB_ARC_CUT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC) o CONJUNCT2) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {(f:real^N->real^N) a, f b}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN
      SIMP_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
      UNDISCH_TAC
       `{x | x IN UNIONS L /\ connected (UNIONS L DELETE x)} =
        {(f:real^N->real^N) a, f b}` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      EXPAND_TAC "Lv" THEN EXPAND_TAC "Vs" THEN EXPAND_TAC "deg" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `u:real^N` THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^N}` THEN
        ASM_REWRITE_TAC[IN_SING];
        ALL_TAC] THEN
      MP_TAC(ISPEC `{e:real^N->bool | e IN L /\ aff_dim e = &1 /\ u IN e}`
        MOI_FSA_CARD_EQ_1) THEN
      ASM_SIMP_TAC[FINITE_RESTRICT] THEN
      DISCH_THEN(X_CHOOSE_TAC `e0:real^N->bool`) THEN
      MATCH_MP_TAC MOI_FGB_ARC_LEAF_CUT THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                            `g:real^N->real^N`; `e0:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Lv:real^N->bool) SUBSET Vs /\ FINITE Lv` STRIP_ASSUME_TAC
  THENL
   [EXPAND_TAC "Lv" THEN CONJ_TAC THENL
     [SET_TAC[]; MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N. u IN Vs ==> deg u <= 2` ASSUME_TAC THENL
   [X_GEN_TAC `u0:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`deg:real^N->num`; `Lv:real^N->bool`;
                   `Vs DIFF Lv:real^N->bool`] NSUM_UNION) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_DIFF] THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `Lv UNION (Vs DIFF Lv):real^N->bool = Vs` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `nsum Lv (deg:real^N->num) = CARD (Lv:real^N->bool)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `nsum Lv (\u:real^N. 1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC NSUM_EQ THEN EXPAND_TAC "Lv" THEN SIMP_TAC[IN_ELIM_THM];
        ASM_SIMP_TAC[NSUM_CONST; MULT_CLAUSES]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\u:real^N. 2`; `deg:real^N->num`; `Vs DIFF Lv:real^N->bool`]
      NSUM_LT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_DIFF] THEN CONJ_TAC THENL
       [X_GEN_TAC `u:real^N` THEN REWRITE_TAC[IN_DIFF] THEN
        EXPAND_TAC "Lv" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        USE_THEN "ge1" (MP_TAC o C MATCH_MP (ASSUME `(u:real^N) IN Vs`)) THEN
        UNDISCH_TAC `~((u:real^N) IN Vs /\ deg u = 1)` THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC;
        EXISTS_TAC `u0:real^N` THEN ASM_REWRITE_TAC[IN_DIFF] THEN
        EXPAND_TAC "Lv" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[NSUM_CONST; FINITE_DIFF; CARD_DIFF] THEN
    UNDISCH_TAC `CARD (Lv:real^N->bool) <= 2` THEN
    SUBGOAL_THEN `CARD (Lv:real^N->bool) <= CARD (Vs:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(u:real^N) IN Vs` ASSUME_TAC THENL
     [EXPAND_TAC "Vs" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    USE_THEN "ge1" (MP_TAC o C MATCH_MP (ASSUME `(u:real^N) IN Vs`)) THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(u:real^N) IN Vs`) o
      check (fun th -> can (find_term ((=) `2`)) (concl th) &&
                       is_forall(concl th))) THEN
    EXPAND_TAC "deg" THEN REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  MP_TAC(ISPECL [`\u:real^N. 2`; `deg:real^N->num`; `Vs:real^N->bool`]
    NSUM_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    USE_THEN "ge1" (MP_TAC o C MATCH_MP (ASSUME `(u:real^N) IN Vs`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N` o check (fun th ->
      is_neg(snd(strip_forall(concl th))) )) THEN
    UNDISCH_TAC `(u:real^N) IN Vs` THEN EXPAND_TAC "Vs" THEN
    EXPAND_TAC "deg" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[] THEN ARITH_TAC;
    ASM_SIMP_TAC[NSUM_CONST] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* K. Combinatorial 2-manifolds with boundary (locally finite): vertex     *)
(* links are circles or arcs; simplices have dimension at most 2; an edge  *)
(* lies in one or two triangles, in exactly two when it meets a point off  *)
(* the boundary; a vertex off the boundary has a circle link.              *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_CMB2_LINK = prove
 (`!c (v:real^N).
     combinatorial_manifold_with_boundary 2 c /\ {v} IN c
     ==> simplicial_complex (simplicial_link c v) /\
         ((?k:real^N->bool f:real^N->real^N g. &2 simplex k /\
              homeomorphism (relative_frontier k,UNIONS (simplicial_link c v))
                            (f,g) /\
              complex_euler (simplicial_link c v) = &0) \/
          (?k:real^N->bool f:real^N->real^N g. &1 simplex k /\
              pl_homeomorphism (k,UNIONS (simplicial_link c v)) (f,g)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[pl_sphere; pl_ball] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THENL
   [DISJ1_TAC THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                          `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
    MP_TAC(ISPECL [`relative_frontier (k:real^N->bool)`;
                   `&1 - (-- &1) pow 2`;
                   `simplicial_link c (v:real^N)`; `f:real^N->real^N`;
                   `g:real^N->real^N`] MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FEU_EULER_SIMPLEX_FRONTIER THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN
        ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_BOUNDED]];
      DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                          `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FGB_CMB2_LINK_DIM = prove
 (`!c (v:real^N) s.
     combinatorial_manifold_with_boundary 2 c /\ {v} IN c /\
     s IN simplicial_link c v
     ==> aff_dim s <= &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FGB_CMB2_LINK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MATCH_MP_TAC MOI_FSA_LK_DIM THEN
    MAP_EVERY EXISTS_TAC [`simplicial_link c (v:real^N)`; `k:real^N->bool`;
                          `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FGB_ARC_DIM THEN
    MAP_EVERY EXISTS_TAC [`simplicial_link c (v:real^N)`; `k:real^N->bool`;
                          `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_MESON_TAC[pl_homeomorphism]]);;

let MOI_FGB_CMB2_DIM = prove
 (`!c s:real^N->bool.
     combinatorial_manifold_with_boundary 2 c /\ s IN c ==> aff_dim s <= &2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_FM3_LF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
    MOI_FGB_CMB2_LINK_DIM) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim(convex hull ((v:real^N) INSERT s')) = aff_dim s' + &1` THEN
  UNDISCH_TAC `s:real^N->bool = convex hull (v INSERT s')` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN INT_ARITH_TAC);;

let MOI_FGB_CMB2_EDGE_LINK = prove
 (`!c e:real^N->bool.
     combinatorial_manifold_with_boundary 2 c /\ e IN c /\ aff_dim e = &1
     ==> ?v u. {v} IN c /\ {u} IN simplicial_link c v /\
               e = convex hull (v INSERT {u}) /\
               CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} =
               CARD {d | d IN simplicial_link c v /\ aff_dim d = &1 /\ u IN d}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_FM3_LF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(s':real^N->bool) = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `aff_dim(convex hull ((v:real^N) INSERT s')) = aff_dim s' + &1` THEN
    UNDISCH_TAC `e:real^N->bool = convex hull (v INSERT s')` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?u:real^N. s' = {u}` (X_CHOOSE_THEN `u:real^N` SUBST_ALL_TAC)
  THENL [ASM_MESON_TAC[AFF_DIM_EQ_0]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v:real^N`; `u:real^N`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `{u:real^N}`;
                 `&1:int`; `&2:int`] MOI_FM3_LINK_CARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `e:real^N->bool = convex hull (v INSERT {u})` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SING_SUBSET]);;

let MOI_FGB_CMB2_EDGE = prove
 (`!c e:real^N->bool.
     combinatorial_manifold_with_boundary 2 c /\ e IN c /\ aff_dim e = &1
     ==> CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 1 \/
         CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_FGB_CMB2_EDGE_LINK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` (X_CHOOSE_THEN `u:real^N`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FGB_CMB2_LINK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [DISJ2_TAC THEN MATCH_MP_TAC MOI_FSA_LK_DEG2 THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                          `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `k:real^N->bool`;
                   `f:real^N->real^N`; `g:real^N->real^N`]
      MOI_FGB_ARC_DEGREES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `u:real^N` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let MOI_FGB_CMB2_EDGE_INT = prove
 (`!c e (x:real^N).
     combinatorial_manifold_with_boundary 2 c /\ e IN c /\ aff_dim e = &1 /\
     x IN e /\ ~(x IN surface_boundary c)
     ==> CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_FGB_CMB2_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((x:real^N) IN surface_boundary c)` THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_FGB_CMB2_VERTEX_INT = prove
 (`!c (w:real^N).
     combinatorial_manifold_with_boundary 2 c /\ {w} IN c /\
     ~(w IN surface_boundary c)
     ==> pl_sphere 1 (UNIONS (simplicial_link c w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  UNDISCH_TAC `combinatorial_manifold_with_boundary 2 (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `pl_sphere 1 (UNIONS (simplicial_link c (w:real^N)))` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`simplicial_link c (w:real^N)`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`]
    MOI_FGB_ARC_DEGREES) THEN
  ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`; `{u:real^N}`]
    MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`; `{u:real^N}`;
                 `&1:int`; `&2:int`] MOI_FM3_LINK_CARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[SING_SUBSET] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((w:real^N) IN surface_boundary c)` THEN
  REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `convex hull ((w:real^N) INSERT {u})` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim(convex hull ((w:real^N) INSERT {u})) = aff_dim {u} + &1` THEN
  REWRITE_TAC[AFF_DIM_SING] THEN CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* L. Charts of a combinatorial surface at points off its boundary.  The    *)
(* standard triangle S0 = conv{0,e1,e2} of real^2 and the affine            *)
(* parametrization y |-> p + y1 (q - p) + y2 (r - p) of a triangle; the     *)
(* triangle chart (relative interior of a triangle), the vertex chart (open *)
(* star, the cone over a circle link, as MOI_STA_STAR_PLH one dimension     *)
(* down) and the edge chart (two triangles unfolded).                       *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_INDEP_TRI = prove
 (`!p q r:real^N.
     ~affine_dependent {p,q,r} /\ ~(p = q) /\ ~(p = r) /\ ~(q = r)
     ==> !a b. a % (q - p) + b % (r - p) = vec 0 ==> a = &0 /\ b = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `independent {q - p:real^N, r - p}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:real^N`; `{q:real^N,r}`] DEPENDENT_IMP_AFFINE_DEPENDENT) THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[independent];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`q - p:real^N`; `r - p:real^N`; `a:real`; `b:real`]
    INDEPENDENT_2) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `q - p:real^N = r - p <=> q = r`] THEN
  MESON_TAC[]);;

let MOI_FGB_STD_TRI = prove
 (`~affine_dependent {vec 0:real^2, basis 1, basis 2} /\
   ~(vec 0:real^2 = basis 1) /\ ~(vec 0:real^2 = basis 2) /\
   ~(basis 1:real^2 = basis 2) /\
   &2 simplex (convex hull {vec 0:real^2, basis 1, basis 2}) /\
   affine hull (convex hull {vec 0:real^2, basis 1, basis 2}) = (:real^2) /\
   open (relative_interior (convex hull {vec 0:real^2, basis 1, basis 2}))`,
  SUBGOAL_THEN
   `~(vec 0:real^2 = basis 1) /\ ~(vec 0:real^2 = basis 2) /\
    ~(basis 1:real^2 = basis 2)`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT; BASIS_COMPONENT;
             ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {vec 0:real^2, basis 1, basis 2}` ASSUME_TAC
  THENL
   [MP_TAC(INST_TYPE [`:2`,`:N`] AFFINE_INDEPENDENT_STDBASIS) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[DIMINDEX_2; EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    MESON_TAC[ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `aff_dim (convex hull {vec 0:real^2, basis 1, basis 2}) = &2`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT;
                 MOI_FGB_CARD3] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[simplex] THEN
    EXISTS_TAC `{vec 0:real^2, basis 1, basis 2}` THEN
    ASM_SIMP_TAC[MOI_FGB_CARD3] THEN INT_ARITH_TAC;
    REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_2] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `affine hull (convex hull {vec 0:real^2, basis 1, basis 2}) = (:real^2)`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_2] THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR; OPEN_INTERIOR]]]);;

let MOI_FGB_TRI_MAP = prove
 (`!p q r:real^N.
     ~affine_dependent {p,q,r} /\ ~(p = q) /\ ~(p = r) /\ ~(q = r)
     ==> ?l'. linear l' /\
              (!y:real^2. l' (y$1 % (q - p) + y$2 % (r - p)) = y) /\
              (!z. z IN affine hull {p,q,r}
                   ==> p + (l' (z - p))$1 % (q - p) + (l' (z - p))$2 % (r - p) =
                       z) /\
              IMAGE (\y:real^2. p + y$1 % (q - p) + y$2 % (r - p))
                    (convex hull {vec 0, basis 1, basis 2}) =
              convex hull {p,q,r} /\
              IMAGE (\y:real^2. p + y$1 % (q - p) + y$2 % (r - p))
                    (relative_interior (convex hull {vec 0, basis 1, basis 2})) =
              relative_interior (convex hull {p,q,r}) /\
              IMAGE (\y:real^2. p + y$1 % (q - p) + y$2 % (r - p))
                    (relative_frontier (convex hull {vec 0, basis 1, basis 2})) =
              relative_frontier (convex hull {p,q,r})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = \y:real^2. y$1 % (q - p) + y$2 % (r - p:real^N)` THEN
  SUBGOAL_THEN `linear (L:real^2->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[linear; VECTOR_ADD_COMPONENT;
                                     VECTOR_MUL_COMPONENT] THEN
    REPEAT GEN_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^2. (L:real^2->real^N) x = L y ==> x = y` ASSUME_TAC
  THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "L" THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`] MOI_FGB_INDEP_TRI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`(x:real^2)$1 - (y:real^2)$1`;
                               `(x:real^2)$2 - (y:real^2)$2`]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC
       `(x:real^2)$1 % (q - p) + x$2 % (r - p:real^N) =
        (y:real^2)$1 % (q - p) + y$2 % (r - p)` THEN
      VECTOR_ARITH_TAC;
      SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `L:real^2->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y:real^2. (l':real^N->real^2) (L y) = y` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    REWRITE_TAC[o_THM; I_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y:real^2. p + y$1 % (q - p) + y$2 % (r - p:real^N)) =
    (\x. p + x) o (L:real^2->real^N)`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN
  MP_TAC(ISPECL [`L:real^2->real^N`;
                 `convex hull {vec 0:real^2, basis 1, basis 2}`]
    RELATIVE_INTERIOR_INJECTIVE_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`L:real^2->real^N`;
                 `convex hull {vec 0:real^2, basis 1, basis 2}`]
    RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM RELATIVE_INTERIOR_TRANSLATION;
              GSYM RELATIVE_FRONTIER_TRANSLATION] THEN
  MP_TAC(ISPECL [`L:real^2->real^N`; `{vec 0:real^2, basis 1, basis 2}`]
    CONVEX_HULL_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM CONVEX_HULL_TRANSLATION] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^N. p + x) (IMAGE (L:real^2->real^N)
                                    {vec 0, basis 1, basis 2}) = {p,q,r}`
  SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES] THEN EXPAND_TAC "L" THEN
    SIMP_TAC[VEC_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID;
                VECTOR_ADD_RID] THEN
    REWRITE_TAC[VECTOR_ARITH `p + (q - p):real^N = q`];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN EXISTS_TAC `l':real^N->real^2` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(y:real^2)$1 % (q - p) + y$2 % (r - p:real^N) = L y`
    SUBST1_TAC THENL [EXPAND_TAC "L" THEN REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^N` THEN REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
    (X_CHOOSE_THEN `cc:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `z - p:real^N = L(vector[b; cc]:real^2)` SUBST1_TAC THENL
   [EXPAND_TAC "L" THEN ASM_REWRITE_TAC[VECTOR_2] THEN
    SUBGOAL_THEN `a = &1 - b - cc` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ASM_REWRITE_TAC[VECTOR_2] THEN
    SUBGOAL_THEN `a = &1 - b - cc` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]]);;

let MOI_FGB_SIMPLEX_2_VERTICES = prove
 (`!k:real^N->bool.
     &2 simplex k
     ==> ?p q r. ~affine_dependent {p,q,r} /\ ~(p = q) /\ ~(p = r) /\
                 ~(q = r) /\ k = convex hull {p,q,r}`,
  GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
    UNDISCH_TAC `&(CARD (v:real^N->bool)):int = &2 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    (X_CHOOSE_THEN `r:real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`; `r:real^N`] THEN
  ASM_MESON_TAC[]);;

let MOI_FGB_SIMPLEX_RF_R2 = prove
 (`!k:real^N->bool.
     &2 simplex k
     ==> ?S:real^2->bool f g.
           &2 simplex S /\
           pl_homeomorphism (relative_frontier S,relative_frontier k) (f,g)`,
  GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    (X_CHOOSE_THEN `r:real^N` STRIP_ASSUME_TAC)) o
    MATCH_MP MOI_FGB_SIMPLEX_2_VERTICES) THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`] MOI_FGB_TRI_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `convex hull {vec 0:real^2, basis 1, basis 2}` THEN
  EXISTS_TAC `\y:real^2. p + y$1 % (q - p) + y$2 % (r - p:real^N)` THEN
  EXISTS_TAC `\z:real^N. (l':real^N->real^2) (z - p)` THEN
  REWRITE_TAC[MOI_FGB_STD_TRI] THEN
  SUBGOAL_THEN
   `pl_map_on (relative_frontier (convex hull {vec 0:real^2, basis 1, basis 2}))
              (\y:real^2. p + y$1 % (q - p) + y$2 % (r - p:real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\y:real^2. (\y. y$1 % (q - p) + y$2 % (r - p:real^N)) y + p` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
        MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
        MESON_TAC[MOI_FGB_STD_TRI; SIMPLEX_IMP_POLYTOPE];
        REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        REPEAT GEN_TAC THEN VECTOR_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[homeomorphism] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z:real^N. z IN relative_frontier(convex hull {p,q,r})
               ==> p + (l' (z - p):real^2)$1 % (q - p) +
                   (l' (z - p))$2 % (r - p) = z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `relative_frontier(convex hull {p,q,r}) SUBSET affine hull {p:real^N,q,r}`
    MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `closure(convex hull {p:real^N,q,r})` THEN
      REWRITE_TAC[relative_frontier; SUBSET_DIFF] THEN
      MP_TAC(ISPEC `convex hull {p:real^N,q,r}` CLOSURE_SUBSET_AFFINE_HULL) THEN
      REWRITE_TAC[AFFINE_HULL_CONVEX_HULL];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `(p + x) - p:real^N = x`] THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
    UNDISCH_TAC
     `IMAGE (\y:real^2. p + y$1 % (q - p) + y$2 % (r - p:real^N))
            (relative_frontier (convex hull {vec 0, basis 1, basis 2})) =
      relative_frontier (convex hull {p,q,r})` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(p + x) - p:real^N = x`; IMAGE_ID];
    SUBGOAL_THEN
     `(\z:real^N. (l':real^N->real^2) (z - p)) = l' o (\z. z - p)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON]]);;

(* The closed star of a vertex with a circle link is PL homeomorphic to a   *)
(* triangle of real^2, the link going onto its boundary: the proof of       *)
(* MOI_FM3_STAR_SPHERE (pc_moi_fnd_m3a.ml) one dimension down.             *)

let MOI_FGB_STAR_DISK = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c /\
        pl_sphere 1 (UNIONS (simplicial_link c v))
        ==> ?S:real^2->bool p q.
                &2 simplex S /\
                pl_homeomorphism
                  (UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)},
                   S)
                  (p,q) /\
                IMAGE p (UNIONS (simplicial_link c v)) = relative_frontier S /\
                ~(UNIONS (simplicial_link c v) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_sphere 1 (UNIONS (simplicial_link c (v:real^N)))` THEN
  REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f0:real^N->real^N`
    (X_CHOOSE_THEN `g0:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_FGB_SIMPLEX_RF_R2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^2->bool` (X_CHOOSE_THEN `f1:real^2->real^N`
    (X_CHOOSE_THEN `g1:real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier S,UNIONS (simplicial_link c (v:real^N)))
      ((f0:real^N->real^N) o (f1:real^2->real^N),
       (g1:real^N->real^2) o (g0:real^N->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((g1:real^N->real^2) o (g0:real^N->real^N))
          (UNIONS (simplicial_link c (v:real^N))) = relative_frontier S /\
    IMAGE ((f0:real^N->real^N) o (f1:real^2->real^N)) (relative_frontier S) =
          UNIONS (simplicial_link c v)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `pl_homeomorphism (relative_frontier S,UNIONS (simplicial_link c (v:real^N)))
        ((f0:real^N->real^N) o (f1:real^2->real^N),
         (g1:real^N->real^2) o (g0:real^N->real^N))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^2->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`relative_frontier S:real^2->bool`; `UNIONS (simplicial_link c (v:real^N))`;
    `simplex_barycentre (S:real^2->bool)`; `v:real^N`;
    `(f0:real^N->real^N) o (f1:real^2->real^N)`;
    `(g1:real^N->real^2) o (g0:real^N->real^N)`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `S:real^2->bool` THEN
  EXISTS_TAC `moi_con_conemap (UNIONS (simplicial_link c v)) (v:real^N)
               (simplex_barycentre (S:real^2->bool))
               ((g1:real^N->real^2) o (g0:real^N->real^N))` THEN
  EXISTS_TAC `moi_con_conemap (relative_frontier S)
               (simplex_barycentre (S:real^2->bool)) (v:real^N)
               ((f0:real^N->real^N) o (f1:real^2->real^N))` THEN
  ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE ((g1:real^N->real^2) o (g0:real^N->real^N))
                      (UNIONS (simplicial_link c (v:real^N)))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^N. x IN s ==> (f:real^N->real^2) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_CONEMAP_ON_BASE THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `~(relative_frontier S:real^2->bool = {})` THEN
    UNDISCH_TAC
     `IMAGE ((f0:real^N->real^N) o (f1:real^2->real^N)) (relative_frontier S) =
      UNIONS (simplicial_link c (v:real^N))` THEN
    SET_TAC[]]);;

let MOI_FGB_SIMPLEX_INTERIOR_2 = prove
 (`!S:real^2->bool.
        &2 simplex S ==> S DIFF relative_frontier S = interior S`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `relative_interior S:real^2->bool = interior S`
  (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_2] THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (S:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[relative_frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
  MP_TAC(ISPEC `S:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]);;

(* The vertex chart: the proof of MOI_STA_VERTEX_CHART (pc_moi_star.ml) one *)
(* dimension down, in the pl_homeomorphism form.                            *)

let MOI_FGB_VERTEX_CHART = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c /\
        pl_sphere 1 (UNIONS (simplicial_link c v))
        ==> ?p:real^N->real^2 q.
                open (IMAGE p (moi_sta_open_star c v)) /\
                pl_homeomorphism
                  (moi_sta_open_star c v,IMAGE p (moi_sta_open_star c v)) (p,q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FGB_STAR_DISK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^2->bool` (X_CHOOSE_THEN `p:real^N->real^2`
    (X_CHOOSE_THEN `q:real^2->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_OPEN_STAR_OPEN)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `homeomorphism
      (UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)},S)
      ((p:real^N->real^2),(q:real^2->real^N)) /\
    pl_map_on
      (UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c (v:real^N))})
      p /\
    pl_map_on S q`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)}
         ==> (q:real^2->real^N) ((p:real^N->real^2) x) = x) /\
    IMAGE p
      (UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c (v:real^N))}) =
    S`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `homeomorphism
        (UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)},S)
        ((p:real^N->real^2),(q:real^2->real^N))` THEN
    SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_sta_open_star c (v:real^N) SUBSET
    UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_OPEN_STAR_EQ)
    THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (simplicial_link c (v:real^N)) SUBSET
    UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c v)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_CON_IN_CONE] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`y:real^N`; `&1`] THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p:real^N->real^2) (moi_sta_open_star c v) = interior S`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_OPEN_STAR_EQ)
    THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPEC `S:real^2->bool` MOI_FGB_SIMPLEX_INTERIOR_2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC
     `IMAGE (p:real^N->real^2) (UNIONS (simplicial_link c (v:real^N))) =
      relative_frontier S` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_STA_IMAGE_DIFF THEN EXISTS_TAC `q:real^2->real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:real^N->real^2`; `q:real^2->real^N`] THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR; pl_homeomorphism] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC
     `IMAGE (p:real^N->real^2) (moi_sta_open_star c v) = interior S` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC
     [`UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c (v:real^N))}`;
      `S:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC
     `UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link c (v:real^N))}` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `open_in (subtopology euclidean (UNIONS c))
              (moi_sta_open_star c (v:real^N))` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_LF_COMPLEX];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `S:real^2->bool` THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_OPEN THEN REWRITE_TAC[OPEN_INTERIOR]]);;

(* ------------------------------------------------------------------------- *)
(* M. More charts: carriers and open stars of points of a locally finite   *)
(* complex, the triangle chart, the edge chart (two triangles unfolded) and *)
(* the chart at an arbitrary point off the boundary of a surface.           *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_OPEN_IN_LP = prove
 (`!c (u:real^N->bool).
        lf_simplicial_complex c /\ open_in (subtopology euclidean (UNIONS c)) u
        ==> locally_polyhedral u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_LF_COMPLEX]);;

let MOI_FGB_CARRIER = prove
 (`!c (z:real^N).
        lf_simplicial_complex c /\ z IN UNIONS c
        ==> ?s. s IN c /\ z IN relative_interior s /\
                !t. t IN c /\ z IN t ==> s SUBSET t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  UNDISCH_TAC `(z:real^N) IN UNIONS c` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `convex (t0:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:real^N->bool`; `z:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t INTER t0:real^N->bool` THEN
  REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
  EXISTS_TAC `t0:real^N->bool` THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[]]);;

let MOI_FGB_OSTAR_EQ = prove
 (`!c (e:real^N->bool) x.
        lf_simplicial_complex c /\ e IN c /\ x IN relative_interior e
        ==> moi_sta_open_star c x =
            UNIONS {relative_interior s | s IN c /\ e SUBSET s}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  SUBGOAL_THEN `(x:real^N) IN e` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; moi_sta_open_star; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st")) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:real^N`] MOI_FGB_CARRIER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^N) IN s` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
     [USE_THEN "st" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `relative_interior s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s INTER e:real^N->bool` THEN
    REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
    EXISTS_TAC `e:real^N->bool` THEN REWRITE_TAC[SUBSET_REFL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `r:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    UNDISCH_TAC `(z:real^N) IN r` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN s` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET t` (fun th -> ASM SET_TAC[th]) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t INTER s:real^N->bool` THEN
    REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
    EXISTS_TAC `s:real^N->bool` THEN REWRITE_TAC[SUBSET_REFL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[]]);;

let MOI_FGB_STD_RELINT = prove
 (`relative_interior (convex hull {vec 0:real^2, basis 1, basis 2}) =
   {y:real^2 | &0 < y$1 /\ &0 < y$2 /\ y$1 + y$2 < &1}`,
  SUBGOAL_THEN `~collinear {vec 0:real^2, basis 1, basis 2}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; MOI_FGB_STD_TRI]; ALL_TAC] THEN
  SIMP_TAC[RELATIVE_INTERIOR_INTERIOR; MOI_FGB_STD_TRI] THEN
  ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `v:real^2` THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
      (X_CHOOSE_THEN `cc:real` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`&1 - (v:real^2)$1 - v$2`; `(v:real^2)$1`; `(v:real^2)$2`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN
    REAL_ARITH_TAC]);;

let MOI_FGB_AFFINE2_CONT = prove
 (`!(p:real^N) a b s.
        (\y:real^2. p + y$1 % a + y$2 % b) continuous_on s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REPEAT GEN_TAC THEN VECTOR_ARITH_TAC);;

let MOI_FGB_MAXIMAL_OSTAR = prove
 (`!c (t:real^N->bool) x.
        lf_simplicial_complex c /\ t IN c /\ x IN relative_interior t /\
        (!s. s IN c /\ t SUBSET s ==> s = t)
        ==> moi_sta_open_star c x = relative_interior t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "max")))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `x:real^N`]
    MOI_FGB_OSTAR_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `{relative_interior s | s IN c /\ (t:real^N->bool) SUBSET s} =
    {relative_interior t}`
  (fun th -> REWRITE_TAC[th; UNIONS_1]) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    USE_THEN "max" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

let MOI_FGB_MAXIMAL_DIM2 = prove
 (`!c (t:real^N->bool) s.
        lf_simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
        t IN c /\ aff_dim t = &2 /\ s IN c /\ t SUBSET s
        ==> s = t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dim")
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t:real^N->bool) face_of s` ASSUME_TAC THENL
   [SUBGOAL_THEN `t:real^N->bool = t INTER s` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(t:real^N->bool) < aff_dim(s:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &2` MP_TAC THENL
   [USE_THEN "dim" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN INT_ARITH_TAC);;

let MOI_FGB_TRI_PLH = prove
 (`!t:real^N->bool.
        &2 simplex t /\ locally_polyhedral (relative_interior t)
        ==> ?p:real^N->real^2 q.
              IMAGE p (relative_interior t) =
              relative_interior (convex hull {vec 0, basis 1, basis 2}) /\
              pl_homeomorphism
                (relative_interior t,
                 relative_interior (convex hull {vec 0, basis 1, basis 2}))
                (p,q)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `t:real^N->bool` MOI_FGB_SIMPLEX_2_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^N` (X_CHOOSE_THEN `q0:real^N`
    (X_CHOOSE_THEN `r0:real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `t = convex hull {p0, q0, r0:real^N}` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`p0:real^N`; `q0:real^N`; `r0:real^N`] MOI_FGB_TRI_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y:real^2. (l':real^N->real^2)
                 ((p0 + y$1 % (q0 - p0) + y$2 % (r0 - p0)) - p0) = y`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ARITH `(p + a + b) - p:real^N = a + b`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\w:real^N. (l':real^N->real^2) (w - p0))
          (relative_interior (convex hull {p0, q0, r0})) =
    relative_interior (convex hull {vec 0:real^2, basis 1, basis 2})`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `IMAGE (\y:real^2. p0 + y$1 % (q0 - p0) + y$2 % (r0 - p0))
            (relative_interior (convex hull {vec 0, basis 1, basis 2})) =
      relative_interior (convex hull {p0, q0, r0:real^N})` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  EXISTS_TAC `\w:real^N. (l':real^N->real^2) (w - p0)` THEN
  EXISTS_TAC `\y:real^2. p0 + y$1 % (q0 - p0) + y$2 % (r0 - p0:real^N)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!z:real^N. z IN affine hull s ==> P z`) (concl th))) THEN
      MATCH_MP_TAC(SET_RULE `!s t u x:real^N. x IN s /\ s SUBSET t /\ t SUBSET u
                                             ==> x IN u`) THEN
      EXISTS_TAC `relative_interior (convex hull {p0, q0, r0}):real^N->bool` THEN
      EXISTS_TAC `convex hull {p0, q0, r0}:real^N->bool` THEN
      ASM_REWRITE_TAC[RELATIVE_INTERIOR_SUBSET;
                      CONVEX_HULL_SUBSET_AFFINE_HULL];
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `(\w:real^N. (l':real^N->real^2) (w - p0)) = (\w. l' w - l' p0)`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[FUN_EQ_THM; LINEAR_SUB]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[MOI_FGB_AFFINE2_CONT]];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\w:real^N. (l':real^N->real^2) w + --(l' p0)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[LINEAR_SUB] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[]]]);;

let MOI_FGB_TRI_CHART = prove
 (`!c (t:real^N->bool) x.
        lf_simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
        t IN c /\ aff_dim t = &2 /\ x IN relative_interior t
        ==> ?U (p:real^N->real^2) q.
                open_in (subtopology euclidean (UNIONS c)) U /\ x IN U /\
                open (IMAGE p U) /\ pl_homeomorphism (U,IMAGE p U) (p,q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dim")
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  SUBGOAL_THEN `moi_sta_open_star c (x:real^N) = relative_interior t`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FGB_MAXIMAL_OSTAR THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FGB_MAXIMAL_DIM2 THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (UNIONS c)) (relative_interior t:real^N->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_sta_open_star c (x:real^N) = relative_interior t` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 simplex (t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPEC `t:real^N->bool` MOI_FGB_TRI_PLH) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FGB_OPEN_IN_LP THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^2` (X_CHOOSE_THEN `q:real^2->real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`relative_interior t:real^N->bool`;
                        `p:real^N->real^2`; `q:real^2->real^N`] THEN
  ASM_REWRITE_TAC[MOI_FGB_STD_TRI]);;

let MOI_FGB_UNFOLD_IMAGE = prove
 (`!p q a1 a2:real^N.
     ~affine_dependent {p,q,a1} /\ ~affine_dependent {p,q,a2} /\
     ~(p = q) /\ ~(a1 = p) /\ ~(a1 = q) /\ ~(a2 = p) /\ ~(a2 = q)
     ==> IMAGE (\y:real^2. p + y$1 % (q - p) + max (y$2) (&0) % (a1 - p) +
                           max (--(y$2)) (&0) % (a2 - p))
               {y | &0 < y$1 /\ y$1 + abs(y$2) < &1} =
         relative_interior(convex hull {p,q}) UNION
         relative_interior(convex hull {p,q,a1}) UNION
         relative_interior(convex hull {p,q,a2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `a1:real^N`] MOI_FGB_TRI_MAP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:real^N->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `a2:real^N`] MOI_FGB_TRI_MAP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:real^N->real^2` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC
   `IMAGE (\y:real^2. p + y$1 % (q - p) + y$2 % (a1 - p))
          (relative_interior (convex hull {vec 0, basis 1, basis 2})) =
    relative_interior (convex hull {p, q, a1:real^N})` THEN
  UNDISCH_TAC
   `IMAGE (\y:real^2. p + y$1 % (q - p) + y$2 % (a2 - p))
          (relative_interior (convex hull {vec 0, basis 1, basis 2})) =
    relative_interior (convex hull {p, q, a2:real^N})` THEN
  REPLICATE_TAC 2 (DISCH_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT] THEN
  ASM_SIMP_TAC[OPEN_SEGMENT_ALT; MOI_FGB_STD_RELINT] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^2`
      (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (REAL_ARITH `&0 < (y:real^2)$2 \/ (y:real^2)$2 < &0 \/ y$2 = &0`) THENL
     [DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `y:real^2` THEN
      SUBGOAL_THEN `max ((y:real^2)$2) (&0) = y$2 /\ max (--(y$2)) (&0) = &0`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN ASM_REAL_ARITH_TAC;
      DISJ2_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `vector[(y:real^2)$1; --(y$2)]:real^2` THEN
      REWRITE_TAC[VECTOR_2] THEN
      SUBGOAL_THEN `max ((y:real^2)$2) (&0) = &0 /\
                    max (--(y$2)) (&0) = --(y$2)`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN ASM_REAL_ARITH_TAC;
      DISJ1_TAC THEN EXISTS_TAC `(y:real^2)$1` THEN
      SUBGOAL_THEN `max ((y:real^2)$2) (&0) = &0 /\ max (--(y$2)) (&0) = &0`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]];
    STRIP_TAC THENL
     [EXISTS_TAC `vector[u; &0]:real^2` THEN
      ASM_REWRITE_TAC[VECTOR_2; REAL_NEG_0; REAL_MAX_ACI; REAL_ABS_0] THEN
      CONJ_TAC THENL [VECTOR_ARITH_TAC; ASM_REAL_ARITH_TAC];
      EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `max ((x:real^2)$2) (&0) = x$2 /\ max (--(x$2)) (&0) = &0`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `vector[(x:real^2)$1; --(x$2)]:real^2` THEN
      ASM_REWRITE_TAC[VECTOR_2] THEN
      SUBGOAL_THEN `max (--((x:real^2)$2)) (&0) = &0 /\
                    max (--(--(x$2))) (&0) = x$2`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN ASM_REAL_ARITH_TAC]]);;

let MOI_FGB_PL_COORD2 = prove
 (`!i. pl_map_on (:real^2) (\y:real^2. lift(--(y$i))) /\
       pl_map_on (:real^2) (\y:real^2. lift(y$i))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^2)`; `i:num`; `&0`] MOI_PTR_PL_LIFT_COORD) THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV; REAL_SUB_LZERO; REAL_SUB_RZERO]);;

let MOI_FGB_UNFOLD_PL = prove
 (`!p q a1 a2:real^N.
     pl_map_on (:real^2)
       (\y. p + y$1 % (q - p) + max (y$2) (&0) % (a1 - p) +
            max (--(y$2)) (&0) % (a2 - p))`,
  REPEAT GEN_TAC THEN
  REPEAT(MATCH_MP_TAC PL_MAP_ON_ADD THEN CONJ_TAC) THENL
   [SIMP_TAC[PL_MAP_ON_CONST; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV];
    MATCH_MP_TAC MOI_FGB_PL_SCALE_VECTOR THEN REWRITE_TAC[MOI_FGB_PL_COORD2];
    MATCH_MP_TAC MOI_FGB_PL_SCALE_VECTOR THEN
    MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN
    SIMP_TAC[MOI_FGB_PL_COORD2; MOI_PTR_PL_LIFT_CONST; LOCALLY_POLYHEDRAL_OPEN;
             OPEN_UNIV];
    MATCH_MP_TAC MOI_FGB_PL_SCALE_VECTOR THEN
    MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN
    SIMP_TAC[MOI_FGB_PL_COORD2; MOI_PTR_PL_LIFT_CONST; LOCALLY_POLYHEDRAL_OPEN;
             OPEN_UNIV]]);;

let MOI_FGB_UNFOLD_DOMAIN = prove
 (`compact {y:real^2 | &0 <= y$1 /\ abs(y$2) <= &1 - y$1} /\
   open {y:real^2 | &0 < y$1 /\ y$1 + abs(y$2) < &1} /\
   {y:real^2 | &0 < y$1 /\ y$1 + abs(y$2) < &1} SUBSET
   {y:real^2 | &0 <= y$1 /\ abs(y$2) <= &1 - y$1}`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [REWRITE_TAC[bounded; IN_ELIM_THM] THEN EXISTS_TAC `&2` THEN
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
      MP_TAC(ISPEC `y:real^2` NORM_LE_L1) THEN
      REWRITE_TAC[DIMINDEX_2; SUM_2] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN
       `{y:real^2 | &0 <= y$1 /\ abs(y$2) <= &1 - y$1} =
        {y | y$1 >= &0} INTER {y | vector[&1; &1] dot y <= &1} INTER
        {y | vector[&1; -- &1] dot y <= &1}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; DOT_2; VECTOR_2] THEN
        REAL_ARITH_TAC;
        REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
        REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE; CLOSED_HALFSPACE_LE]]];
    SUBGOAL_THEN
     `{y:real^2 | &0 < y$1 /\ y$1 + abs(y$2) < &1} =
      {y | y$1 > &0} INTER {y | vector[&1; &1] dot y < &1} INTER
      {y | vector[&1; -- &1] dot y < &1}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; DOT_2; VECTOR_2] THEN
      REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_LT]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

let MOI_FGB_SUPERSET_DIM = prove
 (`!c (e:real^N->bool) s.
        lf_simplicial_complex c /\ e IN c /\ s IN c /\ e SUBSET s /\ ~(s = e)
        ==> aff_dim e < aff_dim s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
  SUBGOAL_THEN `(e:real^N->bool) face_of s` ASSUME_TAC THENL
   [SUBGOAL_THEN `e:real^N->bool = e INTER s` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]);;

let MOI_FGB_EDGE_OSTAR = prove
 (`!c (e:real^N->bool) x p q a1 a2.
        lf_simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
        e IN c /\ aff_dim e = &1 /\ x IN relative_interior e /\
        e = convex hull {p,q} /\
        convex hull {p,q,a1} IN c /\ convex hull {p,q,a2} IN c /\
        (!tr. tr IN c /\ aff_dim tr = &2 /\ e SUBSET tr
              ==> tr = convex hull {p,q,a1} \/ tr = convex hull {p,q,a2})
        ==> moi_sta_open_star c x =
            relative_interior(convex hull {p,q}) UNION
            relative_interior(convex hull {p,q,a1}) UNION
            relative_interior(convex hull {p,q,a2})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dim")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (LABEL_TAC "tri"))))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `x:real^N`]
    MOI_FGB_OSTAR_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) SUBSET convex hull {p,q,a1} /\
                e SUBSET convex hull {p,q,a2}`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{relative_interior s | s IN c /\ (e:real^N->bool) SUBSET s} =
    {relative_interior (convex hull {p,q}), relative_interior(convex hull {p,q,a1}),
     relative_interior(convex hull {p,q,a2})}`
  SUBST1_TAC THENL
   [ALL_TAC; REWRITE_TAC[UNIONS_INSERT; UNIONS_0; UNION_EMPTY]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `s:real^N->bool = e` THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) = &2` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`;
                     `s:real^N->bool`] MOI_FGB_SUPERSET_DIM) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &2` MP_TAC THENL
       [USE_THEN "dim" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `s = convex hull {p,q,a1} \/ s = convex hull {p,q,a2:real^N}`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "tri" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    STRIP_TAC THENL
     [EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL];
      EXISTS_TAC `convex hull {p,q,a1}:real^N->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `convex hull {p,q,a2}:real^N->bool` THEN ASM_REWRITE_TAC[]]]);;

let MOI_FGB_EDGE_CHART = prove
 (`!c (e:real^N->bool) x.
        lf_simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
        e IN c /\ aff_dim e = &1 /\
        CARD {tr | tr IN c /\ aff_dim tr = &2 /\ e SUBSET tr} = 2 /\
        x IN relative_interior e
        ==> ?U (p:real^N->real^2) q.
                open_in (subtopology euclidean (UNIONS c)) U /\ x IN U /\
                open (IMAGE p U) /\ pl_homeomorphism (U,IMAGE p U) (p,q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_FGB_EDGE_DATA2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^N` (X_CHOOSE_THEN `q0:real^N`
    (X_CHOOSE_THEN `a1:real^N` (X_CHOOSE_THEN `a2:real^N`
      STRIP_ASSUME_TAC)))) THEN
  ABBREV_TAC
   `Fu = \y:real^2. p0 + y$1 % (q0 - p0) + max (y$2) (&0) % (a1 - p0) +
                    max (--(y$2)) (&0) % (a2 - p0:real^N)` THEN
  ABBREV_TAC `V = {y:real^2 | &0 < y$1 /\ y$1 + abs(y$2) < &1}` THEN
  ABBREV_TAC `D = {y:real^2 | &0 <= y$1 /\ abs(y$2) <= &1 - y$1}` THEN
  SUBGOAL_THEN `IMAGE (Fu:real^2->real^N) V = moi_sta_open_star c x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `x:real^N`;
                   `p0:real^N`; `q0:real^N`; `a1:real^N`; `a2:real^N`]
      MOI_FGB_EDGE_OSTAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MAP_EVERY EXPAND_TAC ["Fu"; "V"] THEN
    MATCH_MP_TAC MOI_FGB_UNFOLD_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN moi_sta_open_star c x` ASSUME_TAC THENL
   [REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM; IN_UNIONS] THEN
    CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    EXISTS_TAC `e:real^N->bool` THEN
    ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (D:real^2->bool) /\ open (V:real^2->bool) /\
                V SUBSET D`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "V"] THEN REWRITE_TAC[MOI_FGB_UNFOLD_DOMAIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fu:real^2->real^N) continuous_on D` ASSUME_TAC THENL
   [EXPAND_TAC "Fu" THEN REWRITE_TAC[MOI_SCF_UNFOLD_CONT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y z:real^2. y IN D /\ z IN D /\ (Fu:real^2->real^N) y = Fu z ==> y = z`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MAP_EVERY EXPAND_TAC ["D"; "Fu"] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_SCF_UNFOLD_INJ THEN
    MAP_EVERY EXISTS_TAC [`p0:real^N`; `q0:real^N`; `a1:real^N`; `a2:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`D:real^2->bool`; `Fu:real^2->real^N`;
                 `IMAGE (Fu:real^2->real^N) D`] HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^N->real^2` ASSUME_TAC) THEN
  SUBGOAL_THEN
   `homeomorphism (V,moi_sta_open_star c x) ((Fu:real^2->real^N),G)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`D:real^2->bool`; `IMAGE (Fu:real^2->real^N) D`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (Fu:real^2->real^N) V = moi_sta_open_star c x` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (V,moi_sta_open_star c x) ((Fu:real^2->real^N),G)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; LOCALLY_POLYHEDRAL_OPEN] THEN
    EXPAND_TAC "Fu" THEN REWRITE_TAC[MOI_FGB_UNFOLD_PL];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (G:real^N->real^2) (moi_sta_open_star c x) = V`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `homeomorphism (V,moi_sta_open_star c x) ((Fu:real^2->real^N),G)` THEN
    SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`moi_sta_open_star c (x:real^N)`; `G:real^N->real^2`;
                        `Fu:real^2->real^N`] THEN
  ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN] THEN
  ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]);;

let MOI_FGB_SURF_CHART = prove
 (`!c (x:real^N).
        combinatorial_manifold_with_boundary 2 c /\
        x IN UNIONS c DIFF surface_boundary c
        ==> ?U (p:real^N->real^2) q.
                open_in (subtopology euclidean (UNIONS c)) U /\ x IN U /\
                open (IMAGE p U) /\ pl_homeomorphism (U,IMAGE p U) (p,q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> aff_dim s <= &2` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FGB_CMB2_DIM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_FGB_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `aff_dim(s:real^N->bool) = &0 \/ aff_dim s = &1 \/ aff_dim s = &2`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 <= aff_dim(s:real^N->bool)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_POS_LE] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &2` MP_TAC THENL
     [ASM_MESON_TAC[]; INT_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `aff_dim(s:real^N->bool) = &0` THEN
    REWRITE_TAC[AFF_DIM_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `w:real^N = x` SUBST_ALL_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_FGB_VERTEX_CHART) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FGB_CMB2_VERTEX_INT THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^2` (X_CHOOSE_THEN `q:real^2->real^N`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`moi_sta_open_star c (x:real^N)`; `p:real^N->real^2`;
                          `q:real^2->real^N`] THEN
    ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN] THEN
    REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    MATCH_MP_TAC MOI_FGB_EDGE_CHART THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FGB_CMB2_EDGE_INT THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FGB_TRI_CHART THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FGB_CHART_RESTRICT = prove
 (`!X U W (p:real^N->real^2) q.
        open_in (subtopology euclidean X) U /\
        open_in (subtopology euclidean X) W /\
        open (IMAGE p U) /\ pl_homeomorphism (U,IMAGE p U) (p,q)
        ==> open_in (subtopology euclidean X) (U INTER W) /\
            open (IMAGE p (U INTER W)) /\
            pl_homeomorphism (U INTER W,IMAGE p (U INTER W)) (p,q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (U,IMAGE p U) ((p:real^N->real^2),q) /\
                pl_map_on U p`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean U) (U INTER W:real^N->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean X) (W:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `O:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`subtopology euclidean X:(real^N)topology`;
                   `U:real^N->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `IMAGE (p:real^N->real^2) U` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`q:real^2->real^N`; `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `IMAGE (p:real^N->real^2) U`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[INTER_SUBSET];
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN
      UNDISCH_TAC `open_in (subtopology euclidean U) (U INTER W:real^N->bool)` THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `p:real^N->real^2`]
        PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL) THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* N. Plane lemmas for the curve case: the cube bump of real^2, avoidance   *)
(* of finitely many lines, one-dimensional polyhedra as finite unions of    *)
(* segments (also with a PL function affine on each piece), and two         *)
(* segments sharing two points.                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_PL_INFNORM_2 = prove
 (`!c:real^2. pl_map_on (:real^2) (\x. lift(infnorm(x - c)))`,
  GEN_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `\x:real^2. lift(max (max (x$1 - (c:real^2)$1) (c$1 - x$1))
                                  (max (x$2 - c$2) (c$2 - x$2)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIV; INFNORM_2; VECTOR_SUB_COMPONENT; LIFT_EQ] THEN
    REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN CONJ_TAC) THEN
    SIMP_TAC[MOI_PTR_PL_LIFT_COORD; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]]);;

let MOI_FGB_BETA_PL_2 = prove
 (`!(c:real^2) r.
     pl_map_on (:real^2)
       (\x. lift(min (&1) (max (&0) (&2 - infnorm(x - c) / r))))`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MOI_PTR_PL_LIFT_MIN THEN
  SIMP_TAC[MOI_PTR_PL_LIFT_CONST; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
  MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN
  SIMP_TAC[MOI_PTR_PL_LIFT_CONST; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `\x:real^2. lift(&2) + lift(--(inv r) * infnorm(x - c))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIV; GSYM LIFT_ADD; LIFT_EQ; real_div] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC PL_MAP_ON_ADD THEN
    SIMP_TAC[MOI_PTR_PL_LIFT_CONST; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
    MATCH_MP_TAC MOI_PTR_PL_LIFT_CMUL THEN REWRITE_TAC[MOI_FGB_PL_INFNORM_2]]);;

let MOI_FGB_CUBE_2 = prove
 (`!(c:real^2) r.
     {y | infnorm(y - c) <= r} = interval[c - r % vec 1,c + r % vec 1] /\
     {y | infnorm(y - c) < r} = interval(c - r % vec 1,c + r % vec 1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_2; FORALL_2;
              INFNORM_2; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_FGB_CUBE_FACTS_2 = prove
 (`!(c:real^2) r.
     compact {y | infnorm(y - c) <= r} /\
     polytope {y | infnorm(y - c) <= r} /\
     open {y | infnorm(y - c) < r}`,
  REWRITE_TAC[MOI_FGB_CUBE_2; COMPACT_INTERVAL; POLYTOPE_INTERVAL;
              OPEN_INTERVAL]);;

let MOI_FGB_CUBE_IN_OPEN_2 = prove
 (`!(c:real^2) O.
     open O /\ c IN O ==> ?r. &0 < r /\ {y | infnorm(y - c) <= &3 * r} SUBSET O`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real^2` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / &6` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(c:real^2,e)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `c - y:real^2` NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2; dist] THEN
  UNDISCH_TAC `infnorm(y - c:real^2) <= &3 * e / &6` THEN
  REWRITE_TAC[INFNORM_2; VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC);;

let MOI_FGB_AVOID_2 = prove
 (`!fs:(real^2->bool)->bool e.
     FINITE fs /\ (!a. a IN fs ==> affine a /\ ~(a = (:real^2))) /\ &0 < e
     ==> ?d. norm d < e /\ !a. a IN fs ==> ~(d IN a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`fs:(real^2->bool)->bool`; `(:real^2)`] MOI_FGP_AVOID_AFFINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_HULL_UNIV] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `ball(vec 0:real^2,e)`) THEN
  REWRITE_TAC[AFFINE_HULL_UNIV; SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_BALL;
              BALL_EQ_EMPTY] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real^2` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(d:real^2) IN ball(vec 0,e)` THEN REWRITE_TAC[IN_BALL_0]);;

let MOI_FGB_LINE_PROPER_2 = prove
 (`!u w:real^2. affine (affine hull {u,w}) /\ ~(affine hull {u,w} = (:real^2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFFINE_AFFINE_HULL] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `{u:real^2,w}` AFF_DIM_AFFINE_HULL) THEN
  ASM_REWRITE_TAC[AFF_DIM_UNIV; DIMINDEX_2] THEN
  MP_TAC(ISPEC `{u:real^2,w}` AFF_DIM_LE_CARD) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  SUBGOAL_THEN `CARD {u:real^2,w} <= 2` MP_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
             NOT_IN_EMPTY] THEN
    COND_CASES_TAC THEN ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC]);;

let MOI_FGB_AFFINE_PREIMAGE_PROPER = prove
 (`!(a:real^2) c S.
     affine S /\ ~(S = (:real^2)) /\ ~(c = &0)
     ==> affine {d | a + c % d IN S} /\ ~({d | a + c % d IN S} = (:real^2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[affine; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`; `u:real`; `v:real`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `a + c % (u % x + v % y) =
                  u % (a + c % x) + v % (a + c % y:real^2)`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `v = &1 - u` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      UNDISCH_TAC `affine(S:real^2->bool)` THEN REWRITE_TAC[affine] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_TAC THEN UNDISCH_TAC `~(S:real^2->bool = (:real^2))` THEN
    REWRITE_TAC[EXTENSION; IN_UNIV] THEN X_GEN_TAC `z:real^2` THEN
    UNDISCH_TAC `{d | a + c % d IN S} = (:real^2)` THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `inv c % (z - a):real^2`) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
    REWRITE_TAC[VECTOR_ARITH `a + (z - a):real^N = z`]]);;

let MOI_FGB_DIM1_SEGMENTS = prove
 (`!S:real^N->bool.
     moi_ptr_dim_polyhedron 1 S
     ==> ?P. FINITE P /\ S = UNIONS P /\ !s. s IN P ==> ?a b. s = segment[a,b]`,
  GEN_TAC THEN REWRITE_TAC[moi_ptr_dim_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{k:real^N->bool | k IN u /\ ~(k = {})}` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `u:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC COMPACT_CONVEX_COLLINEAR_SEGMENT THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_CONVEX; COLLINEAR_AFF_DIM]]);;

let MOI_FGB_DIM1_COMPACT = prove
 (`!S:real^N->bool. moi_ptr_dim_polyhedron 1 S ==> compact S`,
  GEN_TAC THEN REWRITE_TAC[moi_ptr_dim_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_UNIONS THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT]);;

let MOI_FGB_AFFINE_PIECES = prove
 (`!S (f:real^M->real^N).
     moi_ptr_dim_polyhedron 1 S /\ pl_map_on S f
     ==> ?P. FINITE P /\ S = UNIONS P /\
             !s. s IN P
                 ==> (?a b. s = segment[a,b]) /\
                     ?l y. linear l /\ !z. z IN s ==> f z = l z + y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `S:real^M->bool` MOI_FGB_DIM1_SEGMENTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P0:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^M->bool`; `f:real^M->real^N`]
    MOI_PLM_PL_MAP_ON_COMPACT_FINITE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_FGB_DIM1_COMPACT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{k INTER s | k IN c /\ s IN P0 /\ ~(k INTER s:real^M->bool = {})}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(\k s:real^M->bool. k INTER s) x y |
                 x IN c /\ y IN (\x:real^M->bool. (P0:(real^M->bool)->bool)) x}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?k:real^M->bool. k IN c /\ x IN k` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^M) IN S` THEN
        UNDISCH_TAC `S:real^M->bool = UNIONS c` THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
        REWRITE_TAC[IN_UNIONS];
        ALL_TAC] THEN
      SUBGOAL_THEN `?s:real^M->bool. s IN P0 /\ x IN s` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^M) IN S` THEN
        UNDISCH_TAC `S:real^M->bool = UNIONS P0` THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
        REWRITE_TAC[IN_UNIONS];
        ALL_TAC] THEN
      EXISTS_TAC `k INTER s:real^M->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `s:real^M->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `x:real^M` THEN X_GEN_TAC `r:real^M->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^M->bool`
        (X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
      UNDISCH_TAC `(x:real^M) IN r` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      STRIP_TAC THEN
      UNDISCH_TAC `S:real^M->bool = UNIONS P0` THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `r:real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `s:real^M->bool`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONVEX_COLLINEAR_SEGMENT THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `?a b:real^M. s = segment[a,b]` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[COMPACT_INTER; CONVEX_INTER; POLYTOPE_IMP_COMPACT;
                   POLYTOPE_IMP_CONVEX; COMPACT_SEGMENT; CONVEX_SEGMENT] THEN
      MATCH_MP_TAC COLLINEAR_SUBSET THEN
      EXISTS_TAC `segment[a:real^M,b]` THEN
      REWRITE_TAC[COLLINEAR_SEGMENT; INTER_SUBSET];
      SUBGOAL_THEN `?l y. linear l /\ !z. z IN k ==> (f:real^M->real^N) z = l z + y`
      MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      SIMP_TAC[IN_INTER]]]);;

let MOI_FGB_SEGS_INF = prove
 (`!A B u w z1 z2:real^N.
     z1 IN segment[A,B] /\ z2 IN segment[A,B] /\
     z1 IN segment[u,w] /\ z2 IN segment[u,w] /\ ~(z1 = z2)
     ==> ~(u = w) /\ A IN affine hull {u,w} /\ B IN affine hull {u,w}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(u:real^N = w)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(z1:real^N = z2)` THEN
    UNDISCH_TAC `(z1:real^N) IN segment[u,w]` THEN
    UNDISCH_TAC `(z2:real^N) IN segment[u,w]` THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN segment[A,B] \/ x IN segment[u,w]
               ==> x IN affine hull {z1,z2}`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`z1:real^N`; `z2:real^N`; `x:real^N`]
      COLLINEAR_3_AFFINE_HULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MATCH_MP_TAC COLLINEAR_SUBSET THEN EXISTS_TAC `segment[A:real^N,B]` THEN
      REWRITE_TAC[COLLINEAR_SEGMENT] THEN ASM SET_TAC[];
      MATCH_MP_TAC COLLINEAR_SUBSET THEN EXISTS_TAC `segment[u:real^N,w]` THEN
      REWRITE_TAC[COLLINEAR_SEGMENT] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN affine hull {z1,z2} ==> x IN affine hull {u,w}`
  (fun th -> CONJ_TAC THEN MATCH_MP_TAC th THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
             REWRITE_TAC[ENDS_IN_SEGMENT]) THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:real^N`; `w:real^N`; `x:real^N`] COLLINEAR_3_AFFINE_HULL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC COLLINEAR_SUBSET THEN
  EXISTS_TAC `affine hull {z1:real^N,z2}` THEN CONJ_TAC THENL
   [REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
    MAP_EVERY EXISTS_TAC [`z1:real^N`; `z2:real^N`] THEN REWRITE_TAC[SUBSET_REFL];
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT]]);;

let MOI_FGB_AFFINE_SEG_IMAGE = prove
 (`!(g:real^M->real^N) l y a b.
     linear l /\ (!z. z IN segment[a,b] ==> g z = l z + y)
     ==> IMAGE g (segment[a,b]) = segment[g a,g b]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^M->real^N) a = l a + y /\ g b = l b + y`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `IMAGE (\z. (l:real^M->real^N) z + y) (segment[a,b])` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!f g s:real^M->bool. (!x. x IN s ==> (f:real^M->real^N) x = g x)
                           ==> IMAGE f s = IMAGE g s`) THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
    REWRITE_TAC[SEGMENT_TRANSLATION] THEN
    ASM_SIMP_TAC[CLOSED_SEGMENT_LINEAR_IMAGE] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF]]);;

let MOI_FGB_AFFINE_ZERO_ENDS = prove
 (`!(f:real^M->real^1) l y a b.
     linear l /\ (!z. z IN segment[a,b] ==> f z = l z + y) /\
     f a = vec 0 /\ f b = vec 0
     ==> !z. z IN segment[a,b] ==> f z = vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "aff")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(l:real^M->real^1) a = --y /\ l b = --y` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:real^M->real^1) a = l a + y /\ f b = l b + y` MP_TAC THENL
     [CONJ_TAC THEN USE_THEN "aff" MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT];
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
  USE_THEN "aff" (fun th ->
    REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^M) IN segment[a,b]`)]) THEN
  UNDISCH_TAC `(z:real^M) IN segment[a,b]` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN VECTOR_ARITH_TAC);;

let MOI_FGB_PUSH_SEG_IMAGE = prove
 (`!(phi:real^2->real) d l y a b.
     linear l /\ (!z. z IN segment[a,b] ==> lift(phi z) = l z + y)
     ==> IMAGE (\z. z + phi z % d) (segment[a,b]) =
         segment[a + phi a % d,b + phi b % d]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^2. z + phi z % (d:real^2)`;
                 `\z:real^2. z + drop((l:real^2->real^1) z) % (d:real^2)`;
                 `drop(y:real^1) % (d:real^2)`; `a:real^2`; `b:real^2`]
    MOI_FGB_AFFINE_SEG_IMAGE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN REWRITE_TAC[LINEAR_ID] THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `phi(z:real^2) = drop((l:real^2->real^1) z + y)` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LIFT_DROP];
      REWRITE_TAC[DROP_ADD] THEN VECTOR_ARITH_TAC]]);;

let MOI_FGB_DIM1_LP = prove
 (`!S:real^N->bool. moi_ptr_dim_polyhedron 1 S ==> locally_polyhedral S`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
  MATCH_MP_TAC MOI_PTR_DIM_POLYHEDRON_IMP_PL_POLYHEDRON THEN
  EXISTS_TAC `1` THEN ASM_REWRITE_TAC[]);;

let MOI_FGB_FINITE_ATMOST1 = prove
 (`!r:A->bool. (!x y. x IN r /\ y IN r ==> x = y) ==> FINITE r`,
  GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `r:A->bool = {}` THEN
  ASM_REWRITE_TAC[FINITE_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{a:A}` THEN REWRITE_TAC[FINITE_SING] THEN ASM SET_TAC[]);;

let MOI_FGB_PUSH_BAD_FIN = prove
 (`!(SA:real^2->bool) SB (phi:real^2->real) e.
     moi_ptr_dim_polyhedron 1 SA /\ moi_ptr_dim_polyhedron 1 SB /\
     pl_map_on (:real^2) (\x. lift(phi x)) /\ &0 < e
     ==> ?d. norm d < e /\
             !y. y limit_point_of (IMAGE (\z. z + phi z % d) SA INTER SB)
                 ==> phi y = &0 /\ y IN SA INTER SB /\
                     y limit_point_of (SA INTER SB)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_map_on SA (\x:real^2. lift(phi x))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; MOI_FGB_DIM1_LP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`SA:real^2->bool`; `\x:real^2. lift(phi x)`]
    MOI_FGB_AFFINE_PIECES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `PA:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?(ea:(real^2->bool)->real^2) (eb:(real^2->bool)->real^2)
     (L:(real^2->bool)->real^2->real^1) (Y:(real^2->bool)->real^1).
       !s. s IN PA
           ==> s = segment[ea s,eb s] /\ linear (L s) /\
               !z. z IN s ==> lift(phi z) = L s z + Y s`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `s:real^2->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^2->bool` o check (fun th ->
      can (term_match [] `!s:real^2->bool. s IN PA ==> P s`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `SB:real^2->bool` MOI_FGB_DIM1_SEGMENTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `PB:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?(eu:(real^2->bool)->real^2) (ew:(real^2->bool)->real^2).
       !t. t IN PB ==> t = segment[eu t,ew t]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `G = \s t. if (~(phi((ea:(real^2->bool)->real^2) s) = &0) \/
                  ~(phi((eb:(real^2->bool)->real^2) s) = &0)) /\
                 ~((eu:(real^2->bool)->real^2) t = ew t)
              then (if ~(phi(ea s) = &0)
                    then {d:real^2 | ea s + phi(ea s) % d IN
                                     affine hull {eu t, ew t}}
                    else {d:real^2 | eb s + phi(eb s) % d IN
                                     affine hull {eu t, ew t}})
              else {}` THEN
  MP_TAC(ISPECL
   [`{(G:(real^2->bool)->(real^2->bool)->real^2->bool) s t |
      s IN PA /\ t IN PB}`; `e:real`] MOI_FGB_AVOID_2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `{(G:(real^2->bool)->(real^2->bool)->real^2->bool) x y |
         x IN PA /\ y IN (\x:real^2->bool. (PB:(real^2->bool)->bool)) x}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
      REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`a:real^2->bool`; `s:real^2->bool`; `t:real^2->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC) THEN
      EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THENL
       [COND_CASES_TAC THEN
        MATCH_MP_TAC MOI_FGB_AFFINE_PREIMAGE_PROPER THEN
        ASM_REWRITE_TAC[MOI_FGB_LINE_PROPER_2] THEN ASM_MESON_TAC[];
        REWRITE_TAC[AFFINE_EMPTY] THEN MESON_TAC[UNIV_NOT_EMPTY]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "avoid"))) THEN
  EXISTS_TAC `d:real^2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s. s IN PA
        ==> IMAGE (\z:real^2. z + phi z % d) s =
            segment[(ea:(real^2->bool)->real^2) s + phi(ea s) % d,
                    (eb:(real^2->bool)->real^2) s + phi(eb s) % d]`
  (LABEL_TAC "img") THENL
   [X_GEN_TAC `s:real^2->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^2->bool` o check (fun th ->
      can (term_match [] `!s:real^2->bool. s IN PA ==> s = segment[a s,b s] /\ P s`)
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`phi:real^2->real`; `d:real^2`;
                   `(L:(real^2->bool)->real^2->real^1) s`;
                   `(Y:(real^2->bool)->real^1) s`;
                   `(ea:(real^2->bool)->real^2) s`;
                   `(eb:(real^2->bool)->real^2) s`] MOI_FGB_PUSH_SEG_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s = segment[(ea:(real^2->bool)->real^2) s,eb s]` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [ASSUME `s = segment[(ea:(real^2->bool)->real^2) s,eb s]`] THEN
        ACCEPT_TAC th)];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s z. s IN PA /\ phi((ea:(real^2->bool)->real^2) s) = &0 /\
          phi((eb:(real^2->bool)->real^2) s) = &0 /\ z IN s
          ==> phi z = &0`
  (LABEL_TAC "zero") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^2->bool` o check (fun th ->
      can (term_match [] `!s:real^2->bool. s IN PA ==> s = segment[a s,b s] /\ P s`)
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\x:real^2. lift(phi x)`; `(L:(real^2->bool)->real^2->real^1) s`;
                   `(Y:(real^2->bool)->real^1) s`;
                   `(ea:(real^2->bool)->real^2) s`;
                   `(eb:(real^2->bool)->real^2) s`] MOI_FGB_AFFINE_ZERO_ENDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LIFT_NUM] THEN
      UNDISCH_TAC `s = segment[(ea:(real^2->bool)->real^2) s,eb s]` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
    UNDISCH_TAC `s = segment[(ea:(real^2->bool)->real^2) s,eb s]` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t z1 z2. s IN PA /\ t IN PB /\
                (~(phi((ea:(real^2->bool)->real^2) s) = &0) \/
                 ~(phi((eb:(real^2->bool)->real^2) s) = &0)) /\
                z1 IN IMAGE (\z:real^2. z + phi z % d) s INTER t /\
                z2 IN IMAGE (\z:real^2. z + phi z % d) s INTER t
                ==> z1 = z2`
  (LABEL_TAC "one") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "mv") STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "img" (fun th ->
      LABEL_TAC "imgs" (MATCH_MP th (ASSUME `(s:real^2->bool) IN PA`))) THEN
    SUBGOAL_THEN `t = segment[(eu:(real^2->bool)->real^2) t,ew t]` ASSUME_TAC
    THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!z. z IN IMAGE (\z:real^2. z + phi z % d) s INTER t
          ==> z IN segment[(ea:(real^2->bool)->real^2) s + phi(ea s) % (d:real^2),
                           (eb:(real^2->bool)->real^2) s + phi(eb s) % d] /\
              z IN segment[(eu:(real^2->bool)->real^2) t,ew t]`
    ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `(z:real^2) IN IMAGE (\z:real^2. z + phi z % d) s` THEN
        USE_THEN "imgs" (fun th -> REWRITE_TAC[th]);
        UNDISCH_TAC `(z:real^2) IN t` THEN
        UNDISCH_TAC `t = segment[(eu:(real^2->bool)->real^2) t,ew t]` THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
        SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`(ea:(real^2->bool)->real^2) s + phi(ea s) % (d:real^2)`;
      `(eb:(real^2->bool)->real^2) s + phi(eb s) % (d:real^2)`;
      `(eu:(real^2->bool)->real^2) t`; `(ew:(real^2->bool)->real^2) t`;
      `z1:real^2`; `z2:real^2`] MOI_FGB_SEGS_INF) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    USE_THEN "avoid" (MP_TAC o SPEC
      `(G:(real^2->bool)->(real^2->bool)->real^2->bool) s t`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`s:real^2->bool`; `t:real^2->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "G" THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC
   `YM = UNIONS {IMAGE (\z:real^2. z + phi z % d) s INTER t | s,t |
                 s IN PA /\ t IN PB /\
                 (~(phi((ea:(real^2->bool)->real^2) s) = &0) \/
                  ~(phi((eb:(real^2->bool)->real^2) s) = &0))}` THEN
  ABBREV_TAC
   `YZ = UNIONS {s INTER t:real^2->bool | s,t | s IN PA /\ t IN PB /\
                 phi((ea:(real^2->bool)->real^2) s) = &0 /\
                 phi((eb:(real^2->bool)->real^2) s) = &0}` THEN
  SUBGOAL_THEN
   `IMAGE (\z:real^2. z + phi z % d) (UNIONS PA) INTER UNIONS PB SUBSET
    YM UNION YZ`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["YM"; "YZ"] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; IN_UNION; IN_UNIONS] THEN
    X_GEN_TAC `y:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN2
      ASSUME_TAC (X_CHOOSE_THEN `s:real^2->bool` STRIP_ASSUME_TAC)))
      (X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC
     `~(phi((ea:(real^2->bool)->real^2) s) = &0) \/
      ~(phi((eb:(real^2->bool)->real^2) s) = &0)` THENL
     [DISJ1_TAC THEN
      EXISTS_TAC `IMAGE (\z:real^2. z + phi z % d) s INTER t` THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`s:real^2->bool`; `t:real^2->bool`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_INTER; IN_IMAGE] THEN ASM_MESON_TAC[]];
      DISJ2_TAC THEN EXISTS_TAC `s INTER t:real^2->bool` THEN
      SUBGOAL_THEN `phi(z:real^2) = &0` ASSUME_TAC THENL
       [USE_THEN "zero" MATCH_MP_TAC THEN EXISTS_TAC `s:real^2->bool` THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `y:real^2 = z` SUBST_ALL_TAC THENL
       [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`s:real^2->bool`; `t:real^2->bool`] THEN
        ASM_MESON_TAC[];
        ASM_REWRITE_TAC[IN_INTER]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (YM:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "YM" THEN REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `{(\s t. IMAGE (\z:real^2. z + phi z % d) s INTER t) x y |
         x IN PA /\ y IN (\x:real^2->bool. (PB:(real^2->bool)->bool)) x}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
      REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `s:real^2->bool`; `t:real^2->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC) THEN
      MATCH_MP_TAC MOI_FGB_FINITE_ATMOST1 THEN
      MAP_EVERY X_GEN_TAC [`z1:real^2`; `z2:real^2`] THEN STRIP_TAC THEN
      USE_THEN "one" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`s:real^2->bool`; `t:real^2->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (YZ:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "YZ" THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `{(\s t:real^2->bool. s INTER t) x y |
         x IN PA /\ y IN (\x:real^2->bool. (PB:(real^2->bool)->bool)) x}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
      REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `s:real^2->bool`; `t:real^2->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC) THEN
      MATCH_MP_TAC CLOSED_INTER THEN
      ASM_MESON_TAC[CLOSED_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. y IN YZ ==> phi y = &0 /\ y IN UNIONS PA INTER UNIONS PB`
  ASSUME_TAC THENL
   [EXPAND_TAC "YZ" THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_INTER; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:real^2`; `r:real^2->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^2->bool`
      (X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC)) MP_TAC) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [USE_THEN "zero" MATCH_MP_TAC THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^2) limit_point_of YZ` ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^2) limit_point_of (YM UNION YZ)` MP_TAC THENL
     [MATCH_MP_TAC LIMPT_SUBSET THEN
      EXISTS_TAC
       `IMAGE (\z:real^2. z + phi z % d) (UNIONS PA) INTER UNIONS PB` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[LIMIT_POINT_UNION] THEN ASM_MESON_TAC[LIMIT_POINT_FINITE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^2) IN YZ` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSED_LIMPT]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC LIMPT_SUBSET THEN
  EXISTS_TAC `YZ:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]);;

let MOI_FGB_LOCAL_EDGE = prove
 (`!t (A:real^N) B z.
     simplicial_complex t /\ (!s. s IN t ==> aff_dim s <= &1) /\
     segment[A,B] IN t /\ ~(A = B) /\ z IN segment(A,B)
     ==> ?r. &0 < r /\
             UNIONS t INTER ball(z,r) =
             {z + s % (B - A) | s IN (:real)} INTER ball(z,r)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dim")
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN t /\ z IN s ==> s = segment[A,B]`
  (LABEL_TAC "only") THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `segment[A:real^N,B] SUBSET s` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s INTER segment[A:real^N,B]` THEN
      REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
      EXISTS_TAC `segment[A:real^N,B]` THEN REWRITE_TAC[SUBSET_REFL] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN
      ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `aff_dim(segment[A:real^N,B]) < aff_dim(s:real^N->bool)`
    MP_TAC THENL
     [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `segment[A:real^N,B] = segment[A,B] INTER s` SUBST1_TAC
        THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &1` MP_TAC THENL
     [USE_THEN "dim" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS {s:real^N->bool | s IN t /\ ~(z IN s)})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS {s:real^N->bool | s IN t /\ ~(z IN s)}`; `z:real^N`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "far"))) THEN
  UNDISCH_TAC `(z:real^N) IN segment(A,B)` THEN REWRITE_TAC[IN_SEGMENT] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(B - A:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ABBREV_TAC `r = min r1 (min v (&1 - v) * norm(B - A:real^N))` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN UNIONS t /\ dist(z,x) < r ==> ?s. x = z + s % (B - A)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^N) IN s` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      USE_THEN "far" (MP_TAC o SPEC `x:real^N`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        UNDISCH_TAC `dist(z:real^N,x) < r` THEN EXPAND_TAC "r" THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN segment[A,B]` MP_TAC THENL
     [USE_THEN "only" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
        (CONJ (ASSUME `(s:real^N->bool) IN t`) (ASSUME `(z:real^N) IN s`)))]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u - v:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s'. dist(z:real^N,z + s' % (B - A)) < r ==> z + s' % (B - A) IN UNIONS t`
  ASSUME_TAC THENL
   [X_GEN_TAC `s':real` THEN DISCH_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `segment[A:real^N,B]` THEN ASM_REWRITE_TAC[IN_SEGMENT] THEN
    EXISTS_TAC `v + s':real` THEN
    SUBGOAL_THEN `abs(s') * norm(B - A:real^N) < min v (&1 - v) * norm(B - A)`
    MP_TAC THENL
     [UNDISCH_TAC `dist(z:real^N,z + s' % (B - A)) < r` THEN EXPAND_TAC "r" THEN
      REWRITE_TAC[dist; VECTOR_ARITH `z - (z + s % x):real^N = --(s % x)`;
                  NORM_NEG; NORM_MUL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_UNIV; IN_BALL] THEN
  ASM_MESON_TAC[]);;

let MOI_FGB_INDEP_2D = prove
 (`!v w:real^N s t. ~collinear {vec 0, v, w} /\ s % v = t % w
                    ==> s = &0 /\ t = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~collinear {vec 0, v:real^N, w}` THEN
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `t = &0` THENL
   [UNDISCH_TAC `s % (v:real^N) = t % w` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_EQ_0];
    FIRST_X_ASSUM(MP_TAC o SPEC `s / t`) THEN
    UNDISCH_TAC `s % (v:real^N) = t % w` THEN
    DISCH_THEN(MP_TAC o AP_TERM `(%) (inv t):real^N->real^N`) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
    REWRITE_TAC[real_div] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_MUL_SYM]]);;

let MOI_FGB_PARALLEL_HULL = prove
 (`!a b u w z:real^N.
     collinear {vec 0, b - a, w - u} /\ ~(u = w) /\
     z IN segment[a,b] /\ z IN affine hull {u,w}
     ==> a IN affine hull {u,w}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `collinear {vec 0, b - a, w - u:real^N}` THEN
  REWRITE_TAC[COLLINEAR_LEMMA] THEN STRIP_TAC THENL
   [UNDISCH_TAC `(z:real^N) IN segment[a,b]` THEN
    UNDISCH_TAC `b - a:real^N = vec 0` THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SEGMENT_REFL; IN_SING] THEN
    DISCH_THEN(SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `w - u:real^N = vec 0` THEN ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `w - u:real^N = c % (b - a)` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `b - a:real^N = inv c % (w - u)` ASSUME_TAC THENL
   [UNDISCH_TAC `w - u:real^N = c % (b - a)` THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID];
    ALL_TAC] THEN
  UNDISCH_TAC `w - u:real^N = c % (b - a)` THEN DISCH_THEN(K ALL_TAC) THEN
  UNDISCH_TAC `(z:real^N) IN segment[a,b]` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(z:real^N) IN affine hull {u,w}` THEN
  REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `q:real`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`p + t / c`; `q - t / c`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a:real^N = z - t % (b - a)` SUBST1_TAC THENL
   [UNDISCH_TAC `z:real^N = (&1 - t) % a + t % b` THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBST1_TAC(ASSUME `b - a:real^N = inv c % (w - u)`) THEN
  SUBST1_TAC(ASSUME `z:real^N = p % u + q % w`) THEN
  REWRITE_TAC[real_div; VECTOR_MUL_ASSOC] THEN VECTOR_ARITH_TAC);;

let MOI_FGB_HULL_PROPER_2 = prove
 (`!t:real^2->bool.
     aff_dim t <= &1 ==> affine (affine hull t) /\ ~(affine hull t = (:real^2))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `t:real^2->bool` AFF_DIM_AFFINE_HULL) THEN
  ASM_REWRITE_TAC[AFF_DIM_UNIV; DIMINDEX_2] THEN ASM_INT_ARITH_TAC);;

let MOI_FGB_DIM1_CARRIER = prove
 (`!t (x:real^N) (ea:(real^N->bool)->real^N) eb.
     simplicial_complex t /\ (!s. s IN t ==> aff_dim s <= &1) /\
     (!s. s IN t /\ aff_dim s = &1 ==> ~(ea s = eb s) /\ s = segment[ea s,eb s]) /\
     x IN UNIONS t /\ ~({x} IN t)
     ==> ?s. s IN t /\ aff_dim s = &1 /\ x IN segment(ea s,eb s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dim")
    (CONJUNCTS_THEN2 (LABEL_TAC "ends") STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS t` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(aff_dim(s:real^N->bool) = &0)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `(x:real^N) IN {a}` THEN REWRITE_TAC[IN_SING] THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= aff_dim(s:real^N->bool)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_POS_LE] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &1` MP_TAC THENL
     [USE_THEN "dim" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "ends" (MP_TAC o SPEC `s:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[open_segment; IN_DIFF] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN s` THEN
    UNDISCH_TAC `s = segment[(ea:(real^N->bool)->real^N) s,eb s]` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  CONJ_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `~({x:real^N} IN t)` THEN REWRITE_TAC[] THEN
  (SUBGOAL_THEN `{x:real^N} face_of s` ASSUME_TAC THENL
    [REWRITE_TAC[FACE_OF_SING] THEN
     UNDISCH_TAC `s = segment[(ea:(real^N->bool)->real^N) s,eb s]` THEN
     DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
     ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT];
     ASM_MESON_TAC[]]));;

let MOI_FGB_TRANSLATE_BALL = prove
 (`!S (d:real^N) x0 r.
     IMAGE (\x. x + d) S INTER ball(x0 + d,r) =
     IMAGE (\x. x + d) (S INTER ball(x0,r))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_BALL] THEN
  MESON_TAC[NORM_ARITH `dist(x0 + d:real^N,x + d) = dist(x0,x)`]);;

let MOI_FGB_TRANSLATE_LINE = prove
 (`!(x0:real^N) d v.
     IMAGE (\x. x + d) {x0 + s % v | s IN (:real)} =
     {(x0 + d) + s % v | s IN (:real)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    EXISTS_TAC `x0 + s % v:real^N` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [VECTOR_ARITH_TAC; EXISTS_TAC `s:real` THEN REWRITE_TAC[]]]);;

let MOI_FGB_CROSS_GENERIC = prove
 (`!tA tB (ea:(real^2->bool)->real^2) eb eu ew e.
     simplicial_complex tA /\ simplicial_complex tB /\
     (!k. k IN tA ==> aff_dim k <= &1) /\ (!k. k IN tB ==> aff_dim k <= &1) /\
     &0 < e
     ==> ?d. norm d < e /\
             (!a k. {a} IN tA /\ k IN tB ==> ~(a + d IN affine hull k)) /\
             (!u k. {u} IN tB /\ k IN tA ==> ~(u - d IN affine hull k)) /\
             (!s t. s IN tA /\ t IN tB /\ aff_dim s = &1 /\ aff_dim t = &1 /\
                    collinear {vec 0, eb s - ea s, ew t - eu t}
                    ==> ~(ea s + d IN affine hull {eu t, ew t}))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "dA") (CONJUNCTS_THEN2 (LABEL_TAC "dB")
     ASSUME_TAC)))) THEN
  SUBGOAL_THEN `FINITE (tA:(real^2->bool)->bool) /\ FINITE (tB:(real^2->bool)->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^2. {x} = {y} ==> x = y` ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {a:real^2 | {a} IN tA} /\ FINITE {a:real^2 | {a} IN tB}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `G = \s t. if aff_dim(s:real^2->bool) = &1 /\ aff_dim(t:real^2->bool) = &1 /\
                 collinear {vec 0, (eb:(real^2->bool)->real^2) s - ea s,
                            (ew:(real^2->bool)->real^2) t - eu t}
              then {d:real^2 | ea s + &1 % d IN affine hull {eu t, ew t}}
              else {}` THEN
  MP_TAC(ISPECL
   [`{{d:real^2 | a + &1 % d IN affine hull k} | a,k | {a} IN tA /\ k IN tB} UNION
     {{d:real^2 | u + --(&1) % d IN affine hull k} | u,k | {u} IN tB /\ k IN tA}
     UNION {(G:(real^2->bool)->(real^2->bool)->real^2->bool) s t |
            s IN tA /\ t IN tB}`; `e:real`] MOI_FGB_AVOID_2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `{(\a k. {d:real^2 | a + &1 % d IN affine hull k}) x y |
         x IN {a:real^2 | {a} IN tA} /\
         y IN (\x:real^2. (tB:(real^2->bool)->bool)) x}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `{(\u k. {d:real^2 | u + --(&1) % d IN affine hull k}) x y |
         x IN {a:real^2 | {a} IN tB} /\
         y IN (\x:real^2. (tA:(real^2->bool)->bool)) x}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `{(G:(real^2->bool)->(real^2->bool)->real^2->bool) x y |
         x IN tA /\ y IN (\x:real^2->bool. (tB:(real^2->bool)->bool)) x}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `D:real^2->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC MOI_FGB_AFFINE_PREIMAGE_PROPER THEN
        REWRITE_TAC[REAL_OF_NUM_EQ; ARITH] THEN
        MATCH_MP_TAC MOI_FGB_HULL_PROPER_2 THEN USE_THEN "dB" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_FGB_AFFINE_PREIMAGE_PROPER THEN
        REWRITE_TAC[REAL_NEG_EQ_0; REAL_OF_NUM_EQ; ARITH] THEN
        MATCH_MP_TAC MOI_FGB_HULL_PROPER_2 THEN USE_THEN "dA" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        EXPAND_TAC "G" THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
         [MATCH_MP_TAC MOI_FGB_AFFINE_PREIMAGE_PROPER THEN
          REWRITE_TAC[REAL_OF_NUM_EQ; ARITH; MOI_FGB_LINE_PROPER_2];
          REWRITE_TAC[AFFINE_EMPTY] THEN MESON_TAC[UNIV_NOT_EMPTY]]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "avoid"))) THEN
  EXISTS_TAC `d:real^2` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^2`; `k:real^2->bool`] THEN STRIP_TAC THEN
    USE_THEN "avoid" (MP_TAC o SPEC `{d:real^2 | a + &1 % d IN affine hull k}`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`a:real^2`; `k:real^2->bool`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM; VECTOR_MUL_LID]];
    MAP_EVERY X_GEN_TAC [`u:real^2`; `k:real^2->bool`] THEN STRIP_TAC THEN
    USE_THEN "avoid"
      (MP_TAC o SPEC `{d:real^2 | u + --(&1) % d IN affine hull k}`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`u:real^2`; `k:real^2->bool`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM; VECTOR_ARITH `u + --(&1) % d:real^N = u - d`]];
    MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `t:real^2->bool`] THEN STRIP_TAC THEN
    USE_THEN "avoid"
      (MP_TAC o SPEC `(G:(real^2->bool)->(real^2->bool)->real^2->bool) s t`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`s:real^2->bool`; `t:real^2->bool`] THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "G" THEN ASM_REWRITE_TAC[IN_ELIM_THM; VECTOR_MUL_LID]]]);;

let MOI_FGB_BALL_SHRINK = prove
 (`!A B (z:real^N) r r'.
     A INTER ball(z,r) = B INTER ball(z,r) /\ r' <= r
     ==> A INTER ball(z,r') = B INTER ball(z,r')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z:real^N`; `r':real`; `r:real`] SUBSET_BALL) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FGB_CROSS_LOCAL = prove
 (`!tA tB (ea:(real^2->bool)->real^2) eb eu ew (d:real^2) z.
     simplicial_complex tA /\ simplicial_complex tB /\
     (!k. k IN tA ==> aff_dim k <= &1) /\ (!k. k IN tB ==> aff_dim k <= &1) /\
     (!s. s IN tA /\ aff_dim s = &1 ==> ~(ea s = eb s) /\ s = segment[ea s,eb s]) /\
     (!s. s IN tB /\ aff_dim s = &1 ==> ~(eu s = ew s) /\ s = segment[eu s,ew s]) /\
     (!a k. {a} IN tA /\ k IN tB ==> ~(a + d IN affine hull k)) /\
     (!u k. {u} IN tB /\ k IN tA ==> ~(u - d IN affine hull k)) /\
     (!s t. s IN tA /\ t IN tB /\ aff_dim s = &1 /\ aff_dim t = &1 /\
            collinear {vec 0, eb s - ea s, ew t - eu t}
            ==> ~(ea s + d IN affine hull {eu t, ew t})) /\
     z IN IMAGE (\x. x + d) (UNIONS tA) INTER UNIONS tB
     ==> ?r v w. &0 < r /\ ~collinear {vec 0, v, w} /\
                 IMAGE (\x. x + d) (UNIONS tA) INTER ball(z,r) =
                 {z + s % v | s IN (:real)} INTER ball(z,r) /\
                 UNIONS tB INTER ball(z,r) =
                 {z + s % w | s IN (:real)} INTER ball(z,r)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "dA") (CONJUNCTS_THEN2 (LABEL_TAC "dB")
   (CONJUNCTS_THEN2 (LABEL_TAC "eA") (CONJUNCTS_THEN2 (LABEL_TAC "eB")
   (CONJUNCTS_THEN2 (LABEL_TAC "v1") (CONJUNCTS_THEN2 (LABEL_TAC "v2")
   (CONJUNCTS_THEN2 (LABEL_TAC "v3") MP_TAC))))))))) THEN
  REWRITE_TAC[IN_INTER; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  SUBGOAL_THEN `~({x:real^2} IN tA)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(z:real^2) IN UNIONS tB` THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "v1" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `{x:real^2} IN tA`) (ASSUME `(k:real^2->bool) IN tB`)))) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN
    UNDISCH_TAC `(z:real^2) IN k` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~({z:real^2} IN tB)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(x:real^2) IN UNIONS tA` THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "v2" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `{z:real^2} IN tB`) (ASSUME `(k:real^2->bool) IN tA`)))) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(x + d) - d:real^N = x`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tA:(real^2->bool)->bool`; `x:real^2`;
                 `ea:(real^2->bool)->real^2`; `eb:(real^2->bool)->real^2`]
    MOI_FGB_DIM1_CARRIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tB:(real^2->bool)->bool`; `z:real^2`;
                 `eu:(real^2->bool)->real^2`; `ew:(real^2->bool)->real^2`]
    MOI_FGB_DIM1_CARRIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "eA" (fun th -> MP_TAC(MATCH_MP th (CONJ
    (ASSUME `(s:real^2->bool) IN tA`) (ASSUME `aff_dim(s:real^2->bool) = &1`)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
  USE_THEN "eB" (fun th -> MP_TAC(MATCH_MP th (CONJ
    (ASSUME `(t:real^2->bool) IN tB`) (ASSUME `aff_dim(t:real^2->bool) = &1`)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
  MP_TAC(ISPECL [`tA:(real^2->bool)->bool`; `(ea:(real^2->bool)->real^2) s`;
                 `(eb:(real^2->bool)->real^2) s`; `x:real^2`] MOI_FGB_LOCAL_EDGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tB:(real^2->bool)->bool`; `(eu:(real^2->bool)->real^2) t`;
                 `(ew:(real^2->bool)->real^2) t`; `z:real^2`] MOI_FGB_LOCAL_EDGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `~collinear {vec 0, (eb:(real^2->bool)->real^2) s - ea s,
                (ew:(real^2->bool)->real^2) t - eu t}`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "v3" (fun th -> MP_TAC(MATCH_MP th
     (CONJ (ASSUME `(s:real^2->bool) IN tA`) (CONJ (ASSUME `(t:real^2->bool) IN tB`)
      (CONJ (ASSUME `aff_dim(s:real^2->bool) = &1`)
      (CONJ (ASSUME `aff_dim(t:real^2->bool) = &1`)
       (ASSUME `collinear {vec 0, (eb:(real^2->bool)->real^2) s - ea s,
                           (ew:(real^2->bool)->real^2) t - eu t}`))))))) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FGB_PARALLEL_HULL THEN
    MAP_EVERY EXISTS_TAC [`(eb:(real^2->bool)->real^2) s + d`; `z:real^2`] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(b + d) - (a + d):real^N = b - a`] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN segment((ea:(real^2->bool)->real^2) s,eb s)` THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
        SEGMENT_OPEN_SUBSET_CLOSED)) THEN
      REWRITE_TAC[IN_SEGMENT] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] SEGMENT_OPEN_SUBSET_CLOSED) THEN
      UNDISCH_TAC `(z:real^2) IN segment((eu:(real^2->bool)->real^2) t,ew t)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`min r1 r2:real`; `(eb:(real^2->bool)->real^2) s - ea s`;
    `(ew:(real^2->bool)->real^2) t - eu t`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FGB_BALL_SHRINK THEN EXISTS_TAC `r1:real` THEN
    REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
    UNDISCH_TAC
     `UNIONS tA INTER ball(x:real^2,r1) =
      {x + s' % ((eb:(real^2->bool)->real^2) s - ea s) | s' IN (:real)} INTER
      ball(x,r1)` THEN
    DISCH_THEN(MP_TAC o AP_TERM `IMAGE (\x:real^2. x + d)`) THEN
    REWRITE_TAC[GSYM MOI_FGB_TRANSLATE_BALL; MOI_FGB_TRANSLATE_LINE] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FGB_BALL_SHRINK THEN EXISTS_TAC `r2:real` THEN
    REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
    UNDISCH_TAC
     `UNIONS tB INTER ball(z:real^2,r2) =
      {z + s % ((ew:(real^2->bool)->real^2) t - eu t) | s IN (:real)} INTER
      ball(z,r2)` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FGB_LOCAL_ISOLATED = prove
 (`!Z:real^N->bool.
     compact Z /\ (!z. z IN Z ==> ?r. &0 < r /\ Z INTER ball(z,r) SUBSET {z})
     ==> FINITE Z`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Z:real^N->bool`; `Z:real^N->bool`] DISCRETE_EQ_FINITE_COMPACT) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(z:real^N) limit_point_of Z` THEN
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `Z INTER ball(z:real^N,r) SUBSET {z}` THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_SING] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]);;

let MOI_FGB_TWO_LINES = prove
 (`!A B (z:real^N) r v w.
     ~collinear {vec 0, v, w} /\
     A INTER ball(z,r) = {z + s % v | s IN (:real)} INTER ball(z,r) /\
     B INTER ball(z,r) = {z + s % w | s IN (:real)} INTER ball(z,r)
     ==> A INTER B INTER ball(z,r) SUBSET {z}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_SING] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN {z + s % v | s IN (:real)} INTER ball(z,r) /\
                y IN {z + s % w | s IN (:real)} INTER ball(z,r)`
  MP_TAC THENL
   [UNDISCH_TAC `A INTER ball(z:real^N,r) =
                 {z + s % v | s IN (:real)} INTER ball(z,r)` THEN
    UNDISCH_TAC `B INTER ball(z:real^N,r) =
                 {z + s % w | s IN (:real)} INTER ball(z,r)` THEN
    REPLICATE_TAC 2 (DISCH_THEN(SUBST1_TAC o SYM)) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `a:real` ASSUME_TAC) ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:real` ASSUME_TAC) ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`v:real^N`; `w:real^N`; `a:real`; `b:real`] MOI_FGB_INDEP_2D) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `y:real^N = z + a % v` THEN UNDISCH_TAC `y:real^N = z + b % w` THEN
    VECTOR_ARITH_TAC;
    STRIP_TAC THEN UNDISCH_TAC `y:real^N = z + a % v` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID]]);;

let MOI_FGB_CROSS_FIN = prove
 (`!(SA:real^2->bool) SB e.
     moi_ptr_dim_polyhedron 1 SA /\ moi_ptr_dim_polyhedron 1 SB /\ &0 < e
     ==> ?d. norm d < e /\
             FINITE (IMAGE (\x. x + d) SA INTER SB) /\
             !z. z IN IMAGE (\x. x + d) SA INTER SB
                 ==> ?r v w. &0 < r /\ ~collinear {vec 0, v, w} /\
                             IMAGE (\x. x + d) SA INTER ball(z,r) =
                             {z + s % v | s IN (:real)} INTER ball(z,r) /\
                             SB INTER ball(z,r) =
                             {z + s % w | s IN (:real)} INTER ball(z,r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact(SA:real^2->bool) /\ compact(SB:real^2->bool)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FGB_DIM1_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `SA:real^2->bool`] MOI_PTR_DIM_POLYHEDRON_TRIANGULATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tA:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`1`; `SB:real^2->bool`] MOI_PTR_DIM_POLYHEDRON_TRIANGULATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tB:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `UNIONS tA = (SA:real^2->bool)` THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `UNIONS tB = (SB:real^2->bool)` THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN
   `?(ea:(real^2->bool)->real^2) eb.
      !s. s IN tA /\ aff_dim s = &1 ==> ~(ea s = eb s) /\ s = segment[ea s,eb s]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `s:real^2->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tA:(real^2->bool)->bool`; `s:real^2->bool`] MOI_SCF_EDGE) THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?(eu:(real^2->bool)->real^2) ew.
      !s. s IN tB /\ aff_dim s = &1 ==> ~(eu s = ew s) /\ s = segment[eu s,ew s]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `s:real^2->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tB:(real^2->bool)->bool`; `s:real^2->bool`] MOI_SCF_EDGE) THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tA:(real^2->bool)->bool`; `tB:(real^2->bool)->bool`;
                 `ea:(real^2->bool)->real^2`; `eb:(real^2->bool)->real^2`;
                 `eu:(real^2->bool)->real^2`; `ew:(real^2->bool)->real^2`;
                 `e:real`] MOI_FGB_CROSS_GENERIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real^2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (\x. x + d) (UNIONS tA) INTER UNIONS tB
        ==> ?r v w. &0 < r /\ ~collinear {vec 0, v, w} /\
                    IMAGE (\x. x + d) (UNIONS tA) INTER ball(z,r) =
                    {z + s % v | s IN (:real)} INTER ball(z,r) /\
                    UNIONS tB INTER ball(z,r) =
                    {z + s % w | s IN (:real)} INTER ball(z,r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FGB_CROSS_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`ea:(real^2->bool)->real^2`; `eb:(real^2->bool)->real^2`;
                          `eu:(real^2->bool)->real^2`; `ew:(real^2->bool)->real^2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MATCH_MP_TAC MOI_FGB_LOCAL_ISOLATED THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_INTER THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN ASM_SIMP_TAC[COMPACT_TRANSLATION];
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `v:real^2`
      (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INTER_ASSOC] THEN
    MATCH_MP_TAC MOI_FGB_TWO_LINES THEN
    MAP_EVERY EXISTS_TAC [`v:real^2`; `w:real^2`] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* O. Chart pushes on the surface: one-dimensional slices through a chart, *)
(* limit points under injective continuous maps, and gluing a PLH of the    *)
(* plane supported in a compact subset of a chart image into a PLH of the   *)
(* surface (identity off the chart).                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_POLYTOPE_PL = prove
 (`!C:real^N->bool. polytope C ==> pl_polyhedron C`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{C:real^N->bool}` THEN
  REWRITE_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN
  GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_FGB_DIM1_INTER_PL = prove
 (`!J Q:real^N->bool.
     moi_ptr_dim_polyhedron 1 J /\ pl_polyhedron Q
     ==> moi_ptr_dim_polyhedron 1 (J INTER Q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ptr_dim_polyhedron; pl_polyhedron] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `u:(real^N->bool)->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `v:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `{k INTER k':real^N->bool | k IN u /\ k' IN v}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(\k k':real^N->bool. k INTER k') x y |
                 x IN u /\ y IN (\x:real^N->bool. (v:(real^N->bool)->bool)) x}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `r:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `k':real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(k:real^N->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC AFF_DIM_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
      ASM_MESON_TAC[]];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `t1:real^N->bool` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `t2:real^N->bool` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `t1 INTER t2:real^N->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      MAP_EVERY EXISTS_TAC [`t1:real^N->bool`; `t2:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `k':real^N->bool`
          STRIP_ASSUME_TAC)) MP_TAC)) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `k':real^N->bool` THEN ASM_REWRITE_TAC[]]]]);;

let MOI_FGB_CHART_SLICE = prove
 (`!(J:real^N->bool) U (p:real^N->real^2) q C.
     moi_ptr_dim_polyhedron 1 J /\
     pl_homeomorphism (U,IMAGE p U) (p,q) /\
     polytope C /\ C SUBSET IMAGE p U
     ==> moi_ptr_dim_polyhedron 1 (IMAGE p (J INTER U) INTER C)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (U,IMAGE p U) ((p:real^N->real^2),q) /\
                pl_map_on U p /\ pl_map_on (IMAGE p U) q`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN U ==> (q:real^2->real^N) ((p:real^N->real^2) x) = x) /\
    (!y. y IN IMAGE p U ==> p (q y) = y) /\
    IMAGE q (IMAGE p U) = U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (U,IMAGE p U) ((p:real^N->real^2),q)` THEN
    SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (IMAGE (q:real^2->real^N) C)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_SIMP_TAC[MOI_FGB_POLYTOPE_PL] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `IMAGE (p:real^N->real^2) U` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p:real^N->real^2) (J INTER U) INTER C =
    IMAGE p (J INTER IMAGE (q:real^2->real^N) C)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `y:real^2` THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y':real^2`
          STRIP_ASSUME_TAC)))) THEN
      SUBGOAL_THEN `(y':real^2) IN IMAGE (p:real^N->real^2) U` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^N) IN U` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PTR_DIM_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FGB_DIM1_INTER_PL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!a b c:real^N->bool. b SUBSET c ==> a INTER b SUBSET c`) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_PTR_DIM_POLYHEDRON_IMP_PL_POLYHEDRON THEN
    EXISTS_TAC `1` THEN MATCH_MP_TAC MOI_FGB_DIM1_INTER_PL THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FGB_LIMPT_IMAGE = prove
 (`!(f:real^M->real^N) U S x.
     f continuous_on U /\ (!x y. x IN U /\ y IN U /\ f x = f y ==> x = y) /\
     S SUBSET U /\ x IN U /\ x limit_point_of S
     ==> f x limit_point_of IMAGE f S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC `(f:real^M->real^N) continuous_on U` THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^M) limit_point_of S` THEN
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:real^M->real^N) y` THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[SUBSET];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MOI_FGB_GLUE_PUSH = prove
 (`!X U (p:real^N->real^2) q (P:real^2->real^2) P' C.
     locally_polyhedral X /\ open_in (subtopology euclidean X) U /\
     pl_homeomorphism (U,IMAGE p U) (p,q) /\
     pl_homeomorphism ((:real^2),(:real^2)) (P,P') /\
     compact C /\ C SUBSET IMAGE p U /\ (!y. ~(y IN C) ==> P y = y)
     ==> pl_homeomorphism (X,X) ((\x. if x IN U then q(P(p x)) else x),
                                (\x. if x IN U then q(P'(p x)) else x)) /\
         (!x. x IN X /\ ~(x IN IMAGE q C)
              ==> (if x IN U then q(P(p x)) else x) = x) /\
         (!x. x IN IMAGE q C ==> (if x IN U then q(P(p x)) else x) IN IMAGE q C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (U,IMAGE p U) ((p:real^N->real^2),q) /\
                pl_map_on U p /\ pl_map_on (IMAGE p U) q`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN U ==> (q:real^2->real^N) ((p:real^N->real^2) x) = x) /\
    (!y. y IN IMAGE p U ==> p (q y) = y) /\ IMAGE q (IMAGE p U) = U /\
    p continuous_on U /\ q continuous_on IMAGE p U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (U,IMAGE p U) ((p:real^N->real^2),q)` THEN
    SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y:real^2. P' ((P:real^2->real^2) y) = y) /\ (!y. P (P' y) = y) /\
    P continuous_on (:real^2) /\ P' continuous_on (:real^2) /\
    pl_map_on (:real^2) P`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism ((:real^2),(:real^2))
                   ((P:real^2->real^2),(P':real^2->real^2))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. ~(y IN C) ==> P' y = y` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(P:real^2->real^2) y = y` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. y IN C ==> P y IN C /\ P' y IN C` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THENL
     [SUBGOAL_THEN `(P:real^2->real^2) (P y) = P y` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `P':real^2->real^2`) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `(P':real^2->real^2) (P' y) = P' y` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `P:real^2->real^2`) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. y IN IMAGE p U ==> P y IN IMAGE (p:real^N->real^2) U /\
                                  P' y IN IMAGE p U`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `(y:real^2) IN C` THENL
     [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (q:real^2->real^N) C)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (q:real^2->real^N) C SUBSET U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `H = \x:real^N. if x IN U then (q:real^2->real^N)((P:real^2->real^2)((p:real^N->real^2) x)) else x` THEN
  ABBREV_TAC `G = \x:real^N. if x IN U then (q:real^2->real^N)((P':real^2->real^2)((p:real^N->real^2) x)) else x` THEN
  SUBGOAL_THEN
   `(!x. x IN X /\ ~(x IN IMAGE (q:real^2->real^N) C) ==> (H:real^N->real^N) x = x) /\
    (!x. x IN X /\ ~(x IN IMAGE (q:real^2->real^N) C) ==> (G:real^N->real^N) x = x)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["H"; "G"] THEN REWRITE_TAC[] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    (SUBGOAL_THEN `~((p:real^N->real^2) x IN C)` ASSUME_TAC THENL
      [DISCH_TAC THEN UNDISCH_TAC `~((x:real^N) IN IMAGE (q:real^2->real^N) C)` THEN
       REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(p:real^N->real^2) x` THEN
       ASM_SIMP_TAC[];
       ASM_SIMP_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN U ==> (H:real^N->real^N) x IN U /\ G x IN U) /\
    (!x. x IN X /\ ~(x IN U) ==> H x = x /\ G x = x)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["H"; "G"] THEN SIMP_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^N->real^2) x IN IMAGE p U` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN X ==> (G:real^N->real^N) ((H:real^N->real^N) x) = x /\ H (G x) = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_CASES_TAC `(x:real^N) IN U` THENL
     [ALL_TAC; ASM_SIMP_TAC[]] THEN
    SUBGOAL_THEN `(p:real^N->real^2) x IN IMAGE p U` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["H"; "G"] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(q:real^2->real^N) ((P:real^2->real^2) ((p:real^N->real^2) x)) IN U /\
      q ((P':real^2->real^2) (p x)) IN U`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(q:real^2->real^N) o (P:real^2->real^2) o (p:real^N->real^2)
      continuous_on U /\
    q o (P':real^2->real^2) o p continuous_on U`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV] THEN NO_TAC) THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (p:real^N->real^2) U` THEN ASM_REWRITE_TAC[IMAGE_o] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(H:real^N->real^N) continuous_on X /\ (G:real^N->real^N) continuous_on X`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `X = (U:real^N->bool) UNION (X DIFF IMAGE (q:real^2->real^N) C)` SUBST1_TAC
    THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `open_in (subtopology euclidean (U UNION (X DIFF IMAGE (q:real^2->real^N) C))) (U:real^N->bool) /\
      open_in (subtopology euclidean (U UNION (X DIFF IMAGE (q:real^2->real^N) C)))
              (X DIFF IMAGE (q:real^2->real^N) C)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(U:real^N->bool) UNION (X DIFF IMAGE (q:real^2->real^N) C) = X`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
      REWRITE_TAC[OPEN_IN_REFL] THEN
      MATCH_MP_TAC CLOSED_SUBSET THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL_OPEN THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `(q:real^2->real^N) o (P:real^2->real^2) o (p:real^N->real^2)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "H" THEN SIMP_TAC[o_THM];
      MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `\x:real^N. x` THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; IN_DIFF] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `(q:real^2->real^N) o (P':real^2->real^2) o (p:real^N->real^2)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN SIMP_TAC[o_THM];
      MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `\x:real^N. x` THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; IN_DIFF] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on X (H:real^N->real^N)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_MAP_ON_LOCAL] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^N) IN U` THENL
     [UNDISCH_TAC `open_in (subtopology euclidean X) (U:real^N->bool)` THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `O:real^N->bool` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `U:real^N->bool`)) THEN
      MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `(q:real^2->real^N) o (P:real^2->real^2) o (p:real^N->real^2)` THEN
      CONJ_TAC THENL [EXPAND_TAC "H" THEN SIMP_TAC[o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
      EXISTS_TAC `IMAGE (p:real^N->real^2) U` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[]];
      EXISTS_TAC `(:real^N) DIFF IMAGE (q:real^2->real^N) C` THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\x:real^N. x` THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV] THEN ASM_MESON_TAC[];
        REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
        MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
        ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (if x IN U then (q:real^2->real^N)((P:real^2->real^2)((p:real^N->real^2) x))
         else x) = (H:real^N->real^N) x`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN X ==> (H:real^N->real^N) x IN X /\ (G:real^N->real^N) x IN X`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^N) IN U` THENL
     [SUBGOAL_THEN `(H:real^N->real^N) x IN U /\ (G:real^N->real^N) x IN U`
      MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(U:real^N->bool) SUBSET X` THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[homeomorphism] THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MAP_EVERY (fun t -> TRY(EXISTS_TAC t THEN ASM_SIMP_TAC[] THEN NO_TAC))
     [`(G:real^N->real^N) x`; `(H:real^N->real^N) x`];
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN IMAGE (p:real^N->real^2) U` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^2->real^N) y IN U` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "H" THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(P:real^2->real^2) y` THEN
    ASM_SIMP_TAC[]]);;

(* The plane cube bump: 1 on the cube of radius r about c, 0 off the cube  *)
(* of radius 2 r, Lipschitz with constant 1/r.                              *)

let moi_fgb_bump = new_definition
 `moi_fgb_bump (c:real^2) r (y:real^2) =
    min (&1) (max (&0) (&2 - infnorm(y - c) / r))`;;

let MOI_FGB_BUMP2 = prove
 (`!(c:real^2) r.
     &0 < r
     ==> pl_map_on (:real^2) (\y. lift(moi_fgb_bump c r y)) /\
         (!y. &0 <= moi_fgb_bump c r y /\ moi_fgb_bump c r y <= &1) /\
         (!y y'. abs(moi_fgb_bump c r y - moi_fgb_bump c r y') <=
                 norm(y - y') / r) /\
         (!y. infnorm(y - c) <= r ==> moi_fgb_bump c r y = &1) /\
         (!y. ~(y IN {y | infnorm(y - c) <= &2 * r}) ==> moi_fgb_bump c r y = &0) /\
         (!y. &0 < moi_fgb_bump c r y <=> infnorm(y - c) < &2 * r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_fgb_bump; IN_ELIM_THM] THEN
  REWRITE_TAC[MOI_FGB_BETA_PL_2] THEN
  ASM_SIMP_TAC[MOI_FGB_BETA_LIPSCHITZ] THEN
  SUBGOAL_THEN `!y:real^2. infnorm(y - c) / r <= &1 <=> infnorm(y - c) <= r`
  (fun th -> REWRITE_TAC[GSYM th]) THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. infnorm(y - c) < &2 * r <=> infnorm(y - c) / r < &2`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. infnorm(y - c) <= &2 * r <=> infnorm(y - c) / r <= &2`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let MOI_FGB_FIX_OUTSIDE = prove
 (`!(P:real^N->real^N) P' C.
     (!y. P' (P y) = y) /\ (!y. P (P' y) = y) /\ (!y. ~(y IN C) ==> P y = y)
     ==> (!y. y IN C ==> P y IN C) /\ (!y. ~(y IN C) ==> P' y = y) /\
         (!y. y IN C ==> P' y IN C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^N. ~(y IN C) ==> P' y = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_FGB_LIMPT_LOCAL = prove
 (`!(x:real^N) s t. x limit_point_of s /\ open t /\ x IN t
                    ==> x limit_point_of (s INTER t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^N) limit_point_of s` THEN
  REWRITE_TAC[LIMPT_APPROACHABLE; IN_INTER] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min e r`) THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ball(x:real^N,r) SUBSET t` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]);;

let MOI_FGB_UNIF_DELTA = prove
 (`!(q:real^2->real^N) C e.
     q continuous_on C /\ compact C /\ &0 < e
     ==> ?del. &0 < del /\
               !y y'. y IN C /\ y' IN C /\ norm(y' - y) < del
                      ==> dist(q y',q y) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`q:real^2->real^N`; `C:real^2->bool`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[dist] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* P. One generic chart push on the surface (phase 1): every limit point of *)
(* the new intersection is an old one outside the open push region.        *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_CHART_FACTS = prove
 (`!U (p:real^N->real^2) q.
     pl_homeomorphism (U,IMAGE p U) (p,q)
     ==> (!x. x IN U ==> q (p x) = x) /\
         (!y. y IN IMAGE p U ==> p (q y) = y) /\
         IMAGE q (IMAGE p U) = U /\
         p continuous_on U /\ q continuous_on IMAGE p U /\
         (!x y. x IN U /\ y IN U /\ p x = p y ==> x = y) /\
         (!x y. x IN IMAGE p U /\ y IN IMAGE p U /\ q x = q y ==> x = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_FGB_CHART_PUSH_IMAGE = prove
 (`!X (J:real^N->bool) U (p:real^N->real^2) q (P:real^2->real^2) H.
     J SUBSET X /\ U SUBSET X /\
     pl_homeomorphism (U,IMAGE p U) (p,q) /\
     (!y. y IN IMAGE p U ==> P y IN IMAGE p U) /\
     (!x. x IN U ==> H x = q(P(p x))) /\ (!x. x IN X /\ ~(x IN U) ==> H x = x)
     ==> IMAGE p (IMAGE H J INTER U) = IMAGE P (IMAGE p (J INTER U))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "PU")
   (CONJUNCTS_THEN2 (LABEL_TAC "HU") (LABEL_TAC "HX")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FGB_CHART_FACTS) THEN
  SUBGOAL_THEN `!z:real^N. z IN U ==> (p:real^N->real^2) z IN IMAGE p U`
  ASSUME_TAC THENL [MESON_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. y IN IMAGE p U ==> (q:real^2->real^N) y IN U`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (q:real^2->real^N) (IMAGE p U) = U` THEN
    MESON_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN X_GEN_TAC `y:real^2` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^N` (CONJUNCTS_THEN2 SUBST1_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)
       ASSUME_TAC))) THEN
    SUBGOAL_THEN `(z:real^N) IN X` ASSUME_TAC THENL
     [UNDISCH_TAC `(J:real^N->bool) SUBSET X` THEN
      UNDISCH_TAC `(z:real^N) IN J` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN U` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `(H:real^N->real^N) z = z` ASSUME_TAC THENL
       [USE_THEN "HX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(w:real^N) IN U` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `(p:real^N->real^2) z` THEN CONJ_TAC THENL
     [UNDISCH_TAC `w = (H:real^N->real^N) z` THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "HU" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(z:real^N) IN U`)]) THEN
      SUBGOAL_THEN `(P:real^2->real^2) ((p:real^N->real^2) z) IN IMAGE p U`
      ASSUME_TAC THENL
       [USE_THEN "PU" MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `a:real^2` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(P:real^2->real^2) ((p:real^N->real^2) z) IN IMAGE p U`
    ASSUME_TAC THENL
     [USE_THEN "PU" MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `(q:real^2->real^N) ((P:real^2->real^2) ((p:real^N->real^2) z))` THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `z:real^N` THEN ASM_SIMP_TAC[]]);;

let MOI_FGB_LIMPT_OUTSIDE = prove
 (`!X (J:real^N->bool) K H Q x.
     J SUBSET X /\ (!z. z IN X /\ ~(z IN Q) ==> H z = z) /\
     (!z. z IN Q ==> H z IN Q) /\ closed Q /\ ~(x IN Q) /\
     x limit_point_of (IMAGE H J INTER K)
     ==> x limit_point_of (J INTER K)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `IMAGE (H:real^N->real^N) J INTER K`;
                 `(:real^N) DIFF Q`] MOI_FGB_LIMPT_LOCAL) THEN
  ASM_REWRITE_TAC[GSYM closed; IN_DIFF; IN_UNIV] THEN
  DISCH_TAC THEN MATCH_MP_TAC LIMPT_SUBSET THEN
  EXISTS_TAC `(IMAGE (H:real^N->real^N) J INTER K) INTER ((:real^N) DIFF Q)` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_UNIV; IN_IMAGE] THEN
  X_GEN_TAC `w:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) ASSUME_TAC) ASSUME_TAC) THEN
  SUBGOAL_THEN `~((z:real^N) IN Q)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((w:real^N) IN Q)` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(H:real^N->real^N) z = z` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!z:real^N. z IN X /\ ~(z IN Q) ==> H z = z`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_FGB_CUBES_2 = prove
 (`!(y0:real^2) rho.
     &0 < rho
     ==> compact {y:real^2 | infnorm(y - y0) <= &2 * rho} /\
         polytope {y:real^2 | infnorm(y - y0) <= &3 * rho} /\
         open {y:real^2 | infnorm(y - y0) < &3 * rho} /\
         open {y:real^2 | infnorm(y - y0) < &2 * rho} /\
         {y:real^2 | infnorm(y - y0) <= &2 * rho} SUBSET
         {y | infnorm(y - y0) < &3 * rho} /\
         {y:real^2 | infnorm(y - y0) < &3 * rho} SUBSET
         {y | infnorm(y - y0) <= &3 * rho} /\
         {y:real^2 | infnorm(y - y0) < &2 * rho} SUBSET
         {y | infnorm(y - y0) <= &2 * rho}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MOI_FGB_CUBE_FACTS_2] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_FGB_PHASE1_STEP = prove
 (`!X (J:real^N->bool) K U (p:real^N->real^2) q (y0:real^2) rho e.
     locally_polyhedral X /\ moi_ptr_dim_polyhedron 1 J /\
     moi_ptr_dim_polyhedron 1 K /\ J SUBSET X /\ K SUBSET X /\
     open_in (subtopology euclidean X) U /\
     pl_homeomorphism (U,IMAGE p U) (p,q) /\
     &0 < rho /\ {y | infnorm(y - y0) <= &3 * rho} SUBSET IMAGE p U /\ &0 < e
     ==> ?H G. pl_homeomorphism (X,X) (H,G) /\
               (!x. x IN X /\ ~(x IN U) ==> H x = x) /\
               (!x. x IN X ==> dist(H x,x) < e) /\
               !x. x limit_point_of (IMAGE H J INTER K)
                   ==> x IN J INTER K /\ x limit_point_of (J INTER K) /\
                       ~(x IN IMAGE q {y | infnorm(y - y0) < &2 * rho})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FGB_CHART_FACTS) THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(J:real^N->bool) /\ compact(K:real^N->bool)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FGB_DIM1_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`y0:real^2`; `rho:real`] MOI_FGB_BUMP2) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `phi = moi_fgb_bump y0 rho` THEN
  MP_TAC(ISPECL [`y0:real^2`; `rho:real`] MOI_FGB_CUBES_2) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `{y:real^2 | infnorm(y - y0) <= &3 * rho} SUBSET IMAGE (p:real^N->real^2) U` THEN
  ABBREV_TAC `C = {y:real^2 | infnorm(y - y0) <= &2 * rho}` THEN
  ABBREV_TAC `C' = {y:real^2 | infnorm(y - y0) <= &3 * rho}` THEN
  ABBREV_TAC `O' = {y:real^2 | infnorm(y - y0) < &3 * rho}` THEN
  ABBREV_TAC `C0 = {y:real^2 | infnorm(y - y0) < &2 * rho}` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(C:real^2->bool) SUBSET IMAGE (p:real^N->real^2) U /\
                (C0:real^2->bool) SUBSET C`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(C':real^2->bool) SUBSET IMAGE (p:real^N->real^2) U` THEN
    UNDISCH_TAC `(C:real^2->bool) SUBSET O'` THEN
    UNDISCH_TAC `(O':real^2->bool) SUBSET C'` THEN
    UNDISCH_TAC `(C0:real^2->bool) SUBSET C` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ptr_dim_polyhedron 1 (IMAGE (p:real^N->real^2) (J INTER U) INTER C') /\
    moi_ptr_dim_polyhedron 1 (IMAGE (p:real^N->real^2) (K INTER U) INTER C')`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FGB_CHART_SLICE THEN
    EXISTS_TAC `q:real^2->real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^2->real^N`; `C:real^2->bool`; `e:real`]
    MOI_FGB_UNIF_DELTA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (p:real^N->real^2) U` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `del:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "unif")))] THEN
  MP_TAC(ISPECL [`IMAGE (p:real^N->real^2) (J INTER U) INTER C'`;
                 `IMAGE (p:real^N->real^2) (K INTER U) INTER C'`;
                 `phi:real^2->real`; `min del rho`] MOI_FGB_PUSH_BAD_FIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "bad"))) THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `rho:real`; `d:real^2`] MOI_FGB_PUSH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `norm(d:real^2) < min del rho` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P':real^2->real^2` MP_TAC) THEN
  ABBREV_TAC `P = \y:real^2. y + phi y % d` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(!y:real^2. P' ((P:real^2->real^2) y) = y) /\ (!y. P (P' y) = y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism ((:real^2),(:real^2))
                   ((P:real^2->real^2),(P':real^2->real^2))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. ~(y IN C) ==> (P:real^2->real^2) y = y` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN EXPAND_TAC "P" THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:real^2->real^2`; `P':real^2->real^2`; `C:real^2->bool`]
    MOI_FGB_FIX_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y:real^2. y IN IMAGE (p:real^N->real^2) U ==> (P:real^2->real^2) y IN IMAGE (p:real^N->real^2) U`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^2) IN C` THENL
     [UNDISCH_TAC `(C:real^2->bool) SUBSET IMAGE (p:real^N->real^2) U` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `U:real^N->bool`; `p:real^N->real^2`;
                 `q:real^2->real^N`; `P:real^2->real^2`; `P':real^2->real^2`;
                 `C:real^2->bool`] MOI_FGB_GLUE_PUSH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `H = \x:real^N. if x IN U then (q:real^2->real^N)((P:real^2->real^2)
                    ((p:real^N->real^2) x)) else x` THEN
  ABBREV_TAC
   `G = \x:real^N. if x IN U then (q:real^2->real^N)((P':real^2->real^2)
                    ((p:real^N->real^2) x)) else x` THEN
  SUBGOAL_THEN
   `!x:real^N. (if x IN U then (q:real^2->real^N)((P:real^2->real^2)
                 ((p:real^N->real^2) x)) else x) = H x`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^N. x IN U ==> (H:real^N->real^N) x =
                 (q:real^2->real^N)((P:real^2->real^2)((p:real^N->real^2) x))`
  ASSUME_TAC THENL [EXPAND_TAC "H" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN X /\ ~(x IN U) ==> (H:real^N->real^N) x = x`
  ASSUME_TAC THENL [EXPAND_TAC "H" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (H:real^N->real^N) X = X` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (X,X) ((H:real^N->real^N),(G:real^N->real^N))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  EXISTS_TAC `H:real^N->real^N` THEN EXISTS_TAC `G:real^N->real^N` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^N) IN U` THENL
     [ALL_TAC; ASM_SIMP_TAC[DIST_REFL]] THEN
    ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `(p:real^N->real^2) x IN C` THENL
     [SUBGOAL_THEN `x:real^N = q((p:real^N->real^2) x)`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      USE_THEN "unif" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
      EXPAND_TAC "P" THEN
      REWRITE_TAC[VECTOR_ARITH `(y + a % d) - y:real^N = a % d`; NORM_MUL] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(d:real^2)` THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^N->real^2) x` o check (fun th ->
          can (term_match [] `!y:real^2. &0 <= f y /\ f y <= &1`) (concl th))) THEN
        REAL_ARITH_TAC;
        UNDISCH_TAC `norm(d:real^2) < min del rho` THEN REAL_ARITH_TAC];
      ASM_SIMP_TAC[DIST_REFL]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `closed(J INTER K:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `x limit_point_of (J INTER K:real^N->bool) /\
    ~(x IN IMAGE (q:real^2->real^N) C0)`
  (fun th -> ASM_MESON_TAC[th; CLOSED_LIMPT]) THEN
  SUBGOAL_THEN `compact(IMAGE (q:real^2->real^N) C)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (p:real^N->real^2) U` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^N) IN IMAGE (q:real^2->real^N) C` THENL
   [ALL_TAC;
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FGB_LIMPT_OUTSIDE THEN
      MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `H:real^N->real^N`;
                            `IMAGE (q:real^2->real^N) C`] THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      UNDISCH_TAC `~((x:real^N) IN IMAGE (q:real^2->real^N) C)` THEN
      UNDISCH_TAC `(C0:real^2->bool) SUBSET C` THEN SET_TAC[]]] THEN
  UNDISCH_TAC `(x:real^N) IN IMAGE (q:real^2->real^N) C` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^2` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y:real^2) IN IMAGE (p:real^N->real^2) U` ASSUME_TAC THENL
   [UNDISCH_TAC `(C:real^2->bool) SUBSET IMAGE (p:real^N->real^2) U` THEN
    UNDISCH_TAC `(y:real^2) IN C` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^2->real^N) y IN U` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (q:real^2->real^N) (IMAGE (p:real^N->real^2) U) = U` THEN
    UNDISCH_TAC `(y:real^2) IN IMAGE (p:real^N->real^2) U` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (H:real^N->real^N) J SUBSET X` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (H:real^N->real^N) X = X` THEN
    UNDISCH_TAC `(J:real^N->bool) SUBSET X` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(q:real^2->real^N) y limit_point_of
    ((IMAGE (H:real^N->real^N) J INTER K) INTER U)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean X) (U:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `O1:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(IMAGE (H:real^N->real^N) J INTER K) INTER U =
      (IMAGE H J INTER K) INTER O1`
    SUBST1_TAC THENL
     [UNDISCH_TAC `U:real^N->bool = X INTER O1` THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `IMAGE (H:real^N->real^N) J SUBSET X` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FGB_LIMPT_LOCAL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(q:real^2->real^N) y IN U` THEN
    UNDISCH_TAC `U:real^N->bool = X INTER O1` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(y:real^2) limit_point_of
    IMAGE (p:real^N->real^2) ((IMAGE (H:real^N->real^N) J INTER K) INTER U)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `y = (p:real^N->real^2) ((q:real^2->real^N) y)`
    (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FGB_LIMPT_IMAGE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `J:real^N->bool`; `U:real^N->bool`;
                 `p:real^N->real^2`; `q:real^2->real^N`; `P:real^2->real^2`;
                 `H:real^N->real^N`] MOI_FGB_CHART_PUSH_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `(IMAGE (P:real^2->real^2) (IMAGE (p:real^N->real^2) (J INTER U)) INTER
     IMAGE p (K INTER U)) INTER O' SUBSET
    IMAGE P (IMAGE p (J INTER U) INTER C') INTER (IMAGE p (K INTER U) INTER C')`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `w:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)
      ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^2` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a:real^2) IN C'` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `~((a:real^2) IN C)` ASSUME_TAC THENL
       [UNDISCH_TAC `~((a:real^2) IN C')` THEN
        UNDISCH_TAC `(C:real^2->bool) SUBSET O'` THEN
        UNDISCH_TAC `(O':real^2->bool) SUBSET C'` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(P:real^2->real^2) a = a` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(P:real^2->real^2) a IN O'` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((a:real^2) IN C')` THEN
      UNDISCH_TAC `(O':real^2->bool) SUBSET C'` THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(P:real^2->real^2) a IN O'` THEN
      UNDISCH_TAC `(O':real^2->bool) SUBSET C'` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(y:real^2) limit_point_of
    (IMAGE (P:real^2->real^2) (IMAGE (p:real^N->real^2) (J INTER U) INTER C') INTER
     (IMAGE p (K INTER U) INTER C'))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIMPT_SUBSET THEN
    EXISTS_TAC
     `(IMAGE (P:real^2->real^2) (IMAGE (p:real^N->real^2) (J INTER U)) INTER
       IMAGE p (K INTER U)) INTER O'` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FGB_LIMPT_LOCAL THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIMPT_SUBSET THEN
      EXISTS_TAC
       `IMAGE (p:real^N->real^2) ((IMAGE (H:real^N->real^N) J INTER K) INTER U)` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `IMAGE (p:real^N->real^2) (IMAGE (H:real^N->real^N) J INTER U) =
        IMAGE (P:real^2->real^2) (IMAGE p (J INTER U))` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN SET_TAC[];
      UNDISCH_TAC `(y:real^2) IN C` THEN
      UNDISCH_TAC `(C:real^2->bool) SUBSET O'` THEN SET_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "bad" (MP_TAC o SPEC `y:real^2`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC
     `(y:real^2) limit_point_of
      (IMAGE (P:real^2->real^2) (IMAGE (p:real^N->real^2) (J INTER U) INTER C') INTER
       (IMAGE p (K INTER U) INTER C'))` THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIMPT_SUBSET THEN
    EXISTS_TAC
     `IMAGE (q:real^2->real^N)
        ((IMAGE (p:real^N->real^2) (J INTER U) INTER C') INTER
         (IMAGE p (K INTER U) INTER C'))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FGB_LIMPT_IMAGE THEN
      EXISTS_TAC `IMAGE (p:real^N->real^2) U` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(C':real^2->bool) SUBSET IMAGE (p:real^N->real^2) U` THEN
      SET_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_IMAGE] THEN
      X_GEN_TAC `w:real^2` THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `z1:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `z2:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      SUBGOAL_THEN `z1:real^N = z2` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!x y:real^N. x IN U /\ y IN U /\ (f:real^N->real^2) x = f y ==> x = y`)
            (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `w = (p:real^N->real^2) z1` THEN
        UNDISCH_TAC `w = (p:real^N->real^2) z2` THEN MESON_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `w = (p:real^N->real^2) z2` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[]];
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y':real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y':real^2) IN IMAGE (p:real^N->real^2) U` ASSUME_TAC THENL
     [UNDISCH_TAC `(C:real^2->bool) SUBSET IMAGE (p:real^N->real^2) U` THEN
      UNDISCH_TAC `(C0:real^2->bool) SUBSET C` THEN
      UNDISCH_TAC `(y':real^2) IN C0` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `y:real^2 = y'` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x y:real^2. x IN IMAGE (p:real^N->real^2) U /\
                                          y IN IMAGE p U /\ (f:real^2->real^N) x = f y
                                          ==> x = y`)
          (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(y':real^2) IN C0` THEN EXPAND_TAC "C0" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM(fun th -> if can (term_match []
      `!y:real^2. &0 < f y <=> infnorm(y - c) < &2 * r`) (concl th)
      then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    ASM_REWRITE_TAC[REAL_LT_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Q. Phase 1: finitely many generic chart pushes covering the limit points *)
(* of the intersection make the intersection finite.                        *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_PLH_ID = prove
 (`!X:real^N->bool. locally_polyhedral X ==> pl_homeomorphism (X,X) ((\x. x),(\x. x))`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  ASM_REWRITE_TAC[HOMEOMORPHISM_ID; GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID]);;

let MOI_FGB_PLH_IMAGE_DIM1 = prove
 (`!X (J:real^N->bool) H G.
     pl_homeomorphism (X,X) (H,G) /\ moi_ptr_dim_polyhedron 1 J /\ J SUBSET X
     ==> moi_ptr_dim_polyhedron 1 (IMAGE H J) /\ IMAGE H J SUBSET X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PTR_DIM_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `X:real^N->bool` THEN
    ASM_SIMP_TAC[MOI_FGB_DIM1_LP] THEN ASM_MESON_TAC[pl_homeomorphism];
    UNDISCH_TAC `pl_homeomorphism (X,X) ((H:real^N->real^N),(G:real^N->real^N))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
    UNDISCH_TAC `(J:real^N->bool) SUBSET X` THEN SET_TAC[]]);;

let MOI_FGB_PHASE1_ITER = prove
 (`!X (K:real^N->bool) V (Uf:real^N->real^N->bool) (pf:real^N->real^N->real^2)
    qf cf rf.
     locally_polyhedral X /\ moi_ptr_dim_polyhedron 1 K /\ K SUBSET X
     ==> !Fs. FINITE Fs
             ==> (!z. z IN Fs
                      ==> open_in (subtopology euclidean X) (Uf z) /\ Uf z SUBSET V /\
                          pl_homeomorphism (Uf z,IMAGE (pf z) (Uf z)) (pf z,qf z) /\
                          &0 < rf z /\
                          {y | infnorm(y - cf z) <= &3 * rf z} SUBSET
                          IMAGE (pf z) (Uf z))
             ==> !J e. moi_ptr_dim_polyhedron 1 J /\ J SUBSET X /\ &0 < e
                       ==> ?H G. pl_homeomorphism (X,X) (H,G) /\
                                 (!x. x IN X /\ ~(x IN V) ==> H x = x) /\
                                 (!x. x IN X ==> dist(H x,x) < e) /\
                                 moi_ptr_dim_polyhedron 1 (IMAGE H J) /\
                                 IMAGE H J SUBSET X /\
                                 !x. x limit_point_of (IMAGE H J INTER K)
                                     ==> x IN J INTER K /\
                                         x limit_point_of (J INTER K) /\
                                         !z. z IN Fs
                                             ==> ~(x IN IMAGE (qf z)
                                                   {y | infnorm(y - cf z) <
                                                        &2 * rf z})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`\x:real^N. x`; `\x:real^N. x`] THEN
    ASM_SIMP_TAC[MOI_FGB_PLH_ID; IMAGE_ID; DIST_REFL] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `closed(J INTER K:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC CLOSED_INTER THEN
      ASM_SIMP_TAC[MOI_FGB_DIM1_COMPACT; COMPACT_IMP_CLOSED];
      ASM_MESON_TAC[CLOSED_LIMPT]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z0:real^N`; `Fs:real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_INSERT] THEN DISCH_THEN(LABEL_TAC "ch") THEN
  MAP_EVERY X_GEN_TAC [`J:real^N->bool`; `e:real`] THEN STRIP_TAC THEN
  USE_THEN "ch" (MP_TAC o SPEC `z0:real^N`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `J:real^N->bool`; `K:real^N->bool`;
                 `(Uf:real^N->real^N->bool) z0`; `(pf:real^N->real^N->real^2) z0`;
                 `(qf:real^N->real^2->real^N) z0`; `(cf:real^N->real^2) z0`;
                 `(rf:real^N->real) z0`; `e / &2`] MOI_FGB_PHASE1_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H1:real^N->real^N` (X_CHOOSE_THEN `G1:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "id1")
     (CONJUNCTS_THEN2 (LABEL_TAC "d1") (LABEL_TAC "lp1")))))) THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `J:real^N->bool`; `H1:real^N->real^N`;
                 `G1:real^N->real^N`] MOI_FGB_PLH_IMAGE_DIM1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "IH" (MP_TAC o SPECL [`IMAGE (H1:real^N->real^N) J`; `e / &2`] o
    C MP (GEN `z:real^N` (DISCH `(z:real^N) IN Fs`
      (MP (SPEC `z:real^N` (REWRITE_RULE[] (ASSUME
        `!z:real^N. z = z0 \/ z IN Fs
             ==> open_in (subtopology euclidean X) ((Uf:real^N->real^N->bool) z) /\
                 Uf z SUBSET V /\
                 pl_homeomorphism (Uf z,IMAGE ((pf:real^N->real^N->real^2) z) (Uf z))
                   (pf z,(qf:real^N->real^2->real^N) z) /\
                 &0 < (rf:real^N->real) z /\
                 {y | infnorm(y - (cf:real^N->real^2) z) <= &3 * rf z} SUBSET
                 IMAGE (pf z) (Uf z)`))) (DISJ2 `z:real^N = z0`
          (ASSUME `(z:real^N) IN Fs`)))))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H2:real^N->real^N` (X_CHOOSE_THEN `G2:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "id2")
     (CONJUNCTS_THEN2 (LABEL_TAC "d2") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lp2")))))))) THEN
  EXISTS_TAC `(H2:real^N->real^N) o (H1:real^N->real^N)` THEN
  EXISTS_TAC `(G1:real^N->real^N) o (G2:real^N->real^N)` THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `X:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(H1:real^N->real^N) x = x` SUBST1_TAC THENL
     [USE_THEN "id1" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "id2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(H1:real^N->real^N) x IN X` ASSUME_TAC THENL
     [UNDISCH_TAC `pl_homeomorphism (X,X) ((H1:real^N->real^N),(G1:real^N->real^N))` THEN
      REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
      UNDISCH_TAC `(x:real^N) IN X` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH
     `!a b c:real^N e. dist(a,b) < e / &2 /\ dist(b,c) < e / &2 ==> dist(a,c) < e`) THEN
    EXISTS_TAC `(H1:real^N->real^N) x` THEN
    CONJ_TAC THENL
     [USE_THEN "d2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "d1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REMOVE_THEN "lp2" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    REMOVE_THEN "lp1" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[]]);;

let MOI_FGB_CHART_OPEN_IMAGE = prove
 (`!X U (p:real^N->real^2) q O.
     open_in (subtopology euclidean X) U /\
     pl_homeomorphism (U,IMAGE p U) (p,q) /\ open O /\ O SUBSET IMAGE p U
     ==> open_in (subtopology euclidean X) (IMAGE q O)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FGB_CHART_FACTS) THEN
  SUBGOAL_THEN `IMAGE (q:real^2->real^N) O = {x | x IN U /\ (p:real^N->real^2) x IN O}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^2) IN IMAGE (p:real^N->real^2) U` ASSUME_TAC THENL
       [UNDISCH_TAC `(O:real^2->bool) SUBSET IMAGE (p:real^N->real^2) U` THEN
        UNDISCH_TAC `(y:real^2) IN O` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `IMAGE (q:real^2->real^N) (IMAGE (p:real^N->real^2) U) = U` THEN
      UNDISCH_TAC `(y:real^2) IN IMAGE (p:real^N->real^2) U` THEN SET_TAC[];
      STRIP_TAC THEN EXISTS_TAC `(p:real^N->real^2) x` THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FGB_PHASE1 = prove
 (`!c (J:real^N->bool) K v e.
     combinatorial_manifold_with_boundary 2 c /\
     moi_ptr_dim_polyhedron 1 J /\ moi_ptr_dim_polyhedron 1 K /\
     J SUBSET v /\ K SUBSET UNIONS c DIFF surface_boundary c /\
     open_in (subtopology euclidean (UNIONS c)) v /\ &0 < e
     ==> ?H G. pl_homeomorphism (UNIONS c,UNIONS c) (H,G) /\
               (!x. x IN UNIONS c /\ ~(x IN v) ==> H x = x) /\
               (!x. x IN UNIONS c ==> dist(H x,x) < e) /\
               moi_ptr_dim_polyhedron 1 (IMAGE H J) /\
               IMAGE H J SUBSET v /\
               FINITE (IMAGE H J INTER K)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  ABBREV_TAC `X = UNIONS (c:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `locally_polyhedral (X:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_LF_COMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^N->bool) SUBSET X /\ (K:real^N->bool) SUBSET X`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(v:real^N->bool) SUBSET X` THEN
    UNDISCH_TAC `(J:real^N->bool) SUBSET v` THEN
    UNDISCH_TAC `(K:real^N->bool) SUBSET X DIFF surface_boundary c` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(J:real^N->bool) /\ compact(K:real^N->bool)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FGB_DIM1_COMPACT]; ALL_TAC] THEN
  ABBREV_TAC `B = {x:real^N | x IN J INTER K /\ x limit_point_of (J INTER K)}` THEN
  SUBGOAL_THEN
   `!x:real^N. x IN B
      ==> ?U p q y0 r. open_in (subtopology euclidean X) U /\ U SUBSET v /\
                       pl_homeomorphism (U,IMAGE p U) (p,q) /\ &0 < r /\
                       {y | infnorm(y - y0) <= &3 * r} SUBSET IMAGE p U /\
                       x IN IMAGE q {y:real^2 | infnorm(y - y0) < &2 * r}`
  MP_TAC THENL
   [X_GEN_TAC `x:real^N` THEN EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_FGB_SURF_CHART) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(K:real^N->bool) SUBSET X DIFF surface_boundary c` THEN
      UNDISCH_TAC `(x:real^N) IN K` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U0:real^N->bool` (X_CHOOSE_THEN `p:real^N->real^2`
      (X_CHOOSE_THEN `q:real^2->real^N` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`X:real^N->bool`; `U0:real^N->bool`; `v:real^N->bool`;
                   `p:real^N->real^2`; `q:real^2->real^N`] MOI_FGB_CHART_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN U0 INTER v` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `(J:real^N->bool) SUBSET v` THEN
      UNDISCH_TAC `(x:real^N) IN J` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(p:real^N->real^2) x`; `IMAGE (p:real^N->real^2) (U0 INTER v)`]
      MOI_FGB_CUBE_IN_OPEN_2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`U0 INTER v:real^N->bool`; `p:real^N->real^2`;
                          `q:real^2->real^N`; `(p:real^N->real^2) x`; `r:real`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `(p:real^N->real^2) x` THEN
    REWRITE_TAC[VECTOR_SUB_REFL; INFNORM_0] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`U0 INTER v:real^N->bool`; `p:real^N->real^2`;
                     `q:real^2->real^N`] MOI_FGB_CHART_FACTS) THEN
      ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Uf:real^N->real^N->bool` (X_CHOOSE_THEN
    `pf:real^N->real^N->real^2` (X_CHOOSE_THEN `qf:real^N->real^2->real^N`
    (X_CHOOSE_THEN `cf:real^N->real^2` (X_CHOOSE_THEN `rf:real^N->real`
     (LABEL_TAC "ch")))))) THEN
  SUBGOAL_THEN
   `!x:real^N. x IN B
      ==> ?O. open O /\
              IMAGE ((qf:real^N->real^2->real^N) x)
                {y:real^2 | infnorm(y - (cf:real^N->real^2) x) < &2 * rf x} =
              X INTER O`
  MP_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "ch" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN B`))) THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM OPEN_IN_OPEN] THEN
    MATCH_MP_TAC MOI_FGB_CHART_OPEN_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`(Uf:real^N->real^N->bool) x`;
                          `(pf:real^N->real^N->real^2) x`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(cf:real^N->real^2) x`; `(rf:real^N->real) x`]
      MOI_FGB_CUBES_2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{y:real^2 | infnorm(y - (cf:real^N->real^2) x) <=
                            &3 * (rf:real^N->real) x}` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{y:real^2 | infnorm(y - (cf:real^N->real^2) x) <=
                            &2 * (rf:real^N->real) x}` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{y:real^2 | infnorm(y - (cf:real^N->real^2) x) <
                            &3 * (rf:real^N->real) x}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Of:real^N->real^N->bool` (LABEL_TAC "of")) THEN
  SUBGOAL_THEN `compact(B:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    SUBGOAL_THEN
     `{x:real^N | x IN J INTER K /\ x limit_point_of (J INTER K)} =
      (J INTER K) INTER {x | x limit_point_of (J INTER K)}`
    SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER]; ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    ASM_SIMP_TAC[COMPACT_INTER; CLOSED_LIMPTS];
    ALL_TAC] THEN
  UNDISCH_TAC `compact(B:real^N->bool)` THEN
  REWRITE_TAC[COMPACT_EQ_HEINE_BOREL] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (Of:real^N->real^N->bool) B`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      USE_THEN "of" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN B`))) THEN
      SIMP_TAC[];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "of" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN B`))) THEN
      USE_THEN "ch" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN B`))) THEN
      STRIP_TAC THEN STRIP_TAC THEN
      UNDISCH_TAC
       `IMAGE ((qf:real^N->real^2->real^N) x)
          {y:real^2 | infnorm(y - (cf:real^N->real^2) x) < &2 * rf x} =
        X INTER (Of:real^N->real^N->bool) x` THEN
      UNDISCH_TAC
       `(x:real^N) IN IMAGE ((qf:real^N->real^2->real^N) x)
          {y:real^2 | infnorm(y - (cf:real^N->real^2) x) < &2 * rf x}` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> (b /\ a) /\ c`] THEN
  REWRITE_TAC[FINITE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(real^N->bool)->bool` MP_TAC) THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `K:real^N->bool`; `v:real^N->bool`;
                 `Uf:real^N->real^N->bool`; `pf:real^N->real^N->real^2`;
                 `qf:real^N->real^2->real^N`; `cf:real^N->real^2`;
                 `rf:real^N->real`] MOI_FGB_PHASE1_ITER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `Fs:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "ch" (MP_TAC o SPEC `z:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`J:real^N->bool`; `e:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^N->real^N` (X_CHOOSE_THEN `G:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`H:real^N->real^N`; `G:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN X /\ z IN v` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(J:real^N->bool) SUBSET v` THEN
      UNDISCH_TAC `(v:real^N->bool) SUBSET X` THEN
      UNDISCH_TAC `(z:real^N) IN J` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(H:real^N->real^N) z IN X` ASSUME_TAC THENL
     [UNDISCH_TAC `pl_homeomorphism (X,X) ((H:real^N->real^N),(G:real^N->real^N))` THEN
      REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
      UNDISCH_TAC `(z:real^N) IN X` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(H:real^N->real^N) ((H:real^N->real^N) z) = H z` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x:real^N. x IN X /\ ~(x IN v) ==> (H:real^N->real^N) x = x`)
          (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `G:real^N->real^N`) THEN
    UNDISCH_TAC `pl_homeomorphism (X,X) ((H:real^N->real^N),(G:real^N->real^N))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN UNDISCH_TAC `~((H:real^N->real^N) z IN v)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (H:real^N->real^N) J INTER K)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_INTER THEN ASM_SIMP_TAC[MOI_FGB_DIM1_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (H:real^N->real^N) J INTER K`;
                 `IMAGE (H:real^N->real^N) J INTER K`] DISCRETE_EQ_FINITE_COMPACT) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
    can (term_match [] `!x:real^N. x limit_point_of (IMAGE (H:real^N->real^N) J INTER K)
                                   ==> P x`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^N. z IN Fs /\ x IN (Of:real^N->real^N->bool) z`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(B:real^N->bool) SUBSET UNIONS f'` THEN
    UNDISCH_TAC `f' = IMAGE (Of:real^N->real^N->bool) Fs` THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (fun th ->
    can (term_match [] `!z:real^N. z IN Fs ==> ~((x:real^N) IN (P:real^N->real^N->bool) z)`)
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "of" (MP_TAC o SPEC `z:real^N`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
  UNDISCH_TAC `(J:real^N->bool) SUBSET X` THEN
  UNDISCH_TAC `(x:real^N) IN J INTER K` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* R. Crossing charts: two transverse lines through a point of a chart      *)
(* image give pl_curve_crossing_at (an affine change of plane coordinates  *)
(* sends the two lines to the coordinate axes).                             *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_PLH_UNIV_RESTRICT = prove
 (`!(f:real^N->real^N) g S.
     pl_homeomorphism ((:real^N),(:real^N)) (f,g) /\ locally_polyhedral S
     ==> pl_homeomorphism (S,IMAGE f S) (f,g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(:real^N)`; `(:real^N)`] THEN
    REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[pl_homeomorphism];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[pl_homeomorphism]]);;

let MOI_FGB_LINE_AXIS = prove
 (`!(M:real^2->real^2) (w:real^2) v.
     linear M
     ==> IMAGE (\y. M(y - w)) {w + s % v | s IN (:real)} =
         {s % M v | s IN (:real)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `z:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^2` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `s:real` SUBST1_TAC))) THEN
    EXISTS_TAC `s:real` THEN
    ASM_SIMP_TAC[VECTOR_ARITH `(w + s % v) - w:real^N = s % v`; LINEAR_CMUL];
    DISCH_THEN(X_CHOOSE_THEN `s:real` SUBST1_TAC) THEN
    EXISTS_TAC `w + s % v:real^2` THEN
    ASM_SIMP_TAC[VECTOR_ARITH `(w + s % v) - w:real^N = s % v`; LINEAR_CMUL] THEN
    EXISTS_TAC `s:real` THEN REWRITE_TAC[]]);;

let MOI_FGB_AXES_2 = prove
 (`{s % basis 2 | s IN (:real)} = {y:real^2 | y$1 = &0} /\
   {s % basis 1 | s IN (:real)} = {y:real^2 | y$2 = &0}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN CONJ_TAC THEN
  X_GEN_TAC `y:real^2` THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH;
               REAL_MUL_RZERO] THENL
   [EXISTS_TAC `(y:real^2)$2`; EXISTS_TAC `(y:real^2)$1`] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
           ARITH] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_FGB_CROSS_CHART = prove
 (`!X U (p:real^N->real^2) q J K (w:real^2) r v w'.
     open_in (subtopology euclidean X) U /\ open (IMAGE p U) /\
     pl_homeomorphism (U,IMAGE p U) (p,q) /\
     &0 < r /\ ball(w,r) SUBSET IMAGE p U /\ ~collinear {vec 0, v, w'} /\
     IMAGE p (J INTER U) INTER ball(w,r) = {w + s % v | s IN (:real)} INTER ball(w,r) /\
     IMAGE p (K INTER U) INTER ball(w,r) = {w + s % w' | s IN (:real)} INTER ball(w,r)
     ==> pl_curve_crossing_at X J K (q w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FGB_CHART_FACTS) THEN
  ABBREV_TAC `N = \y:real^2. y$2 % (v:real^2) + y$1 % w'` THEN
  SUBGOAL_THEN `linear (N:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[linear; VECTOR_ADD_COMPONENT;
                                     VECTOR_MUL_COMPONENT] THEN
    REPEAT GEN_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^2. (N:real^2->real^2) x = N y ==> x = y` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "N" THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`v:real^2`; `w':real^2`; `(x:real^2)$2 - (y:real^2)$2`;
                   `(y:real^2)$1 - (x:real^2)$1`] MOI_FGB_INDEP_2D) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^2)$2 % (v:real^2) + x$1 % w' = (y:real^2)$2 % v + y$1 % w'` THEN
      VECTOR_ARITH_TAC;
      SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `N:real^2->real^2` MOI_FGB_LINEAR_PLH_UNIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^2->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(M:real^2->real^2) v = basis 2 /\ M w' = basis 1` STRIP_ASSUME_TAC
  THENL
   [SUBGOAL_THEN `(N:real^2->real^2) (basis 2) = v /\ N (basis 1) = w'`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "N" THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(N:real^2->real^2) (basis 2) = v` THEN
    UNDISCH_TAC `(N:real^2->real^2) (basis 1) = w'` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `u = IMAGE (q:real^2->real^N) (ball(w,r))` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean X) (u:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC MOI_FGB_CHART_OPEN_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `p:real^N->real^2`] THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET U /\ IMAGE (p:real^N->real^2) u = ball(w,r)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (q:real^2->real^N) (IMAGE (p:real^N->real^2) U) = U` THEN
      UNDISCH_TAC `ball(w:real^2,r) SUBSET IMAGE (p:real^N->real^2) U` THEN
      SET_TAC[];
      REWRITE_TAC[GSYM IMAGE_o] THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\y:real^2. y) (ball(w,r))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `!f g s:real^2->bool. (!x. x IN s ==> (f:real^2->real^2) x = g x)
                               ==> IMAGE f s = IMAGE g s`) THEN
        REWRITE_TAC[o_THM] THEN
        UNDISCH_TAC `ball(w:real^2,r) SUBSET IMAGE (p:real^N->real^2) U` THEN
        ASM SET_TAC[];
        REWRITE_TAC[IMAGE_ID]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^2->real^N) w IN u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (u,ball(w,r)) ((p:real^N->real^2),(q:real^2->real^N))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`X:real^N->bool`; `U:real^N->bool`; `u:real^N->bool`;
                   `p:real^N->real^2`; `q:real^2->real^N`] MOI_FGB_CHART_RESTRICT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(U:real^N->bool) INTER u = u` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `(u:real^N->bool) SUBSET U` THEN SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\z:real^2. z - w) (ball(w,r)) = ball(vec 0,r)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL; IN_BALL_0] THEN
    X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `dist(w:real^2,z) < r` THEN
      REWRITE_TAC[dist] THEN NORM_ARITH_TAC;
      DISCH_TAC THEN EXISTS_TAC `y + w:real^2` THEN
      CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `norm(y:real^2) < r` THEN REWRITE_TAC[dist] THEN NORM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (ball(w,r),ball(vec 0,r))
      ((\z:real^2. z - w),(\z:real^2. z + w))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (\z:real^2. z - w) (ball(w,r)) = ball(vec 0,r)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MOI_FGB_PLH_UNIV_RESTRICT THEN
    REWRITE_TAC[MOI_FGB_TRANSLATE_PLH] THEN
    SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (ball(vec 0,r),IMAGE (M:real^2->real^2) (ball(vec 0,r)))
      (M,(N:real^2->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FGB_PLH_UNIV_RESTRICT THEN
    SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_BALL] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (u,IMAGE (M:real^2->real^2) (ball(vec 0,r)))
     ((M:real^2->real^2) o (\z:real^2. z - w) o (p:real^N->real^2),
      ((q:real^2->real^N) o (\z:real^2. z + w)) o (N:real^2->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `ball(vec 0:real^2,r)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `ball(w:real^2,r)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((M:real^2->real^2) o (\z:real^2. z - w) o (p:real^N->real^2)) u =
    IMAGE M (ball(vec 0,r))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^2. (M:real^2->real^2) x = M y ==> x = y`
  (LABEL_TAC "Minj") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `N:real^2->real^2`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!S:real^N->bool.
      IMAGE ((M:real^2->real^2) o (\z:real^2. z - w) o (p:real^N->real^2))
            (S INTER u) =
      IMAGE (\y. M(y - w)) (IMAGE p (S INTER U) INTER ball(w,r))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `IMAGE ((M:real^2->real^2) o (\z:real^2. z - w) o (p:real^N->real^2))
            (S INTER u) =
      IMAGE (\y. M(y - w)) (IMAGE p (S INTER u))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM];
      ALL_TAC] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN X_GEN_TAC `y:real^2` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL
       [EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(u:real^N->bool) SUBSET U` THEN
        UNDISCH_TAC `(z:real^N) IN u` THEN SET_TAC[];
        UNDISCH_TAC `IMAGE (p:real^N->real^2) u = ball(w,r)` THEN
        UNDISCH_TAC `(z:real^N) IN u` THEN UNDISCH_TAC `y = (p:real^N->real^2) z` THEN
        SET_TAC[]];
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `z = (q:real^2->real^N) y` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "u" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((M:real^2->real^2) o (\z:real^2. z - w) o (p:real^N->real^2)) (J INTER u) =
    IMAGE M (ball(vec 0,r)) INTER {y:real^2 | y$1 = &0} /\
    IMAGE ((M:real^2->real^2) o (\z:real^2. z - w) o (p:real^N->real^2)) (K INTER u) =
    IMAGE M (ball(vec 0,r)) INTER {y:real^2 | y$2 = &0}`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!t:real^2->bool. IMAGE (\y. (M:real^2->real^2) (y - w)) (t INTER ball(w,r)) =
                       IMAGE (\y. M(y - w)) t INTER IMAGE M (ball(vec 0,r))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      SUBGOAL_THEN `IMAGE (M:real^2->real^2) (ball(vec 0,r)) =
                    IMAGE (\y. M(y - w)) (ball(w,r))` SUBST1_TAC THENL
       [UNDISCH_TAC `IMAGE (\z:real^2. z - w) (ball(w,r)) = ball(vec 0,r)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF];
        ALL_TAC] THEN
      MATCH_MP_TAC IMAGE_INTER_INJ THEN
      REPEAT GEN_TAC THEN BETA_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `x - w:real^2 = y - w` MP_TAC THENL
       [USE_THEN "Minj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_FGB_LINE_AXIS; MOI_FGB_AXES_2] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pl_curve_crossing_at] THEN
  MAP_EVERY EXISTS_TAC
   [`u:real^N->bool`;
    `(M:real^2->real^2) o (\z:real^2. z - w) o (p:real^N->real^2)`;
    `((q:real^2->real^N) o (\z:real^2. z + w)) o (N:real^2->real^2)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`M:real^2->real^2`; `N:real^2->real^2`; `(:real^2)`;
                   `(:real^2)`; `ball(vec 0:real^2,r)`]
      HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `pl_homeomorphism ((:real^2),(:real^2))
                   ((N:real^2->real^2),(M:real^2->real^2))` THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN SIMP_TAC[pl_homeomorphism];
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(w:real^2) IN IMAGE (p:real^N->real^2) U` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(w:real^2,r) SUBSET IMAGE (p:real^N->real^2) U` THEN
      MP_TAC(ISPECL [`w:real^2`; `r:real`] CENTRE_IN_BALL) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_SIMP_TAC[VECTOR_SUB_REFL] THEN
      MP_TAC(ISPEC `M:real^2->real^2` LINEAR_0) THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* S. One generic translation push near an isolated intersection point      *)
(* (phase 2): afterwards every intersection point in the chart is a         *)
(* crossing.                                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_TRANSLATE_REGION = prove
 (`!(P:real^2->real^2) P' Q1 A C' d (z0:real^2) r.
     (!y. P' (P y) = y) /\ (!y. y IN Q1 ==> P y = y + d) /\ Q1 SUBSET C' /\
     ball(z0,r) SUBSET IMAGE (\y. y + d) Q1
     ==> IMAGE P A INTER ball(z0,r) =
         IMAGE (\y. y + d) (A INTER C') INTER ball(z0,r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER] THEN X_GEN_TAC `z:real^2` THEN
  ASM_CASES_TAC `(z:real^2) IN ball(z0,r)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?b:real^2. b IN Q1 /\ z = b + d` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(z0:real^2,r) SUBSET IMAGE (\y:real^2. y + d) Q1` THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `a:real^2 = b` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `(P:real^2->real^2) b = P a` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `P':real^2->real^2`) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `b:real^2` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(Q1:real^2->bool) SUBSET C'` THEN
    UNDISCH_TAC `(b:real^2) IN Q1` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `a:real^2 = b` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `b + d:real^2 = a + d` THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `b:real^2` THEN ASM_SIMP_TAC[]]);;

let MOI_FGB_PHASE2_STEP = prove
 (`!X (J:real^N->bool) K U (p:real^N->real^2) q (y0:real^2) rho e.
     locally_polyhedral X /\ moi_ptr_dim_polyhedron 1 J /\
     moi_ptr_dim_polyhedron 1 K /\ J SUBSET X /\ K SUBSET X /\
     open_in (subtopology euclidean X) U /\ open (IMAGE p U) /\
     pl_homeomorphism (U,IMAGE p U) (p,q) /\
     &0 < rho /\ {y | infnorm(y - y0) <= &3 * rho} SUBSET IMAGE p U /\
     J INTER K INTER U SUBSET {q y0} /\ &0 < e
     ==> ?H G. pl_homeomorphism (X,X) (H,G) /\
               (!x. x IN X /\ ~(x IN U) ==> H x = x) /\
               (!x. x IN X ==> dist(H x,x) < e) /\
               (!x. x IN X /\ ~(x IN IMAGE q {y | infnorm(y - y0) <= &2 * rho})
                    ==> H x = x) /\
               (!x. x IN IMAGE q {y | infnorm(y - y0) <= &2 * rho}
                    ==> H x IN IMAGE q {y | infnorm(y - y0) <= &2 * rho}) /\
               FINITE (IMAGE H J INTER K INTER U) /\
               !x. x IN IMAGE H J INTER K INTER U
                   ==> pl_curve_crossing_at X (IMAGE H J) K x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FGB_CHART_FACTS) THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(J:real^N->bool) /\ compact(K:real^N->bool)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FGB_DIM1_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`y0:real^2`; `rho:real`] MOI_FGB_BUMP2) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `phi = moi_fgb_bump y0 rho` THEN
  MP_TAC(ISPECL [`y0:real^2`; `rho:real`] MOI_FGB_CUBES_2) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `open {y:real^2 | infnorm(y - y0) < rho} /\
    {y:real^2 | infnorm(y - y0) < rho} SUBSET {y | infnorm(y - y0) <= &2 * rho} /\
    (y0:real^2) IN {y | infnorm(y - y0) < rho}`
  MP_TAC THENL
   [REWRITE_TAC[MOI_FGB_CUBE_FACTS_2; SUBSET; IN_ELIM_THM;
                VECTOR_SUB_REFL; INFNORM_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. y IN {y | infnorm(y - y0) < rho} ==> phi y = &1`
  MP_TAC THENL
   [MP_TAC(ISPECL [`y0:real^2`; `rho:real`] MOI_FGB_BUMP2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!y:real^2. infnorm(y - c) <= r ==> (f:real^2->real) y = &1`)
        (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `{y:real^2 | infnorm(y - y0) <= &3 * rho} SUBSET IMAGE (p:real^N->real^2) U` THEN
  ABBREV_TAC `C = {y:real^2 | infnorm(y - y0) <= &2 * rho}` THEN
  ABBREV_TAC `C' = {y:real^2 | infnorm(y - y0) <= &3 * rho}` THEN
  ABBREV_TAC `O' = {y:real^2 | infnorm(y - y0) < &3 * rho}` THEN
  ABBREV_TAC `C0 = {y:real^2 | infnorm(y - y0) < &2 * rho}` THEN
  ABBREV_TAC `Q1 = {y:real^2 | infnorm(y - y0) < rho}` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(C:real^2->bool) SUBSET IMAGE (p:real^N->real^2) U /\
                (Q1:real^2->bool) SUBSET C' /\ (C:real^2->bool) SUBSET C'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(C':real^2->bool) SUBSET IMAGE (p:real^N->real^2) U` THEN
    UNDISCH_TAC `(C:real^2->bool) SUBSET O'` THEN
    UNDISCH_TAC `(O':real^2->bool) SUBSET C'` THEN
    UNDISCH_TAC `(Q1:real^2->bool) SUBSET C` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^2) IN IMAGE (p:real^N->real^2) U` ASSUME_TAC THENL
   [UNDISCH_TAC `(C:real^2->bool) SUBSET IMAGE (p:real^N->real^2) U` THEN
    UNDISCH_TAC `(Q1:real^2->bool) SUBSET C` THEN
    UNDISCH_TAC `(y0:real^2) IN Q1` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. y IN IMAGE (p:real^N->real^2) (J INTER U) /\
               y IN IMAGE p (K INTER U) ==> y = y0`
  (LABEL_TAC "AB") THENL
   [X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z1:real^N` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `z2:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `z1:real^N = z2` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x y:real^N. x IN U /\ y IN U /\
                              (f:real^N->real^2) x = f y ==> x = y`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `y = (p:real^N->real^2) z1` THEN
      UNDISCH_TAC `y = (p:real^N->real^2) z2` THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `z2 = (q:real^2->real^N) y0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `J INTER K INTER U SUBSET {(q:real^2->real^N) y0}` THEN
      UNDISCH_TAC `(z2:real^N) IN J` THEN UNDISCH_TAC `(z2:real^N) IN K` THEN
      UNDISCH_TAC `(z2:real^N) IN U` THEN SET_TAC[];
      UNDISCH_TAC `y = (p:real^N->real^2) ((q:real^2->real^N) y0)` THEN
      DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!y:real^2. y IN IMAGE (p:real^N->real^2) U
                                        ==> p ((q:real^2->real^N) y) = y`)
          (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ptr_dim_polyhedron 1 (IMAGE (p:real^N->real^2) (J INTER U) INTER C') /\
    moi_ptr_dim_polyhedron 1 (IMAGE (p:real^N->real^2) (K INTER U) INTER C')`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FGB_CHART_SLICE THEN
    EXISTS_TAC `q:real^2->real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d1. &0 < d1 /\
         !a b. a IN (IMAGE (p:real^N->real^2) (J INTER U) INTER C') INTER
                    (C DIFF Q1) /\
               b IN IMAGE p (K INTER U) INTER C'
               ==> d1 <= dist(a,b)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC SEPARATE_COMPACT_CLOSED THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_INTER THEN
      ASM_SIMP_TAC[MOI_FGB_DIM1_COMPACT; COMPACT_DIFF];
      ASM_SIMP_TAC[MOI_FGB_DIM1_COMPACT; COMPACT_IMP_CLOSED];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; NOT_IN_EMPTY] THEN
      X_GEN_TAC `a:real^2` THEN STRIP_TAC THEN
      USE_THEN "AB" (MP_TAC o SPEC `a:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      UNDISCH_TAC `~((a:real^2) IN Q1)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^2->real^N`; `C:real^2->bool`; `e:real`]
    MOI_FGB_UNIF_DELTA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (p:real^N->real^2) U` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `del:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "unif")))] THEN
  MP_TAC(ISPECL [`IMAGE (p:real^N->real^2) (J INTER U) INTER C'`;
                 `IMAGE (p:real^N->real^2) (K INTER U) INTER C'`;
                 `min (min d1 del) rho`] MOI_FGB_CROSS_FIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc")))) THEN
  MP_TAC(ISPECL [`phi:real^2->real`; `rho:real`; `d:real^2`] MOI_FGB_PUSH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `norm(d:real^2) < min (min d1 del) rho` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P':real^2->real^2` MP_TAC) THEN
  ABBREV_TAC `P = \y:real^2. y + phi y % d` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(!y:real^2. P' ((P:real^2->real^2) y) = y) /\ (!y. P (P' y) = y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism ((:real^2),(:real^2))
                   ((P:real^2->real^2),(P':real^2->real^2))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. ~(y IN C) ==> (P:real^2->real^2) y = y` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN EXPAND_TAC "P" THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. y IN Q1 ==> (P:real^2->real^2) y = y + d` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN EXPAND_TAC "P" THEN
    ASM_SIMP_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:real^2->real^2`; `P':real^2->real^2`; `C:real^2->bool`]
    MOI_FGB_FIX_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y:real^2. y IN IMAGE p U ==> (P:real^2->real^2) y IN IMAGE (p:real^N->real^2) U`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^2) IN C` THENL
     [UNDISCH_TAC `(C:real^2->bool) SUBSET IMAGE (p:real^N->real^2) U` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `U:real^N->bool`; `p:real^N->real^2`;
                 `q:real^2->real^N`; `P:real^2->real^2`; `P':real^2->real^2`;
                 `C:real^2->bool`] MOI_FGB_GLUE_PUSH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `H = \x:real^N. if x IN U then (q:real^2->real^N)((P:real^2->real^2)
                    ((p:real^N->real^2) x)) else x` THEN
  ABBREV_TAC
   `G = \x:real^N. if x IN U then (q:real^2->real^N)((P':real^2->real^2)
                    ((p:real^N->real^2) x)) else x` THEN
  SUBGOAL_THEN
   `!x:real^N. (if x IN U then (q:real^2->real^N)((P:real^2->real^2)
                 ((p:real^N->real^2) x)) else x) = H x`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^N. x IN U ==> (H:real^N->real^N) x =
                 (q:real^2->real^N)((P:real^2->real^2)((p:real^N->real^2) x))`
  ASSUME_TAC THENL [EXPAND_TAC "H" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN X /\ ~(x IN U) ==> (H:real^N->real^N) x = x`
  ASSUME_TAC THENL [EXPAND_TAC "H" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:real^2. a IN IMAGE (p:real^N->real^2) (J INTER U) /\
               (P:real^2->real^2) a IN IMAGE p (K INTER U) ==> a IN Q1`
  (LABEL_TAC "key") THENL
   [X_GEN_TAC `a:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^2) IN C` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `(P:real^2->real^2) a = a` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      USE_THEN "AB" (MP_TAC o SPEC `a:real^2`) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          UNDISCH_TAC
           `(P:real^2->real^2) a IN IMAGE (p:real^N->real^2) (K INTER U)` THEN
          ASM_REWRITE_TAC[]];
        DISCH_TAC] THEN
      UNDISCH_TAC `~((a:real^2) IN C)` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(Q1:real^2->bool) SUBSET C` THEN
      UNDISCH_TAC `(y0:real^2) IN Q1` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `(P:real^2->real^2) a`] o
      check (fun th -> can (term_match []
        `!a b:real^2. a IN s /\ b IN t ==> d1 <= dist(a,b)`) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; IN_DIFF] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(C:real^2->bool) SUBSET C'` THEN
        UNDISCH_TAC `(a:real^2) IN C` THEN SET_TAC[];
        UNDISCH_TAC `(C:real^2->bool) SUBSET C'` THEN
        SUBGOAL_THEN `(P:real^2->real^2) a IN C` MP_TAC THENL
         [ASM_SIMP_TAC[]; SET_TAC[]]];
      ALL_TAC] THEN
    EXPAND_TAC "P" THEN
    REWRITE_TAC[dist; VECTOR_ARITH `a - (a + c % d):real^N = --(c % d)`;
                NORM_NEG; NORM_MUL] THEN
    SUBGOAL_THEN `abs((phi:real^2->real) a) * norm(d:real^2) < d1`
    (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(d:real^2)` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:real^2` o check (fun th ->
        can (term_match [] `!y:real^2. &0 <= (f:real^2->real) y /\ f y <= &1`)
          (concl th))) THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `norm(d:real^2) < min (min d1 del) rho` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p:real^N->real^2) (IMAGE (H:real^N->real^N) J INTER U) =
    IMAGE (P:real^2->real^2) (IMAGE p (J INTER U))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FGB_CHART_PUSH_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `q:real^2->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN IMAGE (H:real^N->real^N) J INTER K INTER U
       ==> ?a. a IN IMAGE (p:real^N->real^2) (J INTER U) /\ a IN Q1 /\
               p x = a + d /\ p x IN IMAGE p (K INTER U) INTER C'`
  (LABEL_TAC "cl2") THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(p:real^N->real^2) x IN IMAGE (P:real^2->real^2) (IMAGE p (J INTER U))`
    MP_TAC THENL
     [UNDISCH_TAC
       `IMAGE (p:real^N->real^2) (IMAGE (H:real^N->real^N) J INTER U) =
        IMAGE (P:real^2->real^2) (IMAGE p (J INTER U))` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(p:real^N->real^2) x IN IMAGE p (K INTER U)` ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^2) IN Q1` ASSUME_TAC THENL
     [USE_THEN "key" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(p:real^N->real^2) x IN IMAGE p (K INTER U)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `a:real^2` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    SUBGOAL_THEN `(P:real^2->real^2) a = a + d` (fun th -> REWRITE_TAC[GSYM th]) THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(P:real^2->real^2) a IN C` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!y:real^2. y IN C ==> (P:real^2->real^2) y IN C`)
          (concl th))) THEN
      UNDISCH_TAC `(Q1:real^2->bool) SUBSET C` THEN
      UNDISCH_TAC `(a:real^2) IN Q1` THEN SET_TAC[];
      UNDISCH_TAC `(C:real^2->bool) SUBSET C'` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^N. x IN IMAGE (H:real^N->real^N) J INTER K INTER U /\
                 y IN IMAGE H J INTER K INTER U /\
                 (p:real^N->real^2) x = p y ==> x = y`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x y:real^N. x IN U /\ y IN U /\
                            (f:real^N->real^2) x = f y ==> x = y`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (IMAGE (H:real^N->real^N) J INTER K INTER U)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FINITE_IMAGE_INJ_EQ th)]) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `IMAGE (\x:real^2. x + d) (IMAGE (p:real^N->real^2) (J INTER U) INTER C') INTER
      (IMAGE p (K INTER U) INTER C')` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "cl2" (MP_TAC o C MATCH_MP
      (ASSUME `(x:real^N) IN IMAGE (H:real^N->real^N) J INTER K INTER U`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a:real^2` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    UNDISCH_TAC `(Q1:real^2->bool) SUBSET C'` THEN
    UNDISCH_TAC `(a:real^2) IN Q1` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\y:real^2. y + d) Q1 SUBSET C` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C"; "Q1"] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `a':real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a' - y0:real^2`; `d:real^2`] INFNORM_TRIANGLE) THEN
    MP_TAC(ISPEC `d:real^2` INFNORM_LE_NORM) THEN
    REWRITE_TAC[VECTOR_ARITH `(a + d) - y:real^N = (a - y) + d`] THEN
    UNDISCH_TAC `norm(d:real^2) < min (min d1 del) rho` THEN
    UNDISCH_TAC `infnorm(a' - y0:real^2) < rho` THEN
    REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (\y:real^2. y + d) Q1)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN ASM_SIMP_TAC[OPEN_TRANSLATION];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`H:real^N->real^N`; `G:real^N->real^N`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^N) IN U` THENL
     [ALL_TAC; ASM_SIMP_TAC[DIST_REFL]] THEN
    ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `(p:real^N->real^2) x IN C` THENL
     [SUBGOAL_THEN `x:real^N = q((p:real^N->real^2) x)`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      USE_THEN "unif" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
      EXPAND_TAC "P" THEN
      REWRITE_TAC[VECTOR_ARITH `(y + a % d) - y:real^N = a % d`; NORM_MUL] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(d:real^2)` THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^N->real^2) x` o check (fun th ->
          can (term_match [] `!y:real^2. &0 <= (f:real^2->real) y /\ f y <= &1`)
            (concl th))) THEN
        REAL_ARITH_TAC;
        UNDISCH_TAC `norm(d:real^2) < min (min d1 del) rho` THEN REAL_ARITH_TAC];
      ASM_SIMP_TAC[DIST_REFL]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "cl2" (MP_TAC o C MATCH_MP
      (ASSUME `(x:real^N) IN IMAGE (H:real^N->real^N) J INTER K INTER U`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
       ASSUME_TAC)))) THEN
    REMOVE_THEN "loc" (MP_TAC o SPEC `(p:real^N->real^2) x`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a:real^2` THEN
        ASM_REWRITE_TAC[IN_INTER] THEN
        UNDISCH_TAC `(Q1:real^2->bool) SUBSET C'` THEN
        UNDISCH_TAC `(a:real^2) IN Q1` THEN SET_TAC[];
        UNDISCH_TAC
         `(p:real^N->real^2) x IN IMAGE p (K INTER U) INTER C'` THEN
        REWRITE_TAC[IN_INTER]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `v:real^2`
      (X_CHOOSE_THEN `w':real^2` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(p:real^N->real^2) x IN IMAGE (\y:real^2. y + d) Q1`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a:real^2` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `open (IMAGE (\y:real^2. y + d) Q1)` THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `(p:real^N->real^2) x`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `r2 = min r r1` THEN
    SUBGOAL_THEN `&0 < r2 /\ r2 <= r /\ r2 <= r1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < r1` THEN
      EXPAND_TAC "r2" THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ball((p:real^N->real^2) x,r2) SUBSET IMAGE (\y:real^2. y + d) Q1`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball((p:real^N->real^2) x,r1)` THEN
      ASM_SIMP_TAC[SUBSET_BALL];
      ALL_TAC] THEN
    SUBGOAL_THEN `ball((p:real^N->real^2) x,r2) SUBSET C` ASSUME_TAC THENL
     [UNDISCH_TAC
       `ball((p:real^N->real^2) x,r2) SUBSET IMAGE (\y:real^2. y + d) Q1` THEN
      UNDISCH_TAC `IMAGE (\y:real^2. y + d) Q1 SUBSET C` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (p:real^N->real^2) (IMAGE (H:real^N->real^N) J INTER U) INTER
      ball(p x,r2) =
      {p x + s % v | s IN (:real)} INTER ball(p x,r2)`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`P:real^2->real^2`; `P':real^2->real^2`; `Q1:real^2->bool`;
                     `IMAGE (p:real^N->real^2) (J INTER U)`; `C':real^2->bool`;
                     `d:real^2`; `(p:real^N->real^2) x`; `r2:real`]
        MOI_FGB_TRANSLATE_REGION) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC MOI_FGB_BALL_SHRINK THEN EXISTS_TAC `r:real` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (p:real^N->real^2) (K INTER U) INTER ball(p x,r2) =
      {p x + s % w' | s IN (:real)} INTER ball(p x,r2)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `IMAGE (p:real^N->real^2) (K INTER U) INTER ball(p x,r2) =
        (IMAGE p (K INTER U) INTER C') INTER ball(p x,r2)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `ball((p:real^N->real^2) x,r2) SUBSET C` THEN
        UNDISCH_TAC `(C:real^2->bool) SUBSET C'` THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_FGB_BALL_SHRINK THEN EXISTS_TAC `r:real` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `ball((p:real^N->real^2) x,r2) SUBSET IMAGE p U` ASSUME_TAC THENL
     [UNDISCH_TAC `ball((p:real^N->real^2) x,r2) SUBSET C` THEN
      UNDISCH_TAC `(C:real^2->bool) SUBSET IMAGE (p:real^N->real^2) U` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`X:real^N->bool`; `U:real^N->bool`; `p:real^N->real^2`;
                   `q:real^2->real^N`; `IMAGE (H:real^N->real^N) J`; `K:real^N->bool`;
                   `(p:real^N->real^2) x`; `r2:real`; `v:real^2`; `w':real^2`]
      MOI_FGB_CROSS_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^2->real^N) ((p:real^N->real^2) x) = x`
    (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x:real^N. x IN U ==> (q:real^2->real^N) ((p:real^N->real^2) x) = x`)
        (concl th))) THEN
    UNDISCH_TAC `(x:real^N) IN IMAGE (H:real^N->real^N) J INTER K INTER U` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* T. Phase 2 by induction on the number of non-crossing intersection      *)
(* points, and the curve theorem GENERAL_POSITION_CURVES_2.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_INJ_IMAGE_INTER = prove
 (`!(f:real^N->real^M) s t u.
     (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\ s SUBSET u /\ t SUBSET u
     ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [SET_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `y:real^M` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a:real^N = b` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET]]);;

let MOI_FGB_CURVE_CROSSING_LOCAL = prove
 (`!X (J:real^N->bool) J' K x W.
     pl_curve_crossing_at X J K x /\ open_in (subtopology euclidean X) W /\
     x IN W /\ J INTER W = J' INTER W
     ==> pl_curve_crossing_at X J' K x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_curve_crossing_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `f:real^N->real^2` (X_CHOOSE_THEN `g:real^2->real^N`
      STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `u:real^N->bool`; `W:real^N->bool`;
                 `f:real^N->real^2`; `g:real^2->real^N`] MOI_FGB_CHART_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b:real^N. a IN u /\ b IN u /\ (f:real^N->real^2) a = f b ==> a = b`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (u,IMAGE f u) ((f:real^N->real^2),(g:real^2->real^N))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u INTER W:real^N->bool`; `f:real^N->real^2`;
                        `g:real^2->real^N`] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^2) (u INTER W) SUBSET IMAGE f u` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `J' INTER u INTER W = (J INTER u) INTER (u INTER W:real^N->bool)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `(J:real^N->bool) INTER W = J' INTER W` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^N->real^2`; `J INTER u:real^N->bool`;
                   `u INTER W:real^N->bool`; `u:real^N->bool`]
      MOI_FGB_INJ_IMAGE_INTER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INTER_SUBSET]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^2) (u INTER W) SUBSET IMAGE f u` THEN
    SET_TAC[];
    SUBGOAL_THEN `K INTER u INTER W = (K INTER u) INTER (u INTER W:real^N->bool)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^N->real^2`; `K INTER u:real^N->bool`;
                   `u INTER W:real^N->bool`; `u:real^N->bool`]
      MOI_FGB_INJ_IMAGE_INTER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INTER_SUBSET]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^2) (u INTER W) SUBSET IMAGE f u` THEN
    SET_TAC[]]);;

let MOI_FGB_IMAGE_OUTSIDE = prove
 (`!X (J:real^N->bool) H Q.
     J SUBSET X /\ (!z. z IN X /\ ~(z IN Q) ==> H z = z) /\
     (!z. z IN Q ==> H z IN Q)
     ==> IMAGE H J INTER (X DIFF Q) = J INTER (X DIFF Q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_IMAGE] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)
      STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~((z:real^N) IN Q)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((x:real^N) IN Q)` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN X` ASSUME_TAC THENL
     [UNDISCH_TAC `(J:real^N->bool) SUBSET X` THEN
      UNDISCH_TAC `(z:real^N) IN J` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(H:real^N->real^N) z = z` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!z:real^N. z IN X /\ ~(z IN Q) ==> (H:real^N->real^N) z = z`)
          (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `x = (H:real^N->real^N) z` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!z:real^N. z IN X /\ ~(z IN Q) ==> (H:real^N->real^N) z = z`)
        (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FGB_PLH_KEEPS = prove
 (`!X v (H:real^N->real^N) G J.
     pl_homeomorphism (X,X) (H,G) /\ (!x. x IN X /\ ~(x IN v) ==> H x = x) /\
     J SUBSET v /\ v SUBSET X
     ==> IMAGE H J SUBSET v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_homeomorphism (X,X) ((H:real^N->real^N),(G:real^N->real^N))` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN X /\ z IN v` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(J:real^N->bool) SUBSET v` THEN
    UNDISCH_TAC `(v:real^N->bool) SUBSET X` THEN
    UNDISCH_TAC `(z:real^N) IN J` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(H:real^N->real^N) z IN X` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (H:real^N->real^N) X = X` THEN
    UNDISCH_TAC `(z:real^N) IN X` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(H:real^N->real^N) ((H:real^N->real^N) z) = H z` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x:real^N. x IN X /\ ~(x IN v) ==> (H:real^N->real^N) x = x`)
        (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `G:real^N->real^N`) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((H:real^N->real^N) z IN v)` THEN ASM_REWRITE_TAC[]);;

let MOI_FGB_PHASE2 = prove
 (`!c (K:real^N->bool) v.
     combinatorial_manifold_with_boundary 2 c /\ moi_ptr_dim_polyhedron 1 K /\
     K SUBSET UNIONS c DIFF surface_boundary c /\
     open_in (subtopology euclidean (UNIONS c)) v
     ==> !n (J:real^N->bool) e.
           moi_ptr_dim_polyhedron 1 J /\ J SUBSET v /\ FINITE (J INTER K) /\
           CARD {x | x IN J INTER K /\ ~pl_curve_crossing_at (UNIONS c) J K x} <= n /\
           &0 < e
           ==> ?H G. pl_homeomorphism (UNIONS c,UNIONS c) (H,G) /\
                     (!x. x IN UNIONS c /\ ~(x IN v) ==> H x = x) /\
                     (!x. x IN UNIONS c ==> dist(H x,x) < e) /\
                     FINITE (IMAGE H J INTER K) /\
                     !x. x IN IMAGE H J INTER K
                         ==> pl_curve_crossing_at (UNIONS c) (IMAGE H J) K x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `locally_polyhedral (UNIONS c:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_LF_COMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^N->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [UNDISCH_TAC `(K:real^N->bool) SUBSET UNIONS c DIFF surface_boundary c` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!J:real^N->bool e.
       J SUBSET UNIONS c /\ FINITE (J INTER K) /\
       (!x. x IN J INTER K ==> pl_curve_crossing_at (UNIONS c) J K x) /\ &0 < e
       ==> ?H G. pl_homeomorphism (UNIONS c,UNIONS c) (H,G) /\
                 (!x. x IN UNIONS c /\ ~(x IN v) ==> H x = x) /\
                 (!x. x IN UNIONS c ==> dist(H x,x) < e) /\
                 FINITE (IMAGE H J INTER K) /\
                 !x. x IN IMAGE H J INTER K
                     ==> pl_curve_crossing_at (UNIONS c) (IMAGE H J) K x`
  (LABEL_TAC "idc") THENL
   [REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`\x:real^N. x`; `\x:real^N. x`] THEN
    ASM_SIMP_TAC[MOI_FGB_PLH_ID; IMAGE_ID; DIST_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!J:real^N->bool. FINITE (J INTER K)
      ==> FINITE {x | x IN J INTER K /\ ~pl_curve_crossing_at (UNIONS c) J K x}`
  (LABEL_TAC "fin") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `J INTER K:real^N->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [MAP_EVERY X_GEN_TAC [`J:real^N->bool`; `e:real`] THEN STRIP_TAC THEN
    USE_THEN "idc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(J:real^N->bool) SUBSET v` THEN
      UNDISCH_TAC `(v:real^N->bool) SUBSET UNIONS c` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{x:real^N | x IN J INTER K /\ ~pl_curve_crossing_at (UNIONS c) J K x} = {}`
    MP_TAC THENL
     [USE_THEN "fin" (fun th -> SIMP_TAC[GSYM CARD_EQ_0; MATCH_MP th
        (ASSUME `FINITE (J INTER K:real^N->bool)`)]) THEN
      UNDISCH_TAC
       `CARD {x:real^N | x IN J INTER K /\ ~pl_curve_crossing_at (UNIONS c) J K x}
        <= 0` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`J:real^N->bool`; `e:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(J:real^N->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [UNDISCH_TAC `(J:real^N->bool) SUBSET v` THEN
    UNDISCH_TAC `(v:real^N->bool) SUBSET UNIONS c` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `{x:real^N | x IN J INTER K /\ ~pl_curve_crossing_at (UNIONS c) J K x} = {}`
  THENL
   [USE_THEN "idc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `{x:real^N | x IN J INTER K /\ ~pl_curve_crossing_at (UNIONS c) J K x} = {}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  UNDISCH_TAC
   `(x0:real^N) IN {x | x IN J INTER K /\ ~pl_curve_crossing_at (UNIONS c) J K x}` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x0:real^N`] MOI_FGB_SURF_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(K:real^N->bool) SUBSET UNIONS c DIFF surface_boundary c` THEN
    UNDISCH_TAC `(x0:real^N) IN K` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U0:real^N->bool` (X_CHOOSE_THEN `p:real^N->real^2`
    (X_CHOOSE_THEN `q:real^2->real^N` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `W = v INTER (UNIONS c DIFF ((J INTER K) DELETE (x0:real^N)))` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (W:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL
     [UNDISCH_TAC `(J:real^N->bool) SUBSET UNIONS c` THEN SET_TAC[];
      MATCH_MP_TAC FINITE_IMP_CLOSED THEN ASM_REWRITE_TAC[FINITE_DELETE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `U0:real^N->bool`; `W:real^N->bool`;
                 `p:real^N->real^2`; `q:real^2->real^N`] MOI_FGB_CHART_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `U = U0 INTER (W:real^N->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x0:real^N) IN U` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "W"] THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_DELETE] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(J:real^N->bool) SUBSET v` THEN
    UNDISCH_TAC `(v:real^N->bool) SUBSET UNIONS c` THEN
    UNDISCH_TAC `(x0:real^N) IN J` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET v` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "W"] THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `p:real^N->real^2`; `q:real^2->real^N`]
    MOI_FGB_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(J:real^N->bool) INTER K INTER U SUBSET {(q:real^2->real^N) ((p:real^N->real^2) x0)}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(q:real^2->real^N) ((p:real^N->real^2) x0) = x0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `U0 INTER W = (U:real^N->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC
     `v INTER (UNIONS c DIFF ((J INTER K) DELETE (x0:real^N))) = W` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_ACCEPT_TAC(SET_RULE
     `!J K U0 v X x0:real^N.
        J INTER K INTER U0 INTER v INTER (X DIFF ((J INTER K) DELETE x0))
        SUBSET {x0}`);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(p:real^N->real^2) x0`; `IMAGE (p:real^N->real^2) U`]
    MOI_FGB_CUBE_IN_OPEN_2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `J:real^N->bool`; `K:real^N->bool`;
                 `U:real^N->bool`; `p:real^N->real^2`; `q:real^2->real^N`;
                 `(p:real^N->real^2) x0`; `rho:real`; `e / &2`] MOI_FGB_PHASE2_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H1:real^N->real^N` (X_CHOOSE_THEN `G1:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "idU")
     (CONJUNCTS_THEN2 (LABEL_TAC "d1") (CONJUNCTS_THEN2 (LABEL_TAC "idQ")
      (CONJUNCTS_THEN2 (LABEL_TAC "inQ") (CONJUNCTS_THEN2 ASSUME_TAC
       (LABEL_TAC "crU"))))))))) THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `J:real^N->bool`; `H1:real^N->real^N`;
                 `G1:real^N->real^N`] MOI_FGB_PLH_IMAGE_DIM1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (H1:real^N->real^N) J SUBSET v` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FGB_PLH_KEEPS THEN
    MAP_EVERY EXISTS_TAC [`UNIONS c:real^N->bool`; `G1:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    USE_THEN "idU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(U:real^N->bool) SUBSET v` THEN
    UNDISCH_TAC `~((x:real^N) IN v)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact (IMAGE (q:real^2->real^N)
               {y | infnorm(y - (p:real^N->real^2) x0) <= &2 * rho}) /\
    IMAGE q {y | infnorm(y - p x0) <= &2 * rho} SUBSET U`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(p:real^N->real^2) x0`; `rho:real`] MOI_FGB_CUBES_2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `{y:real^2 | infnorm(y - (p:real^N->real^2) x0) <= &2 * rho} SUBSET
      IMAGE p U`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `{y:real^2 | infnorm(y - (p:real^N->real^2) x0) <= &3 * rho}` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `{y:real^2 | infnorm(y - (p:real^N->real^2) x0) < &3 * rho}` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (p:real^N->real^2) U` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE
       `!(f:real^2->real^N) s t u. IMAGE f s = u /\ t SUBSET s ==> IMAGE f t SUBSET u`) THEN
      EXISTS_TAC `IMAGE (p:real^N->real^2) U` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `J:real^N->bool`; `H1:real^N->real^N`;
                 `IMAGE (q:real^2->real^N)
                    {y | infnorm(y - (p:real^N->real^2) x0) <= &2 * rho}`]
    MOI_FGB_IMAGE_OUTSIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `FINITE (IMAGE (H1:real^N->real^N) J INTER K)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `(IMAGE (H1:real^N->real^N) J INTER K INTER U) UNION (J INTER K)` THEN
    ASM_REWRITE_TAC[FINITE_UNION] THEN
    MATCH_MP_TAC(SET_RULE
     `!A J K U Q X:real^N->bool.
        A INTER (X DIFF Q) = J INTER (X DIFF Q) /\ Q SUBSET U /\ A SUBSET X
        ==> A INTER K SUBSET (A INTER K INTER U) UNION (J INTER K)`) THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (q:real^2->real^N) {y | infnorm(y - (p:real^N->real^2) x0) <= &2 * rho}`;
      `UNIONS c:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:real^N | x IN IMAGE (H1:real^N->real^N) J INTER K /\
                ~pl_curve_crossing_at (UNIONS c) (IMAGE H1 J) K x} SUBSET
    {x | x IN J INTER K /\ ~pl_curve_crossing_at (UNIONS c) J K x} DELETE x0`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_INTER] THEN
    X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((z:real^N) IN U)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC
       `~pl_curve_crossing_at (UNIONS c) (IMAGE (H1:real^N->real^N) J) K z` THEN
      REWRITE_TAC[] THEN USE_THEN "crU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~((z:real^N) IN IMAGE (q:real^2->real^N)
                       {y | infnorm(y - (p:real^N->real^2) x0) <= &2 * rho})`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!a b (z:real^N). a SUBSET b /\ ~(z IN b) ==> ~(z IN a)`) THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN UNIONS c` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!a b (z:real^N). a SUBSET b /\ z IN a ==> z IN b`) THEN
      EXISTS_TAC `IMAGE (H1:real^N->real^N) J` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN J` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!A J X Q (z:real^N). A INTER (X DIFF Q) = J INTER (X DIFF Q) /\
                             z IN A /\ z IN X /\ ~(z IN Q) ==> z IN J`) THEN
      MAP_EVERY EXISTS_TAC
       [`IMAGE (H1:real^N->real^N) J`; `UNIONS c:real^N->bool`;
        `IMAGE (q:real^2->real^N) {y | infnorm(y - (p:real^N->real^2) x0) <= &2 * rho}`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC
       `~pl_curve_crossing_at (UNIONS c) (IMAGE (H1:real^N->real^N) J) K z` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FGB_CURVE_CROSSING_LOCAL THEN
      MAP_EVERY EXISTS_TAC
       [`J:real^N->bool`;
        `UNIONS c DIFF IMAGE (q:real^2->real^N)
           {y | infnorm(y - (p:real^N->real^2) x0) <= &2 * rho}`] THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
      MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `v:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~((z:real^N) IN U)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {x:real^N | x IN IMAGE (H1:real^N->real^N) J INTER K /\
                     ~pl_curve_crossing_at (UNIONS c) (IMAGE H1 J) K x} <= n`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
     `CARD({x:real^N | x IN J INTER K /\ ~pl_curve_crossing_at (UNIONS c) J K x}
           DELETE x0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_DELETE] THEN
      USE_THEN "fin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `(x0:real^N) IN
        {x | x IN J INTER K /\ ~pl_curve_crossing_at (UNIONS c) J K x}`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]; ALL_TAC] THEN
      USE_THEN "fin" (fun th -> SIMP_TAC[CARD_DELETE; MATCH_MP th
        (ASSUME `FINITE (J INTER K:real^N->bool)`)]) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `CARD {x:real^N | x IN J INTER K /\ ~pl_curve_crossing_at (UNIONS c) J K x}
        <= SUC n` THEN
      ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "IH" (MP_TAC o SPECL [`IMAGE (H1:real^N->real^N) J`; `e / &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H2:real^N->real^N` (X_CHOOSE_THEN `G2:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "id2")
     (CONJUNCTS_THEN2 (LABEL_TAC "d2") STRIP_ASSUME_TAC))))) THEN
  EXISTS_TAC `(H2:real^N->real^N) o (H1:real^N->real^N)` THEN
  EXISTS_TAC `(G1:real^N->real^N) o (G2:real^N->real^N)` THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `UNIONS c:real^N->bool` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(H1:real^N->real^N) x = x` SUBST1_TAC THENL
     [USE_THEN "idU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(U:real^N->bool) SUBSET v` THEN
      UNDISCH_TAC `~((x:real^N) IN v)` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "id2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(H1:real^N->real^N) x IN UNIONS c` ASSUME_TAC THENL
     [UNDISCH_TAC
       `pl_homeomorphism (UNIONS c,UNIONS c)
          ((H1:real^N->real^N),(G1:real^N->real^N))` THEN
      REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
      UNDISCH_TAC `(x:real^N) IN UNIONS c` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH
     `!a b c:real^N e. dist(a,b) < e / &2 /\ dist(b,c) < e / &2 ==> dist(a,c) < e`) THEN
    EXISTS_TAC `(H1:real^N->real^N) x` THEN
    CONJ_TAC THENL
     [USE_THEN "d2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "d1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[IMAGE_o; GSYM IN_INTER] THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* U. The curve theorem.                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_FGB_CM1_DIM = prove
 (`!c s:real^N->bool. combinatorial_manifold 1 c /\ s IN c ==> aff_dim s <= &1`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_FM3_LF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (UNIONS (simplicial_link c (v:real^N)))` ASSUME_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold 1 (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[pl_sphere] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPEC `k:real^N->bool` MOI_FGB_SIMPLEX_1_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `IMAGE (f:real^N->real^N) (relative_frontier k) =
      UNIONS (simplicial_link c (v:real^N))`
    (SUBST1_TAC o SYM) THENL
     [UNDISCH_TAC
       `pl_homeomorphism (relative_frontier k,UNIONS (simplicial_link c (v:real^N)))
          ((f:real^N->real^N),(g:real^N->real^N))` THEN
      SIMP_TAC[pl_homeomorphism; homeomorphism];
      ALL_TAC] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{a:real^N,b}` THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[relative_frontier] THEN
    ASM_SIMP_TAC[CLOSURE_SEGMENT; RELATIVE_INTERIOR_SEGMENT] THEN
    REWRITE_TAC[open_segment] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(s':real^N->bool) <= &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE (s':real^N->bool) /\ convex s'` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `UNIONS (simplicial_link c (v:real^N))` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `!x:real^N->bool s. x IN s ==> x SUBSET UNIONS s`) THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(s':real^N->bool) IN c` ASSUME_TAC THENL
         [UNDISCH_TAC `(s':real^N->bool) IN simplicial_link c v` THEN
          REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN SIMP_TAC[];
          ALL_TAC] THEN
        ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX]];
      ALL_TAC] THEN
    ASM_CASES_TAC `s':real^N->bool = {}` THENL
     [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `a:real^N` o
      GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    SUBGOAL_THEN `s' = {a:real^N}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_SING] THEN X_GEN_TAC `b:real^N` THEN EQ_TAC THENL
       [DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        SUBGOAL_THEN `segment[a:real^N,b] SUBSET s'` ASSUME_TAC THENL
         [UNDISCH_TAC `convex(s':real^N->bool)` THEN
          REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `FINITE(segment[a:real^N,b])` MP_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s':real^N->bool` THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[FINITE_SEGMENT] THEN ASM_MESON_TAC[]];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `aff_dim(convex hull ((v:real^N) INSERT s')) = aff_dim s' + &1` THEN
  UNDISCH_TAC `s = convex hull ((v:real^N) INSERT s')` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `aff_dim(s':real^N->bool) <= &0` THEN INT_ARITH_TAC);;

let MOI_FGB_CM1_DIM1 = prove
 (`!j:(real^N->bool)->bool.
     FINITE j /\ combinatorial_manifold 1 j
     ==> moi_ptr_dim_polyhedron 1 (UNIONS j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_ptr_dim_polyhedron] THEN
  EXISTS_TAC `j:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; lf_simplicial_complex;
                  SIMPLEX_IMP_POLYTOPE];
    ASM_MESON_TAC[MOI_FGB_CM1_DIM]]);;

let GENERAL_POSITION_CURVES_2 = prove
 (`!(c:(real^N->bool)->bool) (j:(real^N->bool)->bool) (k:(real^N->bool)->bool) v e.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     FINITE j /\ combinatorial_manifold 1 j /\
     FINITE k /\ combinatorial_manifold 1 k /\
     UNIONS j SUBSET UNIONS c DIFF surface_boundary c /\
     UNIONS k SUBSET UNIONS c DIFF surface_boundary c /\
     open_in (subtopology euclidean (UNIONS c)) v /\ UNIONS j SUBSET v /\ &0 < e
     ==> ?f g. pl_homeomorphism (UNIONS c,UNIONS c) (f,g) /\
               (!x. x IN UNIONS c DIFF v ==> f x = x) /\
               (!x. x IN UNIONS c ==> dist(f x,x) < e) /\
               FINITE (IMAGE f (UNIONS j) INTER UNIONS k) /\
               !x. x IN IMAGE f (UNIONS j) INTER UNIONS k
                   ==> pl_curve_crossing_at (UNIONS c) (IMAGE f (UNIONS j))
                                            (UNIONS k) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_ptr_dim_polyhedron 1 (UNIONS j:real^N->bool) /\
    moi_ptr_dim_polyhedron 1 (UNIONS k:real^N->bool)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FGB_CM1_DIM1]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `UNIONS j:real^N->bool`;
                 `UNIONS k:real^N->bool`; `v:real^N->bool`; `e / &2`]
    MOI_FGB_PHASE1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H1:real^N->real^N` (X_CHOOSE_THEN `G1:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "id1")
     (CONJUNCTS_THEN2 (LABEL_TAC "d1") STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `UNIONS k:real^N->bool`;
                 `v:real^N->bool`] MOI_FGB_PHASE2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`CARD {x:real^N | x IN IMAGE (H1:real^N->real^N) (UNIONS j) INTER UNIONS k /\
                      ~pl_curve_crossing_at (UNIONS c) (IMAGE H1 (UNIONS j))
                                            (UNIONS k) x}`;
    `IMAGE (H1:real^N->real^N) (UNIONS j)`; `e / &2`]) THEN
  ASM_REWRITE_TAC[REAL_HALF; LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `H2:real^N->real^N` (X_CHOOSE_THEN `G2:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "id2")
     (CONJUNCTS_THEN2 (LABEL_TAC "d2") STRIP_ASSUME_TAC))))) THEN
  EXISTS_TAC `(H2:real^N->real^N) o (H1:real^N->real^N)` THEN
  EXISTS_TAC `(G1:real^N->real^N) o (G2:real^N->real^N)` THEN
  REWRITE_TAC[IMAGE_o] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `UNIONS c:real^N->bool` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; o_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(H1:real^N->real^N) x = x` SUBST1_TAC THENL
     [USE_THEN "id1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "id2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(H1:real^N->real^N) x IN UNIONS c` ASSUME_TAC THENL
     [UNDISCH_TAC
       `pl_homeomorphism (UNIONS c,UNIONS c)
          ((H1:real^N->real^N),(G1:real^N->real^N))` THEN
      REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
      UNDISCH_TAC `(x:real^N) IN UNIONS c` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH
     `!a b c:real^N e. dist(a,b) < e / &2 /\ dist(b,c) < e / &2 ==> dist(a,c) < e`) THEN
    EXISTS_TAC `(H1:real^N->real^N) x` THEN
    CONJ_TAC THENL
     [USE_THEN "d2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "d1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

