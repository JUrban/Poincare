(* ========================================================================= *)
(* pc_moi_lt_gpb1a: Euclidean tools for the chart step of the loop theorem   *)
(* (pc_moi_lt_gpb1, CHART_STEP = MOI_LGB_CHART_STEP of                       *)
(* pc_moi_lt_gpbstmt.ml).  Contents: injectivity on closed stars from local  *)
(* injectivity (cone scaling); certificates for the injectivity of two       *)
(* triangles sharing a vertex or an edge, stable under small moves of the    *)
(* vertex values; a Lebesgue number for closed stars; the two-to-one bound   *)
(* for small perturbations (compactness on triples); generic points and the  *)
(* one-step dimension count of the general position induction.               *)
(*                                                                           *)
(* Exported (used by pc_moi_lt_gpb1b and pc_moi_lt_gpb1):                   *)
(*   cones and stars: MOI_LGB1_CONE_SHRINK, CONE_INJ, STAR_INJ, PURE2,       *)
(*     INTERIOR_UNIONS_EMPTY, STAR_LEBESGUE;                                *)
(*   triangles: COLLINEAR_AT, COLLINEAR_CROSS, NONCOLL_INDEP, HULL3_DIFF,   *)
(*     HULL3_DIFF_IN, SEG_DIFF_IN, SEG_AFFINE, TRI_REP, TRI_REP2,           *)
(*     TRI_IMAGE, TRI_INJ, TRI_PAIR_CASES, VERTEX_IN, VERTEX_IN_ST;         *)
(*   certificates: VCERT_SUFF, VCERT_EXISTS, VCERT_STABLE, ECERT_SUFF,       *)
(*     ECERT_EXISTS, ECERT_STABLE, TRI_STABLE, DOT_MARGIN;                   *)
(*   stability: VPAIR_STABLE, EPAIR_STABLE, STAR_STABLE, UNION_INJ,         *)
(*     INJ_NEQ, FINITE_EPS;                                                  *)
(*   openness: NONZERO_NEAR, NEG_NEAR, PK3_NORM, PK4_NORM, CONT_TAC (an ML  *)
(*     tactic);                                                              *)
(*   two-to-one: NO_THREE, CLOSED_DIST_GE, IN_PCROSS, TWO_TO_ONE;            *)
(*   general position: GEN_EXISTS.                                           *)
(* (the full names begin with MOI_LGB1_).                                    *)
(* ========================================================================= *)

let moi_lgb1_saved_interface = !the_interface;;
needs "Multivariate/cross.ml";;
the_interface := moi_lgb1_saved_interface;;
needs "src/pc_moi_lt_gpbstmt.ml";;
needs "src/pc_moi_fnd_gpa.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A1. Injectivity on a cone from injectivity near the apex.  If g is       *)
(* affine on the convex sets r1 and r2 through v and injective near v, then *)
(* it is injective on r1 UNION r2: shrink both points towards v by the same *)
(* factor (the images shrink towards g v by the same factor).  Applied to   *)
(* the closed stars of a simplicial complex.                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_CONE_SHRINK = prove
 (`!(g:real^M->real^N) r (v:real^M) t l y.
     convex r /\ v IN r /\ linear l /\ (!x. x IN r ==> g x = l x + y) /\
     &0 <= t /\ t <= &1
     ==> !w. w IN r
             ==> ((&1 - t) % v + t % w) IN r /\
                 g((&1 - t) % v + t % w) = (&1 - t) % g v + t % g w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `((&1 - t) % v + t % w:real^M) IN r` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONVEX_ALT]; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN VECTOR_ARITH_TAC);;

let MOI_LGB1_CONE_INJ = prove
 (`!(g:real^M->real^N) s r1 r2 (v:real^M) n.
     convex r1 /\ convex r2 /\ v IN r1 /\ v IN r2 /\ r1 SUBSET s /\ r2 SUBSET s /\
     (?l y. linear l /\ !x. x IN r1 ==> g x = l x + y) /\
     (?l y. linear l /\ !x. x IN r2 ==> g x = l x + y) /\
     open n /\ v IN n /\
     (!x y. x IN n INTER s /\ y IN n INTER s /\ g x = g y ==> x = y)
     ==> !x y. x IN r1 /\ y IN r2 /\ g x = g y ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l1:real^M->real^N`
                       (X_CHOOSE_THEN `y1:real^N` STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l2:real^M->real^N`
                       (X_CHOOSE_THEN `y2:real^N` STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "inj"))))))))))) THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `z:real^M`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?e. &0 < e /\ ball(v:real^M,e) SUBSET n` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
  ABBREV_TAC `D = norm(x - v:real^M) + norm(z - v) + &1` THEN
  SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MP_TAC(ISPEC `x - v:real^M` NORM_POS_LE) THEN
    MP_TAC(ISPEC `z - v:real^M` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&1`; `e / D`] REAL_DOWN2) THEN
  ASM_SIMP_TAC[REAL_LT_01; REAL_LT_DIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t * D < e` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_RDIV_EQ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^M->real^N`; `r1:real^M->bool`; `v:real^M`; `t:real`;
                 `l1:real^M->real^N`; `y1:real^N`] MOI_LGB1_CONE_SHRINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^M->real^N`; `r2:real^M->bool`; `v:real^M`; `t:real`;
                 `l2:real^M->real^N`; `y2:real^N`] MOI_LGB1_CONE_SHRINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^M. norm(w - v) < D ==> ((&1 - t) % v + t % w) IN n`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; dist] THEN
    REWRITE_TAC[VECTOR_ARITH `v - ((&1 - t) % v + t % w):real^M = t % (v - w)`] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `abs t * norm(v - w:real^M) <= t * D` MP_TAC THENL
     [ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - t) % v + t % x:real^M = (&1 - t) % v + t % z` MP_TAC THENL
   [REMOVE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "D" THEN
      MP_TAC(ISPEC `z - v:real^M` NORM_POS_LE) THEN REAL_ARITH_TAC;
      ASM SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "D" THEN
      MP_TAC(ISPEC `x - v:real^M` NORM_POS_LE) THEN REAL_ARITH_TAC;
      ASM SET_TAC[]];
    REWRITE_TAC[VECTOR_ARITH `a + t % x:real^M = a + t % z <=> t % (x - z) = vec 0`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; VECTOR_SUB_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* A2. Two triangles of real^3 sharing a vertex P meet only in P exactly    *)
(* when a linear functional is positive on the other two vertices of one    *)
(* and negative on those of the other (relative to P); such a certificate   *)
(* survives small moves of the five points.                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_COLLINEAR_AT = prove
 (`!P A B:real^N. collinear{P,A,B} <=> collinear{vec 0,A - P,B - P}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{P,A,B} = {A,P,B:real^N}` SUBST1_TAC THENL
   [SET_TAC[]; GEN_REWRITE_TAC LAND_CONV [COLLINEAR_3] THEN REFL_TAC]);;

let MOI_LGB1_NONCOLL_INDEP = prove
 (`!P A B:real^N.
     ~collinear{P,A,B}
     ==> !u v. u % (A - P) + v % (B - P) = vec 0 ==> u = &0 /\ v = &0`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[MOI_LGB1_COLLINEAR_AT] THEN
  ONCE_REWRITE_TAC[SET_RULE `{a:real^N,b,c} = {a,c,b}`] THEN
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN DISCH_THEN(LABEL_TAC "eq") THEN
  ASM_CASES_TAC `u = &0` THENL
   [REMOVE_THEN "eq" MP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_MUL_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `u % (A - P:real^N) = u % (--(v / u) % (B - P))` MP_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `u * --(v / u) = --v` SUBST1_TAC THENL
     [UNDISCH_TAC `~(u = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REMOVE_THEN "eq" MP_TAC THEN VECTOR_ARITH_TAC;
    ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL]]);;

let MOI_LGB1_HULL3_DIFF = prove
 (`!P A B (z:real^N).
     z IN convex hull {P,A,B}
     ==> ?b c. &0 <= b /\ &0 <= c /\ b + c <= &1 /\
               z - P = b % (A - P) + c % (B - P)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
    (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`b:real`; `c:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a = &1 - b - c` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let MOI_LGB1_HULL3_DIFF_IN = prove
 (`!P A B (z:real^N) b c.
     &0 <= b /\ &0 <= c /\ b + c <= &1 /\ z - P = b % (A - P) + c % (B - P)
     ==> z IN convex hull {P,A,B}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`&1 - b - c`; `b:real`; `c:real`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN VECTOR_ARITH_TAC);;

let MOI_LGB1_VCERT_SUFF = prove
 (`!P A1 A2 B1 B2 (l:real^N).
     &0 < l dot (A1 - P) /\ &0 < l dot (A2 - P) /\
     l dot (B1 - P) < &0 /\ l dot (B2 - P) < &0
     ==> convex hull {P,A1,A2} INTER convex hull {P,B1,B2} SUBSET {P}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_SING] THEN X_GEN_TAC `z:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o MATCH_MP MOI_LGB1_HULL3_DIFF) (MP_TAC o MATCH_MP MOI_LGB1_HULL3_DIFF)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `f:real` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `b * (l dot (A1 - P)) + c * (l dot (A2 - P)) =
    e * (l dot (B1 - P)) + f * (l dot (B2 - P:real^N))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DOT_RMUL; GSYM DOT_RADD] THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b * (l dot (A1 - P:real^N)) /\ &0 <= c * (l dot (A2 - P)) /\
                &0 <= e * --(l dot (B1 - P)) /\ &0 <= f * --(l dot (B2 - P))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `b * (l dot (A1 - P:real^N)) = &0 /\ c * (l dot (A2 - P)) = &0`
  MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_RNEG]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN STRIP_TAC THEN
  UNDISCH_TAC `z - P:real^N = b % (A1 - P) + c % (A2 - P)` THEN
  REWRITE_TAC[ASSUME `b = &0`; ASSUME `c = &0`; VECTOR_MUL_LZERO; VECTOR_ADD_LID;
              VECTOR_SUB_EQ]);;

let MOI_LGB1_VCERT_EXISTS = prove
 (`!P A1 A2 B1 B2:real^N.
     ~collinear{P,A1,A2} /\ ~collinear{P,B1,B2} /\
     convex hull {P,A1,A2} INTER convex hull {P,B1,B2} SUBSET {P}
     ==> ?l. &0 < l dot (A1 - P) /\ &0 < l dot (A2 - P) /\
             l dot (B1 - P) < &0 /\ l dot (B2 - P) < &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "na") (CONJUNCTS_THEN2 (LABEL_TAC "nb")
    (LABEL_TAC "meet"))) THEN
  ABBREV_TAC `C1 = convex hull {A1 - P,A2 - P:real^N}` THEN
  ABBREV_TAC `C2 = IMAGE (--) (convex hull {B1 - P,B2 - P:real^N})` THEN
  SUBGOAL_THEN `convex (C1:real^N->bool) /\ ~(C1 = {}) /\ compact C1 /\
                convex (C2:real^N->bool) /\ ~(C2 = {}) /\ compact C2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C1"; "C2"] THEN
    SIMP_TAC[CONVEX_CONVEX_HULL; CONVEX_NEGATIONS; IMAGE_EQ_EMPTY;
             CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
    CONJ_TAC THEN TRY(MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN
                      REWRITE_TAC[linear] THEN
                      CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC]) THEN
    MATCH_MP_TAC FINITE_IMP_COMPACT_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`convex hull (C1 UNION C2:real^N->bool)`; `vec 0:real^N`]
    SEPARATING_HYPERPLANE_CLOSED_POINT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_CONVEX_HULL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      ASM_SIMP_TAC[COMPACT_UNION];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CONVEX_HULL_UNION_NONEMPTY_EXPLICIT; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `u:real`; `y:real^N`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(x:real^N) IN C1` THEN EXPAND_TAC "C1" THEN
    REWRITE_TAC[CONVEX_HULL_2; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `al:real` (X_CHOOSE_THEN `be:real` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `(y:real^N) IN C2` THEN EXPAND_TAC "C2" THEN
    REWRITE_TAC[CONVEX_HULL_2; IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y0:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `ga:real` (X_CHOOSE_THEN `de:real` STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN
     `((&1 - u) * al) % (A1 - P) + ((&1 - u) * be) % (A2 - P:real^N) =
      (u * ga) % (B1 - P) + (u * de) % (B2 - P)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> lhs(concl th) = `vec 0:real^N`)) THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `P + ((&1 - u) * al) % (A1 - P) + ((&1 - u) * be) % (A2 - P:real^N) = P`
    MP_TAC THENL
     [USE_THEN "meet" (MATCH_MP_TAC o REWRITE_RULE[SUBSET; IN_SING]) THEN
      REWRITE_TAC[IN_INTER] THEN CONJ_TAC THEN
      MATCH_MP_TAC MOI_LGB1_HULL3_DIFF_IN THENL
       [MAP_EVERY EXISTS_TAC [`(&1 - u) * al`; `(&1 - u) * be`];
        MAP_EVERY EXISTS_TAC [`u * ga`; `u * de`]] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE] THEN
      (CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]) THEN
      REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `P + a + b:real^N = P <=> a + b = vec 0`] THEN
    DISCH_TAC THEN
    USE_THEN "na" (MP_TAC o MATCH_MP MOI_LGB1_NONCOLL_INDEP) THEN
    DISCH_THEN(MP_TAC o SPECL [`(&1 - u) * al`; `(&1 - u) * be`]) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `u = &1` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `(&1 - u) * (al + be) = &0` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_ADD_LID]; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_MUL_RID] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "nb" (MP_TAC o MATCH_MP MOI_LGB1_NONCOLL_INDEP) THEN
    DISCH_THEN(MP_TAC o SPECL [`&1 * ga`; `&1 * de`]) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> rand(concl th) =
        `(&1 * ga) % (B1 - P) + (&1 * de) % (B2 - P:real^N)`)) THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
      DISCH_THEN(ACCEPT_TAC o SYM);
      REWRITE_TAC[REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_RZERO; real_gt] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N` (X_CHOOSE_THEN `b:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep")))) THEN
  EXISTS_TAC `l:real^N` THEN
  SUBGOAL_THEN `!w:real^N. w IN C1 UNION C2 ==> b < l dot w` (LABEL_TAC "sep2")
  THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN REMOVE_THEN "sep" MATCH_MP_TAC THEN
    MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A1 - P:real^N) IN C1 /\ (A2 - P) IN C1 /\
                --(B1 - P) IN C2 /\ --(B2 - P) IN C2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C1"; "C2"] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC FUN_IN_IMAGE) THEN MATCH_MP_TAC HULL_INC THEN
    REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REMOVE_THEN "sep2" (MP_TAC o SPEC `A1 - P:real^N`);
    REMOVE_THEN "sep2" (MP_TAC o SPEC `A2 - P:real^N`);
    REMOVE_THEN "sep2" (MP_TAC o SPEC `--(B1 - P):real^N`);
    REMOVE_THEN "sep2" (MP_TAC o SPEC `--(B2 - P):real^N`)] THEN
  ASM_REWRITE_TAC[IN_UNION; DOT_RNEG] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A3. Stability of the certificates under small moves of the points: a    *)
(* fixed functional keeps strict signs (explicit margin); the cross product *)
(* conditions for triangles and for two triangles sharing an edge are open  *)
(* (continuity in the packed tuple of points).                               *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_DOT_MARGIN = prove
 (`!(l:real^N) x y x' y' m e.
     m <= l dot (x - y) /\ e * &2 * (norm l + &1) <= m /\
     norm(x' - x) < e /\ norm(y' - y) < e
     ==> &0 < l dot (x' - y')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l dot (x' - y') = l dot (x - y) + l dot ((x' - x) - (y' - y):real^N)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DOT_RADD] THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:real^N`; `(x' - x) - (y' - y):real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  SUBGOAL_THEN `norm((x' - x) - (y' - y):real^N) <= &2 * e` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`norm(x' - x:real^N) < e`; `norm(y' - y:real^N) < e`] THEN
    NORM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(l:real^N) * norm((x' - x) - (y' - y):real^N) <= norm l * (&2 * e)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e` MP_TAC THENL
   [MP_TAC(ISPEC `x' - x:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_LGB1_VCERT_STABLE = prove
 (`!P A1 A2 B1 B2 (l:real^N).
     &0 < l dot (A1 - P) /\ &0 < l dot (A2 - P) /\
     l dot (B1 - P) < &0 /\ l dot (B2 - P) < &0
     ==> ?e. &0 < e /\
             !P' A1' A2' B1' B2'.
               norm(P' - P) < e /\ norm(A1' - A1) < e /\ norm(A2' - A2) < e /\
               norm(B1' - B1) < e /\ norm(B2' - B2) < e
               ==> &0 < l dot (A1' - P') /\ &0 < l dot (A2' - P') /\
                   l dot (B1' - P') < &0 /\ l dot (B2' - P') < &0`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `m = min (min (l dot (A1 - P)) (l dot (A2 - P)))
                      (min (l dot (P - B1)) (l dot (P - B2:real^N)))` THEN
  SUBGOAL_THEN `&0 < m /\ m <= l dot (A1 - P) /\ m <= l dot (A2 - P) /\
                m <= l dot (P - B1) /\ m <= l dot (P - B2:real^N)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN RULE_ASSUM_TAC(REWRITE_RULE[DOT_RSUB]) THEN
    REWRITE_TAC[DOT_RSUB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `m / (&2 * (norm(l:real^N) + &1))` THEN
  SUBGOAL_THEN `&0 < &2 * (norm(l:real^N) + &1)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `l:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  SUBGOAL_THEN `m / (&2 * (norm(l:real^N) + &1)) * &2 * (norm l + &1) <= m`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x < &0 <=> &0 < --x`] THEN
  REWRITE_TAC[GSYM DOT_RNEG; VECTOR_NEG_SUB] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_LGB1_DOT_MARGIN THENL
   [MAP_EVERY EXISTS_TAC [`A1:real^N`; `P:real^N`];
    MAP_EVERY EXISTS_TAC [`A2:real^N`; `P:real^N`];
    MAP_EVERY EXISTS_TAC [`P:real^N`; `B1:real^N`];
    MAP_EVERY EXISTS_TAC [`P:real^N`; `B2:real^N`]] THEN
  MAP_EVERY EXISTS_TAC [`m:real`; `m / (&2 * (norm(l:real^N) + &1))`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_LGB1_COLLINEAR_CROSS = prove
 (`!P A B:real^3. collinear{P,A,B} <=> (A - P) cross (B - P) = vec 0`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[MOI_LGB1_COLLINEAR_AT] THEN
  REWRITE_TAC[CROSS_EQ_0]);;

let MOI_LGB1_NONZERO_NEAR = prove
 (`!(f:real^M->real^N) z.
     f continuous (at z) /\ ~(f z = vec 0)
     ==> ?e. &0 < e /\ !w. norm(w - z) < e ==> ~(f w = vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `norm((f:real^M->real^N) z)`)
    ASSUME_TAC) THEN
  ASM_REWRITE_TAC[NORM_POS_LT] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^M`) THEN ASM_REWRITE_TAC[dist] THEN
  CONV_TAC NORM_ARITH);;

let MOI_LGB1_NEG_NEAR = prove
 (`!(f:real^M->real) z.
     (\w. lift(f w)) continuous (at z) /\ f z < &0
     ==> ?e. &0 < e /\ !w. norm(w - z) < e ==> f w < &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `--((f:real^M->real) z)`)
    ASSUME_TAC) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^M`) THEN
  ASM_REWRITE_TAC[dist; GSYM LIFT_SUB; NORM_LIFT] THEN ASM_REAL_ARITH_TAC);;

let MOI_LGB1_PK3_NORM = prove
 (`!(P:real^N) (A:real^N) (B:real^N) P' A' B'.
     norm(pastecart P' (pastecart A' B') - pastecart P (pastecart A B)) <=
     norm(P' - P) + norm(A' - A) + norm(B' - B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PASTECART_SUB] THEN
  MP_TAC(ISPECL [`P' - P:real^N`; `pastecart (A' - A:real^N) (B' - B:real^N)`]
    NORM_PASTECART_LE) THEN
  MP_TAC(ISPECL [`A' - A:real^N`; `B' - B:real^N`] NORM_PASTECART_LE) THEN
  REAL_ARITH_TAC);;

let MOI_LGB1_PK4_NORM = prove
 (`!(P:real^N) (W:real^N) (A:real^N) (B:real^N) P' W' A' B'.
     norm(pastecart P' (pastecart W' (pastecart A' B')) -
          pastecart P (pastecart W (pastecart A B))) <=
     norm(P' - P) + norm(W' - W) + norm(A' - A) + norm(B' - B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PASTECART_SUB] THEN
  MP_TAC(ISPECL [`P' - P:real^N`; `pastecart (W' - W:real^N) (pastecart (A' - A:real^N) (B' - B:real^N))`]
    NORM_PASTECART_LE) THEN
  MP_TAC(ISPECL [`W' - W:real^N`; `pastecart (A' - A:real^N) (B' - B:real^N)`]
    NORM_PASTECART_LE) THEN
  MP_TAC(ISPECL [`A' - A:real^N`; `B' - B:real^N`] NORM_PASTECART_LE) THEN
  REAL_ARITH_TAC);;

(* Continuity of expressions in the packed points (cross, dot, differences  *)
(* of projections), for the openness of the certificates.                    *)

let MOI_LGB1_CONT_TAC =
  let lin = MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
            REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL;
                        SNDCART_CMUL] in
  let rec tac g =
    FIRST [MATCH_MP_TAC CONTINUOUS_CROSS THEN CONJ_TAC THEN tac;
           MATCH_MP_TAC CONTINUOUS_LIFT_DOT2 THEN CONJ_TAC THEN tac;
           MATCH_MP_TAC CONTINUOUS_SUB THEN CONJ_TAC THEN tac;
           lin] g in
  tac;;

let MOI_LGB1_TRI_STABLE = prove
 (`!P A B:real^3.
     ~collinear{P,A,B}
     ==> ?e. &0 < e /\
             !P' A' B'. norm(P' - P) < e /\ norm(A' - A) < e /\ norm(B' - B) < e
                        ==> ~collinear{P',A',B'}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_LGB1_COLLINEAR_CROSS] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\z:real^(3,(3,3)finite_sum)finite_sum.
       (fstcart(sndcart z) - fstcart z) cross (sndcart(sndcart z) - fstcart z)`;
    `pastecart (P:real^3) (pastecart (A:real^3) (B:real^3))`]
   MOI_LGB1_NONZERO_NEAR) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MOI_LGB1_CONT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / &3` THEN ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &3 <=> &0 < e`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `pastecart (P':real^3) (pastecart (A':real^3) (B':real^3))`) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  (ANTS_TAC THENL
    [MP_TAC(ISPECL [`P:real^3`; `A:real^3`; `B:real^3`; `P':real^3`; `A':real^3`;
                    `B':real^3`] MOI_LGB1_PK3_NORM) THEN
     ASM_REAL_ARITH_TAC;
     SIMP_TAC[]]));;

let MOI_LGB1_ECERT_STABLE = prove
 (`!P W A B:real^3.
     ~(((W - P) cross (A - P)) cross ((W - P) cross (B - P)) = vec 0) \/
     ((W - P) cross (A - P)) dot ((W - P) cross (B - P)) < &0
     ==> ?e. &0 < e /\
             !P' W' A' B'.
               norm(P' - P) < e /\ norm(W' - W) < e /\ norm(A' - A) < e /\
               norm(B' - B) < e
               ==> ~(((W' - P') cross (A' - P')) cross ((W' - P') cross (B' - P')) =
                     vec 0) \/
                   ((W' - P') cross (A' - P')) dot ((W' - P') cross (B' - P')) < &0`,
  REPEAT GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC THENL
   [MP_TAC(ISPECL
     [`\z:real^(3,(3,(3,3)finite_sum)finite_sum)finite_sum.
        ((fstcart(sndcart z) - fstcart z) cross
         (fstcart(sndcart(sndcart z)) - fstcart z)) cross
        ((fstcart(sndcart z) - fstcart z) cross
         (sndcart(sndcart(sndcart z)) - fstcart z))`;
      `pastecart (P:real^3) (pastecart (W:real^3) (pastecart (A:real^3) (B:real^3)))`]
     MOI_LGB1_NONZERO_NEAR);
    MP_TAC(ISPECL
     [`\z:real^(3,(3,(3,3)finite_sum)finite_sum)finite_sum.
        ((fstcart(sndcart z) - fstcart z) cross
         (fstcart(sndcart(sndcart z)) - fstcart z)) dot
        ((fstcart(sndcart z) - fstcart z) cross
         (sndcart(sndcart(sndcart z)) - fstcart z))`;
      `pastecart (P:real^3) (pastecart (W:real^3) (pastecart (A:real^3) (B:real^3)))`]
     MOI_LGB1_NEG_NEAR)] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MOI_LGB1_CONT_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / &4` THEN ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &4 <=> &0 < e`] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `pastecart (P':real^3) (pastecart (W':real^3) (pastecart (A':real^3) (B':real^3)))`) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  (ANTS_TAC THENL
    [MP_TAC(ISPECL [`P:real^3`; `W:real^3`; `A:real^3`; `B:real^3`; `P':real^3`;
                    `W':real^3`; `A':real^3`; `B':real^3`] MOI_LGB1_PK4_NORM) THEN
     ASM_REAL_ARITH_TAC;
     SIMP_TAC[]]));;

(* Two triangles of real^3 sharing the edge [P,W]: the cross product        *)
(* certificate (the normals (W-P) x (A-P) and (W-P) x (B-P) are not         *)
(* positively proportional) forces them to meet only in the edge, and       *)
(* conversely for non-degenerate triangles.                                  *)

let MOI_LGB1_SEG_DIFF_IN = prove
 (`!P W (z:real^N) b. &0 <= b /\ b <= &1 /\ z - P = b % (W - P)
                      ==> z IN segment[P,W]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `b:real` THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  VECTOR_ARITH_TAC);;

let MOI_LGB1_ECERT_SUFF = prove
 (`!P W A B:real^3.
     ~(((W - P) cross (A - P)) cross ((W - P) cross (B - P)) = vec 0) \/
     ((W - P) cross (A - P)) dot ((W - P) cross (B - P)) < &0
     ==> convex hull {P,W,A} INTER convex hull {P,W,B} SUBSET segment[P,W]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP MOI_LGB1_HULL3_DIFF)
    (MP_TAC o MATCH_MP MOI_LGB1_HULL3_DIFF)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `f:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "z2")))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` (X_CHOOSE_THEN `c:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "z1")))))) THEN
  SUBGOAL_THEN `c % ((W - P) cross (A - P)) = f % ((W - P) cross (B - P:real^3))`
  (LABEL_TAC "cr") THENL
   [MP_TAC(AP_TERM `(cross) (W - P:real^3)` (TRANS (SYM(ASSUME
      `z - P:real^3 = b % (W - P) + c % (A - P)`)) (ASSUME
      `z - P:real^3 = e % (W - P) + f % (B - P)`))) THEN
    REWRITE_TAC[CROSS_RADD; CROSS_RMUL; CROSS_REFL; VECTOR_MUL_RZERO;
                VECTOR_ADD_LID];
    ALL_TAC] THEN
  ASM_CASES_TAC `c = &0` THENL
   [MATCH_MP_TAC MOI_LGB1_SEG_DIFF_IN THEN EXISTS_TAC `b:real` THEN
    USE_THEN "z1" SUBST1_TAC THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `f = &0` THENL
   [MATCH_MP_TAC MOI_LGB1_SEG_DIFF_IN THEN EXISTS_TAC `e:real` THEN
    USE_THEN "z2" SUBST1_TAC THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(W - P) cross (A - P) = (f / c) % ((W - P) cross (B - P:real^3))`
  ASSUME_TAC THENL
   [REMOVE_THEN "cr" (MP_TAC o AP_TERM `(%) (inv c):real^3->real^3`) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
    REWRITE_TAC[real_div; REAL_MUL_AC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CROSS_LMUL; CROSS_REFL; VECTOR_MUL_RZERO; DOT_LMUL] THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[REAL_NOT_LT] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[DOT_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC);;

let MOI_LGB1_ECERT_EXISTS = prove
 (`!P W A B:real^3.
     ~collinear{P,W,A} /\ ~collinear{P,W,B} /\
     convex hull {P,W,A} INTER convex hull {P,W,B} SUBSET segment[P,W]
     ==> ~(((W - P) cross (A - P)) cross ((W - P) cross (B - P)) = vec 0) \/
         ((W - P) cross (A - P)) dot ((W - P) cross (B - P)) < &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_LGB1_COLLINEAR_CROSS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "meet"))) THEN
  ONCE_REWRITE_TAC[TAUT `~p \/ q <=> (p ==> q)`] THEN
  ONCE_REWRITE_TAC[CROSS_EQ_0] THEN REWRITE_TAC[COLLINEAR_LEMMA] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:real`) THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 <= x) ==> x < &0`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 <= ((W - P) cross (A - P)) dot ((W - P) cross (B - P:real^3))` THEN
    ASM_REWRITE_TAC[DOT_RMUL] THEN
    SUBGOAL_THEN `&0 < ((W - P) cross (A - P)) dot ((W - P) cross (A - P:real^3))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `~(t = &0)` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((W - P) cross (B - P:real^3) = vec 0)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO];
      ALL_TAC] THEN
    MP_TAC(SPECL [`&0`; `t:real`;
      `((W - P) cross (A - P)) dot ((W - P) cross (A - P:real^3))`] REAL_LE_RMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?s. B - P:real^3 = t % (A - P) + s % (W - P)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(W - P) cross ((B - P) - t % (A - P:real^3)) = vec 0` MP_TAC THENL
     [ASM_REWRITE_TAC[CROSS_RSUB; CROSS_RMUL; VECTOR_SUB_REFL]; ALL_TAC] THEN
    REWRITE_TAC[CROSS_EQ_0; COLLINEAR_LEMMA] THEN STRIP_TAC THENL
     [UNDISCH_TAC `~((W - P) cross (A - P:real^3) = vec 0)` THEN
      ASM_REWRITE_TAC[CROSS_LZERO];
      EXISTS_TAC `&0` THEN FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
      VECTOR_ARITH_TAC;
      EXISTS_TAC `c:real` THEN FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?ep. &0 < ep /\ ep * (abs s + &1) <= &1 /\ ep * (abs s + s + t) <= &1`
  STRIP_ASSUME_TAC THENL
   [ABBREV_TAC `D = &2 * abs s + t + &1` THEN
    SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL
     [EXPAND_TAC "D" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `inv D` THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    SUBGOAL_THEN `inv D * D = &1` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv D * D` THEN
    (CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]]) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "D" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `z:real^3 = P + (ep * abs s) % (W - P) + ep % (B - P)` THEN
  SUBGOAL_THEN `(z:real^3) IN segment[P,W]` MP_TAC THENL
   [USE_THEN "meet" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_INTER] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_LGB1_HULL3_DIFF_IN THENL
     [MAP_EVERY EXISTS_TAC [`ep * (abs s + s)`; `ep * t`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM REAL_ADD_ASSOC] THEN
        ASM_REWRITE_TAC[];
        EXPAND_TAC "z" THEN
        REWRITE_TAC[ASSUME `B - P:real^3 = t % (A - P) + s % (W - P)`] THEN
        VECTOR_ARITH_TAC];
      MAP_EVERY EXISTS_TAC [`ep * abs s`; `ep:real`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        EXPAND_TAC "z" THEN VECTOR_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ep % (B - P:real^3) = (k - ep * abs s) % (W - P)` MP_TAC THENL
   [UNDISCH_TAC `P + (ep * abs s) % (W - P) + ep % (B - P:real^3) = z` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(cross) (W - P:real^3)`) THEN
  REWRITE_TAC[CROSS_RMUL; CROSS_REFL; VECTOR_MUL_RZERO; VECTOR_MUL_EQ_0] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ]);;

(* ------------------------------------------------------------------------- *)
(* A4. Triangulations of std_triangle are pure; vertex forms of triangles;  *)
(* a uniform positive bound over a finite set.                               *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_INTERIOR_UNIONS_EMPTY = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ (!t. t IN c ==> closed t /\ interior t = {})
     ==> interior (UNIONS c) = {}`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; INTERIOR_EMPTY; UNIONS_INSERT; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `c:(real^N->bool)->bool`] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INTERIOR_UNION_EQ_EMPTY]);;

let MOI_LGB1_PURE2 = prove
 (`!(L:(real^2->bool)->bool) k s.
     simplicial_complex L /\ UNIONS L = k /\ convex k /\ ~(interior k = {}) /\
     s IN L /\ ~(s = {})
     ==> ?t. t IN L /\ aff_dim t = &2 /\ s SUBSET t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `!t:real^2->bool. t IN L ==> closed t /\ convex t` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `interior (UNIONS {t:real^2->bool | t IN L /\ ~(aff_dim t = &2)}) = {}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_INTERIOR_UNIONS_EMPTY THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^2->bool` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC EMPTY_INTERIOR_AFF_DIM THEN
    MP_TAC(ISPEC `t:real^2->bool` AFF_DIM_LE_UNIV) THEN
    UNDISCH_TAC `~(aff_dim(t:real^2->bool) = &2)` THEN
    REWRITE_TAC[DIMINDEX_2] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k SUBSET UNIONS {t:real^2->bool | t IN L /\ aff_dim t = &2}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `closed (UNIONS {t:real^2->bool | t IN L /\ aff_dim t = &2})`
    MP_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CLOSURE_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN closure(interior k)` MP_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CLOSURE_INTERIOR] THEN
      ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `~(interior k INTER ball(z:real^2,e / &2) SUBSET
        UNIONS {t:real^2->bool | t IN L /\ ~(aff_dim t = &2)})`
    MP_TAC THENL
     [DISCH_THEN(MP_TAC o MATCH_MP SUBSET_INTERIOR) THEN
      ASM_SIMP_TAC[INTERIOR_OPEN; OPEN_INTER; OPEN_INTERIOR; OPEN_BALL;
                   SUBSET_EMPTY] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `z:real^2` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP; IN_INTER; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^2` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(y:real^2) IN UNIONS L` MP_TAC THENL
       [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
      UNDISCH_TAC `~((y:real^2) IN UNIONS {t | t IN L /\ ~(aff_dim t = &2)})` THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      UNDISCH_TAC `dist(z:real^2,y) < e / &2` THEN
      UNDISCH_TAC `dist(z:real^2,x) < e / &2` THEN NORM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^2. x IN relative_interior s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN k` MP_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[IN_UNIONS] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN UNIONS {t | t IN L /\ aff_dim t = &2}` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s INTER t:real^2->bool = s` (fun th -> ASM SET_TAC[th]) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `s INTER t:real^2->bool`]
    FACE_OF_SUBSET_RELATIVE_FRONTIER) THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[relative_frontier; SUBSET; IN_INTER; IN_DIFF] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]);;

let MOI_LGB1_FINITE_EPS = prove
 (`!(P:A->real->bool) s.
     FINITE s /\ (!x e e'. P x e /\ &0 < e' /\ e' <= e ==> P x e') /\
     (!x. x IN s ==> ?e. &0 < e /\ P x e)
     ==> ?e. &0 < e /\ !x. x IN s ==> P x e`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a ==> b ==> c ==> d`] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; FORALL_IN_INSERT] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  REMOVE_THEN "ih" (MP_TAC o MATCH_MP (TAUT `(p ==> q ==> r) ==> p /\ q ==> r`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e1 e2` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    EXISTS_TAC `e2:real` THEN ASM_SIMP_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC]);;

let MOI_LGB1_TRI_REP = prove
 (`!t (v:real^N).
     &2 simplex t /\ v extreme_point_of t
     ==> ?a b. t = convex hull {v,a,b} /\ ~collinear{v,a,b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC)
    MP_TAC) THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(c:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD(c:real^N->bool)):int = &2 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    (X_CHOOSE_THEN `r:real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `~affine_dependent(c:real^N->bool)` THEN
  UNDISCH_TAC `(v:real^N) IN c` THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [MAP_EVERY EXISTS_TAC [`q:real^N`; `r:real^N`];
    MAP_EVERY EXISTS_TAC [`p:real^N`; `r:real^N`];
    MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`]] THEN
  ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN
  REPEAT CONJ_TAC THEN TRY (AP_TERM_TAC THEN SET_TAC[]) THEN
  ASM_MESON_TAC[INSERT_AC]);;

let MOI_LGB1_TRI_REP2 = prove
 (`!t (v:real^N) w.
     &2 simplex t /\ v extreme_point_of t /\ w extreme_point_of t /\ ~(v = w)
     ==> ?a. t = convex hull {v,w,a} /\ ~collinear{v,w,a}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `v:real^N`] MOI_LGB1_TRI_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `w:real^N = a \/ w = b` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^N) extreme_point_of t` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `a:real^N` THEN
    SUBGOAL_THEN `{v:real^N,w,a} = {v,a,b}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* A5. Affine maps on triangles; two triangles of a complex through a       *)
(* vertex v meet in v or in an edge [v,w]; the injectivity of a map affine  *)
(* on both survives small moves of the five or four vertex values.          *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_TRI_IMAGE = prove
 (`!(f:real^M->real^N) p q r.
     (?l y. linear l /\ !x. x IN convex hull {p,q,r} ==> f x = l x + y)
     ==> IMAGE f (convex hull {p,q,r}) = convex hull {f p, f q, f r}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`\x:real^M. x`; `f:real^M->real^N`; `f:real^M->real^N`;
                 `l:real^M->real^N`; `y:real^N`; `{p:real^M,q,r}`]
    MOI_REAL_IMAGE_SIMPLEX) THEN
  REWRITE_TAC[IMAGE_ID; IMAGE_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]);;

let MOI_LGB1_TRI_INJ = prove
 (`!(f:real^M->real^N) p q r.
     (?l y. linear l /\ !x. x IN convex hull {p,q,r} ==> f x = l x + y) /\
     ~collinear{f p, f q, f r}
     ==> !x x'. x IN convex hull {p,q,r} /\ x' IN convex hull {p,q,r} /\
                f x = f x' ==> x = x'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^M->real^N`
    (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `l:real^M->real^N`; `y:real^N`;
                 `{p:real^M,q,r}`] MOI_FGP_AFFINE_INJ_ON_HULL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
    UNDISCH_TAC `~collinear{(f:real^M->real^N) p,f q,f r}` THEN
    REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC HULL_INC THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]];
    ASM_MESON_TAC[]]);;

let MOI_LGB1_TRI_PAIR_CASES = prove
 (`!(L:(real^N->bool)->bool) t t' v.
     simplicial_complex L /\ t IN L /\ t' IN L /\ aff_dim t = &2 /\
     aff_dim t' = &2 /\ ~(t = t') /\ {v} IN L /\ v IN t /\ v IN t'
     ==> (?a1 a2 b1 b2. t = convex hull {v,a1,a2} /\ t' = convex hull {v,b1,b2} /\
                        ~collinear{v,a1,a2} /\ ~collinear{v,b1,b2} /\
                        t INTER t' = {v}) \/
         (?w a b. t = convex hull {v,w,a} /\ t' = convex hull {v,w,b} /\
                  ~collinear{v,w,a} /\ ~collinear{v,w,b} /\
                  t INTER t' = segment[v,w])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `&2 simplex (t:real^N->bool) /\ &2 simplex (t':real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `({v:real^N} INTER t) face_of t /\ ({v} INTER t') face_of t' /\
                (t INTER t') face_of t /\ (t INTER t') face_of t'`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} INTER t = {v} /\ {v} INTER t' = {v}`
    (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FACE_OF_SING] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t INTER t':real^N->bool = {v}` THENL
   [DISJ1_TAC THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `v:real^N`] MOI_LGB1_TRI_REP) THEN
    MP_TAC(ISPECL [`t':real^N->bool`; `v:real^N`] MOI_LGB1_TRI_REP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `b1:real^N` (X_CHOOSE_THEN `b2:real^N` STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `a1:real^N` (X_CHOOSE_THEN `a2:real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`a1:real^N`; `a2:real^N`; `b1:real^N`; `b2:real^N`] THEN
    ASM_REWRITE_TAC[];
    DISJ2_TAC] THEN
  SUBGOAL_THEN `?w:real^N. ~(w = v) /\ w extreme_point_of t /\ w IN t'`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^N->bool`; `v:real^N`] MOI_LGB1_TRI_REP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `~affine_dependent{v:real^N,a,b}` ASSUME_TAC THENL
     [ASM_MESON_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
    UNDISCH_TAC `(t INTER t':real^N->bool) face_of t` THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
             ASSUME `~affine_dependent{v:real^N,a,b}`] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?w:real^N. w IN u /\ ~(w = v)` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM;
        TAUT `~(p /\ ~q) <=> p ==> q`]) THEN
      UNDISCH_TAC `~(t INTER t':real^N->bool = {v})` THEN
      SUBGOAL_THEN `u SUBSET {v:real^N}` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(v:real^N) IN t INTER t'` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `convex hull u SUBSET {v:real^N}` MP_TAC THENL
       [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[CONVEX_SING]; ALL_TAC] THEN
      UNDISCH_TAC `t INTER t':real^N->bool = convex hull u` THEN SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN ASM SET_TAC[];
      SUBGOAL_THEN `(w:real^N) IN convex hull u` MP_TAC THENL
       [ASM_SIMP_TAC[HULL_INC]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) extreme_point_of t'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t INTER t':real^N->bool`; `t':real^N->bool`; `w:real^N`]
      EXTREME_POINT_OF_FACE) THEN
    MP_TAC(ISPECL [`t INTER t':real^N->bool`; `t:real^N->bool`; `w:real^N`]
      EXTREME_POINT_OF_FACE) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    SUBGOAL_THEN `(w:real^N) IN t` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[extreme_point_of]; MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `v:real^N`; `w:real^N`] MOI_LGB1_TRI_REP2) THEN
  MP_TAC(ISPECL [`t':real^N->bool`; `v:real^N`; `w:real^N`] MOI_LGB1_TRI_REP2) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(v:real^N = w)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`w:real^N`; `a:real^N`; `b:real^N`] THEN
  ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `{v:real^N,w,a}`; `{v:real^N,w,b}`]
    MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL) THEN
  SUBGOAL_THEN `~affine_dependent{v:real^N,w,a} /\ ~affine_dependent{v:real^N,w,b}`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `~(a:real^N = b)` MP_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~collinear{v:real^N,w,a}` THEN UNDISCH_TAC `~collinear{v:real^N,w,b}` THEN
  REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN SET_TAC[]);;

let MOI_LGB1_UNION_INJ = prove
 (`!(f:A->B) s t.
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y) /\
     IMAGE f s INTER IMAGE f t SUBSET IMAGE f (s INTER t)
     ==> !x y. x IN s UNION t /\ y IN s UNION t /\ f x = f y ==> x = y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; IN_UNION] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s") (CONJUNCTS_THEN2 (LABEL_TAC "t")
    (LABEL_TAC "st"))) THEN
  SUBGOAL_THEN `!x y. x IN s /\ y IN t /\ (f:A->B) x = f y ==> x = y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "st" (MP_TAC o SPEC `(f:A->B) x`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:A = z /\ y = z` (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL
     [USE_THEN "s" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      USE_THEN "t" MATCH_MP_TAC THEN ASM_MESON_TAC[]];
    ASM_MESON_TAC[]]);;

let MOI_LGB1_INJ_NEQ = prove
 (`!(f:A->B) s p q.
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     p IN s /\ q IN s /\ ~(p = q)
     ==> ~(f p = f q)`,
  MESON_TAC[]);;

let MOI_LGB1_VPAIR_STABLE = prove
 (`!(f0:real^M->real^3) v a1 a2 b1 b2.
     (?l y. linear l /\ !x. x IN convex hull {v,a1,a2} ==> f0 x = l x + y) /\
     (?l y. linear l /\ !x. x IN convex hull {v,b1,b2} ==> f0 x = l x + y) /\
     convex hull {v,a1,a2} INTER convex hull {v,b1,b2} = {v} /\
     ~collinear{v,a1,a2} /\ ~collinear{v,b1,b2} /\
     (!x y. x IN convex hull {v,a1,a2} UNION convex hull {v,b1,b2} /\
            y IN convex hull {v,a1,a2} UNION convex hull {v,b1,b2} /\
            f0 x = f0 y ==> x = y)
     ==> ?e. &0 < e /\
             !f. (?l y. linear l /\ !x. x IN convex hull {v,a1,a2} ==> f x = l x + y) /\
                 (?l y. linear l /\ !x. x IN convex hull {v,b1,b2} ==> f x = l x + y) /\
                 norm(f v - f0 v) < e /\ norm(f a1 - f0 a1) < e /\
                 norm(f a2 - f0 a2) < e /\ norm(f b1 - f0 b1) < e /\
                 norm(f b2 - f0 b2) < e
                 ==> !x y. x IN convex hull {v,a1,a2} UNION convex hull {v,b1,b2} /\
                           y IN convex hull {v,a1,a2} UNION convex hull {v,b1,b2} /\
                           f x = f y ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fa") (CONJUNCTS_THEN2 (LABEL_TAC "fb")
    (CONJUNCTS_THEN2 (LABEL_TAC "meet") (CONJUNCTS_THEN2 (LABEL_TAC "na")
    (CONJUNCTS_THEN2 (LABEL_TAC "nb") (LABEL_TAC "inj")))))) THEN
  SUBGOAL_THEN `~collinear{(f0:real^M->real^3) v,f0 a1,f0 a2} /\
                ~collinear{(f0:real^M->real^3) v,f0 b1,f0 b2}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THENL
     [USE_THEN "fa" (X_CHOOSE_THEN `l:real^M->real^3` (X_CHOOSE_THEN `y:real^3`
        STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`f0:real^M->real^3`; `l:real^M->real^3`; `y:real^3`;
                     `{v:real^M,a1,a2}`] MOI_FGP_INJ_AFFINE_INDEPENDENT) THEN
      UNDISCH_TAC `~collinear{v:real^M,a1,a2}`;
      USE_THEN "fb" (X_CHOOSE_THEN `l:real^M->real^3` (X_CHOOSE_THEN `y:real^3`
        STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`f0:real^M->real^3`; `l:real^M->real^3`; `y:real^3`;
                     `{v:real^M,b1,b2}`] MOI_FGP_INJ_AFFINE_INDEPENDENT) THEN
      UNDISCH_TAC `~collinear{v:real^M,b1,b2}`] THEN
    REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
    (ANTS_TAC THENL
      [REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
       DISCH_TAC THEN ASM_REWRITE_TAC[]]) THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_LGB1_INJ_NEQ THEN
    EXISTS_TAC `convex hull {v:real^M,a1,a2} UNION convex hull {v,b1,b2}` THEN
    (CONJ_TAC THENL
      [USE_THEN "inj" ACCEPT_TAC; ASM_SIMP_TAC[IN_UNION; HULL_INC; IN_INSERT]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {(f0:real^M->real^3) v,f0 a1,f0 a2} INTER
    convex hull {f0 v,f0 b1,f0 b2} SUBSET {f0 v}`
  ASSUME_TAC THENL
   [USE_THEN "fa" (SUBST1_TAC o SYM o MATCH_MP MOI_LGB1_TRI_IMAGE) THEN
    USE_THEN "fb" (SUBST1_TAC o SYM o MATCH_MP MOI_LGB1_TRI_IMAGE) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; IN_SING] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `x':real^M` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `x:real^M = x'` SUBST_ALL_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `x':real^M = v` SUBST_ALL_TAC THENL
     [MP_TAC(ASSUME `convex hull {v:real^M,a1,a2} INTER convex hull {v,b1,b2} = {v}`) THEN
      ASM SET_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(f0:real^M->real^3) v`; `(f0:real^M->real^3) a1`;
                 `(f0:real^M->real^3) a2`; `(f0:real^M->real^3) b1`;
                 `(f0:real^M->real^3) b2`] MOI_LGB1_VCERT_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real^3` (fun th -> ASSUME_TAC th THEN
    MP_TAC(MATCH_MP MOI_LGB1_VCERT_STABLE th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e1"))) THEN
  MP_TAC(ISPECL [`(f0:real^M->real^3) v`; `(f0:real^M->real^3) a1`;
                 `(f0:real^M->real^3) a2`] MOI_LGB1_TRI_STABLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e2"))) THEN
  MP_TAC(ISPECL [`(f0:real^M->real^3) v`; `(f0:real^M->real^3) b1`;
                 `(f0:real^M->real^3) b2`] MOI_LGB1_TRI_STABLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e3"))) THEN
  EXISTS_TAC `min e1 (min e2 e3)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `f:real^M->real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ga") (CONJUNCTS_THEN2 (LABEL_TAC "gb")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~collinear{(f:real^M->real^3) v,f a1,f a2} /\
                ~collinear{(f:real^M->real^3) v,f b1,f b2}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [USE_THEN "e2" MATCH_MP_TAC; USE_THEN "e3" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LGB1_UNION_INJ THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_TRI_INJ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_LGB1_TRI_INJ THEN ASM_REWRITE_TAC[];
    USE_THEN "ga" (SUBST1_TAC o MATCH_MP MOI_LGB1_TRI_IMAGE) THEN
    USE_THEN "gb" (SUBST1_TAC o MATCH_MP MOI_LGB1_TRI_IMAGE) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
    MATCH_MP_TAC MOI_LGB1_VCERT_SUFF THEN EXISTS_TAC `lam:real^3` THEN
    USE_THEN "e1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB1_SEG_AFFINE = prove
 (`!(f:real^M->real^N) s v w.
     convex s /\ v IN s /\ w IN s /\
     (?l y. linear l /\ !x. x IN s ==> f x = l x + y)
     ==> IMAGE f (segment[v,w]) = segment[f v,f w]`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `l:real^M->real^N`
      (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `!u. &0 <= u /\ u <= &1
                    ==> ((&1 - u) % v + u % w:real^M) IN s /\
                        (f:real^M->real^N) ((&1 - u) % v + u % w) =
                        (&1 - u) % f v + u % f w`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `((&1 - u) % v + u % w:real^M) IN s` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONVEX_ALT]; ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SEGMENT] THEN X_GEN_TAC `z:real^N` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^M` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `u:real` THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(&1 - u) % v + u % w:real^M` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[]]]);;

let MOI_LGB1_EPAIR_STABLE = prove
 (`!(f0:real^M->real^3) v w a b.
     (?l y. linear l /\ !x. x IN convex hull {v,w,a} ==> f0 x = l x + y) /\
     (?l y. linear l /\ !x. x IN convex hull {v,w,b} ==> f0 x = l x + y) /\
     convex hull {v,w,a} INTER convex hull {v,w,b} = segment[v,w] /\
     ~collinear{v,w,a} /\ ~collinear{v,w,b} /\
     (!x y. x IN convex hull {v,w,a} UNION convex hull {v,w,b} /\
            y IN convex hull {v,w,a} UNION convex hull {v,w,b} /\
            f0 x = f0 y ==> x = y)
     ==> ?e. &0 < e /\
             !f. (?l y. linear l /\ !x. x IN convex hull {v,w,a} ==> f x = l x + y) /\
                 (?l y. linear l /\ !x. x IN convex hull {v,w,b} ==> f x = l x + y) /\
                 norm(f v - f0 v) < e /\ norm(f w - f0 w) < e /\
                 norm(f a - f0 a) < e /\ norm(f b - f0 b) < e
                 ==> !x y. x IN convex hull {v,w,a} UNION convex hull {v,w,b} /\
                           y IN convex hull {v,w,a} UNION convex hull {v,w,b} /\
                           f x = f y ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fa") (CONJUNCTS_THEN2 (LABEL_TAC "fb")
    (CONJUNCTS_THEN2 (LABEL_TAC "meet") (CONJUNCTS_THEN2 (LABEL_TAC "na")
    (CONJUNCTS_THEN2 (LABEL_TAC "nb") (LABEL_TAC "inj")))))) THEN
  SUBGOAL_THEN `~collinear{(f0:real^M->real^3) v,f0 w,f0 a} /\
                ~collinear{(f0:real^M->real^3) v,f0 w,f0 b}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THENL
     [USE_THEN "fa" (X_CHOOSE_THEN `l:real^M->real^3` (X_CHOOSE_THEN `y:real^3`
        STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`f0:real^M->real^3`; `l:real^M->real^3`; `y:real^3`;
                     `{v:real^M,w,a}`] MOI_FGP_INJ_AFFINE_INDEPENDENT) THEN
      UNDISCH_TAC `~collinear{v:real^M,w,a}`;
      USE_THEN "fb" (X_CHOOSE_THEN `l:real^M->real^3` (X_CHOOSE_THEN `y:real^3`
        STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`f0:real^M->real^3`; `l:real^M->real^3`; `y:real^3`;
                     `{v:real^M,w,b}`] MOI_FGP_INJ_AFFINE_INDEPENDENT) THEN
      UNDISCH_TAC `~collinear{v:real^M,w,b}`] THEN
    REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
    (ANTS_TAC THENL
      [REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
       DISCH_TAC THEN ASM_REWRITE_TAC[]]) THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_LGB1_INJ_NEQ THEN
    EXISTS_TAC `convex hull {v:real^M,w,a} UNION convex hull {v,w,b}` THEN
    (CONJ_TAC THENL
      [USE_THEN "inj" ACCEPT_TAC; ASM_SIMP_TAC[IN_UNION; HULL_INC; IN_INSERT]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g:real^M->real^3.
      (?l y. linear l /\ !x. x IN convex hull {v,w,a} ==> g x = l x + y)
      ==> IMAGE g (segment[v,w]) = segment[g v,g w]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGB1_SEG_AFFINE THEN
    EXISTS_TAC `convex hull {v:real^M,w,a}` THEN
    ASM_SIMP_TAC[CONVEX_CONVEX_HULL; HULL_INC; IN_INSERT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {(f0:real^M->real^3) v,f0 w,f0 a} INTER
    convex hull {f0 v,f0 w,f0 b} SUBSET segment[f0 v,f0 w]`
  ASSUME_TAC THENL
   [USE_THEN "fa" (SUBST1_TAC o SYM o MATCH_MP MOI_LGB1_TRI_IMAGE) THEN
    USE_THEN "fb" (SUBST1_TAC o SYM o MATCH_MP MOI_LGB1_TRI_IMAGE) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME
      `?l y. linear l /\ !x. x IN convex hull {v,w,a} ==>
             (f0:real^M->real^3) x = l x + y`))]) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `x':real^M` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `x:real^M = x'` SUBST_ALL_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `x':real^M` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `convex hull {v:real^M,w,a} INTER convex hull {v,w,b} = segment[v,w]` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(f0:real^M->real^3) v`; `(f0:real^M->real^3) w`;
                 `(f0:real^M->real^3) a`; `(f0:real^M->real^3) b`]
    MOI_LGB1_ECERT_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_LGB1_ECERT_STABLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e1"))) THEN
  MP_TAC(ISPECL [`(f0:real^M->real^3) v`; `(f0:real^M->real^3) w`;
                 `(f0:real^M->real^3) a`] MOI_LGB1_TRI_STABLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e2"))) THEN
  MP_TAC(ISPECL [`(f0:real^M->real^3) v`; `(f0:real^M->real^3) w`;
                 `(f0:real^M->real^3) b`] MOI_LGB1_TRI_STABLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e3"))) THEN
  EXISTS_TAC `min e1 (min e2 e3)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `f:real^M->real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ga") (CONJUNCTS_THEN2 (LABEL_TAC "gb")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~collinear{(f:real^M->real^3) v,f w,f a} /\
                ~collinear{(f:real^M->real^3) v,f w,f b}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [USE_THEN "e2" MATCH_MP_TAC; USE_THEN "e3" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LGB1_UNION_INJ THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_TRI_INJ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_LGB1_TRI_INJ THEN ASM_REWRITE_TAC[];
    USE_THEN "ga" (SUBST1_TAC o MATCH_MP MOI_LGB1_TRI_IMAGE) THEN
    USE_THEN "gb" (SUBST1_TAC o MATCH_MP MOI_LGB1_TRI_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `?l y. linear l /\ !x. x IN convex hull {v,w,a} ==>
             (f:real^M->real^3) x = l x + y`)]) THEN
    MATCH_MP_TAC MOI_LGB1_ECERT_SUFF THEN
    USE_THEN "e1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A6. Stability of injectivity on a closed star: if f0 is affine on the    *)
(* simplices through v (all faces of triangles through v) and injective on  *)
(* their union, then so is every such f whose vertex values are close to    *)
(* those of f0.  Pairs of triangles meet in v or in an edge [v,w]           *)
(* (MOI_LGB1_TRI_PAIR_CASES); a uniform bound over the finitely many pairs. *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_VERTEX_IN = prove
 (`!(L:(real^N->bool)->bool) p q r.
     simplicial_complex L /\ convex hull {p,q,r} IN L /\ ~collinear{p,q,r}
     ==> {p} IN L /\ {q} IN L /\ {r} IN L`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `~affine_dependent{p:real^N,q,r}` ASSUME_TAC THENL
   [ASM_MESON_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `convex hull {p:real^N,q,r}` THEN
  ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
               IN_INSERT]);;

let MOI_LGB1_VERTEX_IN_ST = prove
 (`!(L:(real^N->bool)->bool) p q r st.
     simplicial_complex L /\ convex hull {p,q,r} IN L /\ ~collinear{p,q,r} /\
     convex hull {p,q,r} SUBSET st
     ==> {p} IN L /\ {q} IN L /\ {r} IN L /\ p IN st /\ q IN st /\ r IN st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `p:real^N`; `q:real^N`; `r:real^N`]
    MOI_LGB1_VERTEX_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]);;

let MOI_LGB1_STAR_STABLE = prove
 (`!(L:(real^2->bool)->bool) v (f0:real^2->real^3).
     simplicial_complex L /\ {v} IN L /\
     (!s. s IN L /\ v IN s ==> ?t. t IN L /\ aff_dim t = &2 /\ s SUBSET t) /\
     (!r. r IN L /\ v IN r ==> ?l y. linear l /\ !x. x IN r ==> f0 x = l x + y) /\
     (!x y. x IN UNIONS {r | r IN L /\ v IN r} /\
            y IN UNIONS {r | r IN L /\ v IN r} /\ f0 x = f0 y ==> x = y)
     ==> ?e. &0 < e /\
             !f. (!r. r IN L /\ v IN r
                      ==> ?l y. linear l /\ !x. x IN r ==> f x = l x + y) /\
                 (!w. {w} IN L /\ w IN UNIONS {r | r IN L /\ v IN r}
                      ==> norm(f w - f0 w) < e)
                 ==> !x y. x IN UNIONS {r | r IN L /\ v IN r} /\
                           y IN UNIONS {r | r IN L /\ v IN r} /\ f x = f y
                           ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pure") (CONJUNCTS_THEN2 (LABEL_TAC "aff0")
      (LABEL_TAC "inj0"))))) THEN
  ABBREV_TAC `St = UNIONS {r:real^2->bool | r IN L /\ v IN r}` THEN
  ABBREV_TAC `Tr = {t:real^2->bool | t IN L /\ aff_dim t = &2 /\ v IN t}` THEN
  SUBGOAL_THEN `FINITE (Tr:(real^2->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Tr" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^2->bool. t IN Tr ==> t IN L /\ v IN t /\ t SUBSET St`
  ASSUME_TAC THENL
   [EXPAND_TAC "Tr" THEN EXPAND_TAC "St" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN St ==> ?t. t IN Tr /\ x IN t` ASSUME_TAC THENL
   [EXPAND_TAC "St" THEN EXPAND_TAC "Tr" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^2` THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^2->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "pure" (MP_TAC o SPEC `r:real^2->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t t'. t IN Tr /\ t' IN Tr
           ==> ?e. &0 < e /\
                   !f. (!r. r IN L /\ v IN r
                            ==> ?l y. linear l /\ !x. x IN r ==> f x = l x + y) /\
                       (!w. {w} IN L /\ w IN St ==> norm(f w - f0 w) < e)
                       ==> !x y. x IN t UNION t' /\ y IN t UNION t' /\
                                 (f:real^2->real^3) x = f y ==> x = y`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real^2->bool`; `t':real^2->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t:real^2->bool) IN L /\ v IN t /\ t SUBSET St /\
                  (t':real^2->bool) IN L /\ v IN t' /\ t' SUBSET St /\
                  aff_dim t = &2 /\ aff_dim t' = &2`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^2->bool) IN Tr` THEN UNDISCH_TAC `(t':real^2->bool) IN Tr` THEN
      EXPAND_TAC "Tr" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x y. x IN t UNION t' /\ y IN t UNION t' /\
                        (f0:real^2->real^3) x = f0 y ==> x = y`
    (LABEL_TAC "inj01") THENL
     [REPEAT STRIP_TAC THEN USE_THEN "inj0" MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `t:real^2->bool = t'` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[UNION_IDEMPOT] THEN
      MP_TAC(ISPECL [`t:real^2->bool`; `v:real^2`] MOI_LGB1_TRI_REP) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [ASM_MESON_TAC[simplicial_complex; AFF_DIM_SIMPLEX];
          REWRITE_TAC[GSYM FACE_OF_SING] THEN
          SUBGOAL_THEN `{v:real^2} = {v} INTER t` SUBST1_TAC THENL
           [ASM SET_TAC[]; ASM_MESON_TAC[simplicial_complex]]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^2`
        STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        lhs(concl th) = `t:real^2->bool`)) THEN
      SUBGOAL_THEN `{a:real^2} IN L /\ {b} IN L` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[MOI_LGB1_VERTEX_IN]; ALL_TAC] THEN
      SUBGOAL_THEN `~collinear{(f0:real^2->real^3) v,f0 a,f0 b}` MP_TAC THENL
       [USE_THEN "aff0" (MP_TAC o SPEC `convex hull {v:real^2,a,b}`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3`
          STRIP_ASSUME_TAC)) THEN
        MP_TAC(ISPECL [`f0:real^2->real^3`; `l:real^2->real^3`; `y:real^3`;
                       `{v:real^2,a,b}`] MOI_FGP_INJ_AFFINE_INDEPENDENT) THEN
        UNDISCH_TAC `~collinear{v:real^2,a,b}` THEN
        REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[UNION_IDEMPOT]) THEN
        (ANTS_TAC THENL
          [REPEAT STRIP_TAC THEN USE_THEN "inj01" MATCH_MP_TAC THEN
           ASM_MESON_TAC[];
           DISCH_TAC THEN ASM_REWRITE_TAC[]]) THEN
        REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_LGB1_INJ_NEQ THEN
        EXISTS_TAC `convex hull {v:real^2,a,b}` THEN
        (CONJ_TAC THENL
          [USE_THEN "inj01" ACCEPT_TAC;
           ASM_SIMP_TAC[HULL_INC; IN_INSERT]]);
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_LGB1_TRI_STABLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st")) THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `f:real^2->real^3` THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_LGB1_TRI_INJ THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "st" MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `convex hull {v:real^2,a,b} SUBSET St` THEN
        MATCH_MP_TAC(SET_RULE `(x:real^2) IN s ==> s SUBSET t ==> x IN t`) THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `t:real^2->bool`; `t':real^2->bool`;
                   `v:real^2`] MOI_LGB1_TRI_PAIR_CASES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      lhs(concl th) = `t:real^2->bool`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      lhs(concl th) = `t':real^2->bool`)) THENL
     [MP_TAC(ISPECL [`f0:real^2->real^3`; `v:real^2`; `a1:real^2`; `a2:real^2`;
                     `b1:real^2`; `b2:real^2`] MOI_LGB1_VPAIR_STABLE);
      MP_TAC(ISPECL [`f0:real^2->real^3`; `v:real^2`; `w:real^2`; `a:real^2`;
                     `b:real^2`] MOI_LGB1_EPAIR_STABLE)] THEN
    (ANTS_TAC THENL [ASM_SIMP_TAC[] THEN USE_THEN "inj01" ACCEPT_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st")) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `f:real^2->real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "aff") (LABEL_TAC "nrm")) THEN
    USE_THEN "st" MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(USE_THEN "aff" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
                             NO_TAC) THEN
    USE_THEN "nrm" MATCH_MP_TAC THEN
    ASM_MESON_TAC[MOI_LGB1_VERTEX_IN_ST];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\p:(real^2->bool)#(real^2->bool) e.
       !f. (!r. r IN L /\ v IN r
                ==> ?l y. linear l /\ !x. x IN r ==> f x = l x + y) /\
           (!w. {w} IN L /\ w IN St ==> norm(f w - f0 w) < e)
           ==> !x y. x IN FST p UNION SND p /\ y IN FST p UNION SND p /\
                     (f:real^2->real^3) x = f y ==> x = y`;
    `(Tr:(real^2->bool)->bool) CROSS Tr`] MOI_LGB1_FINITE_EPS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_CROSS] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`p:(real^2->bool)#(real^2->bool)`; `e:real`; `e':real`] THEN
      STRIP_TAC THEN X_GEN_TAC `f:real^2->real^3` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `f:real^2->real^3`) THEN
      ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e':real` THEN ASM_SIMP_TAC[];
      REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; FST; SND] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "all")) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `f:real^2->real^3` THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?t t'. t IN Tr /\ t' IN Tr /\ (x:real^2) IN t /\ (y:real^2) IN t'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "all" (MP_TAC o SPEC `(t:real^2->bool,t':real^2->bool)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_CROSS]; ALL_TAC] THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(MP_TAC o SPEC `f:real^2->real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION]);;

(* ------------------------------------------------------------------------- *)
(* A7. A Lebesgue number for the closed stars of a finite complex: nearby   *)
(* points lie in a common closed star (open stars are open and cover).      *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_STAR_LEBESGUE = prove
 (`!L:(real^N->bool)->bool.
     simplicial_complex L
     ==> ?d. &0 < d /\
             !x y. x IN UNIONS L /\ y IN UNIONS L /\ dist(x,y) < d
                   ==> ?v. {v} IN L /\ x IN UNIONS {r | r IN L /\ v IN r} /\
                           y IN UNIONS {r | r IN L /\ v IN r}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  ASM_CASES_TAC `UNIONS L:real^N->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN UNIONS L
               ==> ?v. {v} IN L /\
                       !r. r IN L /\ x IN r ==> v IN r`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `{x:real^N}`; `s:real^N->bool`]
      MOI_LGB_MIN_SIMPLEX) THEN
    ASM_REWRITE_TAC[SING_SUBSET] THEN
    DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?v:real^N. v extreme_point_of s0` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX; MEMBER_NOT_EMPTY];
      ALL_TAC] THEN
    EXISTS_TAC `v:real^N` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s0:real^N->bool` THEN
      ASM_REWRITE_TAC[FACE_OF_SING];
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(s0:real^N->bool) SUBSET r` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SING_SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `(v:real^N) IN s ==> s SUBSET r ==> v IN r`) THEN
      ASM_MESON_TAC[extreme_point_of]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`euclidean_metric:(real^N)metric`; `UNIONS L:real^N->bool`;
    `{(:real^N) DIFF UNIONS {r | r IN L /\ ~((v:real^N) IN r)} | v | {v} IN L}`]
   LEBESGUE_COVERING_LEMMA) THEN
  REWRITE_TAC[MTOPOLOGY_EUCLIDEAN_METRIC; COMPACT_IN_EUCLIDEAN; OPEN_IN_EUCLIDEAN;
              MDIAMETER_EUCLIDEAN] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
      REWRITE_TAC[SET_RULE `{(f:real^N->real^N->bool) x | x | (P:real^N->bool) x} = {}
                            <=> !x. ~P x`] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      MESON_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC OPEN_DIFF THEN
      REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{x:real^N,y}`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    MATCH_MP_TAC DIAMETER_LE THEN REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    UNDISCH_TAC `dist(x:real^N,y) < d` THEN UNDISCH_TAC `&0 < d` THEN
    REWRITE_TAC[dist] THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_GSPEC; INSERT_SUBSET; EMPTY_SUBSET; IN_DIFF; IN_UNIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS L` THEN UNDISCH_TAC `(y:real^N) IN UNIONS L` THEN
  REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A8. The two-to-one bound survives perturbations that are uniformly small *)
(* and injective at a fixed scale rho: three points of a fibre would be     *)
(* rho apart, and g separates such triples by a positive amount (compactness *)
(* of the set of rho-separated triples).                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_NO_THREE = prove
 (`!s:A->bool.
     (!a b c. a IN s /\ b IN s /\ c IN s ==> a = b \/ a = c \/ b = c)
     ==> FINITE s /\ CARD s <= 2`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:A->bool = {}` THENL
   [ASM_REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_CASES_TAC `?b:A. b IN s /\ ~(b = a)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `s SUBSET {a:A,b}` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; FINITE_INSERT; FINITE_EMPTY];
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD{a:A,b}` THEN
      ASM_SIMP_TAC[CARD_SUBSET; FINITE_INSERT; FINITE_EMPTY; CARD_LE_2]];
    SUBGOAL_THEN `s = {a:A}` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SIMP_TAC[FINITE_SING; CARD_SING] THEN ARITH_TAC]);;

let MOI_LGB1_CLOSED_DIST_GE = prove
 (`!(p:real^P->real^M) q rho.
     linear p /\ linear q ==> closed {z | rho <= dist(p z,q z)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^P. lift(norm((p:real^P->real^M) z - q z))`;
                 `(:real^P)`; `{w:real^1 | w$1 >= rho}`]
    CONTINUOUS_CLOSED_PREIMAGE) THEN
  REWRITE_TAC[CLOSED_UNIV; CLOSED_HALFSPACE_COMPONENT_GE; IN_UNIV] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON];
    MATCH_MP_TAC(TAUT `p = q ==> p ==> q`) THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP; dist; real_ge]]);;

let MOI_LGB1_IN_PCROSS = prove
 (`!(z:real^(M,N)finite_sum) s t. z IN s PCROSS t <=> fstcart z IN s /\ sndcart z IN t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCROSS; IN_ELIM_THM] THEN
  MESON_TAC[PASTECART_FST_SND; FSTCART_PASTECART; SNDCART_PASTECART]);;

let MOI_LGB1_TWO_TO_ONE = prove
 (`!(g:real^M->real^N) k rho.
     compact k /\ g continuous_on k /\ &0 < rho /\
     (!y. FINITE {x | x IN k /\ g x = y} /\ CARD {x | x IN k /\ g x = y} <= 2)
     ==> ?mu. &0 < mu /\
              !g'. (!x. x IN k ==> dist(g' x,g x) < mu) /\
                   (!x y. x IN k /\ y IN k /\ dist(x,y) < rho /\ g' x = g' y
                          ==> x = y)
                   ==> !y. FINITE {x | x IN k /\ g' x = y} /\
                           CARD {x | x IN k /\ g' x = y} <= 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fib")))) THEN
  SUBGOAL_THEN
   `!x1 x2 x3. x1 IN k /\ x2 IN k /\ x3 IN k /\
               (g:real^M->real^N) x1 = g x2 /\ g x2 = g x3
               ==> x1 = x2 \/ x1 = x3 \/ x2 = x3`
  (LABEL_TAC "g2") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
    USE_THEN "fib" (MP_TAC o SPEC `(g:real^M->real^N) x1`) THEN
    ABBREV_TAC `F1 = {x | x IN k /\ (g:real^M->real^N) x = g x1}` THEN STRIP_TAC THEN
    SUBGOAL_THEN `{x1:real^M,x2,x3} SUBSET F1` ASSUME_TAC THENL
     [EXPAND_TAC "F1" THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `CARD {x1:real^M,x2,x3} = 3` ASSUME_TAC THENL
     [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`{x1:real^M,x2,x3}`; `F1:real^M->bool`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `T3 = {z:real^(M,(M,M)finite_sum)finite_sum | z IN k PCROSS (k PCROSS k) /\
              rho <= dist(fstcart z:real^M,fstcart(sndcart z)) /\
              rho <= dist(fstcart z:real^M,sndcart(sndcart z)) /\
              rho <= dist(fstcart(sndcart z):real^M,sndcart(sndcart z))}` THEN
  SUBGOAL_THEN
   `!x1 x2 x3:real^M.
      x1 IN k /\ x2 IN k /\ x3 IN k /\ rho <= dist(x1,x2) /\ rho <= dist(x1,x3) /\
      rho <= dist(x2,x3)
      ==> pastecart x1 (pastecart x2 x3) IN T3`
  (LABEL_TAC "inT3") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "T3" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                    SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g':real^M->real^N.
      (!x y. x IN k /\ y IN k /\ dist(x,y) < rho /\ g' x = g' y ==> x = y) /\
      (!z:real^(M,(M,M)finite_sum)finite_sum. z IN T3 ==> ~(g'(fstcart z) = g'(fstcart(sndcart z)) /\
                         g'(fstcart(sndcart z)) = g'(sndcart(sndcart z))))
      ==> !y. FINITE {x | x IN k /\ g' x = y} /\
              CARD {x | x IN k /\ g' x = y} <= 2`
  (LABEL_TAC "red") THENL
   [GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "loc") (LABEL_TAC "tri")) THEN
    X_GEN_TAC `y:real^N` THEN MATCH_MP_TAC MOI_LGB1_NO_THREE THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`x1:real^M`; `x2:real^M`; `x3:real^M`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
    USE_THEN "tri" (MP_TAC o SPEC `pastecart (x1:real^M) (pastecart (x2:real^M) (x3:real^M))`) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "inT3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~(x1:real^M = x2)`; UNDISCH_TAC `~(x1:real^M = x3)`;
      UNDISCH_TAC `~(x2:real^M = x3)`] THEN
    REWRITE_TAC[] THEN USE_THEN "loc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `T3:real^(M,(M,M)finite_sum)finite_sum->bool = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `g':real^M->real^N` THEN STRIP_TAC THEN
    USE_THEN "red" MATCH_MP_TAC THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(T3:real^(M,(M,M)finite_sum)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "T3" THEN
    REWRITE_TAC[SET_RULE `{z:real^(M,(M,M)finite_sum)finite_sum | z IN s /\ P z /\ Q z /\ R z} =
                          s INTER {z | P z} INTER {z | Q z} INTER {z | R z}`] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    ASM_SIMP_TAC[COMPACT_PCROSS] THEN
    REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
    MATCH_MP_TAC MOI_LGB1_CLOSED_DIST_GE THEN
    SIMP_TAC[LINEAR_FSTCART; LINEAR_SNDCART; GSYM o_DEF; LINEAR_COMPOSE] THEN
    REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL];
    ALL_TAC] THEN
  ABBREV_TAC
   `F3 = \z:real^(M,(M,M)finite_sum)finite_sum.
          dist((g:real^M->real^N)(fstcart z),g(fstcart(sndcart z))) +
          dist(g(fstcart(sndcart z)),g(sndcart(sndcart z)))` THEN
  MP_TAC(ISPECL [`F3:real^(M,(M,M)finite_sum)finite_sum->real`;
                 `T3:real^(M,(M,M)finite_sum)finite_sum->bool`]
    CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "F3" THEN
    REWRITE_TAC[o_DEF; LIFT_ADD; dist] THEN
    SUBGOAL_THEN
     `!h:real^(M,(M,M)finite_sum)finite_sum->real^M.
        linear h /\ (!z. z IN T3 ==> h z IN k)
        ==> (\z. (g:real^M->real^N)(h z)) continuous_on T3`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(\z. (g:real^M->real^N)((h:real^(M,(M,M)finite_sum)finite_sum->real^M) z)) = g o h` SUBST1_TAC THENL
       [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!z:real^(M,(M,M)finite_sum)finite_sum. z IN T3 ==> fstcart z IN k /\ fstcart(sndcart z) IN k /\
                                  sndcart(sndcart z) IN (k:real^M->bool)`
    ASSUME_TAC THENL
     [EXPAND_TAC "T3" THEN REWRITE_TAC[IN_ELIM_THM; MOI_LGB1_IN_PCROSS] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_SIMP_TAC[LINEAR_FSTCART; LINEAR_SNDCART] THEN
    REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^(M,(M,M)finite_sum)finite_sum`
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < (F3:real^(M,(M,M)finite_sum)finite_sum->real) z0` ASSUME_TAC THENL
   [UNDISCH_TAC `(z0:real^(M,(M,M)finite_sum)finite_sum) IN T3` THEN
    EXPAND_TAC "T3" THEN EXPAND_TAC "F3" THEN
    REWRITE_TAC[IN_ELIM_THM; MOI_LGB1_IN_PCROSS] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ ~(a = &0 /\ b = &0) ==> &0 < a + b`) THEN
    REWRITE_TAC[DIST_POS_LE; DIST_EQ_0] THEN DISCH_TAC THEN
    USE_THEN "g2" (MP_TAC o SPECL [`fstcart(z0:real^(M,(M,M)finite_sum)finite_sum)`;
      `fstcart(sndcart(z0:real^(M,(M,M)finite_sum)finite_sum))`;
      `sndcart(sndcart(z0:real^(M,(M,M)finite_sum)finite_sum))`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; DIST_REFL]))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(F3:real^(M,(M,M)finite_sum)finite_sum->real) z0 / &4` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &4`] THEN
  X_GEN_TAC `g':real^M->real^N` THEN STRIP_TAC THEN
  USE_THEN "red" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^(M,(M,M)finite_sum)finite_sum` THEN DISCH_TAC THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(M,(M,M)finite_sum)finite_sum` o
    check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "F3" THEN REWRITE_TAC[REAL_NOT_LE] THEN
  SUBGOAL_THEN `fstcart(z:real^(M,(M,M)finite_sum)finite_sum) IN k /\ fstcart(sndcart z) IN k /\
                sndcart(sndcart z) IN (k:real^M->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^(M,(M,M)finite_sum)finite_sum) IN T3` THEN
    EXPAND_TAC "T3" THEN REWRITE_TAC[IN_ELIM_THM; MOI_LGB1_IN_PCROSS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `dist((g:real^M->real^N)(fstcart(z:real^(M,(M,M)finite_sum)finite_sum)),g(fstcart(sndcart z))) <
      &2 * ((F3:real^(M,(M,M)finite_sum)finite_sum->real) z0 / &4) /\
    dist((g:real^M->real^N)(fstcart(sndcart(z:real^(M,(M,M)finite_sum)finite_sum))),g(sndcart(sndcart z))) <
      &2 * ((F3:real^(M,(M,M)finite_sum)finite_sum->real) z0 / &4)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(NORM_ARITH
     `!a b:real^N. dist(a,p) < e /\ dist(b,q) < e /\ a = b ==> dist(p,q) < &2 * e`) THENL
     [MAP_EVERY EXISTS_TAC [`(g':real^M->real^N)(fstcart(z:real^(M,(M,M)finite_sum)finite_sum))`;
                            `(g':real^M->real^N)(fstcart(sndcart(z:real^(M,(M,M)finite_sum)finite_sum)))`];
      MAP_EVERY EXISTS_TAC [`(g':real^M->real^N)(fstcart(sndcart(z:real^(M,(M,M)finite_sum)finite_sum)))`;
                            `(g':real^M->real^N)(sndcart(sndcart(z:real^(M,(M,M)finite_sum)finite_sum)))`]] THEN
    ASM_SIMP_TAC[];
    EXPAND_TAC "F3" THEN REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A9. Generic points: in any non-empty relatively open subset of an affine *)
(* set S there is a point outside every affine hull of a subset of a finite *)
(* set X that does not contain S.                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_GEN_EXISTS = prove
 (`!(S:real^N->bool) X U.
     affine S /\ FINITE X /\ open_in (subtopology euclidean S) U /\ ~(U = {})
     ==> ?p. p IN U /\
             !Y. Y SUBSET X /\ ~(S SUBSET affine hull Y) ==> ~(p IN affine hull Y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{affine hull Y | Y | Y SUBSET X /\ ~((S:real^N->bool) SUBSET affine hull Y)}`;
                 `S:real^N->bool`] MOI_FGP_AVOID_AFFINE) THEN
  ASM_SIMP_TAC[HULL_P] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\Y:real^N->bool. affine hull Y) {Y | Y SUBSET X}` THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_POWERSET] THEN
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `Y:real^N->bool` THEN STRIP_TAC THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `Y:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC; AFFINE_AFFINE_HULL] THEN SIMP_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `U:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN MESON_TAC[]]);;

(* Injectivity on the closed star of a vertex from injectivity near it, for  *)
(* maps affine on the simplices through the vertex (MOI_LGB1_CONE_INJ).      *)

let MOI_LGB1_STAR_INJ = prove
 (`!(L:(real^N->bool)->bool) (g:real^N->real^M) v.
     simplicial_complex L /\
     (!r. r IN L /\ v IN r ==> ?l y. linear l /\ !x. x IN r ==> g x = l x + y) /\
     (?n. open n /\ v IN n /\
          !x y. x IN n INTER UNIONS L /\ y IN n INTER UNIONS L /\ g x = g y
                ==> x = y)
     ==> !x y. x IN UNIONS {r | r IN L /\ v IN r} /\
               y IN UNIONS {r | r IN L /\ v IN r} /\ g x = g y ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "aff")
    (X_CHOOSE_THEN `n:real^N->bool` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `r1:real^N->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `r2:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`g:real^N->real^M`; `UNIONS L:real^N->bool`; `r1:real^N->bool`;
                 `r2:real^N->bool`; `v:real^N`; `n:real^N->bool`]
    MOI_LGB1_CONE_INJ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      ASM SET_TAC[];
      ASM SET_TAC[];
      USE_THEN "aff" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "aff" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

