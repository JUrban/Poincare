(* ========================================================================= *)
(* pc_moi_sch3_push: the push property of a 3-simplex (Moise Sec 17, Thms    *)
(* 4-6, pp.118-120): FACE_PUSH and SIMPLEX_PUSH.  The first section gives    *)
(* basic facts on the standard 3-simplex and a cone separation lemma.        *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_sch3_free.ml";;
needs "src/pc_moi_sch3_s2.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_SPU_K0 = prove
 (`convex hull {vec 0:real^3,basis 1,basis 2,basis 3} =
   {z:real^3 | &0 <= z$1 /\ &0 <= z$2 /\ &0 <= z$3 /\ z$1 + z$2 + z$3 <= &1}`,
  SUBGOAL_THEN `{vec 0:real^3,basis 1,basis 2,basis 3} =
                vec 0 INSERT {basis i | 1 <= i /\ i <= dimindex(:3)}`
  SUBST1_TAC THENL [REWRITE_TAC[MOI_SS2_STD_SB]; ALL_TAC] THEN
  REWRITE_TAC[STD_SIMPLEX; DIMINDEX_3; FORALL_3; SUM_3; EXTENSION;
              IN_ELIM_THM] THEN
  REWRITE_TAC[CONJ_ASSOC]);;

let MOI_SPU_INT_K0 = prove
 (`interior(convex hull {vec 0:real^3,basis 1,basis 2,basis 3}) =
   {z:real^3 | &0 < z$1 /\ &0 < z$2 /\ &0 < z$3 /\ z$1 + z$2 + z$3 < &1}`,
  SUBGOAL_THEN `{vec 0:real^3,basis 1,basis 2,basis 3} =
                vec 0 INSERT {basis i | 1 <= i /\ i <= dimindex(:3)}`
  SUBST1_TAC THENL [REWRITE_TAC[MOI_SS2_STD_SB]; ALL_TAC] THEN
  REWRITE_TAC[INTERIOR_STD_SIMPLEX; DIMINDEX_3; FORALL_3; SUM_3; EXTENSION;
              IN_ELIM_THM] THEN
  REWRITE_TAC[CONJ_ASSOC]);;

let MOI_SPU_STD_DISTINCT = prove
 (`~(basis 1:real^3 = basis 2) /\ ~(basis 1:real^3 = basis 3) /\
   ~(basis 2:real^3 = basis 3) /\ ~(vec 0:real^3 = basis 1) /\
   ~(vec 0:real^3 = basis 2) /\ ~(vec 0:real^3 = basis 3)`,
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  SIMP_TAC[BASIS_INJ_EQ; DIMINDEX_3; ARITH; BASIS_NONZERO]);;

let MOI_SPU_RELINT_F0 = prove
 (`relative_interior(convex hull {basis 1:real^3,basis 2,basis 3}) =
   {z:real^3 | &0 < z$1 /\ &0 < z$2 /\ &0 < z$3 /\ z$1 + z$2 + z$3 = &1}`,
  MP_TAC(ISPEC `{basis 1:real^3,basis 2,basis 3}`
    RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT) THEN
  ANTS_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP AFFINE_DEPENDENT_IMP_COLLINEAR_3) THEN
    REWRITE_TAC[MOI_SS2_STD_NONCOL3];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; MOI_SPU_STD_DISTINCT;
              REAL_ADD_RID; VECTOR_ADD_RID] THEN
  REWRITE_TAC[MESON[] `(!x:real^3. x = a \/ x = b \/ x = c ==> P x) <=>
                       P a /\ P b /\ P c`] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^3->real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `\x:real^3. x dot z` THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC]);;

let MOI_SPU_BDF0 = prove
 (`relative_frontier(convex hull {basis 1:real^3,basis 2,basis 3}) =
   {z:real^3 | &0 <= z$1 /\ &0 <= z$2 /\ &0 <= z$3 /\ z$1 + z$2 + z$3 = &1 /\
               (z$1 = &0 \/ z$2 = &0 \/ z$3 = &0)}`,
  REWRITE_TAC[relative_frontier; MOI_SPU_RELINT_F0] THEN
  SUBGOAL_THEN `closed(convex hull {basis 1:real^3,basis 2,basis 3})`
    (fun th -> REWRITE_TAC[MATCH_MP CLOSURE_CLOSED th]) THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
    MATCH_MP_TAC FINITE_IMP_COMPACT THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SS2_STD_F0; EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_SPU_CONE_SEP = prove
 (`!c d:real^N->bool.
     conic c /\ convex c /\ closed c /\ ~(c = {}) /\
     convex d /\ compact d /\ ~(d = {}) /\ DISJOINT c d
     ==> ?a. (!x. x IN c ==> a dot x <= &0) /\ (!x. x IN d ==> &0 < a dot x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^N->bool`; `d:real^N->bool`]
    SEPARATING_HYPERPLANE_CLOSED_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real`
    (CONJUNCTS_THEN2 (LABEL_TAC "c") (LABEL_TAC "d")))) THEN
  EXISTS_TAC `a:real^N` THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [USE_THEN "c" (MP_TAC o SPEC `vec 0:real^N`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONIC_CONTAINS_0]; REWRITE_TAC[DOT_RZERO]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "c" (MP_TAC o SPEC `(b / ((a:real^N) dot x)) % x:real^N`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `conic(c:real^N->bool)` THEN REWRITE_TAC[conic] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[DOT_RMUL] THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
      REAL_ARITH_TAC];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REMOVE_THEN "d" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Separation lemmas for the positive-angle fact on the standard simplex     *)
(* k0 = hull {0,e1,e2,e3} with face f0 = hull{e1,e2,e3} and barycentre       *)
(* b0 of f0.                                                                 *)
(* ========================================================================= *)

let MOI_SPU_SMALL = prove
 (`!t rho m. &0 <= t /\ &0 < m
             ==> ?s. &0 < s /\ s <= &1 / &2 /\ s * t <= &1 /\
                     s * abs rho <= m`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `min (&1 / &2) (min (inv(t + &1)) (m / (abs rho + &1)))` THEN
  SUBGOAL_THEN `&0 < inv(t + &1) /\ &0 < m / (abs rho + &1)` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(t + &1) * t` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      SUBGOAL_THEN `&0 < t + &1` (fun th -> SIMP_TAC[REAL_LE_LDIV_EQ; th]) THENL
       [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `m / (abs rho + &1) * abs rho` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      SUBGOAL_THEN `&0 < abs rho + &1`
        (fun th -> SIMP_TAC[REAL_LE_LDIV_EQ; th]) THENL
       [REAL_ARITH_TAC; REAL_ARITH_TAC]]]);;


let moi_spu_cyc = new_definition
 `moi_spu_cyc (x:real^3) = vector[x$2; x$3; x$1]:real^3`;;

let MOI_SPU_CYC_COMPONENTS = prove
 (`!x:real^3. (moi_spu_cyc x)$1 = x$2 /\ (moi_spu_cyc x)$2 = x$3 /\
              (moi_spu_cyc x)$3 = x$1`,
  REWRITE_TAC[moi_spu_cyc; VECTOR_3]);;

let MOI_SPU_CYC_LINEAR = prove
 (`linear moi_spu_cyc`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; MOI_SPU_CYC_COMPONENTS;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT]);;

let MOI_SPU_CYC_K0 = prove
 (`!x:real^3. moi_spu_cyc x IN convex hull {vec 0,basis 1,basis 2,basis 3} <=>
              x IN convex hull {vec 0,basis 1,basis 2,basis 3}`,
  REWRITE_TAC[MOI_SPU_K0; IN_ELIM_THM; MOI_SPU_CYC_COMPONENTS] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_SPU_CYC_BDF0 = prove
 (`!x:real^3.
     moi_spu_cyc x IN relative_frontier(convex hull {basis 1,basis 2,basis 3}) <=>
     x IN relative_frontier(convex hull {basis 1,basis 2,basis 3})`,
  REWRITE_TAC[MOI_SPU_BDF0; IN_ELIM_THM; MOI_SPU_CYC_COMPONENTS] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_SPU_CYC_DOT = prove
 (`!a x:real^3. a dot moi_spu_cyc x = (vector[a$3; a$1; a$2]:real^3) dot x`,
  REWRITE_TAC[DOT_3; MOI_SPU_CYC_COMPONENTS; VECTOR_3] THEN REAL_ARITH_TAC);;

let MOI_SPU_CYC_POINTS = prove
 (`moi_spu_cyc (vector[&1 / &3; &1 / &3; &1 / &3]) =
   vector[&1 / &3; &1 / &3; &1 / &3] /\
   moi_spu_cyc (basis 2) = basis 1 /\ moi_spu_cyc (basis 3) = basis 2`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MOI_SPU_CYC_COMPONENTS;
              VECTOR_3] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH]);;

let MOI_SPU_K0_FACTS = prove
 (`convex (convex hull {vec 0:real^3,basis 1,basis 2,basis 3}) /\
   compact (convex hull {vec 0:real^3,basis 1,basis 2,basis 3}) /\
   polytope (convex hull {vec 0:real^3,basis 1,basis 2,basis 3}) /\
   vec 0 IN convex hull {vec 0:real^3,basis 1,basis 2,basis 3} /\
   basis 1 IN convex hull {vec 0:real^3,basis 1,basis 2,basis 3} /\
   basis 2 IN convex hull {vec 0:real^3,basis 1,basis 2,basis 3} /\
   basis 3 IN convex hull {vec 0:real^3,basis 1,basis 2,basis 3} /\
   vector[&1 / &3; &1 / &3; &1 / &3] IN
     convex hull {vec 0:real^3,basis 1,basis 2,basis 3}`,
  SIMP_TAC[CONVEX_CONVEX_HULL; COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT;
           POLYTOPE_CONVEX_HULL; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[MOI_SPU_K0; IN_ELIM_THM; VECTOR_3; VEC_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

let MOI_SPU_K0_HALFSPACE = prove
 (`!(a:real^3) r.
     r <= a dot vec 0 /\ r <= a dot basis 1 /\ r <= a dot basis 2 /\
     r <= a dot basis 3
     ==> !x. x IN convex hull {vec 0,basis 1,basis 2,basis 3} ==> r <= a dot x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull {vec 0:real^3,basis 1,basis 2,basis 3} SUBSET
                {x | a dot x >= r}`
    (fun th -> MP_TAC th THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; real_ge]) THEN
  MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GE] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM; real_ge]);;

let MOI_SPU_SEP_DISJ = prove
 (`!p:real^3->bool.
     polytope p /\ p INTER convex hull {vec 0,basis 1,basis 2,basis 3} = {}
     ==> ?a r. (!x. x IN p ==> a dot x <= r) /\
               (!x. x IN convex hull {vec 0,basis 1,basis 2,basis 3}
                    ==> r <= a dot x) /\
               r < a dot vector[&1 / &3; &1 / &3; &1 / &3] /\ r < &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^3->bool`;
                 `convex hull {vec 0:real^3,basis 1,basis 2,basis 3}`]
    SEPARATING_HYPERPLANE_COMPACT_COMPACT) THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT; MOI_SPU_K0_FACTS;
               DISJOINT] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "p")
      (LABEL_TAC "k"))))) THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real`] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    REMOVE_THEN "p" (MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "k" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    USE_THEN "k" (MP_TAC o SPEC `vector[&1 / &3; &1 / &3; &1 / &3]:real^3`) THEN
    REWRITE_TAC[MOI_SPU_K0_FACTS] THEN REAL_ARITH_TAC;
    USE_THEN "k" (MP_TAC o SPEC `vec 0:real^3`) THEN
    REWRITE_TAC[MOI_SPU_K0_FACTS; DOT_RZERO] THEN REAL_ARITH_TAC]);;

let MOI_SPU_POLYTOPE_HULL_INSERT2 = prove
 (`!a b s:real^N->bool.
     polytope s ==> polytope(convex hull (a INSERT b INSERT s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polytope] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(a:real^N) INSERT b INSERT v` THEN
  ASM_REWRITE_TAC[FINITE_INSERT] THEN
  ONCE_REWRITE_TAC[HULL_INSERT] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[HULL_INSERT] THEN REWRITE_TAC[HULL_HULL]);;

let MOI_SPU_EDGE_DISJ = prove
 (`!p (y0:real^3) t rho mu (x:real^3).
     polytope p /\ y0 IN p /\ &0 < y0$1 /\ &0 < y0$2 /\ y0$3 = &0 /\
     y0$1 + y0$2 = &1 /\
     (!z. z IN p /\ z IN convex hull {vec 0,basis 1,basis 2,basis 3}
          ==> z IN relative_frontier(convex hull {basis 1,basis 2,basis 3})) /\
     &0 <= t /\ x IN p /\ &0 <= mu /\ mu <= &1 /\
     t % (x - y0) = mu % basis 3 - y0 - rho % (basis 1 - basis 2)
     ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real`; `rho:real`; `min ((y0:real^3)$1) (y0$2) / &4`]
    MOI_SPU_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `z:real^3 = y0 + s % (mu % basis 3 - y0 - rho % (basis 1 - basis 2))` THEN
  SUBGOAL_THEN `(z:real^3) IN p` ASSUME_TAC THENL
   [SUBGOAL_THEN `z = (&1 - s * t) % y0 + (s * t) % (x:real^3)` SUBST1_TAC
    THENL
     [EXPAND_TAC "z" THEN
      UNDISCH_TAC `t % (x - y0) = mu % basis 3 - y0 -
                                  rho % (basis 1 - basis 2:real^3)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC IN_CONVEX_SET THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; REAL_LE_MUL; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3)$1 = (y0:real^3)$1 - s * y0$1 - s * rho /\
                z$2 = y0$2 - s * y0$2 + s * rho /\ z$3 = s * mu`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s * (y0:real^3)$1 <= y0$1 / &2 /\ s * y0$2 <= y0$2 / &2 /\
                abs(s * rho) <= min (y0$1) (y0$2) / &4 /\
                s * mu <= s /\ &0 <= s * mu /\ s * y0$1 + s * y0$2 = s`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &2 * (y0:real^3)$1` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &2 * (y0:real^3)$2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_REWRITE_TAC[REAL_MUL_RID]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN
  ASM_REWRITE_TAC[MOI_SPU_K0; MOI_SPU_BDF0; IN_ELIM_THM] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_SPU_SEP_EDGE = prove
 (`!p (y0:real^3).
     polytope p /\ y0 IN p /\ &0 < y0$1 /\ &0 < y0$2 /\ y0$3 = &0 /\
     y0$1 + y0$2 = &1 /\
     (!z. z IN p /\ z IN convex hull {vec 0,basis 1,basis 2,basis 3}
          ==> z IN relative_frontier(convex hull {basis 1,basis 2,basis 3}))
     ==> ?a r. (!x. x IN p ==> a dot x <= r) /\
               (!x. x IN convex hull {vec 0,basis 1,basis 2,basis 3}
                    ==> r <= a dot x) /\
               r < a dot vector[&1 / &3; &1 / &3; &1 / &3] /\ r < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `polytope (IMAGE (\x:real^3. --y0 + x) p) /\
    convex (IMAGE (\x:real^3. --y0 + x) p) /\
    vec 0 IN IMAGE (\x:real^3. --y0 + x) p /\
    ~(IMAGE (\x:real^3. --y0 + x) p = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_TRANSLATION_EQ; CONVEX_TRANSLATION_EQ;
                 POLYTOPE_IMP_CONVEX; IMAGE_EQ_EMPTY] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y0:real^3` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = IMAGE (\x:real^3. --y0 + x) p` THEN
  ABBREV_TAC `cc = conic hull (convex hull
     ((basis 1 - basis 2) INSERT --(basis 1 - basis 2) INSERT q)):real^3->bool` THEN
  MP_TAC(ISPECL [`cc:real^3->bool`; `segment[--y0,basis 3 - y0:real^3]`]
    MOI_SPU_CONE_SEP) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "cc" THEN
    REWRITE_TAC[CONIC_CONIC_HULL; CONVEX_SEGMENT; COMPACT_SEGMENT;
                SEGMENT_EQ_EMPTY] THEN
    SIMP_TAC[CONVEX_CONIC_HULL; CONVEX_CONVEX_HULL] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_CONIC_HULL_STRONG THEN DISJ2_TAC THEN DISJ1_TAC THEN
      MATCH_MP_TAC MOI_SPU_POLYTOPE_HULL_INSERT2 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[CONIC_HULL_EQ_EMPTY; CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
      ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `d:real^3` THEN
    REWRITE_TAC[CONIC_HULL_EXPLICIT; IN_ELIM_THM; IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `(w:real^3) IN convex hull
       ((basis 1 - basis 2) INSERT --(basis 1 - basis 2) INSERT q)` THEN
    SIMP_TAC[CONVEX_HULL_INSERT; NOT_INSERT_EMPTY;
             ASSUME `~(q:real^3->bool = {})`] THEN
    SIMP_TAC[HULL_P; ASSUME `convex(q:real^3->bool)`; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real`; `v:real`; `b1:real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `u':real` (X_CHOOSE_THEN `v':real`
          (X_CHOOSE_THEN `b2:real^3` STRIP_ASSUME_TAC))) ASSUME_TAC)))) THEN
    UNDISCH_TAC `(b2:real^3) IN q` THEN EXPAND_TAC "q" THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`p:real^3->bool`; `y0:real^3`; `c * v * v'`;
                   `c * u - c * v * u'`; `m:real`; `x:real^3`]
      MOI_SPU_EDGE_DISJ) THEN
    ASM_SIMP_TAC[REAL_LE_MUL] THEN
    UNDISCH_TAC `d = (&1 - m) % --y0 + m % (basis 3 - y0:real^3)` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (CONJUNCTS_THEN2 (LABEL_TAC "c")
    (LABEL_TAC "d"))) THEN
  SUBGOAL_THEN
   `((basis 1 - basis 2) INSERT --(basis 1 - basis 2) INSERT q) SUBSET
    (cc:real^3->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull ((basis 1 - basis 2) INSERT
                  --(basis 1 - basis 2) INSERT q):real^3->bool` THEN
    REWRITE_TAC[HULL_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN p ==> (a:real^3) dot (--y0 + x) <= &0) /\
    a dot (basis 1 - basis 2) <= &0 /\ a dot --(basis 1 - basis 2) <= &0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(X_GEN_TAC `x:real^3` THEN DISCH_TAC) THEN
    USE_THEN "c" MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_INSERT] THEN
    EXPAND_TAC "q" THEN REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (a:real^3) dot --y0 /\ &0 < a dot (basis 3 - y0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "d" MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DOT_RADD; DOT_RNEG; DOT_RSUB]) THEN
  RULE_ASSUM_TAC(SIMP_RULE[DOT_BASIS; DIMINDEX_3; ARITH]) THEN
  SUBGOAL_THEN `(a:real^3)$2 = a$1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3) dot y0 = a$1` ASSUME_TAC THENL
   [REWRITE_TAC[DOT_3] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y0:real^3)$1 + y0$2 = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `(a:real^3)$1`] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC MOI_SPU_K0_HALFSPACE THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; DOT_RZERO] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[DOT_3; VECTOR_3] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let MOI_SPU_SEP_VERTEX = prove
 (`!p:real^3->bool.
     polytope p /\ basis 1 IN p /\
     (!z. z IN p /\ z IN convex hull {vec 0,basis 1,basis 2,basis 3}
          ==> z = basis 1)
     ==> ?a r. (!x. x IN p ==> a dot x <= r) /\
               (!x. x IN convex hull {vec 0,basis 1,basis 2,basis 3}
                    ==> r <= a dot x) /\
               r < a dot vector[&1 / &3; &1 / &3; &1 / &3] /\ r < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `polytope (IMAGE (\x:real^3. --basis 1 + x) p) /\
    vec 0 IN IMAGE (\x:real^3. --basis 1 + x) p /\
    ~(IMAGE (\x:real^3. --basis 1 + x) p = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_TRANSLATION_EQ; IMAGE_EQ_EMPTY] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `basis 1:real^3` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = IMAGE (\x:real^3. --basis 1 + x) p` THEN
  MP_TAC(ISPECL [`conic hull q:real^3->bool`;
                 `convex hull {--basis 1,basis 2 - basis 1,
                               basis 3 - basis 1:real^3}`]
    MOI_SPU_CONE_SEP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONIC_CONIC_HULL; CONVEX_CONVEX_HULL] THEN
    ASM_SIMP_TAC[CONVEX_CONIC_HULL; POLYTOPE_IMP_CONVEX;
                 CLOSED_CONIC_HULL_STRONG; COMPACT_CONVEX_HULL;
                 FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY;
                 CONIC_HULL_EQ_EMPTY; CONVEX_HULL_EQ_EMPTY;
                 NOT_INSERT_EMPTY] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `d:real^3` THEN
    REWRITE_TAC[CONIC_HULL_EXPLICIT; CONVEX_HULL_3; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real`
       (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)))) THEN
    UNDISCH_TAC `(w:real^3) IN q` THEN EXPAND_TAC "q" THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(d:real^3)$1 = -- &1 /\ d$2 = v /\ d$3 = t`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `d = u % --basis 1 + v % (basis 2 - basis 1) +
                       t % (basis 3 - basis 1:real^3)` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
                  VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `s = inv(c + &1)` THEN
    SUBGOAL_THEN `&0 < s /\ s <= &1 /\ s * c <= &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC;
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
        SUBGOAL_THEN `&0 < c + &1` (fun th -> SIMP_TAC[REAL_LE_LDIV_EQ; th])
        THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `basis 1 + s % d:real^3 IN p` ASSUME_TAC THENL
     [SUBGOAL_THEN `basis 1 + s % d:real^3 =
                    (&1 - s * c) % basis 1 + (s * c) % x`
      SUBST1_TAC THENL
       [UNDISCH_TAC `(d:real^3) = c % w` THEN DISCH_THEN SUBST1_TAC THEN
        ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
        MATCH_MP_TAC IN_CONVEX_SET THEN
        ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; REAL_LE_MUL; REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= s * u /\ &0 <= s * v /\ &0 <= s * t /\
                  s * u + s * v + s * t = s`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_REWRITE_TAC[REAL_MUL_RID];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `basis 1 + s % d:real^3`) THEN
    REWRITE_TAC[MOI_SPU_K0; IN_ELIM_THM; MOI_SS2_STD_POINTS;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (CONJUNCTS_THEN2 (LABEL_TAC "c")
    (LABEL_TAC "d"))) THEN
  SUBGOAL_THEN `!x. x IN p ==> (a:real^3) dot (--basis 1 + x) <= &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "c" MATCH_MP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
    EXPAND_TAC "q" THEN REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (a:real^3) dot --basis 1 /\
                &0 < a dot (basis 2 - basis 1) /\
                &0 < a dot (basis 3 - basis 1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "d" MATCH_MP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
    REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DOT_RADD; DOT_RNEG; DOT_RSUB]) THEN
  RULE_ASSUM_TAC(SIMP_RULE[DOT_BASIS; DIMINDEX_3; ARITH]) THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `(a:real^3)$1`] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC MOI_SPU_K0_HALFSPACE THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; DOT_RZERO] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[DOT_3; VECTOR_3] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let MOI_SPU_SEP_CYC = prove
 (`!p:real^3->bool.
     (?a r. (!x. x IN IMAGE moi_spu_cyc p ==> a dot x <= r) /\
            (!x. x IN convex hull {vec 0,basis 1,basis 2,basis 3}
                 ==> r <= a dot x) /\
            r < a dot vector[&1 / &3; &1 / &3; &1 / &3] /\ r < &0)
     ==> (?a r. (!x. x IN p ==> a dot x <= r) /\
                (!x. x IN convex hull {vec 0,basis 1,basis 2,basis 3}
                     ==> r <= a dot x) /\
                r < a dot vector[&1 / &3; &1 / &3; &1 / &3] /\ r < &0)`,
  GEN_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^3`; `r:real`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`vector[(a:real^3)$3; a$1; a$2]:real^3`; `r:real`] THEN
  REWRITE_TAC[GSYM MOI_SPU_CYC_DOT; MOI_SPU_CYC_POINTS] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN
  DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; MOI_SPU_CYC_K0]);;

let MOI_SPU_CYC_HYP = prove
 (`!p:real^3->bool.
     polytope p /\
     (!z. z IN p /\ z IN convex hull {vec 0,basis 1,basis 2,basis 3}
          ==> z IN relative_frontier(convex hull {basis 1,basis 2,basis 3}))
     ==> polytope (IMAGE moi_spu_cyc p) /\
         (!z. z IN IMAGE moi_spu_cyc p /\
              z IN convex hull {vec 0,basis 1,basis 2,basis 3}
              ==> z IN relative_frontier(convex hull {basis 1,basis 2,basis 3}))`,
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC POLYTOPE_LINEAR_IMAGE THEN
    ASM_REWRITE_TAC[MOI_SPU_CYC_LINEAR];
    REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[MOI_SPU_CYC_K0; MOI_SPU_CYC_BDF0] THEN ASM_MESON_TAC[]]);;

let MOI_SPU_SEP_EDGE_ANY = prove
 (`!p (y:real^3).
     polytope p /\ y IN p /\ y IN convex hull {vec 0,basis 1,basis 2,basis 3} /\
     (!z. z IN p /\ z IN convex hull {vec 0,basis 1,basis 2,basis 3}
          ==> z IN relative_frontier(convex hull {basis 1,basis 2,basis 3})) /\
     ((&0 < y$1 /\ &0 < y$2) \/ (&0 < y$2 /\ &0 < y$3) \/
      (&0 < y$3 /\ &0 < y$1))
     ==> ?a r. (!x. x IN p ==> a dot x <= r) /\
               (!x. x IN convex hull {vec 0,basis 1,basis 2,basis 3}
                    ==> r <= a dot x) /\
               r < a dot vector[&1 / &3; &1 / &3; &1 / &3] /\ r < &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  SUBGOAL_THEN
   `(y:real^3) IN relative_frontier(convex hull {basis 1,basis 2,basis 3})`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOI_SPU_BDF0; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "zero"))))) THEN
  MP_TAC(SPEC `p:real^3->bool` MOI_SPU_CYC_HYP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPEC `IMAGE moi_spu_cyc p` MOI_SPU_CYC_HYP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC MOI_SPU_SEP_EDGE THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MOI_SPU_SEP_CYC THEN
    MATCH_MP_TAC MOI_SPU_SEP_EDGE THEN EXISTS_TAC `moi_spu_cyc y` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; MOI_SPU_CYC_COMPONENTS] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MOI_SPU_SEP_CYC THEN MATCH_MP_TAC MOI_SPU_SEP_CYC THEN
    MATCH_MP_TAC MOI_SPU_SEP_EDGE THEN
    EXISTS_TAC `moi_spu_cyc (moi_spu_cyc y)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; MOI_SPU_CYC_COMPONENTS] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_SPU_SEP_VERTEX_ANY = prove
 (`!p (y:real^3).
     polytope p /\ y IN p /\ (y = basis 1 \/ y = basis 2 \/ y = basis 3) /\
     (!z. z IN p /\ z IN convex hull {vec 0,basis 1,basis 2,basis 3}
          ==> z = y)
     ==> ?a r. (!x. x IN p ==> a dot x <= r) /\
               (!x. x IN convex hull {vec 0,basis 1,basis 2,basis 3}
                    ==> r <= a dot x) /\
               r < a dot vector[&1 / &3; &1 / &3; &1 / &3] /\ r < &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "u")))) THEN
  SUBGOAL_THEN `polytope (IMAGE moi_spu_cyc p) /\
                polytope (IMAGE moi_spu_cyc (IMAGE moi_spu_cyc p))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC POLYTOPE_LINEAR_IMAGE THEN
      ASM_REWRITE_TAC[MOI_SPU_CYC_LINEAR]);
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOI_SPU_SEP_VERTEX THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SPU_SEP_CYC THEN MATCH_MP_TAC MOI_SPU_SEP_VERTEX THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `basis 1:real^3 = moi_spu_cyc (basis 2)` SUBST1_TAC THENL
       [REWRITE_TAC[MOI_SPU_CYC_POINTS]; ASM_SIMP_TAC[FUN_IN_IMAGE]];
      REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; MOI_SPU_CYC_K0] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^3) = basis 2` SUBST1_TAC THENL
       [USE_THEN "u" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[MOI_SPU_CYC_POINTS]]];
    MATCH_MP_TAC MOI_SPU_SEP_CYC THEN MATCH_MP_TAC MOI_SPU_SEP_CYC THEN
    MATCH_MP_TAC MOI_SPU_SEP_VERTEX THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `basis 1:real^3 = moi_spu_cyc (moi_spu_cyc (basis 3))`
      SUBST1_TAC THENL
       [REWRITE_TAC[MOI_SPU_CYC_POINTS]; ASM_SIMP_TAC[FUN_IN_IMAGE]];
      REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; MOI_SPU_CYC_K0] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^3) = basis 3` SUBST1_TAC THENL
       [USE_THEN "u" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[MOI_SPU_CYC_POINTS]]]]);;

let MOI_SPU_BDF0_VERTEX = prove
 (`!y:real^3.
     y IN relative_frontier(convex hull {basis 1,basis 2,basis 3}) /\
     ~((&0 < y$1 /\ &0 < y$2) \/ (&0 < y$2 /\ &0 < y$3) \/
       (&0 < y$3 /\ &0 < y$1))
     ==> y = basis 1 \/ y = basis 2 \/ y = basis 3`,
  REWRITE_TAC[MOI_SPU_BDF0; IN_ELIM_THM; MOI_SS2_STD_POINTS] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_SPU_MID_VERTEX = prove
 (`!y z:real^3.
     (y = basis 1 \/ y = basis 2 \/ y = basis 3) /\
     (z = basis 1 \/ z = basis 2 \/ z = basis 3) /\ ~(y = z)
     ==> (&0 < ((&1 / &2) % (y + z))$1 /\ &0 < ((&1 / &2) % (y + z))$2) \/
         (&0 < ((&1 / &2) % (y + z))$2 /\ &0 < ((&1 / &2) % (y + z))$3) \/
         (&0 < ((&1 / &2) % (y + z))$3 /\ &0 < ((&1 / &2) % (y + z))$1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[MOI_SPU_STD_DISTINCT] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let MOI_SPU_SEP = prove
 (`!p:real^3->bool.
     polytope p /\
     (!z. z IN p /\ z IN convex hull {vec 0,basis 1,basis 2,basis 3}
          ==> z IN relative_frontier(convex hull {basis 1,basis 2,basis 3}))
     ==> ?a r. (!x. x IN p ==> a dot x <= r) /\
               (!x. x IN convex hull {vec 0,basis 1,basis 2,basis 3}
                    ==> r <= a dot x) /\
               r < a dot vector[&1 / &3; &1 / &3; &1 / &3] /\ r < &0`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC
   `p INTER convex hull {vec 0:real^3,basis 1,basis 2,basis 3} = {}` THENL
   [MATCH_MP_TAC MOI_SPU_SEP_DISJ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC
   `?y:real^3. y IN p /\ y IN convex hull {vec 0,basis 1,basis 2,basis 3} /\
               ((&0 < y$1 /\ &0 < y$2) \/ (&0 < y$2 /\ &0 < y$3) \/
                (&0 < y$3 /\ &0 < y$1))` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    MATCH_MP_TAC MOI_SPU_SEP_EDGE_ANY THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN p /\ z IN convex hull {vec 0,basis 1,basis 2,basis 3}
               ==> z = basis 1 \/ z = basis 2 \/ z = basis 3`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SPU_BDF0_VERTEX THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (is_neg o concl)) THEN
  REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_SPU_SEP_VERTEX_ANY THEN EXISTS_TAC `y:real^3` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  ASM_CASES_TAC `z:real^3 = y` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`z:real^3`; `y:real^3`] MOI_SPU_MID_VERTEX) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC
   `~(?y:real^3. y IN p /\ y IN convex hull {vec 0,basis 1,basis 2,basis 3} /\
                 ((&0 < y$1 /\ &0 < y$2) \/ (&0 < y$2 /\ &0 < y$3) \/
                  (&0 < y$3 /\ &0 < y$1)))` THEN
  REWRITE_TAC[] THEN EXISTS_TAC `(&1 / &2) % (z + y):real^3` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&1 / &2) % (z + y):real^3 = (&1 - &1 / &2) % z + (&1 / &2) % y`
  SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC IN_CONVEX_SET THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; MOI_SPU_K0_FACTS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ========================================================================= *)
(* Moise Thm 4 (p.118) on the standard simplex: the cut-down bipyramid bb,   *)
(* the cone map from b0 to 0 (MOI_SA2_CONE_PLH) and its extension by the     *)
(* identity (MOI_SA2_PLH_EXTEND_ID).                                         *)
(* ========================================================================= *)

let MOI_SPU_NBHD = prove
 (`!k u:real^3->bool.
     polytope k /\ open u /\ k SUBSET u
     ==> ?n. polytope n /\ k SUBSET interior n /\ n SUBSET u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `(:real^3) DIFF u`]
    SEPARATE_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT; GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{x + y:real^3 | x IN k /\
                 y IN interval[--((d / &6) % vec 1),(d / &6) % vec 1]}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC POLYTOPE_SUMS THEN ASM_REWRITE_TAC[POLYTOPE_INTERVAL];
    REWRITE_TAC[SUBSET; IN_INTERIOR] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN EXISTS_TAC `d / &6` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^3`; `z - x:real^3`] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `x + (z - x):real^3 = z`] THEN
    REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VECTOR_MUL_COMPONENT;
                VEC_COMPONENT] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`z - x:real^3`; `i:num`] COMPONENT_LE_NORM) THEN
    UNDISCH_TAC `dist(x:real^3,z) < d / &6` THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `x + y:real^3`]) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    MATCH_MP_TAC(TAUT `~b ==> (~a ==> b) ==> a`) THEN
    REWRITE_TAC[REAL_NOT_LE; dist; VECTOR_ARITH `x - (x + y):real^3 = --y`;
                NORM_NEG] THEN
    MP_TAC(ISPEC `y:real^3` NORM_LE_L1) THEN
    REWRITE_TAC[DIMINDEX_3; SUM_3] THEN
    UNDISCH_TAC
     `y IN interval[--((d / &6) % vec 1),(d / &6) % vec 1:real^3]` THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT;
                VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_SPU_STD_SIMPLEX = prove
 (`&3 simplex (convex hull {vec 0:real^3,basis 1,basis 2,basis 3})`,
  REWRITE_TAC[simplex] THEN
  EXISTS_TAC `{vec 0:real^3,basis 1,basis 2,basis 3}` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(INST_TYPE [`:3`,`:N`] AFFINE_INDEPENDENT_STDBASIS) THEN
    REWRITE_TAC[MOI_SS2_STD_SB];
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; MOI_SPU_STD_DISTINCT] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV)]);;

let MOI_SPU_FRONTIER_K0 = prove
 (`frontier(convex hull {vec 0:real^3,basis 1,basis 2,basis 3}) =
   {z:real^3 | &0 <= z$1 /\ &0 <= z$2 /\ &0 <= z$3 /\
               z$1 + z$2 + z$3 <= &1 /\
               (z$1 = &0 \/ z$2 = &0 \/ z$3 = &0 \/ z$1 + z$2 + z$3 = &1)}`,
  REWRITE_TAC[GSYM MOI_SS2_STD_S0] THEN
  MP_TAC(MATCH_MP MOI_SCD_SIMPLEX_FILL MOI_SPU_STD_SIMPLEX) THEN
  SIMP_TAC[]);;

let MOI_SPU_CONE_IMAGE_STD = prove
 (`{r % x | x IN relative_frontier(convex hull {basis 1,basis 2,basis 3}) /\
            &0 <= r /\ r <= &1} =
   (frontier(convex hull {vec 0:real^3,basis 1,basis 2,basis 3}) DIFF
    convex hull {basis 1,basis 2,basis 3}) UNION
   relative_frontier(convex hull {basis 1,basis 2,basis 3})`,
  REWRITE_TAC[MOI_SPU_FRONTIER_K0; MOI_SS2_STD_F0; MOI_SPU_BDF0] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; IN_DIFF] THEN
  X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `x:real^3` MP_TAC)) THEN
    REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    SUBGOAL_THEN `&0 <= r * (x:real^3)$1 /\ &0 <= r * x$2 /\ &0 <= r * x$3 /\
                  r * x$1 + r * x$2 + r * x$3 = r`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL] THEN REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
      ASM_REWRITE_TAC[REAL_MUL_RID];
      ALL_TAC] THEN
    ASM_CASES_TAC `r = &1` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISJ1_TAC THEN
    UNDISCH_TAC `(x:real^3)$1 = &0 \/ x$2 = &0 \/ x$3 = &0` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (z:real^3)$1 /\ &0 <= z$2 /\ &0 <= z$3 /\
                z$1 + z$2 + z$3 <= &1 /\
                (z$1 = &0 \/ z$2 = &0 \/ z$3 = &0)`
  MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `(z:real^3)$1 + z$2 + z$3 = &0` THENL
   [MAP_EVERY EXISTS_TAC [`&0`; `basis 1:real^3`] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; REAL_POS] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (z:real^3)$1 + z$2 + z$3` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(z:real^3)$1 + z$2 + z$3`; `inv((z:real^3)$1 + z$2 + z$3) % z`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
               VECTOR_MUL_LID; VECTOR_MUL_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_ENTIRE; REAL_INV_EQ_0] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_SPU_HALFSPACE_INT = prove
 (`!(a:real^N) r x.
     x IN interior {y | a dot y >= r} /\ a dot x <= r ==> a = vec 0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
  ASM_SIMP_TAC[INTERIOR_HALFSPACE_GE; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let MOI_SPU_B0_INTERIOR = prove
 (`!s:real^3->bool.
     s SUBSET {x | (basis 2 + basis 3) dot x <= &1} INTER
              {x | (basis 1 + basis 3) dot x <= &1} INTER
              {x | (basis 1 + basis 2) dot x <= &1}
     ==> !x. x IN interior s ==> x$2 + x$3 < &1 /\ x$1 + x$3 < &1 /\
                                  x$1 + x$2 < &1`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SUBSET_INTERIOR) THEN
  REWRITE_TAC[INTERIOR_INTER] THEN
  SUBGOAL_THEN `~(basis 2 + basis 3:real^3 = vec 0) /\
                ~(basis 1 + basis 3:real^3 = vec 0) /\
                ~(basis 1 + basis 2:real^3 = vec 0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
                VEC_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTERIOR_HALFSPACE_LE] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; DOT_LADD] THEN
  SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN MESON_TAC[]);;

let MOI_SPU_IMAGE_CONE = prove
 (`!(h:real^N->real^N) t b m.
     convex t /\ compact t /\ b IN relative_interior t /\
     ~(relative_frontier t = {}) /\
     (!x r. x IN relative_frontier t /\ &0 <= r /\ r <= &1
            ==> h (b + r % (x - b)) = m + r % (x - m))
     ==> IMAGE h t =
         {m + r % (x - m) | x IN relative_frontier t /\ &0 <= r /\ r <= &1}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `b:real^N`] MOI_CON_CONE_RF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; MOI_CON_IN_CONE; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^N` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `r:real`
        STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `x:real^N`] THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `x:real^N`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `b + r % (x - b):real^N` THEN
    ASM_SIMP_TAC[] THEN MAP_EVERY EXISTS_TAC [`x:real^N`; `r:real`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SPU_FACE_PUSH_STD = prove
 (`moi_sch3_push (convex hull {vec 0:real^3,basis 1,basis 2,basis 3})
                 (convex hull {basis 1,basis 2,basis 3})
                 (relative_frontier(convex hull {basis 1,basis 2,basis 3}))`,
  REWRITE_TAC[moi_sch3_push] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3->bool`; `v:real^3->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`convex hull {vec 0:real^3,basis 1,basis 2,basis 3}`;
                 `u:real^3->bool`] MOI_SPU_NBHD) THEN
  ASM_REWRITE_TAC[MOI_SPU_K0_FACTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^3->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `pl_polyhedron (v:real^3->bool)` THEN
  REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `cv:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?aa:(real^3->bool)->real^3 rr:(real^3->bool)->real.
      !p. p IN cv
          ==> (!x. x IN p ==> aa p dot x <= rr p) /\
              (!x. x IN convex hull {vec 0,basis 1,basis 2,basis 3}
                   ==> rr p <= aa p dot x) /\
              rr p < aa p dot vector[&1 / &3; &1 / &3; &1 / &3] /\
              rr p < &0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `p:real^3->bool` THEN
    ASM_CASES_TAC `(p:real^3->bool) IN cv` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SPU_SEP THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `v INTER convex hull {vec 0:real^3,basis 1,basis 2,basis 3}
                 SUBSET relative_frontier(convex hull {basis 1,basis 2,basis 3})` THEN
    ASM_REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `bb = (n INTER ({x:real^3 | (basis 2 + basis 3) dot x <= &1} INTER
                   {x | (basis 1 + basis 3) dot x <= &1} INTER
                   {x | (basis 1 + basis 2) dot x <= &1})) INTER
         INTERS (IMAGE (\p:real^3->bool. {x:real^3 | aa p dot x >= rr p}) cv)` THEN
  SUBGOAL_THEN `polytope (bb:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "bb" THEN MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[POLYHEDRON_INTER; POLYHEDRON_HALFSPACE_LE];
      MATCH_MP_TAC POLYHEDRON_INTERS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; POLYHEDRON_HALFSPACE_GE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(bb:real^3->bool) SUBSET n` ASSUME_TAC THENL
   [EXPAND_TAC "bb" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {basis 1:real^3,basis 2,basis 3} SUBSET bb`
  ASSUME_TAC THENL
   [EXPAND_TAC "bb" THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_INTERS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN convex hull {vec 0,basis 1,basis 2,basis 3}`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN convex hull {basis 1,basis 2,basis 3}` THEN
      REWRITE_TAC[MOI_SPU_K0; MOI_SS2_STD_F0; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `n:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      UNDISCH_TAC `(x:real^3) IN convex hull {basis 1,basis 2,basis 3}` THEN
      REWRITE_TAC[MOI_SS2_STD_F0; IN_ELIM_THM; DOT_LADD] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(x:real^3) IN convex hull {basis 1,basis 2,basis 3}` THEN
      REWRITE_TAC[MOI_SS2_STD_F0; IN_ELIM_THM; DOT_LADD] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(x:real^3) IN convex hull {basis 1,basis 2,basis 3}` THEN
      REWRITE_TAC[MOI_SS2_STD_F0; IN_ELIM_THM; DOT_LADD] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      X_GEN_TAC `p:real^3->bool` THEN DISCH_TAC THEN REWRITE_TAC[real_ge] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vec 0 IN interior bb /\
    vector[&1 / &3; &1 / &3; &1 / &3] IN interior (bb:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `interior n INTER {x:real^3 | (basis 2 + basis 3) dot x < &1} INTER
      {x | (basis 1 + basis 3) dot x < &1} INTER
      {x | (basis 1 + basis 2) dot x < &1} INTER
      INTERS (IMAGE (\p:real^3->bool. {x:real^3 | aa p dot x > rr p}) cv)
      SUBSET interior bb`
    MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [EXPAND_TAC "bb" THEN MP_TAC(ISPEC `n:real^3->bool` INTERIOR_SUBSET) THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_INTERS; FORALL_IN_IMAGE;
                    IN_ELIM_THM] THEN
        MESON_TAC[REAL_LT_IMP_LE; real_ge; real_gt];
        REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
        REWRITE_TAC[OPEN_INTERIOR; OPEN_HALFSPACE_LT] THEN
        MATCH_MP_TAC OPEN_INTERS THEN
        ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; OPEN_HALFSPACE_GT]];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(fun th ->
      CONJ_TAC THEN MATCH_MP_TAC th) THEN
    REWRITE_TAC[IN_INTER; IN_INTERS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[DOT_LADD; DOT_RZERO; real_gt] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; VECTOR_3; VEC_COMPONENT] THEN
    ASM_SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    UNDISCH_TAC `convex hull {vec 0:real^3,basis 1,basis 2,basis 3} SUBSET
                 interior n` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[MOI_SPU_K0_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN interior bb
               ==> x$2 + x$3 < &1 /\ x$1 + x$3 < &1 /\ x$1 + x$2 < &1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SPU_B0_INTERIOR THEN EXPAND_TAC "bb" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p x:real^3. p IN cv /\ x IN p ==> ~(x IN interior bb)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(aa:(real^3->bool)->real^3) p`;
                   `(rr:(real^3->bool)->real) p`; `x:real^3`]
      MOI_SPU_HALFSPACE_INT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN
         `interior bb SUBSET
          interior {y:real^3 | (aa:(real^3->bool)->real^3) p dot y >=
                               (rr:(real^3->bool)->real) p}`
        MP_TAC THENL
         [MATCH_MP_TAC SUBSET_INTERIOR THEN EXPAND_TAC "bb" THEN
          REWRITE_TAC[SUBSET; IN_INTER; IN_INTERS; FORALL_IN_IMAGE] THEN
          ASM_MESON_TAC[];
          ASM SET_TAC[]];
        ASM_MESON_TAC[]];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:real^3->bool`) THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN
      STRIP_TAC THEN
      UNDISCH_TAC `!x:real^3. x IN p ==> &0 <= (rr:(real^3->bool)->real) p` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier bb = bb DIFF interior (bb:real^3->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `~(interior bb:real^3->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; frontier;
                 CLOSURE_CLOSED; POLYTOPE_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier(convex hull {basis 1:real^3,basis 2,basis 3}) SUBSET
    relative_frontier bb`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `convex hull {basis 1:real^3,basis 2,basis 3} SUBSET bb` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:real^3) IN
                   relative_frontier(convex hull {basis 1,basis 2,basis 3})` THEN
      REWRITE_TAC[MOI_SPU_BDF0; MOI_SS2_STD_F0; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (is_forall o concl)) THEN
      UNDISCH_TAC `(x:real^3) IN
                   relative_frontier(convex hull {basis 1,basis 2,basis 3})` THEN
      REWRITE_TAC[MOI_SPU_BDF0; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bb:real^3->bool`; `vector[&1 / &3; &1 / &3; &1 / &3]:real^3`;
                 `vec 0:real^3`] MOI_SA2_CONE_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fix")
      (LABEL_TAC "cone"))))) THEN
  MP_TAC(ISPECL [`bb:real^3->bool`; `h:real^3->real^3`; `g:real^3->real^3`]
    MOI_SA2_PLH_EXTEND_ID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "fix" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_DIFF];
    DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^3. if x IN bb then h x else x`;
                        `\x:real^3. if x IN bb then g x else x`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((x:real^3) IN bb)` (fun th -> REWRITE_TAC[th]) THEN
    ASM SET_TAC[];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3->bool` STRIP_ASSUME_TAC) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN USE_THEN "fix" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^3. if x IN bb then h x else x)
          (convex hull {basis 1,basis 2,basis 3}) =
    IMAGE h (convex hull {basis 1,basis 2,basis 3})`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN bb` (fun th -> REWRITE_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^3->real^3`; `convex hull {basis 1:real^3,basis 2,basis 3}`;
                 `vector[&1 / &3; &1 / &3; &1 / &3]:real^3`; `vec 0:real^3`]
    MOI_SPU_IMAGE_CONE) THEN
  ANTS_TAC THENL
   [SIMP_TAC[CONVEX_CONVEX_HULL; COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT;
             FINITE_INSERT; FINITE_EMPTY] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_SPU_RELINT_F0; IN_ELIM_THM; VECTOR_3] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `basis 1:real^3` THEN
      REWRITE_TAC[MOI_SPU_BDF0; IN_ELIM_THM] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "cone" MATCH_MP_TAC THEN
      ASM SET_TAC[]];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_ADD_LID; VECTOR_SUB_RZERO; MOI_SPU_CONE_IMAGE_STD]]);;

(* ========================================================================= *)
(* FACE_PUSH (Moise Thm 4) for every 2-face of every 3-simplex in real^3,    *)
(* transported from the standard simplex by an affine bijection              *)
(* (MOI_SS2_AFFINE_ISO, MOI_SCD_PUSH_PLH).                                   *)
(* ========================================================================= *)

let MOI_SPU_SIMPLEX_FACE = prove
 (`!k f:real^3->bool.
     &3 simplex k /\ f face_of k /\ aff_dim f = &2
     ==> ?w a b c. ~affine_dependent {w,a,b,c} /\ ~(w = a) /\ ~(w = b) /\
                   ~(w = c) /\ ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
                   k = convex hull {w,a,b,c} /\ f = convex hull {a,b,c}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `vv:real^3->bool`
    STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(f:real^3->bool) face_of k` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `cf:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~affine_dependent (cf:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (vv:real^3->bool) /\ FINITE (cf:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD (cf:real^3->bool) = 3 /\ CARD (vv:real^3->bool) = 4`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `aff_dim (f:real^3->bool) = &2` THEN
    UNDISCH_TAC `&(CARD (vv:real^3->bool)):int = &3 + &1` THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[INT_ARITH `x - &1:int = &2 <=> x = &3`; INT_OF_NUM_EQ] THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(cf:real^3->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3`
    (X_CHOOSE_THEN `c:real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `((vv:real^3->bool) DIFF cf) HAS_SIZE 1` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; FINITE_DIFF; CARD_DIFF] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_TAC `w:real^3`) THEN
  SUBGOAL_THEN `(vv:real^3->bool) = {w,a,b,c}` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `(vv:real^3->bool) DIFF cf = {w}` THEN
    UNDISCH_TAC `(cf:real^3->bool) SUBSET vv` THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((w:real^3) IN {a,b,c})` MP_TAC THENL
   [UNDISCH_TAC `{w:real^3,a,b,c} DIFF cf = {w}` THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`w:real^3`; `a:real^3`; `b:real^3`; `c:real^3`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let FACE_PUSH = prove
 (`!k f:real^3->bool.
     &3 simplex k /\ f face_of k /\ aff_dim f = &2
     ==> moi_sch3_push k f (relative_frontier f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `f:real^3->bool`] MOI_SPU_SIMPLEX_FACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (X_CHOOSE_THEN `a:real^3`
    (X_CHOOSE_THEN `b:real^3` (X_CHOOSE_THEN `c:real^3`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`w:real^3`; `a:real^3`; `b:real^3`; `c:real^3`]
    MOI_SS2_AFFINE_ISO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^3->real^3` (X_CHOOSE_THEN
    `l':real^3->real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x y:real^3. (l:real^3->real^3) x = l y ==> x = y`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:real^3->real^3`; `l':real^3->real^3`; `w:real^3`]
    MOI_SS2_AFFINE_PLH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^3. w + (l:real^3->real^3) x)
      {vec 0,basis 1,basis 2,basis 3} = {w,a,b,c} /\
    IMAGE (\x:real^3. w + (l:real^3->real^3) x)
      {basis 1,basis 2,basis 3} = {a,b,c}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES;
                MATCH_MP LINEAR_0 (ASSUME `linear (l:real^3->real^3)`)] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `w + (a - w):real^3 = a`; VECTOR_ADD_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:real^3->real^3`; `w:real^3`;
                 `{vec 0:real^3,basis 1,basis 2,basis 3}`]
    MOI_SS2_AFFINE_IMAGES) THEN
  MP_TAC(ISPECL [`l:real^3->real^3`; `w:real^3`;
                 `{basis 1:real^3,basis 2,basis 3}`]
    MOI_SS2_AFFINE_IMAGES) THEN
  MP_TAC(ISPECL [`l:real^3->real^3`; `w:real^3`;
                 `convex hull {basis 1:real^3,basis 2,basis 3}`]
    MOI_SS2_AFFINE_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`convex hull {vec 0:real^3,basis 1,basis 2,basis 3}`;
                 `convex hull {basis 1:real^3,basis 2,basis 3}`;
                 `relative_frontier(convex hull {basis 1:real^3,basis 2,basis 3})`;
                 `\x:real^3. w + (l:real^3->real^3) x`;
                 `\y:real^3. (l':real^3->real^3) (y - w)`]
    MOI_SCD_PUSH_PLH) THEN
  ASM_REWRITE_TAC[MOI_SPU_FACE_PUSH_STD] THEN
  UNDISCH_TAC
   `relative_frontier (IMAGE (\x:real^3. w + (l:real^3->real^3) x)
                       (convex hull {basis 1,basis 2,basis 3})) =
    IMAGE (\x. w + l x)
          (relative_frontier (convex hull {basis 1,basis 2,basis 3}))` THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

(* ========================================================================= *)
(* PL 2-cells: PLHs between cells and extension of a boundary PLH (cone      *)
(* extension); a PLH of the boundary sphere of a 3-simplex carrying a PL     *)
(* disk onto a 2-face (DISK_COMPLEMENT and gluing).                          *)
(* ========================================================================= *)

let MOI_SPU_TRI_VERTS = prove
 (`!t:real^N->bool.
     &2 simplex t ==> ?e0 e1 e2. ~collinear {e0,e1,e2} /\ t = convex hull {e0,e1,e2}`,
  GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD (c:real^N->bool)):int = &2 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^N` (X_CHOOSE_THEN `e1:real^N`
    (X_CHOOSE_THEN `e2:real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`e0:real^N`; `e1:real^N`; `e2:real^N`] THEN
  ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN
  ASM_MESON_TAC[]);;

let MOI_SPU_CELL_PLH = prove
 (`!d j:real^3->bool e i:real^3->bool.
     pl_cell_with_boundary 2 d j /\ pl_cell_with_boundary 2 e i
     ==> ?f g. pl_homeomorphism (d,e) (f,g) /\ IMAGE f j = i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `t:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^3`
     (X_CHOOSE_THEN `p':real^3->real^3` STRIP_ASSUME_TAC)))
   (X_CHOOSE_THEN `t':real^3->bool` (X_CHOOSE_THEN `q:real^3->real^3`
     (X_CHOOSE_THEN `q':real^3->real^3` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPEC `t:real^3->bool` MOI_SPU_TRI_VERTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^3` (X_CHOOSE_THEN `e1:real^3`
    (X_CHOOSE_THEN `e2:real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`t':real^3->bool`; `e0:real^3`; `e1:real^3`; `e2:real^3`]
    MOI_SS2_TRI_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th)) &&
    fst(dest_var(lhs(concl th))) = "t")) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^3->real^3` (X_CHOOSE_THEN
    `m':real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`(q:real^3->real^3) o ((m:real^3->real^3) o (p':real^3->real^3))`;
    `((p:real^3->real^3) o (m':real^3->real^3)) o (q':real^3->real^3)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `t':real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `convex hull {e0:real^3,e1,e2}` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN
  SUBGOAL_THEN
   `IMAGE (p':real^3->real^3)
      (IMAGE p (relative_frontier (convex hull {e0,e1,e2}))) =
    relative_frontier (convex hull {e0,e1,e2})`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^3. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    UNDISCH_TAC `pl_homeomorphism (convex hull {e0:real^3,e1,e2},d)
                                  (p:real^3->real^3,p')` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t. s SUBSET t /\ (x:real^3) IN s ==> x IN t`) THEN
    EXISTS_TAC `relative_frontier (convex hull {e0:real^3,e1,e2})` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
    MATCH_MP_TAC FINITE_IMP_COMPACT THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ASM_REWRITE_TAC[]]);;

let MOI_SPU_CELL_EXTEND = prove
 (`!d j:real^3->bool e i:real^3->bool (a:real^3->real^3) a'.
     pl_cell_with_boundary 2 d j /\ pl_cell_with_boundary 2 e i /\
     pl_homeomorphism (j,i) (a,a')
     ==> ?f g. pl_homeomorphism (d,e) (f,g) /\ (!x. x IN j ==> f x = a x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `t:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^3`
     (X_CHOOSE_THEN `p':real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))))))
   (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t':real^3->bool` (X_CHOOSE_THEN `q:real^3->real^3`
      (X_CHOOSE_THEN `q':real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))))))
    ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `relative_frontier t SUBSET (t:real^3->bool) /\
    relative_frontier t' SUBSET (t':real^3->bool) /\
    pl_polyhedron(relative_frontier t:real^3->bool) /\
    pl_polyhedron(relative_frontier t':real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; POLYTOPE_IMP_CLOSED;
                  SIMPLEX_IMP_POLYTOPE; MOI_SA2_POLYTOPE_RF_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier t,j)
                  (p:real^3->real^3,p')`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^3->bool`; `d:real^3->bool`; `p:real^3->real^3`;
                   `p':real^3->real^3`; `relative_frontier t:real^3->bool`]
      MOI_FSA_PL_HOMEO_RESTRICT) THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (i,relative_frontier t')
                  (q':real^3->real^3,q)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t':real^3->bool`; `e:real^3->bool`; `q:real^3->real^3`;
                   `q':real^3->real^3`; `relative_frontier t':real^3->bool`]
      MOI_FSA_PL_HOMEO_RESTRICT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `t':real^3->bool`; `2`;
                 `(q':real^3->real^3) o ((a:real^3->real^3) o (p:real^3->real^3))`;
                 `((p':real^3->real^3) o (a':real^3->real^3)) o (q:real^3->real^3)`]
    PL_HOMEOMORPHISM_CONE_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `i:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^3->real^3` (X_CHOOSE_THEN
    `g':real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`(q:real^3->real^3) o ((f':real^3->real^3) o (p':real^3->real^3))`;
    `((p:real^3->real^3) o (g':real^3->real^3)) o (q':real^3->real^3)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `t':real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `?y:real^3. y IN relative_frontier t /\ (x:real^3) = (p:real^3->real^3) y`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
  SUBGOAL_THEN `(p':real^3->real^3) x = y` SUBST1_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[o_THM] THEN
  SUBGOAL_THEN `(a:real^3->real^3) x IN e` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_SPU_CELL_POLY = prove
 (`!n d j:real^N->bool.
     pl_cell_with_boundary n d j
     ==> pl_polyhedron j /\ pl_polyhedron d /\ compact d /\ j SUBSET d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `p:real^N->real^N`
    (X_CHOOSE_THEN `p':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `polytope (t:real^N->bool) /\ relative_frontier t SUBSET t /\
                pl_polyhedron (relative_frontier t)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; RELATIVE_FRONTIER_SUBSET;
                  POLYTOPE_IMP_CLOSED; MOI_SA2_POLYTOPE_RF_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN `d = IMAGE (p:real^N->real^N) t` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT] THEN ASM_MESON_TAC[homeomorphism];
    ASM SET_TAC[]]);;

let MOI_SPU_FACE_SIMPLEX = prove
 (`!k f:real^N->bool.
     &3 simplex k /\ f face_of k /\ aff_dim f = &2
     ==> &2 simplex f /\ f SUBSET relative_frontier k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`&3:int`; `k:real^N->bool`; `f:real^N->bool`]
      SIMPLEX_FACE_OF_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:int` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `m:int = &2` (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    MATCH_MP_TAC FACE_OF_SUBSET_RELATIVE_FRONTIER THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`k:real^N->bool`; `&3:int`] AFF_DIM_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let MOI_SPU_PLH_ID_POLYTOPE = prove
 (`!s:real^N->bool. polytope s ==> pl_homeomorphism (s,s) ((\x. x),(\x. x))`,
  SIMP_TAC[pl_homeomorphism; HOMEOMORPHISM_ID;
           GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID;
           LOCALLY_POLYHEDRAL_POLYTOPE]);;

let MOI_SPU_SPHERE_DISK_PLH = prove
 (`!k d j f:real^3->bool.
     &3 simplex k /\ pl_cell_with_boundary 2 d j /\
     d SUBSET relative_frontier k /\ f face_of k /\ aff_dim f = &2
     ==> ?ph ps. pl_homeomorphism (relative_frontier k,relative_frontier k)
                                  (ph,ps) /\
                 IMAGE ph d = f /\ IMAGE ph j = relative_frontier f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `f:real^3->bool`] MOI_SPU_FACE_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 2 (relative_frontier k:real^3->bool)` ASSUME_TAC
  THENL
   [MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 + 1 = 3`];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 f (relative_frontier f:real^3->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`f:real^3->bool`; `\x:real^3. x`; `\x:real^3. x`] THEN
    ASM_SIMP_TAC[MOI_SPU_PLH_ID_POLYTOPE; SIMPLEX_IMP_POLYTOPE; IMAGE_ID] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; MOI_SPU_PLH_ID_POLYTOPE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier k:real^3->bool`; `d:real^3->bool`;
                 `j:real^3->bool`] DISK_COMPLEMENT) THEN
  MP_TAC(ISPECL [`relative_frontier k:real^3->bool`; `f:real^3->bool`;
                 `relative_frontier f:real^3->bool`] DISK_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`d:real^3->bool`; `j:real^3->bool`; `f:real^3->bool`;
                 `relative_frontier f:real^3->bool`] MOI_SPU_CELL_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `al:real^3->real^3` (X_CHOOSE_THEN
    `al':real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`2`; `d:real^3->bool`; `j:real^3->bool`] MOI_SPU_CELL_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `(relative_frontier k DIFF d) UNION j:real^3->bool`;
                 `j:real^3->bool`] MOI_SPU_CELL_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `(relative_frontier k DIFF f) UNION
                       relative_frontier f:real^3->bool`;
                 `relative_frontier f:real^3->bool`] MOI_SPU_CELL_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_homeomorphism (j,relative_frontier f)
                  (al:real^3->real^3,al')`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:real^3->bool`; `f:real^3->bool`; `al:real^3->real^3`;
                   `al':real^3->real^3`; `j:real^3->bool`]
      MOI_FSA_PL_HOMEO_RESTRICT) THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(relative_frontier k DIFF d) UNION j:real^3->bool`;
                 `j:real^3->bool`;
                 `(relative_frontier k DIFF f) UNION
                  relative_frontier f:real^3->bool`;
                 `relative_frontier f:real^3->bool`;
                 `al:real^3->real^3`; `al':real^3->real^3`]
    MOI_SPU_CELL_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `be:real^3->real^3` (X_CHOOSE_THEN
    `be':real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`d:real^3->bool`;
                 `(relative_frontier k DIFF d) UNION j:real^3->bool`;
                 `f:real^3->bool`;
                 `(relative_frontier k DIFF f) UNION
                  relative_frontier f:real^3->bool`;
                 `al:real^3->real^3`; `al':real^3->real^3`;
                 `be:real^3->real^3`; `be':real^3->real^3`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  SUBGOAL_THEN
   `relative_frontier f SUBSET (f:real^3->bool) /\ closed (f:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; POLYTOPE_IMP_CLOSED;
                  SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `d INTER ((relative_frontier k DIFF d) UNION j) = j:real^3->bool /\
    f INTER ((relative_frontier k DIFF f) UNION relative_frontier f) =
    relative_frontier f:real^3->bool /\
    d UNION ((relative_frontier k DIFF d) UNION j) =
    relative_frontier k:real^3->bool /\
    f UNION ((relative_frontier k DIFF f) UNION relative_frontier f) =
    relative_frontier k:real^3->bool`
  (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^3. if x IN d then (al:real^3->real^3) x else be x`;
    `\y:real^3. if y IN f then (al':real^3->real^3) y else be' y`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I
    [pl_homeomorphism] o check (fun th -> rand(rator(concl th)) =
      `(d:real^3->bool,f:real^3->bool)`)) THEN
  CONJ_TAC THEN MATCH_MP_TAC EQ_TRANS THENL
   [EXISTS_TAC `IMAGE (al:real^3->real^3) d`;
    EXISTS_TAC `IMAGE (al:real^3->real^3) j`] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC(SET_RULE
      `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x)
       ==> IMAGE f s = IMAGE g s`) THEN
     ASM SET_TAC[];
     ASM_MESON_TAC[homeomorphism]]));;

(* ========================================================================= *)
(* SIMPLEX_PUSH (Moise Thms 5-6, pp.119-120).  A PLH of the boundary sphere  *)
(* carrying d onto a 2-face f is extended conewise over the simplex dilated  *)
(* by 2 about an interior point (MOI_SPU_DIL, MOI_SPU_EXTEND_SPHERE_PLH),    *)
(* and FACE_PUSH at f is conjugated by it.                                   *)
(* ========================================================================= *)

let MOI_SPU_DIL = prove
 (`!k (c:real^3).
     &3 simplex k /\ c IN interior k
     ==> pl_homeomorphism ((:real^3),(:real^3))
           ((\x. --c + &2 % x),(\y. inv(&2) % (y - --c))) /\
         (!x. inv(&2) % ((--c + &2 % x) - --c) = x) /\
         (!y. --c + &2 % (inv(&2) % (y - --c)) = y) /\
         polytope (IMAGE (\x. --c + &2 % x) k) /\
         interior (IMAGE (\x. --c + &2 % x) k) =
           IMAGE (\x. --c + &2 % x) (interior k) /\
         relative_frontier (IMAGE (\x. --c + &2 % x) k) =
           IMAGE (\x. --c + &2 % x) (relative_frontier k) /\
         relative_frontier (IMAGE (\x. --c + &2 % x) k) =
           IMAGE (\x. --c + &2 % x) k DIFF
           interior (IMAGE (\x. --c + &2 % x) k) /\
         k SUBSET interior (IMAGE (\x. --c + &2 % x) k) /\
         c IN relative_interior (IMAGE (\x. --c + &2 % x) k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!x:real^3. inv(&2) % ((--c + &2 % x) - --c) = x) /\
                (!y:real^3. --c + &2 % (inv(&2) % (y - --c)) = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. &2 % x`; `\x:real^3. inv(&2) % x`; `--c:real^3`]
    MOI_SS2_AFFINE_PLH) THEN
  REWRITE_TAC[LINEAR_SCALING] THEN ANTS_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN VECTOR_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. &2 % x`; `--c:real^3`; `k:real^3->bool`]
    MOI_SS2_AFFINE_IMAGES) THEN
  REWRITE_TAC[LINEAR_SCALING] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_OF_NUM_EQ; ARITH_EQ];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `interior (IMAGE (\x:real^3. --c + &2 % x) k) =
    IMAGE (\x. --c + &2 % x) (interior k)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!s. IMAGE (\x:real^3. --c + &2 % x) s =
          IMAGE (\x. --c + x) (IMAGE (\x. &2 % x) s)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
    REWRITE_TAC[INTERIOR_TRANSLATION] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTERIOR_INJECTIVE_LINEAR_IMAGE THEN
    SIMP_TAC[LINEAR_SCALING; VECTOR_MUL_LCANCEL; REAL_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `k SUBSET interior (IMAGE (\x:real^3. --c + &2 % x) k)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN EXISTS_TAC `midpoint(c:real^3,x)` THEN CONJ_TAC THENL
     [REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `x:real^3 = c` THENL
     [ASM_REWRITE_TAC[MIDPOINT_REFL]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:real^3->bool`; `c:real^3`; `x:real^3`]
      IN_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CLOSURE_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope (IMAGE (\x:real^3. --c + &2 % x) k)` ASSUME_TAC THENL
   [UNDISCH_TAC `&3 simplex (k:real^3->bool)` THEN REWRITE_TAC[simplex] THEN
    DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\x:real^3. &2 % x`; `--c:real^3`; `vv:real^3->bool`]
      MOI_SS2_AFFINE_IMAGES) THEN
    REWRITE_TAC[LINEAR_SCALING] THEN ANTS_TAC THENL
     [REPEAT GEN_TAC THEN SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_OF_NUM_EQ; ARITH_EQ];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    ASM_SIMP_TAC[FINITE_IMAGE; AFFINE_INDEPENDENT_IMP_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(interior (IMAGE (\x:real^3. --c + &2 % x) k) = {})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!s t:real^3->bool. s SUBSET t /\ ~(s = {}) ==> ~(t = {})`) THEN
    EXISTS_TAC `k:real^3->bool` THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(c:real^3) IN interior k` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_interior (IMAGE (\x:real^3. --c + &2 % x) k) =
    interior (IMAGE (\x:real^3. --c + &2 % x) k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_INTERIOR_NONEMPTY_INTERIOR THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier (IMAGE (\x:real^3. --c + &2 % x) k) =
    IMAGE (\x. --c + &2 % x) k DIFF interior (IMAGE (\x. --c + &2 % x) k)`
  ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    REWRITE_TAC[ASSUME
     `relative_interior (IMAGE (\x:real^3. --c + &2 % x) k) =
      interior (IMAGE (\x:real^3. --c + &2 % x) k)`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CLOSURE_CLOSED THEN
    MATCH_MP_TAC POLYTOPE_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3) IN relative_interior (IMAGE (\x. --c + &2 % x) k)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME
     `relative_interior (IMAGE (\x:real^3. --c + &2 % x) k) =
      interior (IMAGE (\x:real^3. --c + &2 % x) k)`] THEN
    UNDISCH_TAC `k SUBSET interior (IMAGE (\x:real^3. --c + &2 % x) k)` THEN
    MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(c:real^3) IN interior k` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let MOI_SPU_HALF = prove
 (`!c y:real^3. c + inv(&2) % ((--c + &2 % y) - c) = y`,
  REPEAT GEN_TAC THEN VECTOR_ARITH_TAC);;

let MOI_SPU_HALF_R = prove
 (`!c y:real^3 r. c + (r * inv(&2)) % ((--c + &2 % y) - c) = c + r % (y - c)`,
  REPEAT GEN_TAC THEN VECTOR_ARITH_TAC);;

let MOI_SPU_EXTEND_SPHERE_PLH = prove
 (`!k (ph:real^3->real^3) ps.
     &3 simplex k /\
     pl_homeomorphism (relative_frontier k,relative_frontier k) (ph,ps)
     ==> ?k2 fh gh. polytope k2 /\ k SUBSET interior k2 /\
                    pl_homeomorphism (k2,k2) (fh,gh) /\
                    (!x. x IN relative_frontier k ==> fh x = ph x /\ gh x = ps x) /\
                    IMAGE fh k = k /\ IMAGE gh k = k /\
                    (!x. x IN k2 /\ ~(x IN interior k2)
                         ==> ~(fh x IN interior k2))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `c:real^3` o MATCH_MP MOI_FN1_SIMPLEX_3_INTERIOR) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `c:real^3`] MOI_SPU_DIL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k2 = IMAGE (\x:real^3. --c + &2 % x) k` THEN
  DISCH_THEN(fun th -> let ths = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC [el 0 ths; el 1 ths; el 2 ths; el 3 ths;
                          SYM(el 4 ths); SYM(el 5 ths); SYM(el 6 ths);
                          el 7 ths; el 8 ths]) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `&3:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [INT_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `convex (k:real^3->bool) /\ compact k /\ convex (k2:real^3->bool) /\
    compact k2 /\ c IN relative_interior k /\ c IN k /\
    pl_polyhedron (relative_frontier k2:real^3->bool) /\
    ~(relative_frontier k2:real^3->bool = {}) /\
    relative_frontier k SUBSET (k:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
      ASM_MESON_TAC[POLYTOPE_IMP_CONVEX];
      ASM_MESON_TAC[POLYTOPE_IMP_COMPACT];
      ASM_MESON_TAC[INTERIOR_SUBSET_RELATIVE_INTERIOR; SUBSET];
      ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
      ASM_MESON_TAC[MOI_SA2_POLYTOPE_RF_POLYHEDRON];
      UNDISCH_TAC `IMAGE (\x:real^3. --c + &2 % x) (relative_frontier k) =
                   relative_frontier k2` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
      ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; COMPACT_IMP_CLOSED;
                    SIMPLEX_IMP_COMPACT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier k,relative_frontier k2)
                     ((\x:real^3. --c + &2 % x),(\y. inv(&2) % (y - --c)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^3. --c + &2 % x`; `\y:real^3. inv(&2) % (y - --c)`;
                   `relative_frontier k:real^3->bool`] MOI_SCD_PLH_RESTRICT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ph2 = (\x:real^3. --c + &2 % x) o
                    ((ph:real^3->real^3) o (\y. inv(&2) % (y - --c)))` THEN
  ABBREV_TAC `ps2 = ((\x:real^3. --c + &2 % x) o (ps:real^3->real^3)) o
                    (\y. inv(&2) % (y - --c))` THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier k2,relative_frontier k2)
                     (ph2:real^3->real^3,ps2)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ph2"; "ps2"] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier k:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier k:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN relative_frontier k
               ==> ph2 (--c + &2 % x) = --c + &2 % ph x /\
                   ps2 (--c + &2 % x) = --c + &2 % ps x /\
                   (--c + &2 % x) IN relative_frontier k2`
  (LABEL_TAC "ph2") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["ph2"; "ps2"] THEN REWRITE_TAC[o_THM] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (\x:real^3. --c + &2 % x) (relative_frontier k) =
                 relative_frontier k2` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((c:real^3) IN relative_frontier k2) /\
    (!x y. x IN relative_frontier k2 /\ y IN relative_frontier k2 /\
           y IN segment[c,x] ==> y = x) /\
    UNIONS {segment[c,x] | x IN relative_frontier k2} = k2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(c:real^3) IN relative_interior k2` THEN
      REWRITE_TAC[relative_frontier; IN_DIFF] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_RF_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`k2:real^3->bool`; `c:real^3`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_CON_CONE_RF THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `fh = moi_con_conemap (relative_frontier k2) (c:real^3) c
                                   (ph2:real^3->real^3)` THEN
  ABBREV_TAC `gh = moi_con_conemap (relative_frontier k2) (c:real^3) c
                                   (ps2:real^3->real^3)` THEN
  MP_TAC(ISPECL [`relative_frontier k2:real^3->bool`;
                 `relative_frontier k2:real^3->bool`; `c:real^3`; `c:real^3`;
                 `ph2:real^3->real^3`; `ps2:real^3->real^3`]
    MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x r. x IN relative_frontier k2 /\ &0 <= r /\ r <= &1
          ==> (fh:real^3->real^3) (c + r % (x - c)) = c + r % (ph2 x - c) /\
              (gh:real^3->real^3) (c + r % (x - c)) = c + r % (ps2 x - c)`
  (LABEL_TAC "form") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["fh"; "gh"] THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_CON_CONEMAP_EQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x:real^3. x IN relative_frontier k
                ==> ph x IN relative_frontier k /\ ps x IN relative_frontier k) /\
    (!x:real^3. x IN relative_frontier k2 ==> ph2 x IN relative_frontier k2) /\
    (!y:real^3. y IN k2 ==> fh y IN k2 /\ gh y IN k2 /\
                           fh (gh y) = y /\ gh (fh y) = y)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN relative_frontier k
               ==> (fh:real^3->real^3) x = (ph:real^3->real^3) x /\
                   (gh:real^3->real^3) x = (ps:real^3->real^3) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "ph2" (MP_TAC o C MATCH_MP
      (ASSUME `(x:real^3) IN relative_frontier k`)) THEN
    STRIP_TAC THEN
    USE_THEN "form" (MP_TAC o SPECL [`--c + &2 % x:real^3`; `inv(&2)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    ASM_REWRITE_TAC[MOI_SPU_HALF];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN k ==> fh y IN k /\ gh y IN k` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`relative_frontier k:real^3->bool`; `c:real^3`; `y:real^3`]
      MOI_CON_IN_CONE) THEN
    SUBGOAL_THEN `UNIONS {segment[c,x] | x IN relative_frontier k} =
                  (k:real^3->bool)` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_CON_CONE_RF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `r:real`
      STRIP_ASSUME_TAC)) THEN
    USE_THEN "ph2" (MP_TAC o C MATCH_MP
      (ASSUME `(x:real^3) IN relative_frontier k`)) THEN
    STRIP_TAC THEN
    USE_THEN "form" (MP_TAC o SPECL [`--c + &2 % x:real^3`; `r * inv(&2)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[MOI_SPU_HALF_R] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `c + r % (z - c):real^3 = (&1 - r) % c + r % z`] THEN
    CONJ_TAC THEN MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`k2:real^3->bool`; `fh:real^3->real^3`; `gh:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(gh:real^3->real^3) y` THEN ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET];
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(fh:real^3->real^3) y` THEN ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN relative_frontier k2` ASSUME_TAC THENL
     [UNDISCH_TAC `k2 DIFF interior k2 = relative_frontier (k2:real^3->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_DIFF];
      ALL_TAC] THEN
    SUBGOAL_THEN `(fh:real^3->real^3) x IN relative_frontier k2` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `k2 DIFF interior k2 = relative_frontier (k2:real^3->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[IN_DIFF]]);;

let MOI_SPU_SIMPLEX_HAS_FACE = prove
 (`!k:real^3->bool. &3 simplex k ==> ?f. f face_of k /\ aff_dim f = &2`,
  GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(vv:real^3->bool) HAS_SIZE 4` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `(&(CARD (vv:real^3->bool)):int) = &3 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (X_CHOOSE_THEN `a:real^3`
    (X_CHOOSE_THEN `b:real^3` (X_CHOOSE_THEN `c:real^3`
    STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  EXISTS_TAC `convex hull {a:real^3,b,c}` THEN
  SUBGOAL_THEN `~affine_dependent {a:real^3,b,c}` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `{w:real^3,a,b,c}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{a:real^3,b,c}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV)]);;

let MOI_SPU_IMAGE_SWAP = prove
 (`!(ph:real^3->real^3) ps s d j f bf.
     (!x. x IN s ==> ph x IN s /\ ps x IN s /\ ps (ph x) = x /\ ph (ps x) = x) /\
     d SUBSET s /\ j SUBSET d /\ IMAGE ph d = f /\ IMAGE ph j = bf
     ==> IMAGE ps ((s DIFF f) UNION bf) = (s DIFF d) UNION j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
    (fun th -> rhs(concl th) = t))) [`f:real^3->bool`; `bf:real^3->bool`] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNION; IN_DIFF] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THENL
     [DISJ1_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[SUBSET];
      DISJ2_TAC THEN ASM_MESON_TAC[SUBSET]];
    STRIP_TAC THENL
     [EXISTS_TAC `(ph:real^3->real^3) y` THEN ASM_SIMP_TAC[] THEN
      DISJ1_TAC THEN ASM_MESON_TAC[SUBSET];
      EXISTS_TAC `(ph:real^3->real^3) y` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      DISJ2_TAC THEN ASM_MESON_TAC[]]]);;

let SIMPLEX_PUSH = prove
 (`!k d j:real^3->bool.
     &3 simplex k /\ pl_cell_with_boundary 2 d j /\ d SUBSET relative_frontier k
     ==> moi_sch3_push k d j`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC o
    MATCH_MP MOI_SPU_SIMPLEX_HAS_FACE) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `f:real^3->bool`] MOI_SPU_SPHERE_DISK_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ph:real^3->real^3` (X_CHOOSE_THEN
    `ps:real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `ph:real^3->real^3`; `ps:real^3->real^3`]
    MOI_SPU_EXTEND_SPHERE_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real^3->bool` (X_CHOOSE_THEN
    `fh:real^3->real^3` (X_CHOOSE_THEN `gh:real^3->real^3`
      STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `f:real^3->bool`] FACE_PUSH) THEN
  ASM_REWRITE_TAC[moi_sch3_push] THEN DISCH_THEN(LABEL_TAC "fp") THEN
  REWRITE_TAC[moi_sch3_push] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3->bool`; `v:real^3->bool`] THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_SCD_SIMPLEX_FILL (ASSUME `&3 simplex (k:real^3->bool)`)) THEN
  DISCH_THEN(ASSUME_TAC o SYM o CONJUNCT1) THEN
  SUBGOAL_THEN
   `(!x:real^3. x IN relative_frontier k
                ==> ph x IN relative_frontier k /\ ps x IN relative_frontier k /\
                    ps (ph x) = x /\ ph (ps x) = x) /\
    (!y:real^3. y IN k2 ==> fh y IN k2 /\ gh y IN k2 /\
                           fh (gh y) = y /\ gh (fh y) = y) /\
    fh continuous_on k2 /\ pl_map_on k2 (fh:real^3->real^3) /\
    relative_frontier k SUBSET (k:real^3->bool) /\ k SUBSET k2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `k:real^3->bool` RELATIVE_FRONTIER_SUBSET) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    MP_TAC(ISPEC `k2:real^3->bool` INTERIOR_SUBSET) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `u2 = interior k2 DIFF IMAGE (fh:real^3->real^3) (k2 DIFF u)` THEN
  ABBREV_TAC `v2 = IMAGE (fh:real^3->real^3) (v INTER k2)` THEN
  SUBGOAL_THEN `open (u2:real^3->bool) /\ k SUBSET u2 /\ u2 SUBSET interior k2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u2" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_INTERIOR] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k2:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC COMPACT_DIFF THEN ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT]];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(x:real^3) = (gh:real^3->real^3) y` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_polyhedron (v2:real^3->bool) /\
    v2 INTER k SUBSET relative_frontier (f:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v2" THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
      SUBGOAL_THEN `pl_polyhedron (v INTER k2:real^3->bool)` ASSUME_TAC THENL
       [MATCH_MP_TAC PL_POLYHEDRON_INTER THEN
        ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
      EXISTS_TAC `k2:real^3->bool` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN SET_TAC[];
      REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      SUBGOAL_THEN `(x:real^3) IN k` ASSUME_TAC THENL
       [SUBGOAL_THEN `(x:real^3) = (gh:real^3->real^3) y` SUBST1_TAC THENL
         [ASM_MESON_TAC[]; ASM SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^3) IN j` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`2`; `d:real^3->bool`; `j:real^3->bool`]
        MOI_SPU_CELL_POLY) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^3) = (ph:real^3->real^3) x` SUBST1_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  USE_THEN "fp" (MP_TAC o SPECL [`u2:real^3->bool`; `v2:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:real^3->real^3` (X_CHOOSE_THEN
    `g2:real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(MATCH_MP MOI_SCD_PL_HOMEO_UNIV (ASSUME
    `pl_homeomorphism ((:real^3),(:real^3)) (h2:real^3->real^3,g2)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(!x:real^3. ~(x IN u2) ==> g2 x = x) /\
    IMAGE (h2:real^3->real^3) u2 SUBSET u2 /\
    IMAGE (g2:real^3->real^3) u2 SUBSET u2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h2:real^3->real^3`; `g2:real^3->real^3`; `u2:real^3->bool`;
                   `u2:real^3->bool`] MOI_SCD_FIX_OFF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET_REFL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`g2:real^3->real^3`; `h2:real^3->real^3`; `u2:real^3->bool`;
                   `u2:real^3->bool`] MOI_SCD_FIX_OFF) THEN
    ANTS_TAC THENL
     [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
      SIMP_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (k2,k2) (h2:real^3->real^3,g2)` ASSUME_TAC
  THENL
   [MP_TAC(ISPECL [`h2:real^3->real^3`; `g2:real^3->real^3`; `k2:real^3->bool`]
      MOI_SCD_PLH_RESTRICT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^3) IN u2` THENL
       [MP_TAC(ISPEC `k2:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `IMAGE (h2:real^3->real^3) u2 SUBSET u2` THEN
        UNDISCH_TAC `u2 SUBSET interior (k2:real^3->bool)` THEN
        UNDISCH_TAC `(x:real^3) IN u2` THEN SET_TAC[];
        SUBGOAL_THEN `(h2:real^3->real^3) x = x` SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            is_forall(concl th) &&
            can (find_term (fun t -> t = `h2:real^3->real^3`)) (concl th) &&
            is_neg(lhand(snd(dest_forall(concl th)))))) THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]]];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(g2:real^3->real^3) y` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(y:real^3) IN u2` THENL
       [MP_TAC(ISPEC `k2:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `IMAGE (g2:real^3->real^3) u2 SUBSET u2` THEN
        UNDISCH_TAC `u2 SUBSET interior (k2:real^3->bool)` THEN
        UNDISCH_TAC `(y:real^3) IN u2` THEN SET_TAC[];
        SUBGOAL_THEN `(g2:real^3->real^3) y = y` SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            is_forall(concl th) &&
            can (find_term (fun t -> t = `g2:real^3->real^3`)) (concl th) &&
            is_neg(lhand(snd(dest_forall(concl th)))))) THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k2:real^3->bool`;
                 `(gh:real^3->real^3) o ((h2:real^3->real^3) o (fh:real^3->real^3))`;
                 `((gh:real^3->real^3) o (g2:real^3->real^3)) o (fh:real^3->real^3)`]
    MOI_SA2_PLH_EXTEND_ID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `k2:real^3->bool` THEN CONJ_TAC THENL
       [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
        EXISTS_TAC `k2:real^3->bool` THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `~((fh:real^3->real^3) x IN u2)` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^3. if x IN k2
                then ((gh:real^3->real^3) o ((h2:real^3->real^3) o
                      (fh:real^3->real^3))) x
                else x`;
    `\x:real^3. if x IN k2
                then (((gh:real^3->real^3) o (g2:real^3->real^3)) o
                      (fh:real^3->real^3)) x
                else x`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `~((fh:real^3->real^3) x IN u2)` ASSUME_TAC THENL
     [EXPAND_TAC "u2" THEN REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[IN_DIFF];
      ASM_SIMP_TAC[]];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(fh:real^3->real^3) x IN v2` ASSUME_TAC THENL
     [EXPAND_TAC "v2" THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[IN_INTER];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^3->bool) SUBSET k2 /\ j SUBSET d /\
                d SUBSET relative_frontier k`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `d:real^3->bool`; `j:real^3->bool`]
      MOI_SPU_CELL_POLY) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^3. if x IN k2
                      then ((gh:real^3->real^3) o ((h2:real^3->real^3) o
                            (fh:real^3->real^3))) x
                      else x) d =
    IMAGE gh (IMAGE h2 (IMAGE fh d))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN k2` (fun th -> REWRITE_TAC[th; o_THM]) THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (fh:real^3->real^3) d = f` SUBST1_TAC THENL
   [UNDISCH_TAC `IMAGE (ph:real^3->real^3) d = f` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `f:real^3->bool`] MOI_SPU_FACE_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier f SUBSET (f:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; POLYTOPE_IMP_CLOSED;
                  SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `IMAGE (ps:real^3->real^3)
                ((relative_frontier k DIFF f) UNION relative_frontier f)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN relative_frontier k` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN
         (relative_frontier k DIFF f) UNION relative_frontier f` THEN
      UNDISCH_TAC `relative_frontier f SUBSET (f:real^3->bool)` THEN
      UNDISCH_TAC `(f:real^3->bool) SUBSET relative_frontier k` THEN
      SET_TAC[];
      ASM_MESON_TAC[]];
    MATCH_MP_TAC MOI_SPU_IMAGE_SWAP THEN EXISTS_TAC `ph:real^3->real^3` THEN
    ASM_REWRITE_TAC[]]);;

