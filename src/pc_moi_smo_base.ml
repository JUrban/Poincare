(* ========================================================================= *)
(* pc_moi_smo_base (route M): regular charts of the tetrahedra of a finite   *)
(* combinatorial 3-manifold, the tetrahedron charts and the unfolding charts *)
(* over open stars of triangles (a smooth atlas off the 1-skeleton,          *)
(* transition maps affine), and the star charts at vertices.  Main theorem   *)
(* MOI_SMO_BASE : |- !u. MOI_SMO_BASE_STATEMENT u (C3 of pc_moi_smo_defs).   *)
(* This file also loads pc_moi_star.ml (the PL vertex charts                 *)
(* MOI_STA_VERTEX_CHART): C3 implicitly contains the combinatorial facts     *)
(* that every simplex has dimension at most 3 and that every triangle lies   *)
(* in exactly two tetrahedra (otherwise some chart of the two families has a *)
(* non-open image or the triangles are not covered), and these are proved    *)
(* here from the vertex charts by invariance of domain and invariance of     *)
(* dimension.                                                                *)
(* ========================================================================= *)

needs "src/pc_moi_smo_defs.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_real.ml";;
needs "src/pc_moi_star.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Unit regular tetrahedra: Gram computations.  Edge vectors w1 w2 w3    *)
(* from one vertex have unit length and pairwise dot products 1/2.           *)
(* ------------------------------------------------------------------------- *)

let moi_sba_reg = new_definition
 `moi_sba_reg (z1:real^N) z2 z3 z4 <=>
    dist(z1,z2) = &1 /\ dist(z1,z3) = &1 /\ dist(z1,z4) = &1 /\
    dist(z2,z3) = &1 /\ dist(z2,z4) = &1 /\ dist(z3,z4) = &1`;;

let MOI_SBA_DIST1 = prove
 (`!x y:real^N. dist(x,y) = &1 <=> (x - y) dot (x - y) = &1`,
  REWRITE_TAC[dist; NORM_EQ_1]);;

let MOI_SBA_GRAM = prove
 (`!w1 w2 w3:real^N.
     w1 dot w1 = &1 /\ w2 dot w2 = &1 /\ w3 dot w3 = &1 /\
     (w1 - w2) dot (w1 - w2) = &1 /\ (w1 - w3) dot (w1 - w3) = &1 /\
     (w2 - w3) dot (w2 - w3) = &1
     ==> w1 dot w2 = &1 / &2 /\ w1 dot w3 = &1 / &2 /\ w2 dot w3 = &1 / &2`,
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN REAL_ARITH_TAC);;

let MOI_SBA_REG_GRAM = prove
 (`!z1 z2 z3 a:real^N.
     moi_sba_reg z1 z2 z3 a
     ==> (z1 - a) dot (z1 - a) = &1 /\ (z2 - a) dot (z2 - a) = &1 /\
         (z3 - a) dot (z3 - a) = &1 /\
         (z1 - a) dot (z2 - a) = &1 / &2 /\ (z1 - a) dot (z3 - a) = &1 / &2 /\
         (z2 - a) dot (z3 - a) = &1 / &2`,
  REWRITE_TAC[moi_sba_reg; MOI_SBA_DIST1] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SBA_GRAM THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `(x - a) - (y - a):real^N = x - y`]);;

let MOI_SBA_GRAM_INDEP = prove
 (`!w1 w2 w3:real^N c1 c2 c3.
     w1 dot w1 = &1 /\ w2 dot w2 = &1 /\ w3 dot w3 = &1 /\
     w1 dot w2 = &1 / &2 /\ w1 dot w3 = &1 / &2 /\ w2 dot w3 = &1 / &2 /\
     c1 % w1 + c2 % w2 + c3 % w3 = vec 0
     ==> c1 = &0 /\ c2 = &0 /\ c3 = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(c1 % w1 + c2 % w2 + c3 % w3) dot w1 = &0 /\
    (c1 % w1 + c2 % w2 + c3 % w3) dot w2 = &0 /\
    (c1 % w1 + c2 % w2 + c3 % w3) dot (w3:real^N) = &0`
  MP_TAC THENL [ASM_REWRITE_TAC[DOT_LZERO]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DOT_SYM]) THEN
  REWRITE_TAC[DOT_LADD; DOT_LMUL; DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* Orthogonality to the opposite face and the reflected apex, in terms of   *)
(* the edge vectors: with m the centroid offset, -m is orthogonal to every  *)
(* w_j - m, m has squared length 2/3, and 2 m is again an apex.              *)

let MOI_SBA_GRAM_ORTH = prove
 (`!w1 w2 w3:real^N.
     w1 dot w1 = &1 /\ w2 dot w2 = &1 /\ w3 dot w3 = &1 /\
     w1 dot w2 = &1 / &2 /\ w1 dot w3 = &1 / &2 /\ w2 dot w3 = &1 / &2
     ==> (inv(&3) % (w1 + w2 + w3)) dot (w1 - inv(&3) % (w1 + w2 + w3)) = &0 /\
         (inv(&3) % (w1 + w2 + w3)) dot (w2 - inv(&3) % (w1 + w2 + w3)) = &0 /\
         (inv(&3) % (w1 + w2 + w3)) dot (w3 - inv(&3) % (w1 + w2 + w3)) = &0 /\
         (inv(&3) % (w1 + w2 + w3)) dot (inv(&3) % (w1 + w2 + w3)) = &2 / &3 /\
         (w1 - &2 % inv(&3) % (w1 + w2 + w3)) dot
         (w1 - &2 % inv(&3) % (w1 + w2 + w3)) = &1 /\
         (w2 - &2 % inv(&3) % (w1 + w2 + w3)) dot
         (w2 - &2 % inv(&3) % (w1 + w2 + w3)) = &1 /\
         (w3 - &2 % inv(&3) % (w1 + w2 + w3)) dot
         (w3 - &2 % inv(&3) % (w1 + w2 + w3)) = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DOT_SYM]) THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL;
              DOT_SYM] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Three nonzero pairwise orthogonal vectors of real^3 span it, so a vector *)
(* orthogonal to all three is zero.                                          *)

let MOI_SBA_ORTHO3_ZERO = prove
 (`!f1 f2 f3 r:real^3.
     ~(f1 = vec 0) /\ ~(f2 = vec 0) /\ ~(f3 = vec 0) /\
     f1 dot f2 = &0 /\ f1 dot f3 = &0 /\ f2 dot f3 = &0 /\
     r dot f1 = &0 /\ r dot f2 = &0 /\ r dot f3 = &0
     ==> r = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(f1:real^3 = f2) /\ ~(f1 = f3) /\ ~(f2 = f3)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[DOT_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `independent {f1,f2,f3:real^3}` ASSUME_TAC THENL
   [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
    REWRITE_TAC[pairwise; IN_INSERT; NOT_IN_EMPTY; orthogonal] THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[DOT_SYM];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `{f1,f2,f3:real^3}`] CARD_EQ_DIM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET_UNIV; DIM_UNIV; DIMINDEX_3; HAS_SIZE] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET; IN_UNIV; SPAN_3; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real^3`) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real`
    (X_CHOOSE_THEN `w:real` (MP_TAC o AP_TERM `\x:real^3. (r:real^3) dot x`)))) THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; DOT_EQ_0]);;

let MOI_SBA_GRAM_APEX = prove
 (`!w1 w2 w3 d:real^3.
     w1 dot w1 = &1 /\ w2 dot w2 = &1 /\ w3 dot w3 = &1 /\
     w1 dot w2 = &1 / &2 /\ w1 dot w3 = &1 / &2 /\ w2 dot w3 = &1 / &2 /\
     (w1 - d) dot (w1 - d) = &1 /\ (w2 - d) dot (w2 - d) = &1 /\
     (w3 - d) dot (w3 - d) = &1
     ==> d = vec 0 \/ d = &2 % inv(&3) % (w1 + w2 + w3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w1:real^3`; `w2:real^3`; `w3:real^3`] MOI_SBA_GRAM_ORTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `k = &3 / &4 * ((d:real^3) dot d)` THEN
  SUBGOAL_THEN `(d:real^3) - k % inv(&3) % (w1 + w2 + w3) = vec 0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_ORTHO3_ZERO THEN
    MAP_EVERY EXISTS_TAC
     [`w2 - w1:real^3`; `(w3 - w1) - inv(&2) % (w2 - w1):real^3`;
      `inv(&3) % (w1 + w2 + w3):real^3`] THEN
    REWRITE_TAC[GSYM DOT_EQ_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DOT_LSUB; DOT_RSUB; DOT_LADD; DOT_RADD;
                                DOT_LMUL; DOT_RMUL; DOT_SYM]) THEN
    REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL;
                DOT_SYM] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d:real^3 = k % inv(&3) % (w1 + w2 + w3)` ASSUME_TAC THENL
   [UNDISCH_TAC `(d:real^3) - k % inv(&3) % (w1 + w2 + w3) = vec 0` THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^3) dot d = k * k * &2 / &3` ASSUME_TAC THENL
   [UNDISCH_TAC
     `(inv(&3) % (w1 + w2 + w3:real^3)) dot (inv(&3) % (w1 + w2 + w3)) = &2 / &3` THEN
    UNDISCH_TAC `d:real^3 = k % inv(&3) % (w1 + w2 + w3)` THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o BINOP_CONV) [th]) THEN
    REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `k = &0 \/ k = &2` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`&3 / &4 * ((d:real^3) dot d) = k`; `(d:real^3) dot d = k * k * &2 / &3`] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO]);;

(* Point forms.  For a unit regular tetrahedron z1 z2 z3 a: the edge        *)
(* vectors from a are independent, the four points affinely independent,    *)
(* a - c is orthogonal to the face (c its centroid), and the reflected      *)
(* apex (2/3)(z1+z2+z3) - a is again at unit distance from the face; in     *)
(* real^3 these are the only two apexes over the face.                      *)

let MOI_SBA_REG_INDEP = prove
 (`!z1 z2 z3 a:real^N c1 c2 c3.
     moi_sba_reg z1 z2 z3 a /\
     c1 % (z1 - a) + c2 % (z2 - a) + c3 % (z3 - a) = vec 0
     ==> c1 = &0 /\ c2 = &0 /\ c3 = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_SBA_GRAM_INDEP THEN
  MAP_EVERY EXISTS_TAC [`z1 - a:real^N`; `z2 - a:real^N`; `z3 - a:real^N`] THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_SBA_REG_GRAM));;

let MOI_SBA_REG_DISTINCT = prove
 (`!z1 z2 z3 z4:real^N.
     moi_sba_reg z1 z2 z3 z4
     ==> ~(z1 = z2) /\ ~(z1 = z3) /\ ~(z1 = z4) /\
         ~(z2 = z3) /\ ~(z2 = z4) /\ ~(z3 = z4)`,
  REWRITE_TAC[moi_sba_reg] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIST_REFL]) THEN
  RULE_ASSUM_TAC(CONV_RULE REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[]);;

let MOI_SBA_REG_AFFINE_INDEPENDENT = prove
 (`!z1 z2 z3 z4:real^N.
     moi_sba_reg z1 z2 z3 z4 ==> ~affine_dependent {z1,z2,z3,z4}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SBA_REG_DISTINCT) THEN
  SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT_FINITE; FINITE_INSERT; FINITE_EMPTY] THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_ADD_RID; VECTOR_ADD_RID] THEN
  X_GEN_TAC `u:real^N->real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`z1:real^N`; `z2:real^N`; `z3:real^N`; `z4:real^N`;
                 `(u:real^N->real) z1`; `(u:real^N->real) z2`;
                 `(u:real^N->real) z3`] MOI_SBA_REG_INDEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(u:real^N->real) z4 = --(u z1 + u z2 + u z3)` ASSUME_TAC
    THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC
     `(u:real^N->real) z1 % z1 + u z2 % z2 + u z3 % z3 + u z4 % z4 = vec 0` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^N->real) z4 = &0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_SBA_REG_ORTH = prove
 (`!z1 z2 z3 a:real^N.
     moi_sba_reg z1 z2 z3 a
     ==> (a - inv(&3) % (z1 + z2 + z3)) dot (z1 - inv(&3) % (z1 + z2 + z3)) = &0 /\
         (a - inv(&3) % (z1 + z2 + z3)) dot (z2 - inv(&3) % (z1 + z2 + z3)) = &0 /\
         (a - inv(&3) % (z1 + z2 + z3)) dot (z3 - inv(&3) % (z1 + z2 + z3)) = &0 /\
         (a - inv(&3) % (z1 + z2 + z3)) dot (a - inv(&3) % (z1 + z2 + z3)) =
         &2 / &3 /\
         (a - inv(&3) % (z1 + z2 + z3)) dot
         ((&2 / &3 % (z1 + z2 + z3) - a) - inv(&3) % (z1 + z2 + z3)) =
         --(&2 / &3) /\
         moi_sba_reg z1 z2 z3 (&2 / &3 % (z1 + z2 + z3) - a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SBA_REG_GRAM) THEN
  MP_TAC(ISPECL [`z1 - a:real^N`; `z2 - a:real^N`; `z3 - a:real^N`]
                MOI_SBA_GRAM_ORTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_sba_reg (z1:real^N) z2 z3 a` THEN
  REWRITE_TAC[moi_sba_reg] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_SBA_DIST1] THEN
  MAP_EVERY (fun t -> SUBST1_TAC(VECTOR_ARITH t))
   [`a - inv(&3) % (z1 + z2 + z3):real^N =
     --(inv(&3) % ((z1 - a) + (z2 - a) + (z3 - a)))`;
    `(&2 / &3 % (z1 + z2 + z3) - a) - inv(&3) % (z1 + z2 + z3):real^N =
     inv(&3) % ((z1 - a) + (z2 - a) + (z3 - a))`;
    `z1 - inv(&3) % (z1 + z2 + z3):real^N =
     (z1 - a) - inv(&3) % ((z1 - a) + (z2 - a) + (z3 - a))`;
    `z2 - inv(&3) % (z1 + z2 + z3):real^N =
     (z2 - a) - inv(&3) % ((z1 - a) + (z2 - a) + (z3 - a))`;
    `z3 - inv(&3) % (z1 + z2 + z3):real^N =
     (z3 - a) - inv(&3) % ((z1 - a) + (z2 - a) + (z3 - a))`;
    `z1 - (&2 / &3 % (z1 + z2 + z3) - a):real^N =
     (z1 - a) - &2 % inv(&3) % ((z1 - a) + (z2 - a) + (z3 - a))`;
    `z2 - (&2 / &3 % (z1 + z2 + z3) - a):real^N =
     (z2 - a) - &2 % inv(&3) % ((z1 - a) + (z2 - a) + (z3 - a))`;
    `z3 - (&2 / &3 % (z1 + z2 + z3) - a):real^N =
     (z3 - a) - &2 % inv(&3) % ((z1 - a) + (z2 - a) + (z3 - a))`] THEN
  ASM_REWRITE_TAC[DOT_LNEG; DOT_RNEG; REAL_NEG_0; REAL_NEG_NEG]);;

let MOI_SBA_REG_APEX = prove
 (`!z1 z2 z3 a b:real^3.
     moi_sba_reg z1 z2 z3 a /\
     dist(z1,b) = &1 /\ dist(z2,b) = &1 /\ dist(z3,b) = &1
     ==> b = a \/ b = &2 / &3 % (z1 + z2 + z3) - a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SBA_REG_GRAM) THEN
  MP_TAC(ISPECL [`z1 - a:real^3`; `z2 - a:real^3`; `z3 - a:real^3`;
                 `b - a:real^3`] MOI_SBA_GRAM_APEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ARITH `(z - a) - (b - a):real^3 = z - b`] THEN
    ASM_REWRITE_TAC[GSYM MOI_SBA_DIST1];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p ==> p') /\ (q ==> q') ==> p \/ q ==> p' \/ q'`) THEN
  CONJ_TAC THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 2. Explicit relative interiors of small simplices, affine evaluation of  *)
(* convex combinations.                                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_RELINT_4 = prove
 (`!p1 p2 p3 p4 x:real^N.
     ~(p1 = p2) /\ ~(p1 = p3) /\ ~(p1 = p4) /\ ~(p2 = p3) /\ ~(p2 = p4) /\
     ~(p3 = p4) /\ ~affine_dependent {p1,p2,p3,p4}
     ==> (x IN relative_interior(convex hull {p1,p2,p3,p4}) <=>
          ?u1 u2 u3 u4. &0 < u1 /\ &0 < u2 /\ &0 < u3 /\ &0 < u4 /\
                        u1 + u2 + u3 + u4 = &1 /\
                        x = u1 % p1 + u2 % p2 + u3 % p3 + u4 % p4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `{p1,p2,p3,p4}:real^N->bool`
    RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; FORALL_IN_INSERT] THEN
  REWRITE_TAC[REAL_ADD_RID; VECTOR_ADD_RID] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`(u:real^N->real) p1`; `(u:real^N->real) p2`; `(u:real^N->real) p3`;
      `(u:real^N->real) p4`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
     (X_CHOOSE_THEN `u3:real` (X_CHOOSE_THEN `u4:real` STRIP_ASSUME_TAC)))) THEN
    EXISTS_TAC `\y:real^N. if y = p1 then u1:real else if y = p2 then u2
                           else if y = p3 then u3 else u4` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SBA_RELINT_3 = prove
 (`!p1 p2 p3 x:real^N.
     ~(p1 = p2) /\ ~(p1 = p3) /\ ~(p2 = p3) /\ ~affine_dependent {p1,p2,p3}
     ==> (x IN relative_interior(convex hull {p1,p2,p3}) <=>
          ?u1 u2 u3. &0 < u1 /\ &0 < u2 /\ &0 < u3 /\
                     u1 + u2 + u3 = &1 /\
                     x = u1 % p1 + u2 % p2 + u3 % p3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `{p1,p2,p3}:real^N->bool`
    RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; FORALL_IN_INSERT] THEN
  REWRITE_TAC[REAL_ADD_RID; VECTOR_ADD_RID] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`(u:real^N->real) p1`; `(u:real^N->real) p2`; `(u:real^N->real) p3`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
     (X_CHOOSE_THEN `u3:real` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `\y:real^N. if y = p1 then u1:real else if y = p2 then u2 else u3` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SBA_AFFINE_COMB4 = prove
 (`!(l:real^M->real^N) y u1 u2 u3 u4 p1 p2 p3 p4.
     linear l /\ u1 + u2 + u3 + u4 = &1
     ==> l(u1 % p1 + u2 % p2 + u3 % p3 + u4 % p4) + y =
         u1 % (l p1 + y) + u2 % (l p2 + y) + u3 % (l p3 + y) +
         u4 % (l p4 + y)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
  SUBGOAL_THEN `u4 = &1 - u1 - u2 - u3` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let MOI_SBA_AFFINE_COMB3 = prove
 (`!(l:real^M->real^N) y u1 u2 u3 p1 p2 p3.
     linear l /\ u1 + u2 + u3 = &1
     ==> l(u1 % p1 + u2 % p2 + u3 % p3) + y =
         u1 % (l p1 + y) + u2 % (l p2 + y) + u3 % (l p3 + y)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
  SUBGOAL_THEN `u3 = &1 - u1 - u2` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let MOI_SBA_DOT_COMB4 = prove
 (`!(n:real^N) c u1 u2 u3 u4 y1 y2 y3 y4.
     u1 + u2 + u3 + u4 = &1
     ==> n dot ((u1 % y1 + u2 % y2 + u3 % y3 + u4 % y4) - c) =
         u1 * (n dot (y1 - c)) + u2 * (n dot (y2 - c)) +
         u3 * (n dot (y3 - c)) + u4 * (n dot (y4 - c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(u1 % y1 + u2 % y2 + u3 % y3 + u4 % y4) - c:real^N =
    u1 % (y1 - c) + u2 % (y2 - c) + u3 % (y3 - c) + u4 % (y4 - c)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `u4 = &1 - u1 - u2 - u3` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    REWRITE_TAC[DOT_RADD; DOT_RMUL]]);;

let MOI_SBA_DOT_COMB3 = prove
 (`!(n:real^N) c u1 u2 u3 y1 y2 y3.
     u1 + u2 + u3 = &1
     ==> n dot ((u1 % y1 + u2 % y2 + u3 % y3) - c) =
         u1 * (n dot (y1 - c)) + u2 * (n dot (y2 - c)) +
         u3 * (n dot (y3 - c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(u1 % y1 + u2 % y2 + u3 % y3) - c:real^N =
    u1 % (y1 - c) + u2 % (y2 - c) + u3 % (y3 - c)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `u3 = &1 - u1 - u2` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    REWRITE_TAC[DOT_RADD; DOT_RMUL]]);;

(* ------------------------------------------------------------------------- *)
(* 3. Affine maps: continuity and smoothness.                                *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_AFFINE_CONTINUOUS_ON = prove
 (`!(A:real^M->real^N) s.
     (?l y. linear l /\ !x. A x = l x + y) ==> A continuous_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(A:real^M->real^N) = \x. l x + y` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST; ETA_AX]);;

let MOI_SBA_AFFINE_SMOOTH = prove
 (`!(g:real^M->real^N) s.
     (?l y. linear l /\ !x. g x = l x + y) ==> smooth_map_on s g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN
  SUBGOAL_THEN `(g:real^M->real^N) = \x. l x + (\x:real^M. y) x`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; MOI_SMB_SMOOTH_LINEAR]);;

let MOI_SBA_AFFINE_COMPOSE = prove
 (`!(f:real^M->real^N) (g:real^N->real^P).
     (?l y. linear l /\ !x. f x = l x + y) /\
     (?l y. linear l /\ !x. g x = l x + y)
     ==> ?l y. linear l /\ !x. g(f x) = l x + y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `l1:real^M->real^N` (X_CHOOSE_THEN `y1:real^N`
      STRIP_ASSUME_TAC))
   (X_CHOOSE_THEN `l2:real^N->real^P` (X_CHOOSE_THEN `y2:real^P`
      STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`(l2:real^N->real^P) o (l1:real^M->real^N)`;
    `(l2:real^N->real^P) y1 + y2`] THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE; o_THM; LINEAR_ADD] THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 4. Regular maps of a tetrahedron with listed vertices: characterization, *)
(* existence (with a chosen vertex sent to 0), affine left inverse.          *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_STD_REG = prove
 (`moi_sba_reg (inv(sqrt(&2)) % vector[&1;&0;&0]:real^3)
               (inv(sqrt(&2)) % vector[&0;&1;&0])
               (inv(sqrt(&2)) % vector[&0;&0;&1])
               (inv(sqrt(&2)) % vector[&1;&1;&1])`,
  SUBGOAL_THEN `abs(inv(sqrt(&2))) * sqrt(&2) = &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_sba_reg; dist; GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
  REWRITE_TAC[vector_norm; DOT_3; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let MOI_SBA_REG_TRANSLATE = prove
 (`!z1 z2 z3 z4 a:real^N.
     moi_sba_reg z1 z2 z3 z4
     ==> moi_sba_reg (z1 - a) (z2 - a) (z3 - a) (z4 - a)`,
  REWRITE_TAC[moi_sba_reg; NORM_ARITH `dist(x - a:real^N,y - a) = dist(x,y)`]);;

let MOI_SBA_REGMAP_4 = prove
 (`!p1 p2 p3 p4:real^N A:real^N->real^3.
     ~(p1 = p2) /\ ~(p1 = p3) /\ ~(p1 = p4) /\ ~(p2 = p3) /\ ~(p2 = p4) /\
     ~(p3 = p4) /\ ~affine_dependent {p1,p2,p3,p4}
     ==> (moi_smo_regmap (convex hull {p1,p2,p3,p4}) A <=>
          (?l y. linear l /\ !x. A x = l x + y) /\
          moi_sba_reg (A p1) (A p2) (A p3) (A p4))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_smo_regmap] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC
    [MATCH_MP EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT th]) THEN
  REWRITE_TAC[moi_sba_reg; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[DIST_SYM] THEN CONV_TAC TAUT);;

let MOI_SBA_REGMAP_EXISTS = prove
 (`!p1 p2 p3 p4:real^N.
     ~(p1 = p2) /\ ~(p1 = p3) /\ ~(p1 = p4) /\ ~(p2 = p3) /\ ~(p2 = p4) /\
     ~(p3 = p4) /\ ~affine_dependent {p1,p2,p3,p4}
     ==> ?A:real^N->real^3.
            moi_smo_regmap (convex hull {p1,p2,p3,p4}) A /\ A p1 = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `w1 = inv(sqrt(&2)) % vector[&1;&0;&0]:real^3` THEN
  ABBREV_TAC `w2 = inv(sqrt(&2)) % vector[&0;&1;&0]:real^3` THEN
  ABBREV_TAC `w3 = inv(sqrt(&2)) % vector[&0;&0;&1]:real^3` THEN
  ABBREV_TAC `w4 = inv(sqrt(&2)) % vector[&1;&1;&1]:real^3` THEN
  SUBGOAL_THEN `moi_sba_reg (w1 - w1) (w2 - w1) (w3 - w1) (w4 - w1:real^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_REG_TRANSLATE THEN
    MAP_EVERY EXPAND_TAC ["w1"; "w2"; "w3"; "w4"] THEN
    REWRITE_TAC[MOI_SBA_STD_REG];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{p1,p2,p3,p4}:real^N->bool`;
    `\x:real^N. if x = p1 then w1 - w1 else if x = p2 then w2 - w1
                else if x = p3 then w3 - w1 else w4 - w1:real^3`]
   MOI_REAL_AFFINE_EXTEND_POINTS) THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\x:real^N. (l:real^N->real^3) x + y` THEN
  ASM_SIMP_TAC[MOI_SBA_REGMAP_4] THEN
  REWRITE_TAC[VECTOR_SUB_REFL] THEN
  MAP_EVERY EXISTS_TAC [`l:real^N->real^3`; `y:real^3`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_SBA_REGMAP_INV = prove
 (`!p1 p2 p3 p4:real^N A:real^N->real^3.
     ~(p1 = p2) /\ ~(p1 = p3) /\ ~(p1 = p4) /\ ~(p2 = p3) /\ ~(p2 = p4) /\
     ~(p3 = p4) /\ ~affine_dependent {p1,p2,p3,p4} /\
     moi_smo_regmap (convex hull {p1,p2,p3,p4}) A
     ==> ?B:real^3->real^N.
            (?l y. linear l /\ !x. B x = l x + y) /\
            !x. x IN affine hull {p1,p2,p3,p4} ==> B(A x) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_smo_regmap (convex hull {p1,p2,p3,p4:real^N}) A` THEN
  ASM_SIMP_TAC[MOI_SBA_REGMAP_4] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `la:real^N->real^3` (X_CHOOSE_THEN `ya:real^3`
     STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SBA_REG_DISTINCT) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SBA_REG_AFFINE_INDEPENDENT) THEN
  MP_TAC(ISPECL
   [`{(A:real^N->real^3) p1,A p2,A p3,A p4}`;
    `\z:real^3. if z = (A:real^N->real^3) p1 then p1 else if z = A p2 then p2
                else if z = A p3 then p3 else p4:real^N`]
   MOI_REAL_AFFINE_EXTEND_POINTS) THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `lb:real^3->real^N` (X_CHOOSE_THEN `yb:real^N`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\z:real^3. (lb:real^3->real^N) z + yb` THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`lb:real^3->real^N`; `yb:real^N`] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(lb:real^3->real^N) o (la:real^N->real^3)`; `\x:real^N. x`;
    `(lb:real^3->real^N) ya + yb`; `vec 0:real^N`; `{p1,p2,p3,p4:real^N}`]
   MOI_REAL_AFFINE_EQ_ON_AFFINE_HULL) THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE; LINEAR_ID; o_THM; VECTOR_ADD_RID] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    ASM_SIMP_TAC[LINEAR_ADD] THEN VECTOR_ARITH_TAC;
    ASM_SIMP_TAC[LINEAR_ADD; VECTOR_ADD_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* 5. Finite sets of three and four elements.                                *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_SET4_FROM = prove
 (`!V (v:A). FINITE V /\ CARD V = 4 /\ v IN V
             ==> ?a b d. ~(v = a) /\ ~(v = b) /\ ~(v = d) /\ ~(a = b) /\
                         ~(a = d) /\ ~(b = d) /\ V = {v,a,b,d}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(V DELETE (v:A)) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A`
    (X_CHOOSE_THEN `d:A` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `b:A`; `d:A`] THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let MOI_SBA_SET3_FROM = prove
 (`!V (v:A). FINITE V /\ CARD V = 3 /\ v IN V
             ==> ?a b. ~(v = a) /\ ~(v = b) /\ ~(a = b) /\ V = {v,a,b}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(V DELETE (v:A)) HAS_SIZE 2` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let MOI_SBA_SET4_EXTEND = prove
 (`!V (a:A) b d.
     FINITE V /\ CARD V = 4 /\ a IN V /\ b IN V /\ d IN V /\
     ~(a = b) /\ ~(a = d) /\ ~(b = d)
     ==> ?p. ~(p = a) /\ ~(p = b) /\ ~(p = d) /\ V = {a,b,d,p}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(V DIFF {a:A,b,d}) HAS_SIZE 1` MP_TAC THENL
   [SUBGOAL_THEN `CARD {a:A,b,d} = 3` ASSUME_TAC THENL
     [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_DIFF; CARD_DIFF; INSERT_SUBSET;
                 EMPTY_SUBSET] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A` ASSUME_TAC) THEN
  EXISTS_TAC `p:A` THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 6. Vertices of tetrahedra and triangles.                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_TET_VERTS = prove
 (`!tet v:real^N.
     &3 simplex tet /\ v extreme_point_of tet
     ==> ?q2 q3 q4. ~(v = q2) /\ ~(v = q3) /\ ~(v = q4) /\ ~(q2 = q3) /\
                    ~(q2 = q4) /\ ~(q3 = q4) /\
                    ~affine_dependent {v,q2,q3,q4} /\
                    tet = convex hull {v,q2,q3,q4}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SIMPLEX_EXTREME_POINTS) THEN
  MP_TAC(ISPECL [`{x:real^N | x extreme_point_of tet}`; `v:real^N`]
    MOI_SBA_SET4_FROM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `&(CARD {x:real^N | x extreme_point_of tet}):int = &3 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `q3:real^N`
    (X_CHOOSE_THEN `q4:real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`q2:real^N`; `q3:real^N`; `q4:real^N`] THEN
  ASM_MESON_TAC[]);;

let MOI_SBA_TRI_VERTS = prove
 (`!t v:real^N.
     &2 simplex t /\ v extreme_point_of t
     ==> ?q2 q3. ~(v = q2) /\ ~(v = q3) /\ ~(q2 = q3) /\
                 ~affine_dependent {v,q2,q3} /\ t = convex hull {v,q2,q3}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SIMPLEX_EXTREME_POINTS) THEN
  MP_TAC(ISPECL [`{x:real^N | x extreme_point_of t}`; `v:real^N`]
    MOI_SBA_SET3_FROM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `&(CARD {x:real^N | x extreme_point_of t}):int = &2 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `q3:real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`q2:real^N`; `q3:real^N`] THEN
  ASM_MESON_TAC[]);;

let MOI_SBA_TET_OVER_TRI = prove
 (`!tet v q2 q3:real^N.
     &3 simplex tet /\ (convex hull {v,q2,q3}) face_of tet /\
     ~(v = q2) /\ ~(v = q3) /\ ~(q2 = q3) /\ ~affine_dependent {v,q2,q3}
     ==> ?p. ~(p = v) /\ ~(p = q2) /\ ~(p = q3) /\
             ~affine_dependent {v,q2,q3,p} /\ tet = convex hull {v,q2,q3,p}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SIMPLEX_EXTREME_POINTS) THEN
  SUBGOAL_THEN
   `!x:real^N. x IN {v,q2,q3} ==> x extreme_point_of tet`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`convex hull {v,q2,q3}:real^N->bool`; `tet:real^N->bool`;
                   `x:real^N`] EXTREME_POINT_OF_FACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^N | x extreme_point_of tet}`; `v:real^N`;
                 `q2:real^N`; `q3:real^N`] MOI_SBA_SET4_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&(CARD {x:real^N | x extreme_point_of tet}):int = &3 + &1` THEN
      REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT];
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT];
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p:real^N` THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 7. Carriers and open stars in a (locally finite) simplicial complex.     *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_LF_SIMPLEX = prove
 (`!c s:real^N->bool.
     lf_simplicial_complex c /\ s IN c ==> aff_dim s simplex s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o
              GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` ASSUME_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN ASM_REWRITE_TAC[]);;

let MOI_SBA_LF_CONVEX = prove
 (`!c s:real^N->bool.
     lf_simplicial_complex c /\ s IN c ==> convex s /\ closed s`,
  MESON_TAC[MOI_SBA_LF_SIMPLEX; SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED]);;

let MOI_SBA_CARRIER = prove
 (`!c x:real^N.
     lf_simplicial_complex c /\ x IN UNIONS c
     ==> ?r. r IN c /\ x IN relative_interior r`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_SBA_LF_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[lf_simplicial_complex]);;

let MOI_SBA_RELINT_MEETS = prove
 (`!c r s:real^N->bool.
     lf_simplicial_complex c /\ r IN c /\ s IN c /\
     ~(relative_interior r INTER s = {})
     ==> r face_of s /\ r SUBSET s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  SUBGOAL_THEN `(r INTER s) face_of (r:real^N->bool) /\ (r INTER s) face_of s`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) INTER s = r` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(r:real^N->bool) INTER s`; `r:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]]);;

let MOI_SBA_RELINT_EQ = prove
 (`!c r s:real^N->bool.
     lf_simplicial_complex c /\ r IN c /\ s IN c /\
     ~(relative_interior r INTER relative_interior s = {})
     ==> r = s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`; `s:real^N->bool`]
      MOI_SBA_RELINT_MEETS);
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `r:real^N->bool`]
      MOI_SBA_RELINT_MEETS)] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  ASM SET_TAC[]);;

let MOI_SBA_RELINT_DISJ_EQDIM = prove
 (`!c r s:real^N->bool.
     lf_simplicial_complex c /\ r IN c /\ s IN c /\ aff_dim r = aff_dim s /\
     ~(r = s)
     ==> relative_interior r INTER s = {}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`; `s:real^N->bool`]
    MOI_SBA_RELINT_MEETS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:real^N->bool`; `s:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ASM_MESON_TAC[MOI_SBA_LF_CONVEX; INT_LT_REFL]);;

let MOI_SBA_RELINT_DISJ_LOWDIM = prove
 (`!c r s:real^N->bool.
     lf_simplicial_complex c /\ r IN c /\ s IN c /\ aff_dim s < aff_dim r
     ==> relative_interior r INTER s = {}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`; `s:real^N->bool`]
    MOI_SBA_RELINT_MEETS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:real^N->bool`; `s:real^N->bool`] AFF_DIM_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MOI_SBA_OPEN_STAR_ALT = prove
 (`!c s:real^N->bool.
     lf_simplicial_complex c /\ s IN c
     ==> moi_smo_open_star c s =
         {x | x IN UNIONS c /\ !r. r IN c /\ x IN r ==> s SUBSET r}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_smo_open_star; UNIONS_GSPEC; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`;
                     `r:real^N->bool`] MOI_SBA_RELINT_MEETS) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_SBA_CARRIER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) = s INTER r` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[lf_simplicial_complex]]);;

let MOI_SBA_OPEN_STAR_OPEN = prove
 (`!c s:real^N->bool.
     FINITE c /\ lf_simplicial_complex c /\ s IN c
     ==> open_in (subtopology euclidean (UNIONS c)) (moi_smo_open_star c s)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_SBA_OPEN_STAR_ALT] THEN
  SUBGOAL_THEN
   `{x | x IN UNIONS c /\ !r. r IN c /\ x IN r ==> (s:real^N->bool) SUBSET r} =
    UNIONS c INTER ((:real^N) DIFF UNIONS {r | r IN c /\ ~(s SUBSET r)})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_DIFF; IN_UNIV;
                IN_UNIONS] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[GSYM closed] THEN
  MATCH_MP_TAC CLOSED_UNIONS THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
  ASM_MESON_TAC[MOI_SBA_LF_CONVEX]);;

let MOI_SBA_OPEN_STAR_MONO = prove
 (`!c s s':real^N->bool.
     lf_simplicial_complex c /\ s IN c /\ s' IN c /\ s SUBSET s'
     ==> moi_smo_open_star c s' SUBSET moi_smo_open_star c s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_SBA_OPEN_STAR_ALT] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
  TRANS_TAC SUBSET_TRANS `s':real^N->bool` THEN ASM_SIMP_TAC[]);;

let MOI_SBA_OPEN_STAR_VERTEX = prove
 (`!c v:real^N.
     lf_simplicial_complex c /\ {v} IN c
     ==> moi_smo_open_star c {v} = moi_sta_open_star c v`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_SBA_OPEN_STAR_ALT] THEN
  REWRITE_TAC[moi_sta_open_star; SING_SUBSET]);;

let MOI_SBA_RELINT_IN_STAR = prove
 (`!c s:real^N->bool.
     lf_simplicial_complex c /\ s IN c
     ==> relative_interior s SUBSET moi_smo_open_star c s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_smo_open_star] THEN
  MATCH_MP_TAC(SET_RULE
    `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_MESON_TAC[FACE_OF_REFL; MOI_SBA_LF_CONVEX]);;

let MOI_SBA_STAR_SUBSET_UNIONS = prove
 (`!c s:real^N->bool.
     lf_simplicial_complex c /\ s IN c
     ==> moi_smo_open_star c s SUBSET UNIONS c`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_SBA_OPEN_STAR_ALT] THEN SET_TAC[]);;

let MOI_SBA_STAR_IN_XP = prove
 (`!c s:real^N->bool.
     lf_simplicial_complex c /\ s IN c /\ &2 <= aff_dim s
     ==> moi_smo_open_star c s SUBSET
         (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_DIFF] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_STAR_SUBSET_UNIONS; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN moi_smo_open_star c s` THEN
  REWRITE_TAC[moi_smo_open_star; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `e:real^N->bool`]
    MOI_SBA_RELINT_DISJ_LOWDIM) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] AFF_DIM_SUBSET) THEN
    ASM_SIMP_TAC[FACE_OF_IMP_SUBSET] THEN ASM_ARITH_TAC;
    ASM SET_TAC[]]);;

let MOI_SBA_VERTEX_IN = prove
 (`!c s v:real^N.
     lf_simplicial_complex c /\ s IN c /\ v extreme_point_of s ==> {v} IN c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o
              GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING]);;

let MOI_SBA_OPEN_STAR_TET = prove
 (`!c tet:real^N->bool.
     lf_simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &3) /\
     tet IN c /\ aff_dim tet = &3
     ==> moi_smo_open_star c tet = relative_interior tet`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_smo_open_star; UNIONS_GSPEC; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `r:real^N->bool = tet` (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `aff_dim(tet:real^N->bool) < aff_dim(r:real^N->bool)`
    MP_TAC THENL
     [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_MESON_TAC[MOI_SBA_LF_CONVEX];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(r:real^N->bool) <= &3` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `tet:real^N->bool` THEN
    ASM_MESON_TAC[FACE_OF_REFL; MOI_SBA_LF_CONVEX]]);;

let MOI_SBA_OPEN_STAR_TRI = prove
 (`!c t:real^N->bool.
     lf_simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &3) /\
     t IN c /\ aff_dim t = &2
     ==> !x. x IN moi_smo_open_star c t <=>
             x IN relative_interior t \/
             ?tet. tet IN c /\ aff_dim tet = &3 /\ t SUBSET tet /\
                   x IN relative_interior tet`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_smo_open_star; UNIONS_GSPEC; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `r:real^N->bool = t` THENL
     [ASM_MESON_TAC[]; DISJ2_TAC] THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `aff_dim(t:real^N->bool) < aff_dim(r:real^N->bool)`
      MP_TAC THENL
       [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
        ASM_MESON_TAC[MOI_SBA_LF_CONVEX];
        ALL_TAC] THEN
      SUBGOAL_THEN `aff_dim(r:real^N->bool) <= &3` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
    STRIP_TAC THENL
     [EXISTS_TAC `t:real^N->bool` THEN
      ASM_MESON_TAC[FACE_OF_REFL; MOI_SBA_LF_CONVEX];
      EXISTS_TAC `tet:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(t:real^N->bool) = t INTER tet` SUBST1_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[lf_simplicial_complex]]]]);;

(* ------------------------------------------------------------------------- *)
(* 8. The PL vertex charts (pc_moi_star) and invariance of domain: an       *)
(* injective continuous map on a subset of a vertex star that is open in    *)
(* the polyhedron is a homeomorphism onto an open subset of real^3, and     *)
(* conversely the image of an open subset of real^3 under an injective      *)
(* continuous map into a vertex star is open in the polyhedron.             *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_VCHART = prove
 (`!c v:real^N.
     combinatorial_manifold 3 c /\ {v} IN c
     ==> ?p:real^N->real^3 q.
           open (IMAGE p (moi_smo_open_star c {v})) /\
           homeomorphism (moi_smo_open_star c {v},
                          IMAGE p (moi_smo_open_star c {v})) (p,q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SBA_OPEN_STAR_VERTEX] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_VERTEX_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p:real^N->real^3` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `homeomorphic_map
      (subtopology euclidean (moi_sta_open_star c (v:real^N)),
       subtopology euclidean (IMAGE (p:real^N->real^3) (moi_sta_open_star c v)))
      p` THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY] THEN
  MESON_TAC[]);;

let MOI_SBA_IOD_FWD = prove
 (`!c v W (h:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     W SUBSET moi_smo_open_star c {v} /\
     open_in (subtopology euclidean (UNIONS c)) W /\
     h continuous_on W /\
     (!x y. x IN W /\ y IN W /\ h x = h y ==> x = y)
     ==> open (IMAGE h W) /\ ?h'. homeomorphism (W,IMAGE h W) (h,h')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SBA_VCHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^3` (X_CHOOSE_THEN `q:real^3->real^N`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `ov = moi_smo_open_star c {v:real^N}` THEN
  SUBGOAL_THEN `ov SUBSET UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ov" THEN ASM_MESON_TAC[MOI_SBA_STAR_SUBSET_UNIONS]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean ov) (W:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS c:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (p:real^N->real^3) W)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `IMAGE (p:real^N->real^3) ov` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`q:real^3->real^N`; `ov:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (W,IMAGE (p:real^N->real^3) W) (p,q)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`ov:real^N->bool`; `IMAGE (p:real^N->real^3) ov`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[homeomorphism]
   (ASSUME `homeomorphism (W,IMAGE (p:real^N->real^3) W) (p,q)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `((h:real^N->real^3) o (q:real^3->real^N)) continuous_on
    IMAGE (p:real^N->real^3) W /\
    IMAGE (h o q) (IMAGE p W) = IMAGE h W /\
    (!x y. x IN IMAGE p W /\ y IN IMAGE p W /\ (h o q) x = (h o q) y
           ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[o_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME
     `IMAGE ((h:real^N->real^3) o (q:real^3->real^N)) (IMAGE p W) =
      IMAGE h W`)) THEN
    MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(h:real^N->real^3) o (q:real^3->real^N)`;
                 `IMAGE (p:real^N->real^3) W`]
    INVARIANCE_OF_DOMAIN_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` ASSUME_TAC) THEN
  EXISTS_TAC `(q:real^3->real^N) o (g:real^3->real^3)` THEN
  MATCH_MP_TAC HOMEOMORPHISM_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`((h:real^N->real^3) o (q:real^3->real^N)) o (p:real^N->real^3)`;
    `(q:real^3->real^N) o (g:real^3->real^3)`] THEN
  REPEAT CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME
     `IMAGE ((h:real^N->real^3) o (q:real^3->real^N)) (IMAGE p W) =
      IMAGE h W`)) THEN
    MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (p:real^N->real^3) W` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[o_THM];
    REWRITE_TAC[]]);;

let MOI_SBA_IOD_REV = prove
 (`!c v (L:real^3->bool) (xi:real^3->real^N).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     open L /\ xi continuous_on L /\
     (!x y. x IN L /\ y IN L /\ xi x = xi y ==> x = y) /\
     IMAGE xi L SUBSET moi_smo_open_star c {v}
     ==> open_in (subtopology euclidean (UNIONS c)) (IMAGE xi L)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SBA_VCHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^3` (X_CHOOSE_THEN `q:real^3->real^N`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `ov = moi_smo_open_star c {v:real^N}` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `open (IMAGE ((p:real^N->real^3) o (xi:real^3->real^N)) L)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[o_THM] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; FUN_IN_IMAGE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (xi:real^3->real^N) L =
    {x | x IN ov /\ (p:real^N->real^3) x IN IMAGE (p o xi) L}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IMAGE_o] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(x:real^N) = y` (fun th -> ASM_MESON_TAC[th]) THEN
      ASM_MESON_TAC[SUBSET; IN_IMAGE]];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `ov:real^N->bool` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[];
    SUBST1_TAC(SYM(ASSUME `moi_smo_open_star c {v:real^N} = ov`)) THEN
    MATCH_MP_TAC MOI_SBA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 9. Every simplex of a combinatorial 3-manifold has dimension at most 3  *)
(* (topological dimension of an open vertex star), and every triangle lies *)
(* in some tetrahedron.                                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_EXTREME_EXISTS = prove
 (`!c s:real^N->bool.
     lf_simplicial_complex c /\ s IN c /\ ~(s = {})
     ==> ?v. v extreme_point_of s /\ {v} IN c /\ v IN s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_LF_CONVEX; MOI_SBA_LF_SIMPLEX; SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_SBA_VERTEX_IN]; ASM_MESON_TAC[extreme_point_of]]);;

let MOI_SBA_DIM_STAR = prove
 (`!c v:real^N.
     combinatorial_manifold 3 c /\ {v} IN c
     ==> dimension (moi_smo_open_star c {v}) <= &3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SBA_VCHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^3` (X_CHOOSE_THEN `q:real^3->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `dimension (moi_smo_open_star c {v:real^N}) =
    dimension (IMAGE (p:real^N->real^3) (moi_smo_open_star c {v}))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_DIMENSION THEN REWRITE_TAC[homeomorphic] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  TRANS_TAC INT_LE_TRANS
   `aff_dim (IMAGE (p:real^N->real^3) (moi_smo_open_star c {v:real^N}))` THEN
  REWRITE_TAC[DIMENSION_LE_AFF_DIM] THEN
  MP_TAC(ISPEC `IMAGE (p:real^N->real^3) (moi_smo_open_star c {v:real^N})`
    AFF_DIM_LE_UNIV) THEN
  REWRITE_TAC[DIMINDEX_3]);;

let MOI_SBA_DIM_LE3 = prove
 (`!c s:real^N->bool.
     combinatorial_manifold 3 c /\ s IN c ==> aff_dim s <= &3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_SBA_EXTREME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `relative_interior s SUBSET moi_smo_open_star c {v:real^N}`
  ASSUME_TAC THENL
   [TRANS_TAC SUBSET_TRANS `moi_smo_open_star c (s:real^N->bool)` THEN
    ASM_SIMP_TAC[MOI_SBA_RELINT_IN_STAR] THEN
    MATCH_MP_TAC MOI_SBA_OPEN_STAR_MONO THEN ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = dimension(relative_interior s)`
  SUBST1_TAC THENL
   [ASM_MESON_TAC[DIMENSION_EQ_AFF_DIM; CONVEX_RELATIVE_INTERIOR;
                  AFF_DIM_RELATIVE_INTERIOR; MOI_SBA_LF_CONVEX];
    ALL_TAC] THEN
  TRANS_TAC INT_LE_TRANS `dimension (moi_smo_open_star c {v:real^N})` THEN
  ASM_SIMP_TAC[DIMENSION_SUBSET; MOI_SBA_DIM_STAR]);;

(* ------------------------------------------------------------------------- *)
(* 10. Vertex description of a triangle and of the tetrahedra over it.     *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_LF_SUBSET_FACE = prove
 (`!c s s':real^N->bool.
     lf_simplicial_complex c /\ s IN c /\ s' IN c /\ s SUBSET s'
     ==> s face_of s'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) = s INTER s'` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real^N->bool`; `s':real^N->bool`] o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  ASM_SIMP_TAC[]);;

let MOI_SBA_TRI_SETUP = prove
 (`!c t v:real^N.
     lf_simplicial_complex c /\ t IN c /\ aff_dim t = &2 /\
     v extreme_point_of t
     ==> ?q2 q3. ~(v = q2) /\ ~(v = q3) /\ ~(q2 = q3) /\
                 ~affine_dependent {v,q2,q3} /\ t = convex hull {v,q2,q3} /\
                 !tet. tet IN c /\ aff_dim tet = &3 /\ t SUBSET tet
                       ==> ?p. ~(p = v) /\ ~(p = q2) /\ ~(p = q3) /\
                               ~affine_dependent {v,q2,q3,p} /\
                               tet = convex hull {v,q2,q3,p}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `v:real^N`] MOI_SBA_TRI_VERTS) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
      MOI_SBA_LF_SIMPLEX) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q2:real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q3:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `tet:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_SBA_TET_OVER_TRI THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`]
      MOI_SBA_LF_SIMPLEX) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBST1_TAC(SYM(ASSUME `t = convex hull {v:real^N,q2,q3}`)) THEN
  MATCH_MP_TAC MOI_SBA_LF_SUBSET_FACE THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

(* The difference vectors of an affinely independent 4-point set are        *)
(* linearly independent.                                                     *)

let MOI_SBA_AFF_INDEP_DIFF = prove
 (`!a b c d:real^N.
     ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d) /\
     ~affine_dependent {a,b,c,d}
     ==> !x y z. x % (b - a) + y % (c - a) + z % (d - a) = vec 0
                 ==> x = &0 /\ y = &0 /\ z = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `~affine_dependent {a:real^N,b,c,d}` THEN
  SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT_FINITE; FINITE_INSERT; FINITE_EMPTY] THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_ADD_RID; VECTOR_ADD_RID] THEN
  DISCH_THEN(MP_TAC o SPEC
   `\w:real^N. if w = a then --(x + y + z) else if w = b then x
               else if w = c then y else z`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~r ==> p /\ q /\ s) ==> ~(p /\ q /\ s) ==> r`) THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    UNDISCH_TAC `~(x = &0 /\ y = &0 /\ z = &0)` THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THENL
     [EXISTS_TAC `b:real^N`; EXISTS_TAC `c:real^N`; EXISTS_TAC `d:real^N`] THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `x % (b - a) + y % (c - a) + z % (d - a):real^N = vec 0` THEN
    VECTOR_ARITH_TAC]);;

let MOI_SBA_COORD_AFFINE = prove
 (`!v w1 w2 w3:real^N.
     ?l y. linear l /\
           !s:real^3. v + s$1 % w1 + s$2 % w2 + s$3 % w3 = l s + y`,
  REPEAT GEN_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\s:real^3. s$1 % w1 + s$2 % w2 + s$3 % (w3:real^N)`; `v:real^N`] THEN
  REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 11. A continuous injective parametrization, by an open subset of real^3, *)
(* of the open triangle together with the open tetrahedra on its two sides  *)
(* (used to show that no third tetrahedron meets the triangle).             *)
(* ------------------------------------------------------------------------- *)

let moi_sba_xi = new_definition
 `moi_sba_xi (v:real^N) q2 q3 p1 p2 (s:real^3) =
    if &0 <= s$3 then v + s$1 % (q2 - v) + s$2 % (q3 - v) + s$3 % (p1 - v)
    else v + s$1 % (q2 - v) + s$2 % (q3 - v) + --(s$3) % (p2 - v)`;;

let moi_sba_lam = new_definition
 `moi_sba_lam = {s:real^3 | &0 < s$1 /\ &0 < s$2 /\ s$1 + s$2 + s$3 < &1 /\
                            s$1 + s$2 - s$3 < &1}`;;

let MOI_SBA_LAM_OPEN = prove
 (`open moi_sba_lam`,
  SUBGOAL_THEN
   `moi_sba_lam =
    {s:real^3 | s$1 > &0} INTER {s | s$2 > &0} INTER
    {s | (basis 1 + basis 2 + basis 3) dot s < &1} INTER
    {s | (basis 1 + basis 2 - basis 3) dot s < &1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_sba_lam; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    SIMP_TAC[DOT_LADD; DOT_LSUB; DOT_BASIS; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_LT]]);;

let MOI_SBA_XI_CONT = prove
 (`!v q2 q3 p1 p2:real^N s. moi_sba_xi v q2 q3 p1 p2 continuous_on s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `{x:real^3 | x$3 >= &0} UNION {x | x$3 <= &0}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN REAL_ARITH_TAC] THEN
  SUBGOAL_THEN
   `moi_sba_xi (v:real^N) q2 q3 p1 p2 =
    \s. if &0 <= s$3 then v + s$1 % (q2 - v) + s$2 % (q3 - v) + s$3 % (p1 - v)
        else v + s$1 % (q2 - v) + s$2 % (q3 - v) + s$3 % (v - p2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_sba_xi] THEN GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
  REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE; CLOSED_HALFSPACE_COMPONENT_LE] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_CONTINUOUS_ON THEN
    REWRITE_TAC[MOI_SBA_COORD_AFFINE];
    MATCH_MP_TAC MOI_SBA_AFFINE_CONTINUOUS_ON THEN
    REWRITE_TAC[MOI_SBA_COORD_AFFINE];
    REWRITE_TAC[IN_ELIM_THM; real_ge] THEN X_GEN_TAC `s:real^3` THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[];
      SUBGOAL_THEN `(s:real^3)$3 = &0` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]]]);;

let MOI_SBA_XI_PIECES = prove
 (`!v q2 q3 p1 p2:real^N s.
     ~(v = q2) /\ ~(v = q3) /\ ~(q2 = q3) /\
     ~(p1 = v) /\ ~(p1 = q2) /\ ~(p1 = q3) /\
     ~(p2 = v) /\ ~(p2 = q2) /\ ~(p2 = q3) /\
     ~affine_dependent {v,q2,q3} /\
     ~affine_dependent {v,q2,q3,p1} /\ ~affine_dependent {v,q2,q3,p2} /\
     s IN moi_sba_lam
     ==> (&0 < s$3
          ==> moi_sba_xi v q2 q3 p1 p2 s IN
              relative_interior(convex hull {v,q2,q3,p1})) /\
         (s$3 = &0
          ==> moi_sba_xi v q2 q3 p1 p2 s IN
              relative_interior(convex hull {v,q2,q3})) /\
         (s$3 < &0
          ==> moi_sba_xi v q2 q3 p1 p2 s IN
              relative_interior(convex hull {v,q2,q3,p2}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sba_lam; IN_ELIM_THM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`;
                   `moi_sba_xi (v:real^N) q2 q3 p1 p2 s`] MOI_SBA_RELINT_4) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`&1 - (s:real^3)$1 - s$2 - s$3`; `(s:real^3)$1`; `(s:real^3)$2`;
      `(s:real^3)$3`] THEN
    ASM_SIMP_TAC[moi_sba_xi; REAL_LT_IMP_LE] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`;
                   `moi_sba_xi (v:real^N) q2 q3 p1 p2 s`] MOI_SBA_RELINT_3) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`&1 - (s:real^3)$1 - s$2`; `(s:real^3)$1`; `(s:real^3)$2`] THEN
    ASM_REWRITE_TAC[moi_sba_xi; REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p2:real^N`;
                   `moi_sba_xi (v:real^N) q2 q3 p1 p2 s`] MOI_SBA_RELINT_4) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`&1 - (s:real^3)$1 - s$2 + s$3`; `(s:real^3)$1`; `(s:real^3)$2`;
      `--((s:real^3)$3)`] THEN
    ASM_SIMP_TAC[moi_sba_xi; REAL_ARITH `x < &0 ==> ~(&0 <= x)`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
      VECTOR_ARITH_TAC]]);;

let MOI_SBA_XI_CENTER = prove
 (`!v q2 q3 p1 p2:real^N.
     vector[&1 / &3; &1 / &3; &0] IN moi_sba_lam /\
     moi_sba_xi v q2 q3 p1 p2 (vector[&1 / &3; &1 / &3; &0]) =
     inv(&3) % (v + q2 + q3)`,
  REWRITE_TAC[moi_sba_lam; moi_sba_xi; IN_ELIM_THM; VECTOR_3] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC);;

let MOI_SBA_XI_INJ = prove
 (`!v q2 q3 p1 p2:real^N.
     ~(v = q2) /\ ~(v = q3) /\ ~(q2 = q3) /\
     ~(p1 = v) /\ ~(p1 = q2) /\ ~(p1 = q3) /\
     ~(p2 = v) /\ ~(p2 = q2) /\ ~(p2 = q3) /\
     ~affine_dependent {v,q2,q3} /\
     ~affine_dependent {v,q2,q3,p1} /\ ~affine_dependent {v,q2,q3,p2} /\
     relative_interior(convex hull {v,q2,q3,p2}) INTER
     convex hull {v,q2,q3,p1} = {}
     ==> !s s'. s IN moi_sba_lam /\ s' IN moi_sba_lam /\
                moi_sba_xi v q2 q3 p1 p2 s = moi_sba_xi v q2 q3 p1 p2 s'
                ==> s = s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. s IN moi_sba_lam /\ &0 <= s$3
        ==> moi_sba_xi (v:real^N) q2 q3 p1 p2 s IN convex hull {v,q2,q3,p1}`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`;
                   `p2:real^N`; `s:real^3`] MOI_SBA_XI_PIECES) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(s:real^3)$3 = &0` THEN
    ASM_REWRITE_TAC[REAL_LT_REFL] THEN STRIP_TAC THENL
     [SUBGOAL_THEN
       `relative_interior(convex hull {v,q2,q3}) SUBSET
        convex hull {v:real^N,q2,q3,p1}`
      MP_TAC THENL
       [TRANS_TAC SUBSET_TRANS `convex hull {v:real^N,q2,q3}` THEN
        REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[];
        ASM SET_TAC[]];
      SUBGOAL_THEN `&0 < (s:real^3)$3` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPEC `convex hull {v:real^N,q2,q3,p1}`
        RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN moi_sba_lam /\ s$3 < &0
        ==> moi_sba_xi (v:real^N) q2 q3 p1 p2 s IN
            relative_interior(convex hull {v,q2,q3,p2})`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`;
                   `p2:real^N`; `s:real^3`] MOI_SBA_XI_PIECES) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^3`; `s':real^3`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= (s:real^3)$3` THEN
  ASM_CASES_TAC `&0 <= (s':real^3)$3` THENL
   [UNDISCH_TAC
     `moi_sba_xi (v:real^N) q2 q3 p1 p2 s = moi_sba_xi v q2 q3 p1 p2 s'` THEN
    ASM_REWRITE_TAC[moi_sba_xi] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`]
      MOI_SBA_AFF_INDEP_DIFF) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`(s:real^3)$1 - (s':real^3)$1`; `(s:real^3)$2 - (s':real^3)$2`;
      `(s:real^3)$3 - (s':real^3)$3`]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC
       `v + (s:real^3)$1 % (q2 - v) + s$2 % (q3 - v) + s$3 % (p1 - v) =
        v + (s':real^3)$1 % (q2 - v) + s'$2 % (q3 - v) + s'$3 % (p1 - v:real^N)` THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN
     `moi_sba_xi (v:real^N) q2 q3 p1 p2 s IN convex hull {v,q2,q3,p1} /\
      moi_sba_xi (v:real^N) q2 q3 p1 p2 s' IN
      relative_interior(convex hull {v,q2,q3,p2})`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> x < &0`]; ASM SET_TAC[]];
    SUBGOAL_THEN
     `moi_sba_xi (v:real^N) q2 q3 p1 p2 s' IN convex hull {v,q2,q3,p1} /\
      moi_sba_xi (v:real^N) q2 q3 p1 p2 s IN
      relative_interior(convex hull {v,q2,q3,p2})`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> x < &0`]; ASM SET_TAC[]];
    UNDISCH_TAC
     `moi_sba_xi (v:real^N) q2 q3 p1 p2 s = moi_sba_xi v q2 q3 p1 p2 s'` THEN
    ASM_REWRITE_TAC[moi_sba_xi] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p2:real^N`]
      MOI_SBA_AFF_INDEP_DIFF) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`(s:real^3)$1 - (s':real^3)$1`; `(s:real^3)$2 - (s':real^3)$2`;
      `(s':real^3)$3 - (s:real^3)$3`]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC
       `v + (s:real^3)$1 % (q2 - v) + s$2 % (q3 - v) + --(s$3) % (p2 - v) =
        v + (s':real^3)$1 % (q2 - v) + s'$2 % (q3 - v) +
        --(s'$3) % (p2 - v:real^N)` THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 12. Every triangle of a finite combinatorial 3-manifold lies in exactly  *)
(* two tetrahedra: in none would make its open star a 2-dimensional open    *)
(* subset of a 3-dimensional vertex star; in one would make the regular     *)
(* image of its open star an open set inside a closed half-space touching   *)
(* the boundary plane; in three would make the open triangle with two of    *)
(* the open tetrahedra (an open set of real^3 by invariance of domain)      *)
(* open in the polyhedron, although the third tetrahedron approaches it.   *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_TRI_IN_TET = prove
 (`!c t:real^N->bool.
     FINITE c /\ combinatorial_manifold 3 c /\ t IN c /\ aff_dim t = &2
     ==> ?tet. tet IN c /\ aff_dim tet = &3 /\ t SUBSET tet`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> aff_dim s <= &3` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_DIM_LE3]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `moi_smo_open_star c t = relative_interior (t:real^N->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
      MOI_SBA_OPEN_STAR_TRI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[EXTENSION; th]) THEN
    X_GEN_TAC `x:real^N` THEN
    MATCH_MP_TAC(TAUT `~q ==> (p \/ q <=> p)`) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_SBA_EXTREME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SBA_VCHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^3` (X_CHOOSE_THEN `q:real^3->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `moi_smo_open_star c t SUBSET moi_smo_open_star c {v:real^N}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_OPEN_STAR_MONO THEN ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`;
                 `moi_smo_open_star c (t:real^N->bool)`; `p:real^N->real^3`]
    MOI_SBA_IOD_FWD) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_SBA_OPEN_STAR_OPEN] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `p':real^3->real^N` ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `dimension (moi_smo_open_star c (t:real^N->bool)) = &3`
  MP_TAC THENL
   [TRANS_TAC EQ_TRANS
     `dimension (IMAGE (p:real^N->real^3) (moi_smo_open_star c t))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_DIMENSION THEN REWRITE_TAC[homeomorphic] THEN
      ASM_MESON_TAC[];
      ASM_SIMP_TAC[DIMENSION_OPEN; DIMINDEX_3] THEN
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MOI_SBA_LF_CONVEX]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `dimension(relative_interior(t:real^N->bool)) = &2`
   (fun th -> REWRITE_TAC[th] THEN INT_ARITH_TAC) THEN
  ASM_MESON_TAC[DIMENSION_EQ_AFF_DIM; CONVEX_RELATIVE_INTERIOR;
                AFF_DIM_RELATIVE_INTERIOR; MOI_SBA_LF_CONVEX]);;

let MOI_SBA_AFFINE_IMAGE_HULL = prove
 (`!(A:real^M->real^N) s.
     (?l y. linear l /\ !x. A x = l x + y)
     ==> IMAGE A (convex hull s) = convex hull (IMAGE A s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(A:real^M->real^N) = \x. l x + y` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM]; ASM_SIMP_TAC[MOI_REAL_AFFINE_IMAGE_CONVEX_HULL]]);;

let MOI_SBA_TRI_NOT_ONE = prove
 (`!c t tet:real^N->bool.
     FINITE c /\ combinatorial_manifold 3 c /\ t IN c /\ aff_dim t = &2 /\
     tet IN c /\ aff_dim tet = &3 /\ t SUBSET tet
     ==> ?tet'. tet' IN c /\ aff_dim tet' = &3 /\ t SUBSET tet' /\
                ~(tet' = tet)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> aff_dim s <= &3` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_DIM_LE3]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!x:real^N. x IN moi_smo_open_star c t <=>
               x IN relative_interior t \/ x IN relative_interior tet`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
      MOI_SBA_OPEN_STAR_TRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `x:real^N` THEN AP_TERM_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `tet':real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `tet':real^N->bool = tet` (fun th -> ASM_MESON_TAC[th]) THEN
      ASM_MESON_TAC[];
      DISCH_TAC THEN EXISTS_TAC `tet:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_SBA_EXTREME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `v:real^N`]
    MOI_SBA_TRI_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `q3:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tet:real^N->bool` o check
    (fun th -> is_forall(concl th) &&
               free_in `q2:real^N` (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `tet:real^N->bool = convex hull {v,q2,q3,p1}`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `t:real^N->bool = convex hull {v,q2,q3}`)) THEN
  MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`]
    MOI_SBA_REGMAP_EXISTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`;
                 `A:real^N->real^3`] MOI_SBA_REGMAP_INV) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^3->real^N`
    (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`;
                 `A:real^N->real^3`] MOI_SBA_REGMAP_4) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SBA_REG_ORTH o
    check (fun th -> concl th =
      `moi_sba_reg ((A:real^N->real^3) v) (A q2) (A q3) (A p1)`)) THEN
  ABBREV_TAC `c0 = inv(&3) % ((A:real^N->real^3) v + A q2 + A q3)` THEN
  ABBREV_TAC `n = (A:real^N->real^3) p1 - c0` THEN
  SUBGOAL_THEN
   `moi_smo_open_star c (convex hull {v,q2,q3}) SUBSET
    convex hull {v:real^N,q2,q3,p1}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(DISJ_CASES_TAC) THENL
     [SUBGOAL_THEN
       `relative_interior(convex hull {v,q2,q3}) SUBSET
        convex hull {v:real^N,q2,q3,p1}`
      MP_TAC THENL
       [TRANS_TAC SUBSET_TRANS `convex hull {v:real^N,q2,q3}` THEN
        REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[];
        ASM SET_TAC[]];
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`;
                 `moi_smo_open_star c (convex hull {v:real^N,q2,q3})`;
                 `A:real^N->real^3`] MOI_SBA_IOD_FWD) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_SBA_OPEN_STAR_OPEN] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SBA_OPEN_STAR_MONO THEN
      ASM_SIMP_TAC[SING_SUBSET; HULL_INC; IN_INSERT];
      MATCH_MP_TAC MOI_SBA_AFFINE_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN
       `(x:real^N) IN convex hull {v,q2,q3,p1} /\
        y IN convex hull {v,q2,q3,p1}`
      MP_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      MP_TAC(ISPEC `{v:real^N,q2,q3,p1}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN
   `IMAGE (A:real^N->real^3) (moi_smo_open_star c (convex hull {v,q2,q3}))
    SUBSET {z | n dot z >= n dot c0}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (A:real^N->real^3) (convex hull {v,q2,q3,p1})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_SBA_AFFINE_IMAGE_HULL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_HALFSPACE_GE; IMAGE_CLAUSES; INSERT_SUBSET;
                EMPTY_SUBSET; IN_ELIM_THM; real_ge] THEN
    MP_TAC(ASSUME `(n:real^3) dot ((A:real^N->real^3) v - c0) = &0`) THEN
    MP_TAC(ASSUME `(n:real^3) dot ((A:real^N->real^3) q2 - c0) = &0`) THEN
    MP_TAC(ASSUME `(n:real^3) dot ((A:real^N->real^3) q3 - c0) = &0`) THEN
    MP_TAC(ASSUME `(n:real^3) dot n = &2 / &3`) THEN
    SUBGOAL_THEN
     `(n:real^3) dot ((A:real^N->real^3) p1) - n dot c0 = n dot n`
    MP_TAC THENL
     [REWRITE_TAC[GSYM DOT_RSUB] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c0 IN IMAGE (A:real^N->real^3)
             (moi_smo_open_star c (convex hull {v,q2,q3}))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `inv(&3) % (v + q2 + q3:real^N)` THEN
    CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME
        `inv(&3) % ((A:real^N->real^3) v + A q2 + A q3) = c0`)) THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
        STRIP_ASSUME_TAC) o check (fun th -> is_exists(concl th) &&
          free_in `A:real^N->real^3` (concl th))) THEN
      REWRITE_TAC[ASSUME `!x:real^N. (A:real^N->real^3) x = l x + y`] THEN
      REWRITE_TAC[VECTOR_ARITH
       `inv(&3) % (v + q2 + q3):real^N = &1 / &3 % v + &1 / &3 % q2 + &1 / &3 % q3`] THEN
      ASM_SIMP_TAC[MOI_SBA_AFFINE_COMB3; REAL_ARITH `&1 / &3 + &1 / &3 + &1 / &3 = &1`] THEN
      VECTOR_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
      MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`;
                     `inv(&3) % (v + q2 + q3:real^N)`] MOI_SBA_RELINT_3) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MAP_EVERY EXISTS_TAC [`&1 / &3`; `&1 / &3`; `&1 / &3`] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DOT_EQ_0] THEN EXPAND_TAC "n" THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{z:real^3 | n dot z >= n dot c0}`;
                 `IMAGE (A:real^N->real^3)
                    (moi_smo_open_star c (convex hull {v,q2,q3}))`]
    INTERIOR_MAXIMAL) THEN
  ASM_SIMP_TAC[INTERIOR_HALFSPACE_GE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `c0:real^3`) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let SPDR5_SBA_MEET = prove
 (`!P (x:real^N) y r t.
     P /\ (P ==> x IN r) /\ y = x /\ y IN t ==> ~(r INTER t = {})`,
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN MESON_TAC[]);;

let MOI_SBA_TRI_NOT_THREE = prove
 (`!c t tet1 tet2 tet3:real^N->bool.
     FINITE c /\ combinatorial_manifold 3 c /\ t IN c /\ aff_dim t = &2 /\
     tet1 IN c /\ aff_dim tet1 = &3 /\ t SUBSET tet1 /\
     tet2 IN c /\ aff_dim tet2 = &3 /\ t SUBSET tet2 /\
     tet3 IN c /\ aff_dim tet3 = &3 /\ t SUBSET tet3 /\
     ~(tet1 = tet2) /\ ~(tet1 = tet3) /\ ~(tet2 = tet3)
     ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (tet3:real^N->bool) /\ closed tet3` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_LF_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior tet2 INTER (tet1:real^N->bool) = {}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_RELINT_DISJ_EQDIM THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r:real^N->bool.
      r IN c /\ ~(r = tet3) /\ ~(relative_interior r INTER
                                 relative_interior tet3 = {}) ==> F`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet3:real^N->bool`;
                   `r:real^N->bool`] MOI_SBA_RELINT_EQ) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^N->bool = tet3)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_SBA_EXTREME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `v:real^N`]
    MOI_SBA_TRI_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `q3:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `tet1:real^N->bool` o check
    (fun th -> is_forall(concl th) && free_in `q2:real^N` (concl th))) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `tet2:real^N->bool` o check
    (fun th -> is_forall(concl th) && free_in `q2:real^N` (concl th))) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `tet1:real^N->bool = convex hull {v,q2,q3,p1}`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `tet2:real^N->bool = convex hull {v,q2,q3,p2}`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `t:real^N->bool = convex hull {v,q2,q3}`)) THEN
  SUBGOAL_THEN
   `relative_interior(convex hull {v,q2,q3}) SUBSET
    moi_smo_open_star c {v:real^N} /\
    relative_interior(convex hull {v,q2,q3,p1}) SUBSET
    moi_smo_open_star c {v} /\
    relative_interior(convex hull {v,q2,q3,p2}) SUBSET
    moi_smo_open_star c {v}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
     [EXISTS_TAC `moi_smo_open_star c (convex hull {v:real^N,q2,q3})`;
      EXISTS_TAC `moi_smo_open_star c (convex hull {v:real^N,q2,q3,p1})`;
      EXISTS_TAC `moi_smo_open_star c (convex hull {v:real^N,q2,q3,p2})`] THEN
    ASM_SIMP_TAC[MOI_SBA_RELINT_IN_STAR] THEN
    MATCH_MP_TAC MOI_SBA_OPEN_STAR_MONO THEN
    ASM_SIMP_TAC[SING_SUBSET; HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `moi_sba_lam`;
                 `moi_sba_xi (v:real^N) q2 q3 p1 p2`] MOI_SBA_IOD_REV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_SBA_LAM_OPEN; MOI_SBA_XI_CONT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SBA_XI_INJ THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `s:real^3` THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`;
                     `p2:real^N`; `s:real^3`] MOI_SBA_XI_PIECES) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN
      DISJ_CASES_TAC(REAL_ARITH `(s:real^3)$3 < &0 \/ s$3 = &0 \/ &0 < s$3`) THENL
       [MATCH_MP_TAC(REWRITE_RULE[SUBSET] (ASSUME
         `relative_interior(convex hull {v:real^N,q2,q3,p2}) SUBSET
          moi_smo_open_star c {v}`)) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_X_ASSUM(DISJ_CASES_TAC) THENL
         [MATCH_MP_TAC(REWRITE_RULE[SUBSET] (ASSUME
           `relative_interior(convex hull {v:real^N,q2,q3}) SUBSET
            moi_smo_open_star c {v}`)) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC(REWRITE_RULE[SUBSET] (ASSUME
           `relative_interior(convex hull {v:real^N,q2,q3,p1}) SUBSET
            moi_smo_open_star c {v}`)) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]]];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`;
                 `p2:real^N`] MOI_SBA_XI_CENTER) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `inv(&3) % (v + q2 + q3:real^N) IN
    relative_interior(convex hull {v,q2,q3})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`;
                   `inv(&3) % (v + q2 + q3:real^N)`] MOI_SBA_RELINT_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`&1 / &3`; `&1 / &3`; `&1 / &3`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&3) % (v + q2 + q3:real^N) IN G` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `inv(&3) % (v + q2 + q3:real^N) IN
      IMAGE (moi_sba_xi v q2 q3 p1 p2) moi_sba_lam`
    MP_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `vector[&1 / &3; &1 / &3; &0]:real^3` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&3) % (v + q2 + q3:real^N) IN tet3` ASSUME_TAC THENL
   [MP_TAC(ISPEC `convex hull {v:real^N,q2,q3}` RELATIVE_INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((G:real^N->bool) INTER relative_interior tet3 = {})`
  MP_TAC THENL
   [MP_TAC(ISPECL [`G:real^N->bool`; `relative_interior tet3:real^N->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `inv(&3) % (v + q2 + q3:real^N)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE (moi_sba_xi v q2 q3 p1 p2) moi_sba_lam`
  MP_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN
    MP_TAC(ISPEC `tet3:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    REWRITE_TAC[IN_UNIONS] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC o
    REWRITE_RULE[IN_IMAGE]) THEN
  MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`;
                 `p2:real^N`; `s:real^3`] MOI_SBA_XI_PIECES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check
    (fun th -> is_forall(concl th) && free_in `tet3:real^N->bool` (concl th) &&
               not (free_in `q2:real^N` (concl th)))) THEN
  DISJ_CASES_TAC(REAL_ARITH `(s:real^3)$3 < &0 \/ s$3 = &0 \/ &0 < s$3`) THENL
   [EXISTS_TAC `convex hull {v:real^N,q2,q3,p2}` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SPDR5_SBA_MEET THEN
    MAP_EVERY EXISTS_TAC [`(s:real^3)$3 < &0`;
                          `moi_sba_xi (v:real^N) q2 q3 p1 p2 s`; `y:real^N`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(DISJ_CASES_TAC) THENL
     [EXISTS_TAC `convex hull {v:real^N,q2,q3}` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SPDR5_SBA_MEET THEN
      MAP_EVERY EXISTS_TAC [`(s:real^3)$3 = &0`;
                            `moi_sba_xi (v:real^N) q2 q3 p1 p2 s`; `y:real^N`] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      EXISTS_TAC `convex hull {v:real^N,q2,q3,p1}` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SPDR5_SBA_MEET THEN
      MAP_EVERY EXISTS_TAC [`&0 < (s:real^3)$3`;
                            `moi_sba_xi (v:real^N) q2 q3 p1 p2 s`; `y:real^N`] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);;

let MOI_SBA_TRI_TWO = prove
 (`!c t:real^N->bool.
     FINITE c /\ combinatorial_manifold 3 c /\ t IN c /\ aff_dim t = &2
     ==> ?tet1 tet2. tet1 IN c /\ aff_dim tet1 = &3 /\ t SUBSET tet1 /\
                     tet2 IN c /\ aff_dim tet2 = &3 /\ t SUBSET tet2 /\
                     ~(tet1 = tet2) /\
                     !tet. tet IN c /\ aff_dim tet = &3 /\ t SUBSET tet
                           ==> tet = tet1 \/ tet = tet2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_SBA_TRI_IN_TET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tet1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`;
                 `tet1:real^N->bool`] MOI_SBA_TRI_NOT_ONE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tet2:real^N->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`tet1:real^N->bool`; `tet2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `tet:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`;
                 `tet1:real^N->bool`; `tet2:real^N->bool`; `tet:real^N->bool`]
    MOI_SBA_TRI_NOT_THREE) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 13. The structure at a triangle: vertices, the two tetrahedra over it,   *)
(* its open star.                                                            *)
(* ------------------------------------------------------------------------- *)

let moi_sba_tri = new_definition
 `moi_sba_tri (c:(real^N->bool)->bool) t v q2 q3 p1 p2 <=>
    ~(v = q2) /\ ~(v = q3) /\ ~(q2 = q3) /\
    ~(p1 = v) /\ ~(p1 = q2) /\ ~(p1 = q3) /\
    ~(p2 = v) /\ ~(p2 = q2) /\ ~(p2 = q3) /\ ~(p1 = p2) /\
    ~affine_dependent {v,q2,q3} /\ ~affine_dependent {v,q2,q3,p1} /\
    ~affine_dependent {v,q2,q3,p2} /\
    t = convex hull {v,q2,q3} /\
    convex hull {v,q2,q3,p1} IN c /\
    aff_dim (convex hull {v,q2,q3,p1}) = &3 /\
    convex hull {v,q2,q3,p2} IN c /\
    aff_dim (convex hull {v,q2,q3,p2}) = &3 /\
    (!tet. tet IN c /\ aff_dim tet = &3 /\ t SUBSET tet
           ==> tet = convex hull {v,q2,q3,p1} \/
               tet = convex hull {v,q2,q3,p2}) /\
    (!x. x IN moi_smo_open_star c t <=>
         x IN relative_interior (convex hull {v,q2,q3}) \/
         x IN relative_interior (convex hull {v,q2,q3,p1}) \/
         x IN relative_interior (convex hull {v,q2,q3,p2})) /\
    relative_interior (convex hull {v,q2,q3,p1}) INTER
    convex hull {v,q2,q3,p2} = {} /\
    relative_interior (convex hull {v,q2,q3,p2}) INTER
    convex hull {v,q2,q3,p1} = {}`;;

let MOI_SBA_TRI_STRUCT = prove
 (`!c t v:real^N.
     FINITE c /\ combinatorial_manifold 3 c /\ t IN c /\ aff_dim t = &2 /\
     v extreme_point_of t
     ==> ?q2 q3 p1 p2. moi_sba_tri c t v q2 q3 p1 p2`,
  REWRITE_TAC[moi_sba_tri] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> aff_dim s <= &3` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_DIM_LE3]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_SBA_TRI_TWO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tet1:real^N->bool` (X_CHOOSE_THEN `tet2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `v:real^N`]
    MOI_SBA_TRI_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q2:real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q3:real^N` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `tet1:real^N->bool` o check
    (fun th -> is_forall(concl th) && free_in `q2:real^N` (concl th))) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p1:real^N` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `tet2:real^N->bool` o check
    (fun th -> is_forall(concl th) && free_in `q2:real^N` (concl th))) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p2:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `tet1:real^N->bool = convex hull {v,q2,q3,p1}`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `tet2:real^N->bool = convex hull {v,q2,q3,p2}`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `t:real^N->bool = convex hull {v,q2,q3}`)) THEN
  SUBGOAL_THEN `~(p1:real^N = p2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_interior (convex hull {v,q2,q3,p1}) INTER
    convex hull {v:real^N,q2,q3,p2} = {} /\
    relative_interior (convex hull {v,q2,q3,p2}) INTER
    convex hull {v:real^N,q2,q3,p1} = {}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_SBA_RELINT_DISJ_EQDIM THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN moi_smo_open_star c (convex hull {v,q2,q3}) <=>
               x IN relative_interior (convex hull {v,q2,q3}) \/
               x IN relative_interior (convex hull {v,q2,q3,p1}) \/
               x IN relative_interior (convex hull {v,q2,q3,p2})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `convex hull {v:real^N,q2,q3}`]
      MOI_SBA_OPEN_STAR_TRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `x:real^N` THEN AP_TERM_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `tet:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `tet:real^N->bool` o check
        (fun th -> is_forall(concl th) && free_in `p2:real^N` (concl th))) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_MESON_TAC[];
      STRIP_TAC THENL
       [EXISTS_TAC `convex hull {v:real^N,q2,q3,p1}`;
        EXISTS_TAC `convex hull {v:real^N,q2,q3,p2}`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 14. Homogeneity of affine maps vanishing at a point, and of convex       *)
(* relative interiors under shrinking towards a point of the closure.       *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_AFFINE_HOMOG = prove
 (`!(A:real^M->real^N) v x s.
     (?l y. linear l /\ !x. A x = l x + y) /\ A v = vec 0
     ==> A(v + s % (x - v)) = s % A x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
     STRIP_ASSUME_TAC)) MP_TAC) THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; LINEAR_SUB] THEN
  REWRITE_TAC[VECTOR_ARITH `l + y:real^N = vec 0 <=> l = --y`] THEN
  DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC);;

let MOI_SBA_SHRINK = prove
 (`!s v x:real^N r.
     convex s /\ closed s /\ v IN s /\ x IN relative_interior s /\
     &0 < r /\ r <= &1
     ==> v + r % (x - v) IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `r:real`; `v:real^N`; `x:real^N`]
    IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK) THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 15. Star charts of open tetrahedra.                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_TET_ATLAS_IN = prove
 (`!c tet (A:real^N->real^3).
     (relative_interior tet,A) IN moi_smo_tet_atlas c <=>
     ?tet'. tet' IN c /\ aff_dim tet' = &3 /\ moi_smo_regmap tet' A /\
            relative_interior tet = relative_interior tet'`,
  REWRITE_TAC[moi_smo_tet_atlas; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let MOI_SBA_TET_STAR = prove
 (`!c tet v:real^N.
     FINITE c /\ combinatorial_manifold 3 c /\ tet IN c /\ aff_dim tet = &3 /\
     v extreme_point_of tet
     ==> ?A. (relative_interior tet,A) IN moi_smo_tet_atlas c /\
             !x s. x IN relative_interior tet /\ &0 < s /\ s <= &1
                   ==> v + s % (x - v) IN relative_interior tet /\
                       A(v + s % (x - v)) = s % A x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tet:real^N->bool`; `v:real^N`] MOI_SBA_TET_VERTS) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`]
      MOI_SBA_LF_SIMPLEX) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `q3:real^N`
    (X_CHOOSE_THEN `q4:real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `q4:real^N`]
    MOI_SBA_REGMAP_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `A:real^N->real^3` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOI_SBA_TET_ATLAS_IN] THEN EXISTS_TAC `tet:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SBA_SHRINK THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_SBA_LF_CONVEX; extreme_point_of];
    MATCH_MP_TAC MOI_SBA_AFFINE_HOMOG THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_smo_regmap (convex hull {v:real^N,q2,q3,q4}) A` THEN
    REWRITE_TAC[moi_smo_regmap] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 16. Membership in the two families of charts.                             *)
(* ------------------------------------------------------------------------- *)

let moi_sba_unf = new_definition
 `moi_sba_unf (c:(real^N->bool)->bool) t (u:real^N->real^3) <=>
    (!x y. x IN moi_smo_open_star c t /\ y IN moi_smo_open_star c t /\
           u x = u y ==> x = y) /\
    (!tet. tet IN c /\ aff_dim tet = &3 /\ t SUBSET tet
           ==> ?A. moi_smo_regmap tet A /\
                   !x. x IN tet INTER moi_smo_open_star c t ==> u x = A x)`;;

let MOI_SBA_UNFOLD_ATLAS_IN = prove
 (`!c U (u:real^N->real^3).
     (U,u) IN moi_smo_unfold_atlas c <=>
     ?t. t IN c /\ aff_dim t = &2 /\ U = moi_smo_open_star c t /\
         moi_sba_unf c t u`,
  REWRITE_TAC[moi_smo_unfold_atlas; IN_ELIM_THM; PAIR_EQ; GSYM moi_sba_unf] THEN
  MESON_TAC[]);;

let MOI_SBA_TET_ATLAS_IN2 = prove
 (`!c U (A:real^N->real^3).
     (U,A) IN moi_smo_tet_atlas c <=>
     ?tet. tet IN c /\ aff_dim tet = &3 /\ U = relative_interior tet /\
           moi_smo_regmap tet A`,
  REWRITE_TAC[moi_smo_tet_atlas; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 17. Heights over a face: an affine functional vanishing at three        *)
(* vertices is, on the open tetrahedron, a positive multiple of its value  *)
(* at the fourth vertex, and vanishes on the open face.                     *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_HEIGHT_REL4 = prove
 (`!(A:real^N->real^3) n c0 p1 p2 p3 p4 x.
     (?l y. linear l /\ !x. A x = l x + y) /\
     ~(p1 = p2) /\ ~(p1 = p3) /\ ~(p1 = p4) /\ ~(p2 = p3) /\ ~(p2 = p4) /\
     ~(p3 = p4) /\ ~affine_dependent {p1,p2,p3,p4} /\
     x IN relative_interior (convex hull {p1,p2,p3,p4}) /\
     n dot (A p1 - c0) = &0 /\ n dot (A p2 - c0) = &0 /\
     n dot (A p3 - c0) = &0
     ==> ?u. &0 < u /\ n dot (A x - c0) = u * (n dot (A p4 - c0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "aff") STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p1:real^N`; `p2:real^N`; `p3:real^N`; `p4:real^N`;
                 `x:real^N`] MOI_SBA_RELINT_4) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
    (X_CHOOSE_THEN `u3:real` (X_CHOOSE_THEN `u4:real` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `u4:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(A:real^N->real^3) (u1 % p1 + u2 % p2 + u3 % p3 + u4 % p4) =
    u1 % A p1 + u2 % A p2 + u3 % A p3 + u4 % A p4`
  SUBST1_TAC THENL
   [REMOVE_THEN "aff" (X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SBA_AFFINE_COMB4 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SBA_DOT_COMB4] THEN REAL_ARITH_TAC);;

let MOI_SBA_HEIGHT_REL3 = prove
 (`!(A:real^N->real^3) n c0 p1 p2 p3 x.
     (?l y. linear l /\ !x. A x = l x + y) /\
     ~(p1 = p2) /\ ~(p1 = p3) /\ ~(p2 = p3) /\ ~affine_dependent {p1,p2,p3} /\
     x IN relative_interior (convex hull {p1,p2,p3}) /\
     n dot (A p1 - c0) = &0 /\ n dot (A p2 - c0) = &0 /\
     n dot (A p3 - c0) = &0
     ==> n dot (A x - c0) = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "aff") STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p1:real^N`; `p2:real^N`; `p3:real^N`; `x:real^N`]
    MOI_SBA_RELINT_3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
    (X_CHOOSE_THEN `u3:real` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(A:real^N->real^3) (u1 % p1 + u2 % p2 + u3 % p3) =
    u1 % A p1 + u2 % A p2 + u3 % A p3`
  SUBST1_TAC THENL
   [REMOVE_THEN "aff" (X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SBA_AFFINE_COMB3 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SBA_DOT_COMB3] THEN REAL_ARITH_TAC);;

let MOI_SBA_REGMAP_AFFINE = prove
 (`!tet (A:real^N->real^3).
     moi_smo_regmap tet A ==> ?l y. linear l /\ !x. A x = l x + y`,
  SIMP_TAC[moi_smo_regmap]);;

let MOI_SBA_REGMAP_INJ = prove
 (`!p1 p2 p3 p4:real^N (A:real^N->real^3) x y.
     ~(p1 = p2) /\ ~(p1 = p3) /\ ~(p1 = p4) /\ ~(p2 = p3) /\ ~(p2 = p4) /\
     ~(p3 = p4) /\ ~affine_dependent {p1,p2,p3,p4} /\
     moi_smo_regmap (convex hull {p1,p2,p3,p4}) A /\
     x IN convex hull {p1,p2,p3,p4} /\ y IN convex hull {p1,p2,p3,p4} /\
     A x = A y
     ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p1:real^N`; `p2:real^N`; `p3:real^N`; `p4:real^N`;
                 `A:real^N->real^3`] MOI_SBA_REGMAP_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^3->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `{p1:real^N,p2,p3,p4}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
  REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 18. The unfolding over a triangle: the two regular maps agree on the     *)
(* triangle and put the two tetrahedra on opposite sides of its plane, so   *)
(* the glued map is injective on the open star.                              *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_UNFOLD_HEIGHTS = prove
 (`!c t v q2 q3 p1 p2 (A1:real^N->real^3) A2 n c0.
     moi_sba_tri c t v q2 q3 p1 p2 /\
     moi_smo_regmap (convex hull {v,q2,q3,p1}) A1 /\
     moi_smo_regmap (convex hull {v,q2,q3,p2}) A2 /\
     n dot (A1 v - c0) = &0 /\ n dot (A1 q2 - c0) = &0 /\
     n dot (A1 q3 - c0) = &0 /\ &0 < n dot (A1 p1 - c0) /\
     A2 v = A1 v /\ A2 q2 = A1 q2 /\ A2 q3 = A1 q3 /\
     n dot (A2 p2 - c0) < &0
     ==> !x. x IN moi_smo_open_star c t
             ==> (x IN convex hull {v,q2,q3,p1} /\
                  &0 <= n dot (A1 x - c0)) \/
                 (~(x IN convex hull {v,q2,q3,p1}) /\
                  x IN convex hull {v,q2,q3,p2} /\
                  n dot (A2 x - c0) < &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sba_tri] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `t:real^N->bool = convex hull {v,q2,q3}`)) THEN
  X_GEN_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `relative_interior(convex hull {v,q2,q3}) SUBSET
        convex hull {v:real^N,q2,q3,p1}`
      MP_TAC THENL
       [TRANS_TAC SUBSET_TRANS `convex hull {v:real^N,q2,q3}` THEN
        REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[];
        ASM SET_TAC[]];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC MOI_SBA_HEIGHT_REL3 THEN
      MAP_EVERY EXISTS_TAC [`v:real^N`; `q2:real^N`; `q3:real^N`] THEN
      ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE]];
    DISJ1_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`A1:real^N->real^3`; `n:real^3`; `c0:real^3`; `v:real^N`;
                   `q2:real^N`; `q3:real^N`; `p1:real^N`; `x:real^N`]
      MOI_SBA_HEIGHT_REL4) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`A2:real^N->real^3`; `n:real^3`; `c0:real^3`; `v:real^N`;
                   `q2:real^N`; `q3:real^N`; `p2:real^N`; `x:real^N`]
      MOI_SBA_HEIGHT_REL4) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < u * --h ==> u * h < &0`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_SBA_UNFOLD_INJ = prove
 (`!c t v q2 q3 p1 p2 (A1:real^N->real^3) A2 n c0.
     moi_sba_tri c t v q2 q3 p1 p2 /\
     moi_smo_regmap (convex hull {v,q2,q3,p1}) A1 /\
     moi_smo_regmap (convex hull {v,q2,q3,p2}) A2 /\
     n dot (A1 v - c0) = &0 /\ n dot (A1 q2 - c0) = &0 /\
     n dot (A1 q3 - c0) = &0 /\ &0 < n dot (A1 p1 - c0) /\
     A2 v = A1 v /\ A2 q2 = A1 q2 /\ A2 q3 = A1 q3 /\
     n dot (A2 p2 - c0) < &0
     ==> !x y. x IN moi_smo_open_star c t /\ y IN moi_smo_open_star c t /\
               (if x IN convex hull {v,q2,q3,p1} then A1 x else A2 x) =
               (if y IN convex hull {v,q2,q3,p1} then A1 y else A2 y)
               ==> x = y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SBA_UNFOLD_HEIGHTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_sba_tri] o CONJUNCT1) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eq"))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o check
    (fun th -> is_forall(concl th) && free_in `n:real^3` (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check
    (fun th -> is_forall(concl th) && free_in `n:real^3` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  REMOVE_THEN "eq" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [MATCH_MP_TAC MOI_SBA_REGMAP_INJ THEN
    MAP_EVERY EXISTS_TAC
     [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`; `A1:real^N->real^3`] THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `&0 <= (n:real^3) dot ((A1:real^N->real^3) y - c0)` THEN
    UNDISCH_TAC `(n:real^3) dot ((A2:real^N->real^3) x - c0) < &0` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&0 <= (n:real^3) dot ((A1:real^N->real^3) x - c0)` THEN
    UNDISCH_TAC `(n:real^3) dot ((A2:real^N->real^3) y - c0) < &0` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC MOI_SBA_REGMAP_INJ THEN
    MAP_EVERY EXISTS_TAC
     [`v:real^N`; `q2:real^N`; `q3:real^N`; `p2:real^N`; `A2:real^N->real^3`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SBA_UNFOLD_BUILD = prove
 (`!c t v q2 q3 p1 p2 (A1:real^N->real^3).
     lf_simplicial_complex c /\ moi_sba_tri c t v q2 q3 p1 p2 /\
     moi_smo_regmap (convex hull {v,q2,q3,p1}) A1
     ==> ?A2. moi_smo_regmap (convex hull {v,q2,q3,p2}) A2 /\
              A2 v = A1 v /\ A2 q2 = A1 q2 /\ A2 q3 = A1 q3 /\
              moi_sba_unf c t
                (\x. if x IN convex hull {v,q2,q3,p1} then A1 x else A2 x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[moi_sba_tri] (ASSUME
    `moi_sba_tri (c:(real^N->bool)->bool) t v q2 q3 p1 p2`)) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `t:real^N->bool = convex hull {v,q2,q3}`)) THEN
  MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`;
                 `A1:real^N->real^3`] MOI_SBA_REGMAP_4) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SBA_REG_ORTH o check
    (fun th -> concl th =
      `moi_sba_reg ((A1:real^N->real^3) v) (A1 q2) (A1 q3) (A1 p1)`)) THEN
  SUBGOAL_THEN
   `?A2:real^N->real^3.
      (?l y. linear l /\ !x. A2 x = l x + y) /\
      A2 v = A1 v /\ A2 q2 = A1 q2 /\ A2 q3 = A1 q3 /\
      A2 p2 = &2 / &3 % (A1 v + A1 q2 + A1 q3) - A1 p1`
  (X_CHOOSE_THEN `A2:real^N->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THENL
   [MP_TAC(ISPECL
     [`{v,q2,q3,p2}:real^N->bool`;
      `\x:real^N. if x = v then (A1:real^N->real^3) v else if x = q2 then A1 q2
                  else if x = q3 then A1 q3
                  else &2 / &3 % (A1 v + A1 q2 + A1 q3) - A1 p1`]
     MOI_REAL_AFFINE_EXTEND_POINTS) THEN
    ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `l2:real^N->real^3` (X_CHOOSE_THEN `y2:real^3`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `\x:real^N. (l2:real^N->real^3) x + y2` THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`l2:real^N->real^3`; `y2:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `A2:real^N->real^3` THEN
  SUBGOAL_THEN `moi_smo_regmap (convex hull {v,q2,q3,p2}) (A2:real^N->real^3)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p2:real^N`;
                   `A2:real^N->real^3`] MOI_SBA_REGMAP_4) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_sba_unf] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`c:(real^N->bool)->bool`; `convex hull {v:real^N,q2,q3}`; `v:real^N`;
      `q2:real^N`; `q3:real^N`; `p1:real^N`; `p2:real^N`;
      `A1:real^N->real^3`; `A2:real^N->real^3`;
      `(A1:real^N->real^3) p1 - inv(&3) % (A1 v + A1 q2 + A1 q3)`;
      `inv(&3) % ((A1:real^N->real^3) v + A1 q2 + A1 q3)`]
     MOI_SBA_UNFOLD_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `tet:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tet:real^N->bool` o check
    (fun th -> is_forall(concl th) && free_in `p2:real^N` (concl th) &&
               not (free_in `A1:real^N->real^3` (concl th)))) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `A1:real^N->real^3` THEN ASM_SIMP_TAC[IN_INTER];
    EXISTS_TAC `A2:real^N->real^3` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull {v,q2,q3}` ASSUME_TAC THENL
     [MP_TAC(ISPEC `convex hull {v:real^N,q2,q3}` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `l1:real^N->real^3` (X_CHOOSE_THEN `y1:real^3`
      STRIP_ASSUME_TAC) o check (fun th -> is_exists(concl th) &&
        free_in `A1:real^N->real^3` (concl th))) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `l2:real^N->real^3` (X_CHOOSE_THEN `y2:real^3`
      STRIP_ASSUME_TAC) o check (fun th -> is_exists(concl th) &&
        free_in `A2:real^N->real^3` (concl th))) THEN
    MP_TAC(ISPECL [`l1:real^N->real^3`; `l2:real^N->real^3`; `y1:real^3`;
                   `y2:real^3`; `{v:real^N,q2,q3}`]
      MOI_REAL_AFFINE_EQ_ON_CONVEX_HULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 19. Star charts over triangles: the unfolding with the vertex v at 0 is   *)
(* homogeneous of degree 1 about v.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_HULL_SHRINK = prove
 (`!s v x:real^N r.
     FINITE s /\ v IN s /\ x IN relative_interior (convex hull s) /\
     &0 < r /\ r <= &1
     ==> v + r % (x - v) IN relative_interior (convex hull s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SBA_SHRINK THEN
  ASM_SIMP_TAC[CONVEX_CONVEX_HULL; HULL_INC; COMPACT_IMP_CLOSED;
               COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT]);;

let MOI_SBA_UNFOLD_STAR = prove
 (`!c t v:real^N.
     FINITE c /\ combinatorial_manifold 3 c /\ t IN c /\ aff_dim t = &2 /\
     v extreme_point_of t
     ==> ?w. moi_sba_unf c t w /\
             !x s. x IN moi_smo_open_star c t /\ &0 < s /\ s <= &1
                   ==> v + s % (x - v) IN moi_smo_open_star c t /\
                       w(v + s % (x - v)) = s % w x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `v:real^N`]
    MOI_SBA_TRI_STRUCT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `q3:real^N`
    (X_CHOOSE_THEN `p1:real^N` (X_CHOOSE_THEN `p2:real^N` ASSUME_TAC)))) THEN
  MP_TAC(REWRITE_RULE[moi_sba_tri] (ASSUME
    `moi_sba_tri (c:(real^N->bool)->bool) t v q2 q3 p1 p2`)) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `t:real^N->bool = convex hull {v,q2,q3}`)) THEN
  MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`]
    MOI_SBA_REGMAP_EXISTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `convex hull {v:real^N,q2,q3}`;
                 `v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`; `p2:real^N`;
                 `A1:real^N->real^3`] MOI_SBA_UNFOLD_BUILD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A2:real^N->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:real^N. if x IN convex hull {v,q2,q3,p1}
                         then (A1:real^N->real^3) x else A2 x` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(!x s. (A1:real^N->real^3)(v + s % (x - v)) = s % A1 x) /\
    (!x s. (A2:real^N->real^3)(v + s % (x - v)) = s % A2 x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN MATCH_MP_TAC MOI_SBA_AFFINE_HOMOG THEN
    ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `s:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN
     `v + s % (x - v) IN relative_interior (convex hull {v:real^N,q2,q3})`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SBA_HULL_SHRINK THEN
      ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `relative_interior(convex hull {v,q2,q3}) SUBSET
      convex hull {v:real^N,q2,q3,p1}`
    ASSUME_TAC THENL
     [TRANS_TAC SUBSET_TRANS `convex hull {v:real^N,q2,q3}` THEN
      REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN MATCH_MP_TAC HULL_MONO THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(x:real^N) IN convex hull {v,q2,q3,p1} /\
      v + s % (x - v) IN convex hull {v,q2,q3,p1}`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    SUBGOAL_THEN
     `v + s % (x - v) IN relative_interior (convex hull {v:real^N,q2,q3,p1})`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SBA_HULL_SHRINK THEN
      ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `convex hull {v:real^N,q2,q3,p1}` RELATIVE_INTERIOR_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN
     `v + s % (x - v) IN relative_interior (convex hull {v:real^N,q2,q3,p2})`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SBA_HULL_SHRINK THEN
      ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~((x:real^N) IN convex hull {v,q2,q3,p1}) /\
      ~(v + s % (x - v) IN convex hull {v,q2,q3,p1})`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 20. Affine evaluation and agreement on a tetrahedron.                     *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_AFF_EVAL4 = prove
 (`!(A:real^M->real^N) u1 u2 u3 u4 p1 p2 p3 p4.
     (?l y. linear l /\ !x. A x = l x + y) /\ u1 + u2 + u3 + u4 = &1
     ==> A(u1 % p1 + u2 % p2 + u3 % p3 + u4 % p4) =
         u1 % A p1 + u2 % A p2 + u3 % A p3 + u4 % A p4`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
     STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SBA_AFFINE_COMB4 THEN
  ASM_REWRITE_TAC[]);;

let MOI_SBA_AFF_EQ_HULL4 = prove
 (`!(A:real^M->real^N) B p1 p2 p3 p4 x.
     (?l y. linear l /\ !x. A x = l x + y) /\
     (?l y. linear l /\ !x. B x = l x + y) /\
     A p1 = B p1 /\ A p2 = B p2 /\ A p3 = B p3 /\ A p4 = B p4 /\
     x IN convex hull {p1,p2,p3,p4}
     ==> A x = B x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `l1:real^M->real^N` (X_CHOOSE_THEN `y1:real^N`
     STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `l2:real^M->real^N` (X_CHOOSE_THEN `y2:real^N`
      STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`l1:real^M->real^N`; `l2:real^M->real^N`; `y1:real^N`;
                 `y2:real^N`; `{p1:real^M,p2,p3,p4}`]
    MOI_REAL_AFFINE_EQ_ON_CONVEX_HULL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
      [ASSUME `!x:real^M. (A:real^M->real^N) x = l1 x + y1`;
       ASSUME `!x:real^M. (B:real^M->real^N) x = l2 x + y2`]) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 21. Rigidity of unfoldings: in any unfolding of a triangle the two       *)
(* regular maps agree on the triangle and the second apex is the mirror     *)
(* image of the first (it cannot coincide with it by injectivity).          *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_UNFOLD_SHAPE = prove
 (`!c t v q2 q3 p1 p2 (u:real^N->real^3).
     lf_simplicial_complex c /\
     moi_sba_tri c t v q2 q3 p1 p2 /\ moi_sba_unf c t u
     ==> ?A1 A2. moi_smo_regmap (convex hull {v,q2,q3,p1}) A1 /\
                 moi_smo_regmap (convex hull {v,q2,q3,p2}) A2 /\
                 (!x. x IN convex hull {v,q2,q3,p1} INTER moi_smo_open_star c t
                      ==> u x = A1 x) /\
                 (!x. x IN convex hull {v,q2,q3,p2} INTER moi_smo_open_star c t
                      ==> u x = A2 x) /\
                 A2 v = A1 v /\ A2 q2 = A1 q2 /\ A2 q3 = A1 q3 /\
                 A2 p2 = &2 / &3 % (A1 v + A1 q2 + A1 q3) - A1 p1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[moi_sba_tri] (ASSUME
    `moi_sba_tri (c:(real^N->bool)->bool) t v q2 q3 p1 p2`)) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `t:real^N->bool = convex hull {v,q2,q3}`)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_sba_unf] o check
    (fun th -> concl th =
       `moi_sba_unf c (convex hull {v,q2,q3}) (u:real^N->real^3)`)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `convex hull {v:real^N,q2,q3,p1}` o check
    (fun th -> is_forall(concl th) && free_in `u:real^N->real^3` (concl th) &&
               not (free_in `p1:real^N` (concl th)))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:real^N->real^3` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `convex hull {v:real^N,q2,q3,p2}` o check
    (fun th -> is_forall(concl th) && free_in `u:real^N->real^3` (concl th) &&
               not (free_in `p1:real^N` (concl th)))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A2:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`A1:real^N->real^3`; `A2:real^N->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(?l y. linear l /\ !x. (A1:real^N->real^3) x = l x + y) /\
    (?l y. linear l /\ !x. (A2:real^N->real^3) x = l x + y)`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN relative_interior (convex hull {v:real^N,q2,q3})
        ==> (A1:real^N->real^3) x = A2 x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(x:real^N) IN moi_smo_open_star c (convex hull {v,q2,q3}) /\
      x IN convex hull {v,q2,q3,p1} /\ x IN convex hull {v,q2,q3,p2}`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `convex hull {v:real^N,q2,q3}` RELATIVE_INTERIOR_SUBSET) THEN
      SUBGOAL_THEN
       `convex hull {v,q2,q3} SUBSET convex hull {v:real^N,q2,q3,p1} /\
        convex hull {v,q2,q3} SUBSET convex hull {v:real^N,q2,q3,p2}`
      MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ASM SET_TAC[]];
      ASM_MESON_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(A2:real^N->real^3) v = A1 v /\ A2 q2 = A1 q2 /\ A2 q3 = A1 q3`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `l1:real^N->real^3` (X_CHOOSE_THEN `y1:real^3`
      STRIP_ASSUME_TAC) o check (fun th -> is_exists(concl th) &&
        free_in `A1:real^N->real^3` (concl th) &&
        not(free_in `A2:real^N->real^3` (concl th)))) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `l2:real^N->real^3` (X_CHOOSE_THEN `y2:real^3`
      STRIP_ASSUME_TAC) o check (fun th -> is_exists(concl th) &&
        free_in `A2:real^N->real^3` (concl th) &&
        not(free_in `A1:real^N->real^3` (concl th)))) THEN
    MP_TAC(ISPECL [`l1:real^N->real^3`; `l2:real^N->real^3`; `y1:real^3`;
                   `y2:real^3`; `relative_interior(convex hull {v:real^N,q2,q3})`]
      MOI_REAL_AFFINE_EQ_ON_AFFINE_HULL) THEN
    SIMP_TAC[AFFINE_HULL_RELATIVE_INTERIOR; CONVEX_CONVEX_HULL;
             AFFINE_HULL_CONVEX_HULL] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE
        [ASSUME `!x:real^N. (A1:real^N->real^3) x = l1 x + y1`;
         ASSUME `!x:real^N. (A2:real^N->real^3) x = l2 x + y2`]) THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN ASM_SIMP_TAC[HULL_INC; IN_INSERT]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `moi_sba_reg ((A1:real^N->real^3) v) (A1 q2) (A1 q3) (A1 p1) /\
    moi_sba_reg ((A2:real^N->real^3) v) (A2 q2) (A2 q3) (A2 p2)`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`;
                     `A1:real^N->real^3`] MOI_SBA_REGMAP_4);
      MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p2:real^N`;
                     `A2:real^N->real^3`] MOI_SBA_REGMAP_4)] THEN
    ANTS_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[moi_sba_reg] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(A1:real^N->real^3) v`; `(A1:real^N->real^3) q2`;
                 `(A1:real^N->real^3) q3`; `(A1:real^N->real^3) p1`;
                 `(A2:real^N->real^3) p2`] MOI_SBA_REG_APEX) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `inv(&4) % (v + q2 + q3 + p1:real^N) IN
    relative_interior(convex hull {v,q2,q3,p1}) /\
    inv(&4) % (v + q2 + q3 + p2:real^N) IN
    relative_interior(convex hull {v,q2,q3,p2})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`;
                     `inv(&4) % (v + q2 + q3 + p1:real^N)`] MOI_SBA_RELINT_4);
      MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p2:real^N`;
                     `inv(&4) % (v + q2 + q3 + p2:real^N)`] MOI_SBA_RELINT_4)] THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
    MAP_EVERY EXISTS_TAC [`&1 / &4`; `&1 / &4`; `&1 / &4`; `&1 / &4`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(u:real^N->real^3) (inv(&4) % (v + q2 + q3 + p1)) =
    u (inv(&4) % (v + q2 + q3 + p2))`
  MP_TAC THENL
   [SUBGOAL_THEN
     `(u:real^N->real^3) (inv(&4) % (v + q2 + q3 + p1)) =
      A1 (inv(&4) % (v + q2 + q3 + p1)) /\
      (u:real^N->real^3) (inv(&4) % (v + q2 + q3 + p2)) =
      A2 (inv(&4) % (v + q2 + q3 + p2))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH
     `inv(&4) % (v + q2 + q3 + p:real^N) =
      &1 / &4 % v + &1 / &4 % q2 + &1 / &4 % q3 + &1 / &4 % p`] THEN
    ASM_SIMP_TAC[MOI_SBA_AFF_EVAL4;
                 REAL_ARITH `&1 / &4 + &1 / &4 + &1 / &4 + &1 / &4 = &1`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `inv(&4) % (v + q2 + q3 + p1:real^N) = inv(&4) % (v + q2 + q3 + p2)`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check
     (fun th -> is_forall(concl th) && free_in `u:real^N->real^3` (concl th) &&
                is_forall(snd(dest_forall(concl th))))) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[VECTOR_ARITH
     `inv(&4) % (v + q2 + q3 + p1:real^N) = inv(&4) % (v + q2 + q3 + p2) <=>
      p1 = p2`]]);;

(* ------------------------------------------------------------------------- *)
(* 22. Two unfoldings of the same triangle differ by one affine map of     *)
(* real^3.                                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_TRANS_SAME = prove
 (`!c t (u:real^N->real^3) u'.
     FINITE c /\ combinatorial_manifold 3 c /\ t IN c /\ aff_dim t = &2 /\
     moi_sba_unf c t u /\ moi_sba_unf c t u'
     ==> ?g. smooth_map_on (IMAGE u (moi_smo_open_star c t)) g /\
             !x. x IN moi_smo_open_star c t ==> g(u x) = u' x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_SBA_EXTREME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `v:real^N`]
    MOI_SBA_TRI_STRUCT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `q3:real^N`
    (X_CHOOSE_THEN `p1:real^N` (X_CHOOSE_THEN `p2:real^N` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `v:real^N`;
                 `q2:real^N`; `q3:real^N`; `p1:real^N`; `p2:real^N`;
                 `u:real^N->real^3`] MOI_SBA_UNFOLD_SHAPE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:real^N->real^3` (X_CHOOSE_THEN `A2:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `v:real^N`;
                 `q2:real^N`; `q3:real^N`; `p1:real^N`; `p2:real^N`;
                 `u':real^N->real^3`] MOI_SBA_UNFOLD_SHAPE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1':real^N->real^3` (X_CHOOSE_THEN `A2':real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(REWRITE_RULE[moi_sba_tri] (ASSUME
    `moi_sba_tri (c:(real^N->bool)->bool) t v q2 q3 p1 p2`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`;
                 `A1:real^N->real^3`] MOI_SBA_REGMAP_INV) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real^3->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(?l y. linear l /\ !x. (A1:real^N->real^3) x = l x + y) /\
    (?l y. linear l /\ !x. (A2:real^N->real^3) x = l x + y) /\
    (?l y. linear l /\ !x. (A1':real^N->real^3) x = l x + y) /\
    (?l y. linear l /\ !x. (A2':real^N->real^3) x = l x + y)`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN affine hull {v,q2,q3,p1} ==> (B1:real^3->real^N) (A1 x) = x`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?l y. linear l /\ !x. (A1':real^N->real^3) ((B1:real^3->real^N) x) = l x + y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `\y. (A1':real^N->real^3) ((B1:real^3->real^N) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z. z IN convex hull {v,q2,q3,p1}
        ==> (A1':real^N->real^3) ((B1:real^3->real^N) (A1 z)) = A1' z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPEC `{v:real^N,q2,q3,p1}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^N) IN convex hull {v,q2,q3,p1}` THENL
   [SUBGOAL_THEN
     `(u:real^N->real^3) x = A1 x /\ (u':real^N->real^3) x = A1' x`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull {v,q2,q3,p2}` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN moi_smo_open_star c t` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `convex hull {v:real^N,q2,q3}` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `convex hull {v:real^N,q2,q3,p1}` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `convex hull {v:real^N,q2,q3,p2}` RELATIVE_INTERIOR_SUBSET) THEN
    SUBGOAL_THEN
     `convex hull {v,q2,q3} SUBSET convex hull {v:real^N,q2,q3,p1}`
    MP_TAC THENL [MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~((x:real^N) IN convex hull {v,q2,q3,p1})` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(u:real^N->real^3) x = A2 x /\ (u':real^N->real^3) x = A2' x`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. (A1':real^N->real^3) ((B1:real^3->real^N) ((A2:real^N->real^3) z))`;
    `A2':real^N->real^3`; `v:real^N`; `q2:real^N`; `q3:real^N`; `p2:real^N`;
    `x:real^N`] MOI_SBA_AFF_EQ_HULL4) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(v:real^N) IN convex hull {v,q2,q3,p1} /\ q2 IN convex hull {v,q2,q3,p1} /\
    q3 IN convex hull {v,q2,q3,p1}`
  STRIP_ASSUME_TAC THENL [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH
   `&2 / &3 % (a + b + c) - d:real^3 =
    &2 / &3 % a + &2 / &3 % b + &2 / &3 % c + --(&1) % d`] THEN
  SUBGOAL_THEN
   `(B1:real^3->real^N)
      (&2 / &3 % (A1:real^N->real^3) v + &2 / &3 % A1 q2 + &2 / &3 % A1 q3 +
       --(&1) % A1 p1) =
    &2 / &3 % v + &2 / &3 % q2 + &2 / &3 % q3 + --(&1) % p1`
  SUBST1_TAC THENL
   [W(fun (asl,w) -> MP_TAC(ISPECL
      [`B1:real^3->real^N`; `&2 / &3`; `&2 / &3`; `&2 / &3`; `--(&1)`;
       `(A1:real^N->real^3) v`; `(A1:real^N->real^3) q2`;
       `(A1:real^N->real^3) q3`; `(A1:real^N->real^3) p1`] MOI_SBA_AFF_EVAL4)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `(B1:real^3->real^N) (A1 v) = v /\ B1 (A1 q2) = q2 /\ B1 (A1 q3) = q3 /\
      B1 ((A1:real^N->real^3) p1) = p1`
    (fun th -> REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC(ISPECL
    [`A1':real^N->real^3`; `&2 / &3`; `&2 / &3`; `&2 / &3`; `--(&1)`;
     `v:real^N`; `q2:real^N`; `q3:real^N`; `p1:real^N`] MOI_SBA_AFF_EVAL4)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 23. Transition maps between charts that are regular maps of one          *)
(* tetrahedron on the overlap: an affine map of real^3.                      *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_TRANS_GT = prove
 (`!c tet U V (phi:real^N->real^3) psi A A'.
     lf_simplicial_complex c /\ tet IN c /\ aff_dim tet = &3 /\
     moi_smo_regmap tet A /\ moi_smo_regmap tet A' /\
     U INTER V SUBSET tet /\
     (!x. x IN U INTER V ==> phi x = A x /\ psi x = A' x)
     ==> ?g. smooth_map_on (IMAGE phi (U INTER V)) g /\
             !x. x IN U INTER V ==> g(phi x) = psi x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(tet:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(tet:real^N->bool) = &3` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`]
    MOI_SBA_EXTREME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tet:real^N->bool`; `v:real^N`] MOI_SBA_TET_VERTS) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`]
      MOI_SBA_LF_SIMPLEX) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `q3:real^N`
    (X_CHOOSE_THEN `q4:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `tet:real^N->bool = convex hull {v,q2,q3,q4}`)) THEN
  MP_TAC(ISPECL [`v:real^N`; `q2:real^N`; `q3:real^N`; `q4:real^N`;
                 `A:real^N->real^3`] MOI_SBA_REGMAP_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^3->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  EXISTS_TAC `\y. (A':real^N->real^3) ((B:real^3->real^N) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_SMOOTH THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(phi:real^N->real^3) x = A x /\ (psi:real^N->real^3) x = A' x`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPEC `{v:real^N,q2,q3,q4}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 24. Two distinct triangles lie in at most one common tetrahedron.        *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_TWO_TRI_TET_SUBSET = prove
 (`!c t t' r r':real^N->bool.
     lf_simplicial_complex c /\
     t IN c /\ t' IN c /\ aff_dim t = &2 /\ aff_dim t' = &2 /\ ~(t = t') /\
     r IN c /\ r' IN c /\ aff_dim r = &3 /\ aff_dim r' = &3 /\
     t SUBSET r /\ t' SUBSET r /\ t SUBSET r' /\ t' SUBSET r'
     ==> r SUBSET r'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) INTER r' = r`
   (fun th -> MP_TAC th THEN SET_TAC[]) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `((r:real^N->bool) INTER r') face_of r` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`r:real^N->bool`; `r':real^N->bool`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((r:real^N->bool) INTER r') IN c` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o
                GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim((r:real^N->bool) INTER r') < &3` ASSUME_TAC THENL
   [UNDISCH_TAC `aff_dim(r:real^N->bool) = &3` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
    ASM_MESON_TAC[MOI_SBA_LF_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN c /\ aff_dim s = &2 /\ s SUBSET r INTER r'
                     ==> s = r INTER r'`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `aff_dim (s:real^N->bool) < aff_dim ((r:real^N->bool) INTER r')`
    MP_TAC THENL
     [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_INTER THEN ASM_MESON_TAC[MOI_SBA_LF_CONVEX];
        MATCH_MP_TAC MOI_SBA_LF_SUBSET_FACE THEN
        EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `aff_dim((r:real^N->bool) INTER r') < &3` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `t = (r:real^N->bool) INTER r' /\ t' = r INTER r'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_SBA_TWO_TRI_TET_UNIQUE = prove
 (`!c t t' r r':real^N->bool.
     lf_simplicial_complex c /\
     t IN c /\ t' IN c /\ aff_dim t = &2 /\ aff_dim t' = &2 /\ ~(t = t') /\
     r IN c /\ r' IN c /\ aff_dim r = &3 /\ aff_dim r' = &3 /\
     t SUBSET r /\ t' SUBSET r /\ t SUBSET r' /\ t' SUBSET r'
     ==> r = r'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC MOI_SBA_TWO_TRI_TET_SUBSET THENL
   [MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `t:real^N->bool`;
                          `t':real^N->bool`];
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `t:real^N->bool`;
                          `t':real^N->bool`]] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 25. The charts of the two families are homeomorphisms of open subsets of *)
(* the polyhedron minus the 1-skeleton onto open subsets of real^3.          *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_UNF_CONTINUOUS = prove
 (`!c t (u:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\ t IN c /\ aff_dim t = &2 /\
     moi_sba_unf c t u
     ==> u continuous_on moi_smo_open_star c t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_SBA_EXTREME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `v:real^N`]
    MOI_SBA_TRI_STRUCT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `q3:real^N`
    (X_CHOOSE_THEN `p1:real^N` (X_CHOOSE_THEN `p2:real^N` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `v:real^N`;
                 `q2:real^N`; `q3:real^N`; `p1:real^N`; `p2:real^N`;
                 `u:real^N->real^3`] MOI_SBA_UNFOLD_SHAPE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:real^N->real^3` (X_CHOOSE_THEN `A2:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `moi_smo_open_star c t =
    (convex hull {v,q2,q3,p1} INTER moi_smo_open_star c t) UNION
    (convex hull {v:real^N,q2,q3,p2} INTER moi_smo_open_star c t)`
  SUBST1_TAC THENL
   [MP_TAC(REWRITE_RULE[moi_sba_tri] (ASSUME
      `moi_sba_tri (c:(real^N->bool)->bool) t v q2 q3 p1 p2`)) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `moi_smo_open_star c t SUBSET
      convex hull {v,q2,q3,p1} UNION convex hull {v:real^N,q2,q3,p2}`
    MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNION] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real^N` THEN
      MP_TAC(ISPEC `convex hull {v:real^N,q2,q3}` RELATIVE_INTERIOR_SUBSET) THEN
      MP_TAC(ISPEC `convex hull {v:real^N,q2,q3,p1}` RELATIVE_INTERIOR_SUBSET) THEN
      MP_TAC(ISPEC `convex hull {v:real^N,q2,q3,p2}` RELATIVE_INTERIOR_SUBSET) THEN
      SUBGOAL_THEN
       `convex hull {v,q2,q3} SUBSET convex hull {v:real^N,q2,q3,p1}`
      MP_TAC THENL [MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ALL_TAC] THEN
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL THEN
  SUBGOAL_THEN
   `closed(convex hull {v:real^N,q2,q3,p1}) /\
    closed(convex hull {v:real^N,q2,q3,p2})`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT;
             FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CLOSED_IN_CLOSED] THEN
    EXISTS_TAC `convex hull {v:real^N,q2,q3,p1}` THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN
    EXISTS_TAC `convex hull {v:real^N,q2,q3,p2}` THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `A1:real^N->real^3` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC MOI_SBA_AFFINE_CONTINUOUS_ON THEN
    ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `A2:real^N->real^3` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC MOI_SBA_AFFINE_CONTINUOUS_ON THEN
    ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE]]);;

let MOI_SBA_CHART_GEN = prove
 (`!c v U (phi:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     U SUBSET moi_smo_open_star c {v} /\
     open_in (subtopology euclidean (UNIONS c)) U /\
     U SUBSET (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}) /\
     phi continuous_on U /\
     (!x y. x IN U /\ y IN U /\ phi x = phi y ==> x = y)
     ==> open_in (subtopology euclidean
                   (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})) U /\
         open (IMAGE phi U) /\
         homeomorphic_map
           (subtopology (subtopology euclidean
              (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})) U,
            subtopology euclidean (IMAGE phi U)) phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `U:real^N->bool`;
                 `phi:real^N->real^3`] MOI_SBA_IOD_FWD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `h':real^3->real^N`)) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    SUBGOAL_THEN
     `(UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}) INTER U =
      (U:real^N->bool)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 26. Chart conditions, covering and transition maps of the atlas formed   *)
(* by the tetrahedron charts and the unfolding charts.                       *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_CHART_OK_TET = prove
 (`!c tet U (phi:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\
     tet IN c /\ aff_dim tet = &3 /\ U = relative_interior tet /\
     moi_smo_regmap tet phi
     ==> open_in (subtopology euclidean
                   (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})) U /\
         open (IMAGE phi U) /\
         homeomorphic_map
           (subtopology (subtopology euclidean
              (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})) U,
            subtopology euclidean (IMAGE phi U)) phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> aff_dim s <= &3` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_DIM_LE3]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `U = relative_interior (tet:real^N->bool)`)) THEN
  SUBGOAL_THEN `~(tet:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(tet:real^N->bool) = &3` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`]
    MOI_SBA_EXTREME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `relative_interior tet = moi_smo_open_star c (tet:real^N->bool)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SBA_OPEN_STAR_TET THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SBA_CHART_GEN THEN EXISTS_TAC `v:real^N` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SBA_OPEN_STAR_MONO THEN ASM_REWRITE_TAC[SING_SUBSET];
    MATCH_MP_TAC MOI_SBA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SBA_STAR_IN_XP THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    MATCH_MP_TAC MOI_SBA_AFFINE_CONTINUOUS_ON THEN
    ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tet:real^N->bool`; `v:real^N`] MOI_SBA_TET_VERTS) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`]
        MOI_SBA_LF_SIMPLEX) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `q3:real^N`
      (X_CHOOSE_THEN `q4:real^N` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC MOI_SBA_REGMAP_INJ THEN
    MAP_EVERY EXISTS_TAC
     [`v:real^N`; `q2:real^N`; `q3:real^N`; `q4:real^N`;
      `phi:real^N->real^3`] THEN
    UNDISCH_TAC `moi_smo_regmap tet (phi:real^N->real^3)` THEN
    UNDISCH_TAC `(x:real^N) IN moi_smo_open_star c tet` THEN
    UNDISCH_TAC `(y:real^N) IN moi_smo_open_star c tet` THEN
    SUBST1_TAC(SYM(ASSUME
      `relative_interior tet = moi_smo_open_star c (tet:real^N->bool)`)) THEN
    SUBST1_TAC(ASSUME `tet = convex hull {v:real^N,q2,q3,q4}`) THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `convex hull {v:real^N,q2,q3,q4}` RELATIVE_INTERIOR_SUBSET) THEN
    ASM SET_TAC[]]);;

let MOI_SBA_CHART_OK_UNF = prove
 (`!c t U (phi:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\
     t IN c /\ aff_dim t = &2 /\ U = moi_smo_open_star c t /\
     moi_sba_unf c t phi
     ==> open_in (subtopology euclidean
                   (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})) U /\
         open (IMAGE phi U) /\
         homeomorphic_map
           (subtopology (subtopology euclidean
              (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})) U,
            subtopology euclidean (IMAGE phi U)) phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check
    (fun th -> concl th = `U = moi_smo_open_star c (t:real^N->bool)`)) THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_SBA_EXTREME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_SBA_CHART_GEN THEN EXISTS_TAC `v:real^N` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SBA_OPEN_STAR_MONO THEN ASM_REWRITE_TAC[SING_SUBSET];
    MATCH_MP_TAC MOI_SBA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SBA_STAR_IN_XP THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    MATCH_MP_TAC MOI_SBA_UNF_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[moi_sba_unf]]);;

let MOI_SBA_CHART_OK = prove
 (`!c U (phi:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c
     ==> open_in (subtopology euclidean
                   (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})) U /\
         open (IMAGE phi U) /\
         homeomorphic_map
           (subtopology (subtopology euclidean
              (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})) U,
            subtopology euclidean (IMAGE phi U)) phi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_UNION; MOI_SBA_TET_ATLAS_IN2; MOI_SBA_UNFOLD_ATLAS_IN] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC MOI_SBA_CHART_OK_TET THEN EXISTS_TAC `tet:real^N->bool`;
    MATCH_MP_TAC MOI_SBA_CHART_OK_UNF THEN EXISTS_TAC `t:real^N->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_SBA_ATLAS_COVER = prove
 (`!c x:real^N.
     FINITE c /\ combinatorial_manifold 3 c /\
     x IN (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})
     ==> ?U phi. (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c /\
                 x IN U`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_SBA_CARRIER) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `aff_dim(r:real^N->bool) = &2 \/ aff_dim r = &3`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`]
      MOI_SBA_DIM_LE3) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(aff_dim(r:real^N->bool) <= &1)` MP_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC
       `(x:real^N) IN UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}` THEN
      REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
      MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[];
      INT_ARITH_TAC];
    ALL_TAC] THEN
  (SUBGOAL_THEN `~(r:real^N->bool = {})` ASSUME_TAC THENL
    [ASM_MESON_TAC[RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY]; ALL_TAC]) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`]
    MOI_SBA_EXTREME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `aff_dim(r:real^N->bool) = &2 \/ aff_dim r = &3` THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`; `v:real^N`]
      MOI_SBA_UNFOLD_STAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->real^3` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`moi_smo_open_star c (r:real^N->bool)`; `w:real^N->real^3`] THEN
    REWRITE_TAC[IN_UNION; MOI_SBA_UNFOLD_ATLAS_IN] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MOI_SBA_RELINT_IN_STAR; SUBSET]];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`; `v:real^N`]
      MOI_SBA_TET_STAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`relative_interior (r:real^N->bool)`;
                          `A:real^N->real^3`] THEN
    ASM_REWRITE_TAC[IN_UNION]]);;

let MOI_SBA_CHART_ON_TET = prove
 (`!c U (phi:real^N->real^3) tet.
     FINITE c /\ combinatorial_manifold 3 c /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c /\
     tet IN c /\ aff_dim tet = &3 /\ ~(U INTER relative_interior tet = {})
     ==> relative_interior tet SUBSET U /\
         ?A. moi_smo_regmap tet A /\
             !x. x IN relative_interior tet ==> phi x = A x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_UNION; MOI_SBA_TET_ATLAS_IN2; MOI_SBA_UNFOLD_ATLAS_IN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check
      (fun th -> concl th = `U = relative_interior (tet':real^N->bool)`)) THEN
    SUBGOAL_THEN `tet':real^N->bool = tet` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_SBA_RELINT_EQ THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET_REFL] THEN EXISTS_TAC `phi:real^N->real^3` THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST_ALL_TAC o check
      (fun th -> concl th = `U = moi_smo_open_star c (t:real^N->bool)`)) THEN
    SUBGOAL_THEN `(t:real^N->bool) SUBSET tet` ASSUME_TAC THENL
     [UNDISCH_TAC
       `~(moi_smo_open_star c t INTER relative_interior (tet:real^N->bool) = {})` THEN
      ASM_SIMP_TAC[MOI_SBA_OPEN_STAR_ALT] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      MP_TAC(ISPEC `tet:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [TRANS_TAC SUBSET_TRANS `moi_smo_open_star c (tet:real^N->bool)` THEN
      ASM_SIMP_TAC[MOI_SBA_RELINT_IN_STAR] THEN
      MATCH_MP_TAC MOI_SBA_OPEN_STAR_MONO THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tet:real^N->bool` o CONJUNCT2 o
      GEN_REWRITE_RULE I [moi_sba_unf]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `A:real^N->real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      MATCH_MP_TAC(SET_RULE `!s. x IN s /\ s SUBSET t ==> (x:real^N) IN t`) THEN
      EXISTS_TAC `moi_smo_open_star c (tet:real^N->bool)` THEN
      ASM_SIMP_TAC[MOI_SBA_OPEN_STAR_MONO] THEN
      ASM_MESON_TAC[MOI_SBA_RELINT_IN_STAR; SUBSET]]]);;

let MOI_SBA_UU_CARRIER = prove
 (`!c t t' y:real^N.
     lf_simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &3) /\
     t IN c /\ t' IN c /\ aff_dim t = &2 /\ aff_dim t' = &2 /\ ~(t = t') /\
     y IN moi_smo_open_star c t /\ y IN moi_smo_open_star c t'
     ==> ?r. r IN c /\ aff_dim r = &3 /\ t SUBSET r /\ t' SUBSET r /\
             y IN relative_interior r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_SBA_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_STAR_SUBSET_UNIONS; SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^N->bool) SUBSET r /\ (t':real^N->bool) SUBSET r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^N) IN moi_smo_open_star c t` THEN
    UNDISCH_TAC `(y:real^N) IN moi_smo_open_star c t'` THEN
    ASM_SIMP_TAC[MOI_SBA_OPEN_STAR_ALT; IN_ELIM_THM] THEN
    MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN c /\ aff_dim s = &2 /\ s SUBSET r /\
                     aff_dim r = &2 ==> s = r`
  (LABEL_TAC "eqr") THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `aff_dim (s:real^N->bool) < aff_dim (r:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_SBA_LF_CONVEX];
        MATCH_MP_TAC MOI_SBA_LF_SUBSET_FACE THEN
        EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `r:real^N->bool`] AFF_DIM_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `aff_dim(r:real^N->bool) <= &3` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `aff_dim(r:real^N->bool) = &2` THENL
   [USE_THEN "eqr" (fun th -> MP_TAC(SPEC `t:real^N->bool` th) THEN
                              MP_TAC(SPEC `t':real^N->bool` th)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    POP_ASSUM MP_TAC THEN INT_ARITH_TAC]);;

let MOI_SBA_TRANS_VIA_TET = prove
 (`!c U (phi:real^N->real^3) V psi r.
     FINITE c /\ combinatorial_manifold 3 c /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c /\
     (V,psi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c /\
     r IN c /\ aff_dim r = &3 /\
     ~(U INTER V = {}) /\ U INTER V SUBSET relative_interior r
     ==> ?g. smooth_map_on (IMAGE phi (U INTER V)) g /\
             !x. x IN U INTER V ==> g(phi x) = psi x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `U:real^N->bool`;
                 `phi:real^N->real^3`; `r:real^N->bool`] MOI_SBA_CHART_ON_TET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `A:real^N->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `V:real^N->bool`;
                 `psi:real^N->real^3`; `r:real^N->bool`] MOI_SBA_CHART_ON_TET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `A':real^N->real^3` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC MOI_SBA_TRANS_GT THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `r:real^N->bool`;
                        `A:real^N->real^3`; `A':real^N->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ASM_MESON_TAC[SUBSET]]);;

let MOI_SBA_ATLAS_TRANS = prove
 (`!c U (phi:real^N->real^3) V psi.
     FINITE c /\ combinatorial_manifold 3 c /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c /\
     (V,psi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c
     ==> ?g. smooth_map_on (IMAGE phi (U INTER V)) g /\
             !x. x IN U INTER V ==> g(phi x) = psi x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> aff_dim s <= &3` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_DIM_LE3]; ALL_TAC] THEN
  ASM_CASES_TAC `U INTER V:real^N->bool = {}` THENL
   [EXISTS_TAC `\y:real^3. vec 0:real^3` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(?r. r IN c /\ aff_dim r = &3 /\ U INTER V SUBSET relative_interior r) \/
    (?t. t IN c /\ aff_dim t = &2 /\ U = moi_smo_open_star c t /\
         V = moi_smo_open_star c t /\ moi_sba_unf c t phi /\
         moi_sba_unf c t (psi:real^N->real^3))`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(U:real^N->bool,(phi:real^N->real^3)) IN
       moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c`;
      `(V:real^N->bool,(psi:real^N->real^3)) IN
       moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c`] THEN
    REWRITE_TAC[IN_UNION; MOI_SBA_TET_ATLAS_IN2; MOI_SBA_UNFOLD_ATLAS_IN] THEN
    STRIP_TAC THEN STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `tet':real^N->bool` THEN ASM SET_TAC[];
      DISJ1_TAC THEN EXISTS_TAC `tet:real^N->bool` THEN ASM SET_TAC[];
      DISJ1_TAC THEN EXISTS_TAC `tet:real^N->bool` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `t:real^N->bool = t'` THENL
     [DISJ2_TAC THEN EXISTS_TAC `t:real^N->bool` THEN ASM_MESON_TAC[];
      DISJ1_TAC] THEN
    UNDISCH_TAC `~(U INTER V:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`;
                   `t':real^N->bool`; `x0:real^N`] MOI_SBA_UU_CARRIER) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET; IN_INTER] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`;
                   `t':real^N->bool`; `y:real^N`] MOI_SBA_UU_CARRIER) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r':real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `r':real^N->bool = r` (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC MOI_SBA_TWO_TRI_TET_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`c:(real^N->bool)->bool`; `t:real^N->bool`; `t':real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC MOI_SBA_TRANS_VIA_TET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[INTER_IDEMPOT] THEN MATCH_MP_TAC MOI_SBA_TRANS_SAME THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SBA_ATLAS = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold 3 c
     ==> smooth_manifold_atlas
           (subtopology euclidean
              (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}))
           (moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[smooth_manifold_atlas; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_SBA_CHART_OK THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_SBA_ATLAS_COVER THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_SBA_ATLAS_TRANS THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 27. Star charts and the main theorem C3.                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_SBA_STAR_ATLAS_IN = prove
 (`!c v U (kappa:real^N->real^3).
     (U,kappa) IN moi_smo_star_atlas c v <=>
     (U,kappa) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                  moi_smo_edge_atlas c /\
     !x t. x IN U /\ &0 < t /\ t <= &1
           ==> v + t % (x - v) IN U /\ kappa(v + t % (x - v)) = t % kappa x`,
  REWRITE_TAC[moi_smo_star_atlas; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let MOI_SBA_TET_STAR_CHART = prove
 (`!c tet v:real^N.
     FINITE c /\ combinatorial_manifold 3 c /\ tet IN c /\ aff_dim tet = &3 /\
     v extreme_point_of tet
     ==> ?A. (relative_interior tet,A) IN moi_smo_star_atlas c v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`; `v:real^N`]
    MOI_SBA_TET_STAR) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `A:real^N->real^3` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MOI_SBA_STAR_ATLAS_IN; IN_UNION]);;

let MOI_SBA_TRI_STAR_CHART = prove
 (`!c t v:real^N.
     FINITE c /\ combinatorial_manifold 3 c /\ t IN c /\ aff_dim t = &2 /\
     v extreme_point_of t
     ==> ?w. (moi_smo_open_star c t,w) IN moi_smo_star_atlas c v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `v:real^N`]
    MOI_SBA_UNFOLD_STAR) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N->real^3` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MOI_SBA_STAR_ATLAS_IN; IN_UNION] THEN
  DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[MOI_SBA_UNFOLD_ATLAS_IN] THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_SMO_BASE = prove
 (`!u:N->bool. MOI_SMO_BASE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[MOI_SMO_BASE_STATEMENT] THEN
  X_GEN_TAC `c:(real^N->bool)->bool` THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SBA_ATLAS THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SBA_TET_STAR_CHART THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SBA_TRI_STAR_CHART THEN
    ASM_REWRITE_TAC[]]);;

