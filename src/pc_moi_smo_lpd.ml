needs "src/pc_moi_smo_edge.ml";;
needs "src/pc_moi_smo_link.ml";;
needs "src/pc_moi_smo_vertex.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_smo_lpd (route M): C7, MOI_SMO_LINK_PD_STATEMENT.  For a vertex v  *)
(* of a finite combinatorial 3-manifold c the link carries a subdivision L   *)
(* and a homeomorphism h onto S^2 that is conically piecewise smooth for the *)
(* link atlas.  h is the radial projection of the PL homeomorphism F of the  *)
(* link onto the boundary of a tetrahedron about 0 (from pl_sphere 2), L a   *)
(* subdivision on which F is affine.                                         *)
(* The first part gives basic algebra of the unit map, cell smoothness,      *)
(* kernels.                                                                  *)
(* ========================================================================= *)

let MOI_SLP_SC_LF = prove
 (`!L:(real^N->bool)->bool. simplicial_complex L ==> lf_simplicial_complex L`,
  MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]);;

let MOI_SLP_AFFINE_HULL_4 = prove
 (`!a b c d:real^N.
     affine hull {a,b,c,d} =
     {u % a + v % b + w % c + t % d | u + v + w + t = &1}`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[AFFINE_HULL_FINITE; FINITE_INSERT; FINITE_RULES] THEN
  SIMP_TAC[AFFINE_HULL_FINITE_STEP; FINITE_INSERT; FINITE_RULES] THEN
  REWRITE_TAC[REAL_ARITH `x - y = z:real <=> x = y + z`;
              VECTOR_ARITH `x - y = z:real^N <=> x = y + z`] THEN
  REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN SET_TAC[]);;

let MOI_SLP_AFFINE_HULL_4_UNIV = prove
 (`!a b c d:real^3.
     ~affine_dependent {a,b,c,d} /\ ~(a = b) /\ ~(a = c) /\ ~(a = d) /\
     ~(b = c) /\ ~(b = d) /\ ~(c = d)
     ==> affine hull {a,b,c,d} = (:real^3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN
  ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC);;

(* Every point of real^3 is an affine combination of the images of four      *)
(* points whose images are affinely independent.                             *)

let MOI_SLP_AFFINE_ONTO4 = prove
 (`!(A:real^N->real^3) p1 p2 p3 p4.
     (?l y. linear l /\ !x. A x = l x + y) /\
     ~affine_dependent {A p1,A p2,A p3,A p4} /\
     ~(A p1 = A p2) /\ ~(A p1 = A p3) /\ ~(A p1 = A p4) /\
     ~(A p2 = A p3) /\ ~(A p2 = A p4) /\ ~(A p3 = A p4)
     ==> !z. ?x. x IN affine hull {p1,p2,p3,p4} /\ A x = z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `z:real^3` THEN
  MP_TAC(ISPECL [`(A:real^N->real^3) p1`; `(A:real^N->real^3) p2`;
                 `(A:real^N->real^3) p3`; `(A:real^N->real^3) p4`]
    MOI_SLP_AFFINE_HULL_4_UNIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^3` o MATCH_MP (SET_RULE
    `s = (:real^3) ==> !x. x IN s`)) THEN
  REWRITE_TAC[MOI_SLP_AFFINE_HULL_4; IN_ELIM_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u1:real`; `u2:real`; `u3:real`; `u4:real`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `u1 % p1 + u2 % p2 + u3 % p3 + u4 % (p4:real^N)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOI_SLP_AFFINE_HULL_4; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`u1:real`; `u2:real`; `u3:real`; `u4:real`] THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[MOI_SBA_AFF_EVAL4]]);;

(* ------------------------------------------------------------------------- *)
(* The unit map y |-> y / |y|.                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_UNIT_CMUL = prove
 (`!c y:real^N. &0 < c ==> inv(norm(c % y)) % (c % y) = inv(norm y) % y`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < c ==> abs c = c`] THEN
  ASM_CASES_TAC `y:real^N = vec 0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_INV_MUL] THEN
  UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD);;

let MOI_SLP_UNIT_NORM = prove
 (`!y:real^N. ~(y = vec 0) ==> norm(inv(norm y) % y) = &1`,
  SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0]);;

let MOI_SLP_UNIT_EQ = prove
 (`!y z:real^N.
     ~(y = vec 0) /\ ~(z = vec 0) /\ inv(norm y) % y = inv(norm z) % z
     ==> y = (norm y / norm z) % z`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x:real^N. norm(y:real^N) % x`) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID] THEN
  REWRITE_TAC[real_div]);;

let MOI_SLP_OPEN_NONZERO = prove
 (`open {z:real^N | ~(z = vec 0)}`,
  REWRITE_TAC[SET_RULE `{z:real^N | ~(z = a)} = (:real^N) DELETE a`] THEN
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV]);;

let MOI_SLP_INV_NORM_SMOOTH = prove
 (`!s. open s /\ (!y:real^N. y IN s ==> ~(y = vec 0))
       ==> smooth_map_on s (\y. lift(inv(norm y)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift(norm y)`]
    SMOOTH_MAP_ON_LIFT_INV) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[NORM_EQ_0] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. y`] SMOOTH_MAP_ON_LIFT_NORM) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_ID]);;

let MOI_SLP_UNIT_SMOOTH = prove
 (`!s. open s /\ (!y:real^N. y IN s ==> ~(y = vec 0))
       ==> smooth_map_on s (\y. inv(norm y) % y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift(inv(norm y))`;
                 `\y:real^N. y`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_ID; MOI_SLP_INV_NORM_SMOOTH]);;

let MOI_SLP_UNIT_KERNEL = prove
 (`!y w:real^N.
     ~(y = vec 0) /\ frechet_derivative (\y. inv(norm y) % y) (at y) w = vec 0
     ==> ?a. w = a % y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\y:real^N. lift(inv(norm y))) has_derivative
     frechet_derivative (\y:real^N. lift(inv(norm y))) (at y)) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{z:real^N | ~(z = vec 0)}`; `\y:real^N. lift(inv(norm y))`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    REWRITE_TAC[MOI_SLP_OPEN_NONZERO] THEN ANTS_TAC THENL
     [MATCH_MP_TAC MOI_SLP_INV_NORM_SMOOTH THEN
      REWRITE_TAC[MOI_SLP_OPEN_NONZERO; IN_ELIM_THM];
      DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  ABBREV_TAC `D = frechet_derivative (\y:real^N. lift(inv(norm y))) (at y)` THEN
  MP_TAC(ISPECL [`\y:real^N. inv(norm y)`; `\h:real^N. drop((D:real^N->real^1) h)`;
                 `\y:real^N. y`; `\h:real^N. h`; `y:real^N`]
    HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX; HAS_DERIVATIVE_ID] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  EXISTS_TAC `--(norm(y:real^N) * drop((D:real^N->real^1) w))` THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x:real^N. norm(y:real^N) % x`) THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; VECTOR_MUL_RZERO] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID] THEN
  VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tangent spaces of cells, affine hulls, and cell smoothness.               *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_TANGENT_MONO = prove
 (`!s t:real^N->bool.
     s SUBSET t ==> moi_smo_tangent s SUBSET moi_smo_tangent t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_smo_tangent] THEN
  MATCH_MP_TAC SPAN_MONO THEN ASM SET_TAC[]);;

let MOI_SLP_AFF_TANGENT = prove
 (`!s x w:real^N.
     x IN affine hull s /\ w IN moi_smo_tangent s ==> x + w IN affine hull s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_smo_tangent s SUBSET {u - x | u IN affine hull (s:real^N->bool)}`
  MP_TAC THENL
   [REWRITE_TAC[moi_smo_tangent] THEN MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^N`] THEN STRIP_TAC THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `(y - z) + x:real^N` THEN
      CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
      SUBGOAL_THEN `(y - z) + x:real^N = x + &1 % (y - z)` SUBST1_TAC THENL
       [VECTOR_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
      ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC];
      MATCH_MP_TAC AFFINE_DIFFS_SUBSPACE THEN
      ASM_REWRITE_TAC[AFFINE_AFFINE_HULL]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `x + u - x:real^N = u`]]);;

let MOI_SLP_CELL_SMOOTH_EQ = prove
 (`!s (f:real^N->real^M) g.
     moi_smo_cell_smooth s f /\ (!x. x IN s ==> f x = g x)
     ==> moi_smo_cell_smooth s g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_smo_cell_smooth] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^N->real^M` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_SLP_CELL_SMOOTH_SUBSET = prove
 (`!s t (f:real^N->real^M).
     moi_smo_cell_smooth s f /\ t SUBSET s ==> moi_smo_cell_smooth t f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_smo_cell_smooth] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^M` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `s:real^N->bool`] MOI_SLP_TANGENT_MONO) THEN
    ASM SET_TAC[]]);;

(* Chain rule through an affine map.                                         *)

let MOI_SLP_CHAIN_AFFINE = prove
 (`!(P:real^M->real^K) (l:real^N->real^M) y x w.
     linear l /\ P differentiable (at (l x + y))
     ==> frechet_derivative (\x. P(l x + y)) (at x) w =
         frechet_derivative P (at (l x + y)) (l w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\x:real^N. l x + y:real^M) has_derivative l) (at x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`l:real^N->real^M`; `l:real^N->real^M`;
                   `\x:real^N. y:real^M`; `\h:real^N. vec 0:real^M`;
                   `at (x:real^N)`] HAS_DERIVATIVE_ADD) THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; HAS_DERIVATIVE_CONST] THEN
    REWRITE_TAC[VECTOR_ADD_RID; ETA_AX];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. l x + y:real^M`; `P:real^M->real^K`;
                 `l:real^N->real^M`;
                 `frechet_derivative (P:real^M->real^K)
                    (at ((l:real^N->real^M) x + y))`;
                 `x:real^N`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]));;

(* The general cell-smoothness criterion: P smooth on an open set W with     *)
(* radial kernels (the unit map, the gnomonic projection), composed with an  *)
(* affine map whose linear part sends no tangent vector of s to a multiple  *)
(* of the image point.                                                       *)

let MOI_SLP_CELL_SMOOTH_GEN = prove
 (`!(P:real^3->real^M) W (l:real^N->real^3) y s.
     open W /\ smooth_map_on W P /\
     (!z w. z IN W /\ frechet_derivative P (at z) w = vec 0 ==> ?a. w = a % z) /\
     linear l /\ (!x. x IN s ==> l x + y IN W) /\
     (!x w a. x IN s /\ w IN moi_smo_tangent s /\ l w = a % (l x + y)
              ==> w = vec 0)
     ==> moi_smo_cell_smooth s (\x. P(l x + y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_smo_cell_smooth] THEN
  EXISTS_TAC `{x:real^N | l x + y IN (W:real^3->bool)}` THEN
  EXISTS_TAC `\x:real^N. (P:real^3->real^M)(l x + y)` THEN
  SUBGOAL_THEN `open {x:real^N | l x + y IN (W:real^3->bool)}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ADD THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; CONTINUOUS_CONST];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
    MP_TAC(ISPECL [`{x:real^N | l x + y IN (W:real^3->bool)}`; `W:real^3->bool`;
                   `\x:real^N. l x + y:real^3`; `P:real^3->real^M`]
      SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
      MATCH_MP_TAC MOI_SBA_AFFINE_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`l:real^N->real^3`; `y:real^3`] THEN
      ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `w:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(P:real^3->real^M) differentiable (at ((l:real^N->real^3) x + y))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `W:real^3->bool` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `frechet_derivative (\x:real^N. (P:real^3->real^M)(l x + y)) (at x) w =
      vec 0` THEN
    MP_TAC(ISPECL [`P:real^3->real^M`; `l:real^N->real^3`; `y:real^3`;
                   `x:real^N`; `w:real^N`] MOI_SLP_CHAIN_AFFINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?a. (l:real^N->real^3) w = a % (l x + y)` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:real^N`; `a:real`] THEN ASM_REWRITE_TAC[]]);;

(* The kernel condition from: the affine map has no zero on the affine hull  *)
(* and its linear part is injective on the tangent space.                    *)

let MOI_SLP_KERNEL_COND = prove
 (`!(l:real^N->real^3) y s.
     linear l /\ (!x. x IN affine hull s ==> ~(l x + y = vec 0)) /\
     (!w. w IN moi_smo_tangent s /\ l w = vec 0 ==> w = vec 0)
     ==> !x w a. x IN s /\ w IN moi_smo_tangent s /\ l w = a % (l x + y)
                 ==> w = vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "nz") (LABEL_TAC "inj"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `a = &0` THENL
   [REMOVE_THEN "inj" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  REMOVE_THEN "nz" (MP_TAC o SPEC `x + (--inv a) % w:real^N`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MOI_SLP_AFF_TANGENT THEN
    ASM_SIMP_TAC[HULL_INC] THEN REWRITE_TAC[moi_smo_tangent] THEN
    MATCH_MP_TAC SPAN_MUL THEN ASM_REWRITE_TAC[GSYM moi_smo_tangent];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(a = &0) ==> --inv a * a = -- &1`] THEN
  REWRITE_TAC[VECTOR_ARITH `(a + -- &1 % (a + b)) + b:real^N = vec 0`]);;

(* ------------------------------------------------------------------------- *)
(* Radial projection of the relative frontier of a 3-dimensional convex body *)
(* onto S^2, and PL maps composed with affine maps.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_RADIAL_HOMEO = prove
 (`!k c0 (A:real^N->real^3).
     convex k /\ bounded k /\ c0 IN relative_interior k /\
     (?l y. linear l /\ !x. A x = l x + y) /\ A c0 = vec 0 /\
     (!x y. x IN affine hull k /\ y IN affine hull k /\ A x = A y ==> x = y) /\
     (!z. ?x. x IN affine hull k /\ A x = z)
     ==> ?g. homeomorphism (relative_frontier k,sphere(vec 0,&1))
                           ((\x. inv(norm(A x)) % A x),g)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "aff")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (LABEL_TAC "onto"))))))) THEN
  SUBGOAL_THEN `relative_frontier k SUBSET affine hull (k:real^N->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    MP_TAC(ISPEC `k:real^N->bool` CLOSURE_SUBSET_AFFINE_HULL) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c0:real^N) IN affine hull k` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `k:real^N->bool`]
      HULL_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((c0:real^N) IN relative_frontier k)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[relative_frontier; IN_DIFF]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN relative_frontier k ==> ~(A x = vec 0:real^3)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `x:real^N = c0` (fun th -> ASM_MESON_TAC[th]) THEN
    REMOVE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N t. A(c0 + t % (x - c0)) = t % (A x):real^3`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC MOI_SBA_AFFINE_HOMOG THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
  ASM_SIMP_TAC[COMPACT_RELATIVE_FRONTIER_BOUNDED] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:real^N. inv(norm((A:real^N->real^3) x)) % A x) =
                  (\y:real^3. inv(norm y) % y) o A` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[MOI_SBA_AFFINE_CONTINUOUS_ON] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC MOI_SLP_UNIT_SMOOTH THEN
      REWRITE_TAC[MOI_SLP_OPEN_NONZERO; IN_ELIM_THM];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      FIRST_ASSUM ACCEPT_TAC];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN
      ASM_SIMP_TAC[MOI_SLP_UNIT_NORM];
      REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_IMAGE] THEN
      X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
      REMOVE_THEN "onto" (MP_TAC o SPEC `u:real^3`) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(x:real^N = c0)` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `norm(u:real^3) = &1` THEN
        UNDISCH_TAC `(A:real^N->real^3) c0 = u` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[NORM_0] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`k:real^N->bool`; `c0:real^N`; `x - c0:real^N`]
        RAY_TO_RELATIVE_FRONTIER) THEN
      ASM_REWRITE_TAC[VECTOR_SUB_EQ; VECTOR_ARITH `c + x - c:real^N = x`] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `c0 + d % (x - c0):real^N` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[MOI_SLP_UNIT_CMUL; REAL_INV_1; VECTOR_MUL_LID]];
    REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(A:real^N->real^3) x1`; `(A:real^N->real^3) x2`]
      MOI_SLP_UNIT_EQ) THEN
    ASM_SIMP_TAC[] THEN
    ABBREV_TAC `mu = norm((A:real^N->real^3) x1) / norm((A:real^N->real^3) x2)` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 < mu` ASSUME_TAC THENL
     [EXPAND_TAC "mu" THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_SIMP_TAC[NORM_POS_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN `x1 = c0 + mu % (x2 - c0):real^N` ASSUME_TAC THENL
     [REMOVE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
        ASM_REWRITE_TAC[AFFINE_AFFINE_HULL] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `mu = &1` THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    ASM_CASES_TAC `mu < &1` THENL
     [MP_TAC(ISPECL [`k:real^N->bool`; `&1 - mu`; `x2:real^N`; `c0:real^N`]
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(x2:real^N) IN relative_frontier k` THEN
          REWRITE_TAC[relative_frontier] THEN SET_TAC[];
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `x2 - (&1 - mu) % (x2 - c0):real^N = x1` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(x1:real^N) IN relative_frontier k` THEN
      REWRITE_TAC[relative_frontier] THEN SET_TAC[];
      SUBGOAL_THEN `&1 < mu` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`k:real^N->bool`; `&1 - inv mu`; `x1:real^N`; `c0:real^N`]
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          FIRST_ASSUM ACCEPT_TAC;
          UNDISCH_TAC `(x1:real^N) IN relative_frontier k` THEN
          REWRITE_TAC[relative_frontier] THEN SET_TAC[];
          SUBGOAL_THEN `inv mu < &1` MP_TAC THENL
           [ASM_SIMP_TAC[REAL_INV_LT_1]; REAL_ARITH_TAC];
          SUBGOAL_THEN `&0 < inv mu` MP_TAC THENL
           [ASM_SIMP_TAC[REAL_LT_INV_EQ]; REAL_ARITH_TAC]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `x1 - (&1 - inv mu) % (x1 - c0):real^N = c0 + (inv mu * mu) % (x2 - c0)`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                   VECTOR_ARITH `c + x - c:real^N = x`] THEN
      UNDISCH_TAC `(x2:real^N) IN relative_frontier k` THEN
      REWRITE_TAC[relative_frontier] THEN SET_TAC[]]]);;

let MOI_SLP_PL_AFFINE_COMPOSE = prove
 (`!s (f:real^M->real^N) (A:real^N->real^P).
     pl_map_on s f /\ (?l y. linear l /\ !x. A x = l x + y)
     ==> pl_map_on s (\x. A(f x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_map_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `lA:real^N->real^P`
    (X_CHOOSE_THEN `yA:real^P` STRIP_ASSUME_TAC))) THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:(real^M->bool)->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
      STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`(lA:real^N->real^P) o (l:real^M->real^N)`;
                        `(lA:real^N->real^P) y + yA`] THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE; o_THM; LINEAR_ADD] THEN
  REWRITE_TAC[VECTOR_ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Regular maps of 3-simplices are affine bijections of the affine hull onto *)
(* real^3; the PL map Fm of the link onto the boundary of a tetrahedron      *)
(* about 0, its radial projection, and the subdivision L (the setup).        *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_SIMPLEX3_VERTS = prove
 (`!k:real^N->bool.
     &3 simplex k
     ==> ?p1 p2 p3 p4. ~(p1 = p2) /\ ~(p1 = p3) /\ ~(p1 = p4) /\ ~(p2 = p3) /\
                       ~(p2 = p4) /\ ~(p3 = p4) /\
                       ~affine_dependent {p1,p2,p3,p4} /\
                       k = convex hull {p1,p2,p3,p4}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?p:real^N. p IN C` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `&(CARD({}:real^N->bool)):int = &3 + &1` THEN
    REWRITE_TAC[CARD_CLAUSES] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `p:real^N`] MOI_SBA_TET_VERTS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]];
    MESON_TAC[]]);;

let MOI_SLP_REGMAP_PROPS = prove
 (`!p1 p2 p3 p4:real^N (A:real^N->real^3).
     ~(p1 = p2) /\ ~(p1 = p3) /\ ~(p1 = p4) /\ ~(p2 = p3) /\ ~(p2 = p4) /\
     ~(p3 = p4) /\ ~affine_dependent {p1,p2,p3,p4} /\
     moi_smo_regmap (convex hull {p1,p2,p3,p4}) A
     ==> (?l y. linear l /\ !x. A x = l x + y) /\
         (!x y. x IN affine hull {p1,p2,p3,p4} /\
                y IN affine hull {p1,p2,p3,p4} /\ A x = A y ==> x = y) /\
         (!z. ?x. x IN affine hull {p1,p2,p3,p4} /\ A x = z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?l y. linear l /\ !x. (A:real^N->real^3) x = l x + y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_REGMAP_AFFINE THEN
    EXISTS_TAC `convex hull {p1,p2,p3,p4}:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`p1:real^N`; `p2:real^N`; `p3:real^N`; `p4:real^N`;
                   `A:real^N->real^3`] MOI_SBA_REGMAP_INV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real^3->real^N`
      (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
    MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x1:real^N` th) THEN
                            MP_TAC(SPEC `x2:real^N` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MATCH_MP_TAC MOI_SLP_AFFINE_ONTO4 THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p1:real^N`; `p2:real^N`; `p3:real^N`; `p4:real^N`;
                   `A:real^N->real^3`] MOI_SBA_REGMAP_4) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MOI_SBA_REG_AFFINE_INDEPENDENT] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SBA_REG_DISTINCT) THEN SIMP_TAC[]]);;

(* The setup: Fm is the PL homeomorphism of the link onto the boundary of a  *)
(* regular tetrahedron centred at 0, composed from pl_sphere 2; L is a       *)
(* subdivision of the link on which Fm is affine.                            *)

let MOI_SLP_SETUP = prove
 (`!c (v:real^N).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c
     ==> ?L (Fm:real^N->real^3) h'.
            simplicial_complex L /\ UNIONS L = UNIONS(simplicial_link c v) /\
            (!s. s IN L ==> ?s'. s' IN simplicial_link c v /\ s SUBSET s') /\
            (!s. s IN L ==> ?l y. linear l /\ !x. x IN s ==> Fm x = l x + y) /\
            (!x. x IN UNIONS L ==> ~(Fm x = vec 0)) /\
            homeomorphism (UNIONS L,sphere(vec 0,&1))
                          ((\x. inv(norm(Fm x)) % Fm x),h')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SCF_CM_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 2 (UNIONS(simplicial_link c (v:real^N)))` MP_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold 3 (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f0:real^N->real^N`
    (X_CHOOSE_THEN `g0:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_SLP_SIMPLEX3_VERTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^N` (X_CHOOSE_THEN `p2:real^N`
   (X_CHOOSE_THEN `p3:real^N` (X_CHOOSE_THEN `p4:real^N` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`p1:real^N`; `p2:real^N`; `p3:real^N`; `p4:real^N`]
    MOI_SBA_REGMAP_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A0:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p1:real^N`; `p2:real^N`; `p3:real^N`; `p4:real^N`;
                 `A0:real^N->real^3`] MOI_SLP_REGMAP_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj0")
    (LABEL_TAC "onto0"))) THEN
  ABBREV_TAC `c0:real^N = inv(&4) % (p1 + p2 + p3 + p4)` THEN
  ABBREV_TAC `A1 = \x:real^N. (A0:real^N->real^3) x - A0 c0` THEN
  SUBGOAL_THEN `?l y. linear l /\ !x:real^N. (A1:real^N->real^3) x = l x + y`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC) o check (is_exists o concl)) THEN
    MAP_EVERY EXISTS_TAC [`l:real^N->real^3`; `y - (A0:real^N->real^3) c0`] THEN
    EXPAND_TAC "A1" THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c0:real^N) IN relative_interior k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[MOI_SBA_RELINT_4] THEN
    MAP_EVERY EXISTS_TAC [`inv(&4)`; `inv(&4)`; `inv(&4)`; `inv(&4)`] THEN
    EXPAND_TAC "c0" THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `c0:real^N`; `A1:real^N->real^3`]
    MOI_SLP_RADIAL_HOMEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CONVEX_CONVEX_HULL; FINITE_IMP_BOUNDED_CONVEX_HULL; FINITE_INSERT;
             FINITE_EMPTY; AFFINE_HULL_CONVEX_HULL] THEN
    EXPAND_TAC "A1" THEN REWRITE_TAC[VECTOR_SUB_REFL] THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `a - c:real^3 = b - c <=> a = b`] THEN
      USE_THEN "inj0" ACCEPT_TAC;
      X_GEN_TAC `z:real^3` THEN
      REMOVE_THEN "onto0" (MP_TAC o SPEC `z + (A0:real^N->real^3) c0`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `g1:real^3->real^N` ASSUME_TAC)] THEN
  ABBREV_TAC `Fm = \x:real^N. (A1:real^N->real^3)(g0 x)` THEN
  SUBGOAL_THEN
   `pl_map_on (UNIONS(simplicial_link c (v:real^N))) (Fm:real^N->real^3)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Fm" THEN MATCH_MP_TAC MOI_SLP_PL_AFFINE_COMPOSE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphism (UNIONS(simplicial_link c (v:real^N)),sphere(vec 0,&1))
                  ((\x. inv(norm((Fm:real^N->real^3) x)) % Fm x),
                   (f0:real^N->real^N) o (g1:real^3->real^N))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x:real^N. inv(norm((Fm:real^N->real^3) x)) % Fm x) =
                  (\x. inv(norm((A1:real^N->real^3) x)) % A1 x) o
                  (g0:real^N->real^N)`
    SUBST1_TAC THENL
     [EXPAND_TAC "Fm" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier k:real^N->bool` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `Fm:real^N->real^3`]
    SIMPLICIAL_SUBDIVISION_PL_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `Fm:real^N->real^3`;
                        `(f0:real^N->real^N) o (g1:real^3->real^N)`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I
    [HOMEOMORPHISM] o check (fun th -> can (find_term ((=) `g1:real^3->real^N`))
                                         (concl th))) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_RZERO] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Geometry of the link: dimensions, the tetrahedron over a link triangle,   *)
(* its regular charts (affine, injective, Gram bound), carriers.             *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_LINK_DIM = prove
 (`!c (v:real^N) s.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     s IN simplicial_link c v
     ==> aff_dim s <= &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SCF_CM_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `convex hull ((v:real^N) INSERT s)`] MOI_SCF_CF_DIM_LE) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

(* The tetrahedron over a link triangle.                                     *)

let MOI_SLP_TET_FACTS = prove
 (`!c (v:real^N) t.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     t IN simplicial_link c v /\ aff_dim t = &2
     ==> ?p q r. ~(v = p) /\ ~(v = q) /\ ~(v = r) /\ ~(p = q) /\ ~(p = r) /\
                 ~(q = r) /\ ~affine_dependent {v,p,q,r} /\
                 t = convex hull {p,q,r} /\
                 convex hull (v INSERT t) = convex hull {v,p,q,r} /\
                 convex hull {v,p,q,r} IN c /\
                 aff_dim(convex hull {v,p,q,r}) = &3 /\
                 v extreme_point_of convex hull {v,p,q,r} /\
                 t SUBSET convex hull {v,p,q,r} /\
                 v IN convex hull {v,p,q,r} /\
                 ~(v IN affine hull t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SCF_CM_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (MP_TAC o SPEC `v:real^N`) ASSUME_TAC))))) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_SCF_LINK_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~affine_dependent(C:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `(v:real^N) INSERT C` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN
    ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[INT_ARITH `&n - &1:int = &2 <=> &n:int = &3`] THEN
    REWRITE_TAC[INT_OF_NUM_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    (X_CHOOSE_THEN `r:real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`; `r:real^N`] THEN
  SUBGOAL_THEN `~(v:real^N = p) /\ ~(v = q) /\ ~(v = r)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~((v:real^N) IN C)` THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v IN affine hull (t:real^N->bool))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN DISCH_TAC THEN
    UNDISCH_TAC `~affine_dependent((v:real^N) INSERT C)` THEN
    REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `v:real^N` THEN
    REWRITE_TAC[IN_INSERT] THEN
    SUBGOAL_THEN `((v:real^N) INSERT C) DELETE v = C` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull ((v:real^N) INSERT t) = convex hull {v,p,q,r}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SCF_HULL_INSERT_HULL]; ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {v:real^N,p,q,r}` ASSUME_TAC THENL
   [UNDISCH_TAC `~affine_dependent((v:real^N) INSERT C)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `convex hull ((v:real^N) INSERT t) = convex hull {v,p,q,r}`)) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim(convex hull {v:real^N,p,q,r}) = &2 + &1` THEN
  INT_ARITH_TAC);;

(* Gram bound in the face opposite the apex of a unit regular tetrahedron.   *)

let MOI_SLP_DOT_FACE = prove
 (`!z1 z2 z3:real^3 a1 a2 a3 b1 b2 b3.
     z1 dot z1 = &1 /\ z2 dot z2 = &1 /\ z3 dot z3 = &1 /\
     z1 dot z2 = &1 / &2 /\ z1 dot z3 = &1 / &2 /\ z2 dot z3 = &1 / &2 /\
     &0 <= a1 /\ &0 <= a2 /\ &0 <= a3 /\ &0 <= b1 /\ &0 <= b2 /\ &0 <= b3 /\
     a1 + a2 + a3 = &1 /\ b1 + b2 + b3 = &1
     ==> &1 / &2 <= (a1 % z1 + a2 % z2 + a3 % z3) dot
                    (b1 % z1 + b2 % z2 + b3 % z3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z2:real^3) dot z1 = &1 / &2 /\ (z3:real^3) dot z1 = &1 / &2 /\
                (z3:real^3) dot z2 = &1 / &2` STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a1 * b1 /\ &0 <= a2 * b2 /\ &0 <= a3 * b3`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `a1 * b1 + a1 * b2 + a1 * b3 + a2 * b1 + a2 * b2 + a2 * b3 +
    a3 * b1 + a3 * b2 + a3 * b3 = &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `(a1 + a2 + a3) * (b1 + b2 + b3) = &1` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_LID]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 <= a1 * b1` THEN UNDISCH_TAC `&0 <= a2 * b2` THEN
  UNDISCH_TAC `&0 <= a3 * b3` THEN
  UNDISCH_TAC
   `a1 * b1 + a1 * b2 + a1 * b3 + a2 * b1 + a2 * b2 + a2 * b3 +
    a3 * b1 + a3 * b2 + a3 * b3 = &1` THEN
  REAL_ARITH_TAC);;

let MOI_SLP_REG_FACE_DOT = prove
 (`!v p q r:real^N (A:real^N->real^3) x y.
     ~(v = p) /\ ~(v = q) /\ ~(v = r) /\ ~(p = q) /\ ~(p = r) /\ ~(q = r) /\
     ~affine_dependent {v,p,q,r} /\
     moi_smo_regmap (convex hull {v,p,q,r}) A /\ A v = vec 0 /\
     x IN convex hull {p,q,r} /\ y IN convex hull {p,q,r}
     ==> &1 / &2 <= A x dot A y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^N`; `p:real^N`; `q:real^N`; `r:real^N`;
                 `A:real^N->real^3`] MOI_SBA_REGMAP_4) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^N->real^3`
    (X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC)) MP_TAC) THEN
  REWRITE_TAC[moi_sba_reg; MOI_SBA_DIST1; VECTOR_SUB_LZERO; DOT_LNEG;
              DOT_RNEG; REAL_NEG_NEG] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(A:real^N->real^3) p`; `(A:real^N->real^3) q`;
                 `(A:real^N->real^3) r`] MOI_SBA_GRAM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN convex hull {p,q,r}` THEN
  UNDISCH_TAC `(y:real^N) IN convex hull {p,q,r}` THEN
  REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `b1:real` (X_CHOOSE_THEN `b2:real`
    (X_CHOOSE_THEN `b3:real` STRIP_ASSUME_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real` (X_CHOOSE_THEN `a2:real`
    (X_CHOOSE_THEN `a3:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `(A:real^N->real^3) x = a1 % A p + a2 % A q + a3 % A r /\
    (A:real^N->real^3) y = b1 % A p + b2 % A q + b3 % A r`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_SBA_AFFINE_COMB3 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SLP_DOT_FACE THEN ASM_REWRITE_TAC[]);;

(* Regular charts of the tetrahedron over a link triangle with apex at 0.    *)

let MOI_SLP_TET_REG = prove
 (`!c (v:real^N) t.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     t IN simplicial_link c v /\ aff_dim t = &2
     ==> ?A:real^N->real^3.
            (relative_interior(convex hull (v INSERT t)),A) IN
              moi_smo_star_atlas c v /\
            moi_smo_regmap (convex hull (v INSERT t)) A /\ A v = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_SLP_TET_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    (X_CHOOSE_THEN `r:real^N` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `convex hull {v:real^N,p,q,r}`;
                 `v:real^N`] MOI_SVX_TET_REGMAP0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `A:real^N->real^3` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_SBA_STAR_ATLAS_IN; IN_UNION] THEN CONJ_TAC THENL
   [DISJ1_TAC THEN REWRITE_TAC[MOI_SBA_TET_ATLAS_IN2] THEN
    EXISTS_TAC `convex hull {v:real^N,p,q,r}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `s:real`] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `v + s % (x - v):real^N = v - s % (v - x)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SBA_AFFINE_HOMOG THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE]]);;

(* The facts about such a regular chart used downstream.                     *)

let MOI_SLP_REG_GOOD = prove
 (`!c (v:real^N) t (A:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     t IN simplicial_link c v /\ aff_dim t = &2 /\
     moi_smo_regmap (convex hull (v INSERT t)) A /\ A v = vec 0
     ==> (?l y. linear l /\ !x. A x = l x + y) /\
         (!x y. x IN affine hull (convex hull (v INSERT t)) /\
                y IN affine hull (convex hull (v INSERT t)) /\ A x = A y
                ==> x = y) /\
         (!x y. x IN t /\ y IN t ==> &1 / &2 <= A x dot A y) /\
         convex hull (v INSERT t) IN c /\
         aff_dim(convex hull (v INSERT t)) = &3 /\
         v IN convex hull (v INSERT t) /\ t SUBSET convex hull (v INSERT t) /\
         ~(v IN affine hull t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_SLP_TET_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    (X_CHOOSE_THEN `r:real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `moi_smo_regmap (convex hull ((v:real^N) INSERT t)) A` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`v:real^N`; `p:real^N`; `q:real^N`; `r:real^N`;
                 `A:real^N->real^3`] MOI_SLP_REGMAP_PROPS) THEN
  ASM_REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SLP_REG_FACE_DOT THEN
    MAP_EVERY EXISTS_TAC [`v:real^N`; `p:real^N`; `q:real^N`; `r:real^N`] THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(t:real^N->bool) SUBSET convex hull {v,p,q,r}` THEN
    ASM_REWRITE_TAC[]]);;

(* Carriers.                                                                 *)

let MOI_SLP_SEG_CARRIER = prove
 (`!K a b s' r:real^N->bool.
     simplicial_complex K /\ ~(a = b) /\ s' IN K /\ segment[a,b] SUBSET s' /\
     r IN K /\ midpoint(a,b) IN relative_interior r
     ==> segment[a,b] SUBSET r /\ segment(a,b) SUBSET relative_interior r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_SLP_SC_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN s' /\ b IN s'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `midpoint(a:real^N,b) IN segment(a,b)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) face_of s'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `r:real^N->bool`;
                   `s':real^N->bool`] MOI_SBA_RELINT_MEETS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `midpoint(a:real^N,b)` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:real^N,b] SUBSET r` ASSUME_TAC THENL
   [SUBGOAL_THEN `(a:real^N) IN r /\ b IN r` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(r:real^N->bool) face_of s'` THEN REWRITE_TAC[face_of] THEN
      DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
      EXISTS_TAC `midpoint(a:real^N,b)` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      ASM_MESON_TAC[MOI_SBA_LF_CONVEX]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS K` MP_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `y:real^N`] MOI_SBA_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ry:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(ry:real^N->bool) face_of s' /\ ry SUBSET s'` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_RELINT_MEETS THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN ry /\ b IN ry` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(ry:real^N->bool) face_of s'` THEN REWRITE_TAC[face_of] THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `midpoint(a:real^N,b) IN ry` ASSUME_TAC THENL
   [SUBGOAL_THEN `convex(ry:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[MOI_SBA_LF_CONVEX]; ALL_TAC] THEN
    REWRITE_TAC[CONVEX_ALT; midpoint] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `inv(&2)`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) SUBSET ry` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `r:real^N->bool`;
                   `ry:real^N->bool`] MOI_SBA_RELINT_MEETS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `midpoint(a:real^N,b)` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ry:real^N->bool) SUBSET r` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `ry:real^N->bool`;
                   `r:real^N->bool`] MOI_SBA_RELINT_MEETS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ry:real^N->bool = r` (fun th -> ASM_MESON_TAC[th]) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Gnomonic projections of affine maps that vanish at the apex: cell        *)
(* smoothness, injectivity, segments and rays, half planes; rotations.      *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_KERNEL_CONE = prove
 (`!(l:real^N->real^3) y (v:real^N) s tet.
     linear l /\ l v + y = vec 0 /\
     (!x z. x IN affine hull tet /\ z IN affine hull tet /\ l x + y = l z + y
            ==> x = z) /\
     v IN tet /\ s SUBSET tet /\ ~(v IN affine hull s)
     ==> (!x. x IN affine hull s ==> ~(l x + y = vec 0)) /\
         (!w. w IN moi_smo_tangent s /\ l w = vec 0 ==> w = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "inj") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `affine hull s SUBSET affine hull (tet:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN affine hull tet` ASSUME_TAC THENL
   [ASM_SIMP_TAC[HULL_INC]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `x:real^N = v` (fun th -> ASM_MESON_TAC[th]) THEN
    REMOVE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [UNDISCH_TAC `(w:real^N) IN moi_smo_tangent s` THEN
    ASM_REWRITE_TAC[moi_smo_tangent] THEN
    REWRITE_TAC[SET_RULE `{y - z:real^N | y IN {} /\ z IN {}} = {}`] THEN
    REWRITE_TAC[SPAN_EMPTY; IN_SING];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:real^N` o GEN_REWRITE_RULE I
    [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `(x0:real^N) + w IN affine hull s` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SLP_AFF_TANGENT THEN ASM_SIMP_TAC[HULL_INC]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^N) + w = x0` MP_TAC THENL
   [REMOVE_THEN "inj" MATCH_MP_TAC THEN ASM_SIMP_TAC[LINEAR_ADD] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HULL_INC; SUBSET]; VECTOR_ARITH_TAC];
    VECTOR_ARITH_TAC]);;

let MOI_SLP_GNOM_CELL = prove
 (`!(l:real^N->real^3) y (v:real^N) s tet.
     linear l /\ l v + y = vec 0 /\
     (!x z. x IN affine hull tet /\ z IN affine hull tet /\ l x + y = l z + y
            ==> x = z) /\
     v IN tet /\ s SUBSET tet /\ ~(v IN affine hull s) /\
     (!x. x IN s ==> &0 < (l x + y)$3)
     ==> moi_smo_cell_smooth s (\x. moi_smo_gnom(l x + y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_SLP_CELL_SMOOTH_GEN THEN
  EXISTS_TAC `{z:real^3 | z$3 > &0}` THEN
  ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLK_GNOM_SMOOTH THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; IN_ELIM_THM; real_gt] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM; real_gt] THEN
    MAP_EVERY X_GEN_TAC [`z:real^3`; `w:real^3`] THEN STRIP_TAC THEN
    EXISTS_TAC `(w:real^3)$3 / (z:real^3)$3` THEN
    MATCH_MP_TAC MOI_SVX_GNOM_KERNEL THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[IN_ELIM_THM; real_gt];
    MATCH_MP_TAC MOI_SLP_KERNEL_COND THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SLP_KERNEL_CONE THEN
    MAP_EVERY EXISTS_TAC [`v:real^N`; `tet:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SLP_UNIT_CELL = prove
 (`!(l:real^N->real^3) y s.
     linear l /\ (!x. x IN affine hull s ==> ~(l x + y = vec 0)) /\
     (!w. w IN moi_smo_tangent s /\ l w = vec 0 ==> w = vec 0)
     ==> moi_smo_cell_smooth s (\x. inv(norm(l x + y)) % (l x + y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^3. inv(norm z) % z`; `{z:real^3 | ~(z = vec 0)}`;
                 `l:real^N->real^3`; `y:real^3`; `s:real^N->bool`]
    MOI_SLP_CELL_SMOOTH_GEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[MOI_SLP_OPEN_NONZERO; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLP_UNIT_SMOOTH THEN
    REWRITE_TAC[MOI_SLP_OPEN_NONZERO; IN_ELIM_THM];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SLP_UNIT_KERNEL THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[HULL_INC];
    MATCH_MP_TAC MOI_SLP_KERNEL_COND THEN ASM_REWRITE_TAC[]]);;

let MOI_SLP_GNOM_INJ = prove
 (`!(l:real^N->real^3) y (v:real^N) s tet.
     linear l /\ l v + y = vec 0 /\
     (!x z. x IN affine hull tet /\ z IN affine hull tet /\ l x + y = l z + y
            ==> x = z) /\
     v IN tet /\ s SUBSET tet /\ ~(v IN affine hull s) /\
     (!x. x IN s ==> &0 < (l x + y)$3)
     ==> !x1 x2. x1 IN s /\ x2 IN s /\
                 moi_smo_gnom(l x1 + y) = moi_smo_gnom(l x2 + y)
                 ==> x1 = x2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "inj") STRIP_ASSUME_TAC))) THEN
  MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(l:real^N->real^3) x1 + y`; `(l:real^N->real^3) x2 + y`]
    MOI_SLK_GNOM_EQ) THEN
  ASM_SIMP_TAC[] THEN
  ABBREV_TAC `mu = ((l:real^N->real^3) x1 + y)$3 / (l x2 + y)$3` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < mu` ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull s SUBSET affine hull (tet:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x1:real^N) IN affine hull s /\ x2 IN affine hull s`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[HULL_INC]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN affine hull tet` ASSUME_TAC THENL
   [ASM_SIMP_TAC[HULL_INC]; ALL_TAC] THEN
  SUBGOAL_THEN `x1 = v + mu % (x2 - v):real^N` ASSUME_TAC THENL
   [REMOVE_THEN "inj" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
      ASM_REWRITE_TAC[AFFINE_AFFINE_HULL] THEN ASM SET_TAC[];
      ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; LINEAR_SUB] THEN
      UNDISCH_TAC `(l:real^N->real^3) x1 + y = mu % (l x2 + y)` THEN
      SUBGOAL_THEN `y = --((l:real^N->real^3) v)` SUBST1_TAC THENL
       [UNDISCH_TAC `(l:real^N->real^3) v + y = vec 0` THEN VECTOR_ARITH_TAC;
        VECTOR_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_CASES_TAC `mu = &1` THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `~((v:real^N) IN affine hull s)` THEN
  SUBGOAL_THEN `v:real^N = x1 + (mu / (&1 - mu)) % (x1 - x2)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(v + m % (x - v)) + a % ((v + m % (x - v)) - x):real^N =
      v + (m - a * (&1 - m)) % (x - v)`] THEN
    SUBGOAL_THEN `mu - mu / (&1 - mu) * (&1 - mu) = &0` SUBST1_TAC THENL
     [UNDISCH_TAC `~(mu = &1)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
  ASM_REWRITE_TAC[AFFINE_AFFINE_HULL]);;

(* Gnomonic images of segments.                                              *)

let MOI_SLP_GNOM_SEGMENT = prove
 (`!y z:real^3 t.
     &0 < y$3 /\ &0 < z$3 /\ &0 <= t /\ t <= &1
     ==> ?u. &0 <= u /\ u <= &1 /\
             moi_smo_gnom((&1 - t) % y + t % z) =
             (&1 - u) % moi_smo_gnom y + u % moi_smo_gnom z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (&1 - t) * (y:real^3)$3 + t * (z:real^3)$3` ASSUME_TAC THENL
   [ASM_CASES_TAC `t = &0` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `t * (z:real^3)$3 / ((&1 - t) * (y:real^3)$3 + t * (z:real^3)$3)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `a * b / c = (a * b) / c`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> b <= &1 * (a + b)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    REWRITE_TAC[MOI_SLK_GNOM_COMPONENTS; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    UNDISCH_TAC `&0 < (&1 - t) * (y:real^3)$3 + t * (z:real^3)$3` THEN
    UNDISCH_TAC `&0 < (y:real^3)$3` THEN UNDISCH_TAC `&0 < (z:real^3)$3` THEN
    CONV_TAC REAL_FIELD]);;

let MOI_SLP_GNOM_ZERO = prove
 (`!y:real^3. y$1 = &0 /\ y$2 = &0 ==> moi_smo_gnom y = vec 0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; MOI_SLK_GNOM_COMPONENTS;
              VEC_COMPONENT] THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO]);;

let MOI_SLP_GNOM_RAY = prove
 (`!y z:real^3 t.
     y$1 = &0 /\ y$2 = &0 /\ &0 < y$3 /\ &0 < z$3 /\ &0 <= t /\ t <= &1
     ==> ?u. &0 <= u /\ moi_smo_gnom((&1 - t) % y + t % z) = u % moi_smo_gnom z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`y:real^3`; `z:real^3`; `t:real`] MOI_SLP_GNOM_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOI_SLP_GNOM_ZERO; VECTOR_MUL_RZERO; VECTOR_ADD_LID]);;

(* A cone of two complex directions lies in a closed half plane.            *)

let MOI_SLP_CEXP_ARG = prove
 (`!z w:complex.
     ~(z = Cx(&0))
     ==> Im(cexp(--(ii * Cx(Arg z))) * z) = &0 /\
         Im(cexp(--(ii * Cx(Arg z))) * w) = Im(cnj z * w) / norm z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(norm(z:complex) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `cexp(--(ii * Cx(Arg z))) = cnj z / Cx(norm z)` ASSUME_TAC THENL
   [MP_TAC(SPEC `z:complex` ARG) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
      [last(CONJUNCTS th)]) THEN
    REWRITE_TAC[CNJ_MUL; CNJ_CX; CNJ_CEXP; CNJ_II; CNJ_CX] THEN
    REWRITE_TAC[COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG] THEN
    UNDISCH_TAC `~(norm(z:complex) = &0)` THEN
    REWRITE_TAC[GSYM CX_INJ] THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[complex_div; GSYM CX_INV] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `(a * Cx b) * c = Cx b * (a * c)`] THEN
  REWRITE_TAC[IM_MUL_CX; COMPLEX_MUL_CNJ] THEN
  REWRITE_TAC[GSYM CX_POW; IM_CX; REAL_MUL_RZERO] THEN
  REWRITE_TAC[real_div; REAL_MUL_SYM]);;

let MOI_SLP_CONE_HALF = prove
 (`!a1 a2:complex.
     ?b. &0 <= Im(cexp(--(ii * Cx b)) * a1) /\
         &0 <= Im(cexp(--(ii * Cx b)) * a2)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a1 = Cx(&0)` THENL
   [EXISTS_TAC `Arg a2` THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; IM_CX; REAL_LE_REFL] THEN
    ASM_CASES_TAC `a2 = Cx(&0)` THENL
     [ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; IM_CX; REAL_LE_REFL];
      MP_TAC(ISPECL [`a2:complex`; `a2:complex`] MOI_SLP_CEXP_ARG) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= Im(cnj a1 * a2)` THENL
   [EXISTS_TAC `Arg a1` THEN
    MP_TAC(ISPECL [`a1:complex`; `a2:complex`] MOI_SLP_CEXP_ARG) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE];
    ALL_TAC] THEN
  ASM_CASES_TAC `a2 = Cx(&0)` THENL
   [UNDISCH_TAC `~(&0 <= Im(cnj a1 * a2))` THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; IM_CX; REAL_LE_REFL];
    ALL_TAC] THEN
  EXISTS_TAC `Arg a2` THEN
  MP_TAC(ISPECL [`a2:complex`; `a1:complex`] MOI_SLP_CEXP_ARG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE] THEN
  SUBGOAL_THEN `Im(cnj a2 * a1) = --Im(cnj a1 * a2)` SUBST1_TAC THENL
   [SUBGOAL_THEN `cnj a2 * a1 = cnj(cnj a1 * a2)` SUBST1_TAC THENL
     [REWRITE_TAC[CNJ_MUL; CNJ_CNJ; COMPLEX_MUL_SYM]; REWRITE_TAC[IM_CNJ]];
    ASM_REAL_ARITH_TAC]);;

(* Rotations taking a vector to the positive third axis; positivity of the  *)
(* third coordinate on the face opposite the apex.                           *)

let MOI_SLP_ROT_EXISTS = prove
 (`!a:real^3. ?R. orthogonal_transformation R /\ R a = norm a % basis 3`,
  GEN_TAC THEN MATCH_MP_TAC ORTHOGONAL_TRANSFORMATION_EXISTS THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_NORM] THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID]);;

let MOI_SLP_ROT_POS = prove
 (`!(R:real^3->real^3) a b c0.
     orthogonal_transformation R /\ R b = c0 % basis 3 /\ &0 < c0 /\
     &0 < a dot b
     ==> &0 < (R a)$3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(R:real^3->real^3) a dot R b = a dot b` ASSUME_TAC THENL
   [ASM_MESON_TAC[orthogonal_transformation]; ALL_TAC] THEN
  UNDISCH_TAC `(R:real^3->real^3) a dot R b = a dot b` THEN
  ASM_REWRITE_TAC[DOT_RMUL] THEN
  SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < c0 * ((R:real^3->real^3) a)$3` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Half planes for gnomonic images of triangles; relative interior steps;    *)
(* part (1) of moi_smo_conical_pd (h smooth on the closed triangles).        *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_GNOM_COMB_ABS = prove
 (`!W P Q:real^3 a b g.
     W$1 = &0 /\ W$2 = &0 /\ &0 < P$3 /\ &0 < Q$3 /\
     &0 < (a % W + b % P + g % Q)$3
     ==> moi_smo_gnom(a % W + b % P + g % Q) =
         (b * P$3 / (a % W + b % P + g % Q)$3) % moi_smo_gnom P +
         (g * Q$3 / (a % W + b % P + g % Q)$3) % moi_smo_gnom Q`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
  REWRITE_TAC[MOI_SLK_GNOM_COMPONENTS; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
  UNDISCH_TAC `&0 < a * (W:real^3)$3 + b * (P:real^3)$3 + g * (Q:real^3)$3` THEN
  UNDISCH_TAC `&0 < (P:real^3)$3` THEN UNDISCH_TAC `&0 < (Q:real^3)$3` THEN
  CONV_TAC REAL_FIELD);;

let MOI_SLP_GNOM_COMB3 = prove
 (`!(l:real^N->real^3) y w p q a b g.
     linear l /\ (l w + y)$1 = &0 /\ (l w + y)$2 = &0 /\ a + b + g = &1 /\
     &0 < (l p + y)$3 /\ &0 < (l q + y)$3 /\
     &0 < (l (a % w + b % p + g % q) + y)$3
     ==> moi_smo_gnom(l (a % w + b % p + g % q) + y) =
         (b * (l p + y)$3 / (l (a % w + b % p + g % q) + y)$3) %
           moi_smo_gnom(l p + y) +
         (g * (l q + y)$3 / (l (a % w + b % p + g % q) + y)$3) %
           moi_smo_gnom(l q + y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(l:real^N->real^3) (a % w + b % p + g % q) + y =
    a % (l w + y) + b % (l p + y) + g % (l q + y)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_COMB3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_SLP_GNOM_COMB_ABS THEN ASM_REWRITE_TAC[]);;

let MOI_SLP_HALF_PLANE = prove
 (`!(l:real^N->real^3) y w p q.
     linear l /\ (l w + y)$1 = &0 /\ (l w + y)$2 = &0 /\
     (!x. x IN convex hull {w,p,q} ==> &0 < (l x + y)$3)
     ==> ?b. !x. x IN convex hull {w,p,q}
                 ==> &0 <= Im(cexp(--(ii * Cx b)) * moi_smo_gnom(l x + y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_smo_gnom((l:real^N->real^3) p + y)`;
                 `moi_smo_gnom((l:real^N->real^3) q + y)`] MOI_SLP_CONE_HALF) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < ((l:real^N->real^3) p + y)$3 /\ &0 < (l q + y)$3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < ((l:real^N->real^3) x + y)$3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN convex hull {w,p,q}` THEN
  REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real` (X_CHOOSE_THEN `a2:real`
    (X_CHOOSE_THEN `a3:real` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`l:real^N->real^3`; `y:real^3`; `w:real^N`; `p:real^N`;
                 `q:real^N`; `a1:real`; `a2:real`; `a3:real`]
    MOI_SLP_GNOM_COMB3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_ADD_LDISTRIB] THEN
  REWRITE_TAC[COMPLEX_RING `a * Cx b * c = Cx b * (a * c)`] THEN
  REWRITE_TAC[IM_ADD; IM_MUL_CX] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]);;

(* A relative interior point can be moved a little towards any point of the  *)
(* affine hull without leaving the set.                                     *)

let MOI_SLP_RELINT_STEP = prove
 (`!s x0 z:real^N.
     x0 IN relative_interior s /\ z IN affine hull s
     ==> ?e. &0 < e /\ !t. &0 <= t /\ t <= e ==> x0 + t % (z - x0) IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  EXISTS_TAC `e / (&2 * (norm(z - x0:real^N) + &1))` THEN
  SUBGOAL_THEN `&0 < &2 * (norm(z - x0:real^N) + &1)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `z - x0:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  REWRITE_TAC[IN_INTER; IN_BALL] THEN CONJ_TAC THENL
   [REWRITE_TAC[dist; VECTOR_ARITH `x - (x + t % y):real^N = --(t % y)`] THEN
    REWRITE_TAC[NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `e / (&2 * (norm(z - x0:real^N) + &1)) * norm(z - x0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `a / b * c = (a * c) / b`; REAL_LT_LDIV_EQ] THEN
    MP_TAC(ISPEC `z - x0:real^N` NORM_POS_LE) THEN
    UNDISCH_TAC `&0 < e` THEN
    REWRITE_TAC[REAL_ARITH `e * (&2 * (n + &1)) = &2 * e * n + &2 * e`] THEN
    SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    MP_TAC(SPECL [`e:real`; `norm(z - x0:real^N)`] REAL_LE_MUL) THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC]]);;

(* Part (1): the radial projection of an affine map is smooth on a closed   *)
(* triangle, given injectivity of the radial projection on the polyhedron.  *)

let MOI_SLP_TRI_KERNEL = prove
 (`!X s (Fm:real^N->real^3) l y.
     s SUBSET X /\ convex s /\ ~(s = {}) /\ linear l /\
     (!x. x IN s ==> Fm x = l x + y) /\
     (!x. x IN X ==> ~(Fm x = vec 0)) /\
     (!x z. x IN X /\ z IN X /\
            inv(norm(Fm x)) % Fm x = inv(norm(Fm z)) % Fm z ==> x = z)
     ==> (!x. x IN affine hull s ==> ~(l x + y = vec 0)) /\
         (!w. w IN moi_smo_tangent s /\ l w = vec 0 ==> w = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "aff") (CONJUNCTS_THEN2 (LABEL_TAC "nz")
     (LABEL_TAC "inj"))))))) THEN
  SUBGOAL_THEN `?x0:real^N. x0 IN relative_interior s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEMBER_NOT_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^N) IN affine hull s` ASSUME_TAC THENL
   [ASM_SIMP_TAC[HULL_INC]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `x0:real^N`; `&2 % x0 - z:real^N`]
      MOI_SLP_RELINT_STEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&2 % x0 - z:real^N = x0 + &1 % (x0 - z)` SUBST1_TAC THENL
       [VECTOR_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
      ASM_REWRITE_TAC[AFFINE_AFFINE_HULL];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `x0 + e % ((&2 % x0 - z) - x0):real^N = x0` MP_TAC THENL
     [REMOVE_THEN "inj" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN
       `(l:real^N->real^3) (x0 + e % ((&2 % x0 - z) - x0)) + y =
        (&1 + e) % (l x0 + y)`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; LINEAR_SUB] THEN
        SUBGOAL_THEN `y = --((l:real^N->real^3) z)` SUBST1_TAC THENL
         [UNDISCH_TAC `(l:real^N->real^3) z + y = vec 0` THEN VECTOR_ARITH_TAC;
          VECTOR_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_SLP_UNIT_CMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `x0 + e % ((&2 % x0 - z) - x0):real^N = x0 <=>
                              e % (x0 - z) = vec 0`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; VECTOR_SUB_EQ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    REMOVE_THEN "nz" (MP_TAC o SPEC `z:real^N`) THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x0:real^N`; `x0 + w:real^N`]
    MOI_SLP_RELINT_STEP) THEN
  ASM_SIMP_TAC[MOI_SLP_AFF_TANGENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN
  REWRITE_TAC[VECTOR_ARITH `(x0 + w) - x0:real^N = w`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `x0 + e % w:real^N = x0` MP_TAC THENL
   [REMOVE_THEN "inj" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    REWRITE_TAC[VECTOR_ARITH `x0 + e % w:real^N = x0 <=> e % w = vec 0`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]]);;

let MOI_SLP_PART1 = prove
 (`!L (Fm:real^N->real^3).
     simplicial_complex L /\
     (!s. s IN L ==> ?l y. linear l /\ !x. x IN s ==> Fm x = l x + y) /\
     (!x. x IN UNIONS L ==> ~(Fm x = vec 0)) /\
     (!x z. x IN UNIONS L /\ z IN UNIONS L /\
            inv(norm(Fm x)) % Fm x = inv(norm(Fm z)) % Fm z ==> x = z)
     ==> !s. s IN L /\ aff_dim s = &2
             ==> moi_smo_cell_smooth s (\x. inv(norm(Fm x)) % Fm x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real^N->bool` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (is_forall o concl) o
    check (fun th -> can (find_term ((=) `linear:(real^N->real^3)->bool`))
                         (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `convex(s:real^N->bool) /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SBA_LF_CONVEX; MOI_SLP_SC_LF];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `s:real^N->bool`; `Fm:real^N->real^3`;
                 `l:real^N->real^3`; `y:real^3`] MOI_SLP_TRI_KERNEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC MOI_SLP_CELL_SMOOTH_EQ THEN
  EXISTS_TAC `\x:real^N. inv(norm((l:real^N->real^3) x + y)) % (l x + y)` THEN
  ASM_SIMP_TAC[MOI_SLP_UNIT_CELL]);;

(* ------------------------------------------------------------------------- *)
(* Part (4) in general form: a map that is the radial projection of an affine *)
(* map in one chart is a smooth immersion in every chart (through the smooth  *)
(* transitions of the atlas, whose derivatives are injective).                *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_OPEN_IMAGE_SUB = prove
 (`!Y U V (kappa:real^N->real^M).
        open_in (subtopology euclidean Y) U /\
        open_in (subtopology euclidean Y) V /\ V SUBSET U /\
        open (IMAGE kappa U) /\
        homeomorphic_map (subtopology euclidean U,
                          subtopology euclidean (IMAGE kappa U)) kappa
        ==> open (IMAGE kappa V)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_SLK_HMAP) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `g:real^M->real^N`) STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
  EXISTS_TAC `IMAGE (kappa:real^N->real^M) U` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
  MAP_EVERY EXISTS_TAC [`g:real^M->real^N`; `U:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `Y:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]);;

(* Transitions with a smooth left inverse have injective derivatives.        *)

let MOI_SLP_TRANS_INJ = prove
 (`!(G:real^M->real^N) G' W1 W2 y z.
     open W1 /\ open W2 /\ smooth_map_on W1 G /\ smooth_map_on W2 G' /\
     IMAGE G W1 SUBSET W2 /\ (!y. y IN W1 ==> G'(G y) = y) /\ y IN W1 /\
     frechet_derivative G (at y) z = vec 0
     ==> z = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(G:real^M->real^N) y IN W2` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((G:real^M->real^N) has_derivative frechet_derivative G (at y)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `W1:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((G':real^N->real^M) has_derivative frechet_derivative G' (at (G y)))
    (at ((G:real^M->real^N) y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `W2:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^M->real^N`; `G':real^N->real^M`;
                 `frechet_derivative (G:real^M->real^N) (at y)`;
                 `frechet_derivative (G':real^N->real^M) (at ((G:real^M->real^N) y))`;
                 `y:real^M`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(((G':real^N->real^M) o (G:real^M->real^N)) has_derivative
                 (\h. h)) (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `\x:real^M. x` THEN EXISTS_TAC `W1:real^M->bool` THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_ID; o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(G':real^N->real^M) o (G:real^M->real^N)`;
                 `frechet_derivative (G':real^N->real^M) (at ((G:real^M->real^N) y)) o
                  frechet_derivative G (at y)`;
                 `\h:real^M. h`; `y:real^M`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o C AP_THM `z:real^M`) THEN REWRITE_TAC[o_THM] THEN
  UNDISCH_TAC `frechet_derivative (G:real^M->real^N) (at y) z = vec 0` THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(ISPEC `frechet_derivative (G':real^N->real^M)
                         (at ((G:real^M->real^N) y))` LINEAR_0) THEN
  MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN ASM_REWRITE_TAC[]);;

let MOI_SLP_SMALL_MUL = prove
 (`!r n. &0 < r /\ &0 <= n ==> r / (&2 * (n + &1)) * n < r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * (n + &1)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `a / b * c = (a * c) / b`; REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC);;

(* The radial projection of an affine map of real^2 is locally injective    *)
(* only if its derivative is injective.                                      *)

let MOI_SLP_GPSI_KERNEL = prove
 (`!(Phi:real^2->real^3) lP yP W z0 w.
     linear lP /\ (!z. Phi z = lP z + yP) /\ open W /\ z0 IN W /\
     (!z. z IN W ==> ~(Phi z = vec 0)) /\
     (!z1 z2. z1 IN W /\ z2 IN W /\
              inv(norm(Phi z1)) % Phi z1 = inv(norm(Phi z2)) % Phi z2
              ==> z1 = z2) /\
     frechet_derivative (\z. inv(norm(Phi z)) % Phi z) (at z0) w = vec 0
     ==> w = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^2. inv(norm((Phi:real^2->real^3) z)) % Phi z) =
                (\z. (\y. inv(norm y) % y) (lP z + yP))` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  UNDISCH_TAC
   `frechet_derivative (\z:real^2. (\y:real^3. inv(norm y) % y) (lP z + yP))
                       (at z0) w = vec 0` THEN
  SUBGOAL_THEN `(\y:real^3. inv(norm y) % y) differentiable
                (at ((lP:real^2->real^3) z0 + yP))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
    REWRITE_TAC[MOI_SLP_OPEN_NONZERO; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SLP_UNIT_SMOOTH THEN
      REWRITE_TAC[MOI_SLP_OPEN_NONZERO; IN_ELIM_THM];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SLP_CHAIN_AFFINE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(lP:real^2->real^3) z0 + yP`; `(lP:real^2->real^3) w`]
    MOI_SLP_UNIT_KERNEL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` ASSUME_TAC) THEN
  UNDISCH_TAC `open(W:real^2->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z0:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `ep = min (r / (&2 * (norm(w:real^2) + &1)))
                       (&1 / (&2 * (abs a + &1)))` THEN
  SUBGOAL_THEN `&0 < ep /\ ep * norm(w:real^2) < r /\ ep * abs a < &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ep" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
      MP_TAC(ISPEC `w:real^2` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `r / (&2 * (norm(w:real^2) + &1)) * norm w` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN
        REWRITE_TAC[NORM_POS_LE; REAL_MIN_LE; REAL_LE_REFL];
        MATCH_MP_TAC MOI_SLP_SMALL_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE]];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `&1 / (&2 * (abs a + &1)) * abs a` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN
        REWRITE_TAC[REAL_ABS_POS; REAL_MIN_LE; REAL_LE_REFL];
        MATCH_MP_TAC MOI_SLP_SMALL_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + ep * a` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ep:real`; `--(abs a)`; `a:real`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `ep * abs a < &1` THEN REWRITE_TAC[REAL_MUL_RNEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `z0 + ep % w:real^2 IN W` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `z - (z + e % w):real^2 = --(e % w)`;
                NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`];
    ALL_TAC] THEN
  SUBGOAL_THEN `z0 + ep % w:real^2 = z0` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `z1:real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(lP:real^2->real^3) (z0 + ep % w) + yP =
                  (&1 + ep * a) % (lP z0 + yP)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_SLP_UNIT_CMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[VECTOR_ARITH `z + e % w:real^2 = z <=> e % w = vec 0`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]]);;

let MOI_SLP_CHAIN = prove
 (`!(f:real^M->real^N) (g:real^N->real^P) x w.
     f differentiable (at x) /\ g differentiable (at (f x))
     ==> frechet_derivative (g o f) (at x) w =
         frechet_derivative g (at (f x)) (frechet_derivative f (at x) w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `g:real^N->real^P`;
                 `frechet_derivative (f:real^M->real^N) (at x)`;
                 `frechet_derivative (g:real^N->real^P) (at ((f:real^M->real^N) x))`;
                 `x:real^M`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; o_THM]));;

let MOI_SLP_AFFINE_NZ_OPEN = prove
 (`!(Phi:real^M->real^N) l y.
     linear l /\ (!z. Phi z = l z + y) ==> open {z | ~(Phi z = vec 0)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{z:real^M | ~((Phi:real^M->real^N) z = vec 0)} =
                {z | Phi z IN {w:real^N | ~(w = vec 0)}}` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  REWRITE_TAC[MOI_SLP_OPEN_NONZERO] THEN GEN_TAC THEN
  SUBGOAL_THEN `(Phi:real^M->real^N) = (\z. l z + y)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ADD THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; CONTINUOUS_CONST]);;

let MOI_SLP_PART4_GEN = prove
 (`!(X:real^N->bool) sigma U phi V psi S (h:real^N->real^3)
    (lP:real^2->real^3) yP.
     smooth_manifold_atlas (subtopology euclidean X) sigma /\
     (U,phi) IN sigma /\ (V,psi) IN sigma /\
     open_in (subtopology euclidean X) S /\ S SUBSET V /\
     linear lP /\
     (!x. x IN S ==> ~(lP(psi x) + yP = vec 0) /\
                     h x = inv(norm(lP(psi x) + yP)) % (lP(psi x) + yP)) /\
     (!x y. x IN S /\ y IN S /\ h x = h y ==> x = y)
     ==> ?g. smooth_map_on (IMAGE phi (U INTER S)) g /\
             (!x. x IN U INTER S ==> g(phi x) = h x) /\
             (!y z. y IN IMAGE phi (U INTER S) /\
                    frechet_derivative g (at y) z = vec 0 ==> z = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "hS") (LABEL_TAC "hinj")))))))) THEN
  REWRITE_TAC[smooth_manifold_atlas] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ch")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "tr"))) THEN
  USE_THEN "ch" (MP_TAC o SPECL [`U:real^N->bool`; `phi:real^N->real^2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "ch" (MP_TAC o SPECL [`V:real^N->bool`; `psi:real^N->real^2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "tr" (MP_TAC o SPECL [`U:real^N->bool`; `phi:real^N->real^2`;
                                 `V:real^N->bool`; `psi:real^N->real^2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G1"))) THEN
  USE_THEN "tr" (MP_TAC o SPECL [`V:real^N->bool`; `psi:real^N->real^2`;
                                 `U:real^N->bool`; `phi:real^N->real^2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G2"))) THEN
  REMOVE_THEN "ch" (K ALL_TAC) THEN REMOVE_THEN "tr" (K ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBTOPOLOGY_SUBTOPOLOGY]) THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X /\ V SUBSET X` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_IMP_SUBSET THEN
    EXISTS_TAC `euclidean:(real^N)topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `X INTER U:real^N->bool = U /\ X INTER V = V` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(U:real^N->bool) SUBSET X`;
                           `(V:real^N->bool) SUBSET X`] THEN SET_TAC[];
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN `U INTER S SUBSET U INTER (V:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `S SUBSET (V:real^N->bool)` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN U INTER S ==> (G:real^2->real^2)(phi x) = psi x`
  (LABEL_TAC "GS") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN USE_THEN "G1" MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^N) IN U INTER S` THEN
    UNDISCH_TAC `U INTER S SUBSET U INTER (V:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:real^N->real^2) (U INTER V)) /\
                open(IMAGE (psi:real^N->real^2) (V INTER U)) /\
                open(IMAGE (phi:real^N->real^2) (U INTER S)) /\
                open(IMAGE (psi:real^N->real^2) (U INTER S))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_SLP_OPEN_IMAGE_SUB THEN
    EXISTS_TAC `X:real^N->bool` THENL
     [EXISTS_TAC `U:real^N->bool`; EXISTS_TAC `V:real^N->bool`;
      EXISTS_TAC `U:real^N->bool`; EXISTS_TAC `V:real^N->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN
    UNDISCH_TAC `S SUBSET (V:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^2 | ~((lP:real^2->real^3) z + yP = vec 0)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SLP_AFFINE_NZ_OPEN THEN
    MAP_EVERY EXISTS_TAC [`lP:real^2->real^3`; `yP:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {z:real^2 | ~((lP:real^2->real^3) z + yP = vec 0)}
                              (\z. inv(norm(lP z + yP)) % (lP z + yP))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{z:real^2 | ~((lP:real^2->real^3) z + yP = vec 0)}`;
                   `{y:real^3 | ~(y = vec 0)}`; `\z:real^2. (lP:real^2->real^3) z + yP`;
                   `\y:real^3. inv(norm y) % y`] SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[MOI_SLP_OPEN_NONZERO] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      SET_TAC[];
      MATCH_MP_TAC MOI_SBA_AFFINE_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`lP:real^2->real^3`; `yP:real^3`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_SLP_UNIT_SMOOTH THEN
      REWRITE_TAC[MOI_SLP_OPEN_NONZERO; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN U INTER S
                           ==> ~((lP:real^2->real^3)(psi x) + yP = vec 0)`
  (LABEL_TAC "nz") THENL
   [REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN
    USE_THEN "hS" (MP_TAC o CONJUNCT1 o C MATCH_MP
      (ASSUME `(x:real^N) IN S`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(\z. inv(norm((lP:real^2->real^3) z + yP)) % (lP z + yP)) o
              (G:real^2->real^2)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{z:real^2 | ~((lP:real^2->real^3) z + yP = vec 0)}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      USE_THEN "GS" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^N) IN U INTER S`)]) THEN
      USE_THEN "nz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (phi:real^N->real^2) (U INTER V)` THEN
      ASM_SIMP_TAC[IMAGE_SUBSET]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    USE_THEN "GS" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^N) IN U INTER S`)]) THEN
    UNDISCH_TAC `(x:real^N) IN U INTER S` THEN REWRITE_TAC[IN_INTER] THEN
    STRIP_TAC THEN
    USE_THEN "hS" (fun th -> REWRITE_TAC[CONJUNCT2(MATCH_MP th
      (ASSUME `(x:real^N) IN S`))]);
    ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x0:real^N` THEN DISCH_TAC THEN X_GEN_TAC `z:real^2` THEN
  SUBGOAL_THEN `(x0:real^N) IN U INTER V` ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:real^N) IN U INTER S` THEN
    UNDISCH_TAC `U INTER S SUBSET U INTER (V:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^2->real^2)((phi:real^N->real^2) x0) = psi x0`
  ASSUME_TAC THENL
   [USE_THEN "GS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^N->real^2) x0 IN IMAGE phi (U INTER V)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^2->real^2) differentiable (at ((phi:real^N->real^2) x0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (phi:real^N->real^2) (U INTER V)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. inv(norm((lP:real^2->real^3) z + yP)) % (lP z + yP))
                differentiable (at ((G:real^2->real^2)((phi:real^N->real^2) x0)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^2 | ~((lP:real^2->real^3) z + yP = vec 0)}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    USE_THEN "nz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SLP_CHAIN] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL [`G:real^2->real^2`; `G':real^2->real^2`]
    MOI_SLP_TRANS_INJ) THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (phi:real^N->real^2) (U INTER V)`;
                        `IMAGE (psi:real^N->real^2) (V INTER U)`;
                        `(phi:real^N->real^2) x0`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "G1" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^N) IN U INTER V`)]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `(x:real^N) IN U INTER V` THEN SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "G1" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^N) IN U INTER V`)]) THEN
    USE_THEN "G2" MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^N) IN U INTER V` THEN SET_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[]
     (ISPEC `\z:real^2. (lP:real^2->real^3) z + yP` MOI_SLP_GPSI_KERNEL)) THEN
    MAP_EVERY EXISTS_TAC [`lP:real^2->real^3`;
                          `yP:real^3`;
                          `IMAGE (psi:real^N->real^2) (U INTER S)`;
                          `(psi:real^N->real^2) x0`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `frechet_derivative
                  (\z. inv(norm((lP:real^2->real^3) z + yP)) % (lP z + yP))
                  (at ((psi:real^N->real^2) x0))
                  (frechet_derivative (G:real^2->real^2)
                     (at ((phi:real^N->real^2) x0)) z) = vec 0` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN USE_THEN "nz" ACCEPT_TAC;
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x1:real^N` THEN DISCH_TAC THEN
      X_GEN_TAC `x2:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x1:real^N) IN S /\ x2 IN S` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x1:real^N) IN U INTER S` THEN
        UNDISCH_TAC `(x2:real^N) IN U INTER S` THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "hS" (fun th -> REWRITE_TAC[GSYM(CONJUNCT2(MATCH_MP th
        (ASSUME `(x1:real^N) IN S`)))]) THEN
      USE_THEN "hS" (fun th -> REWRITE_TAC[GSYM(CONJUNCT2(MATCH_MP th
        (ASSUME `(x2:real^N) IN S`)))]) THEN
      DISCH_TAC THEN AP_TERM_TAC THEN
      USE_THEN "hinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The angular rescaling in gnomonic coordinates; charts of the link atlas   *)
(* built from star charts; the chart of the tetrahedron over a link          *)
(* triangle.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_GNOM_V3 = prove
 (`!z h. moi_smo_gnom(moi_sed_v3 z h) = z / Cx h`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_smo_gnom; moi_sed_v3; VECTOR_3] THEN
  REWRITE_TAC[COMPLEX_EQ; RE_DIV_CX; IM_DIV_CX] THEN
  REWRITE_TAC[RE_DEF; IM_DEF; VECTOR_2]);;

let MOI_SLP_TWIST_ANG_POLAR = prove
 (`!k th r a z.
     &0 <= r /\ &0 <= a /\ a <= pi /\ &0 < z
     ==> moi_smo_gnom(moi_smo_rotz (k * th)
                       (moi_smo_twist k (moi_sed_v3 (Cx r * cexp(ii * Cx a)) z))) =
         moi_smo_ang k th
           (moi_smo_gnom(moi_smo_rotz th (moi_sed_v3 (Cx r * cexp(ii * Cx a)) z)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a < &2 * pi` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SED_TWIST_POLAR; MOI_SED_ROTZ_POLAR; MOI_SLP_GNOM_V3] THEN
  REWRITE_TAC[moi_smo_ang] THEN
  SUBGOAL_THEN
   `norm((Cx r * cexp(ii * Cx(a + th))) / Cx z) = r / z`
  SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
                NORM_CEXP_II; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= r ==> abs r = r`;
                 REAL_ARITH `&0 < z ==> abs z = z`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cexp(--(ii * Cx th)) * (Cx r * cexp(ii * Cx(a + th))) / Cx z =
    Cx(r / z) * cexp(ii * Cx a)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `cexp(ii * Cx(a + th)) = cexp(ii * Cx a) * cexp(ii * Cx th)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM CEXP_ADD; CX_ADD] THEN AP_TERM_TAC THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MP_TAC(SPEC `ii * Cx th` CEXP_NEG_LMUL) THEN
    REWRITE_TAC[CX_DIV] THEN
    UNDISCH_TAC `&0 < z` THEN
    REWRITE_TAC[GSYM CX_INJ; REAL_ARITH `&0 < z <=> ~(z = &0) /\ &0 <= z`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(Cx z = Cx(&0))` MP_TAC THENL
     [ASM_REWRITE_TAC[CX_INJ]; ALL_TAC] THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `r = &0` THENL
   [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; COMPLEX_MUL_LZERO;
                    complex_div; COMPLEX_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `Arg(Cx(r / z) * cexp(ii * Cx a)) = a` SUBST1_TAC THENL
   [MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC `r / z` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CX_DIV; REAL_ARITH `k * (th + a) = k * a + k * th`] THEN
  SUBGOAL_THEN `~(Cx z = Cx(&0))` MP_TAC THENL
   [REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC COMPLEX_FIELD);;

let MOI_SLP_TWIST_ANG = prove
 (`!k th y:real^3.
     &0 <= y$2 /\ &0 < y$3
     ==> moi_smo_gnom(moi_smo_rotz (k * th) (moi_smo_twist k y)) =
         moi_smo_ang k th (moi_smo_gnom(moi_smo_rotz th y))`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SPEC `y:real^3` MOI_SED_POLAR) THEN
  MATCH_MP_TAC MOI_SLP_TWIST_ANG_POLAR THEN
  ASM_REWRITE_TAC[NORM_POS_LE; ARG; ARG_LE_PI; IM]);;

(* Charts of the link atlas built from star charts.                          *)

let MOI_SLP_LINK_ATLAS_IN = prove
 (`!c (v:real^N) U0 (kappa:real^N->real^3) (R:real^3->real^3).
     (U0,kappa) IN moi_smo_star_atlas c v /\ orthogonal_transformation R
     ==> ({l | l IN UNIONS(simplicial_link c v) /\
               v + inv(&2) % (l - v) IN U0 /\
               &0 < (R(kappa(v + inv(&2) % (l - v))))$3},
          (\l. moi_smo_gnom(R(kappa(v + inv(&2) % (l - v)))))) IN
         moi_smo_link_atlas c v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_smo_link_atlas; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`U0:real^N->bool`; `kappa:real^N->real^3`;
                        `R:real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_SLP_LINK_SMOOTH_ATLAS = prove
 (`!c (v:real^N).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c
     ==> smooth_manifold_atlas (subtopology euclidean (UNIONS(simplicial_link c v)))
                               (moi_smo_link_atlas c v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(:N)` MOI_SMO_LINK_ATLAS_FROM_EDGE) THEN
  REWRITE_TAC[MOI_SMO_EDGE; MOI_SMO_LINK_ATLAS_STATEMENT] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Midpoints with the apex of relative interior points of link simplices.   *)

let MOI_SLP_MID_RELINT_TRI = prove
 (`!v p q r l:real^N.
     ~(v = p) /\ ~(v = q) /\ ~(v = r) /\ ~(p = q) /\ ~(p = r) /\ ~(q = r) /\
     ~affine_dependent {v,p,q,r} /\ l IN relative_interior(convex hull {p,q,r})
     ==> v + inv(&2) % (l - v) IN relative_interior(convex hull {v,p,q,r})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent {p:real^N,q,r}` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `{v:real^N,p,q,r}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(l:real^N) IN relative_interior(convex hull {p,q,r})` THEN
  ASM_SIMP_TAC[MOI_SBA_RELINT_3; MOI_SBA_RELINT_4] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
    (X_CHOOSE_THEN `g:real` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`inv(&2)`; `a / &2`; `b / &2`; `g / &2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  VECTOR_ARITH_TAC);;

let MOI_SLP_MID_RELINT_EDGE = prove
 (`!v p q l:real^N.
     ~(v = p) /\ ~(v = q) /\ ~(p = q) /\ ~affine_dependent {v,p,q} /\
     l IN relative_interior(convex hull {p,q})
     ==> v + inv(&2) % (l - v) IN relative_interior(convex hull {v,p,q})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(l:real^N) IN relative_interior(convex hull {p,q})` THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT] THEN
  REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real`
    STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[MOI_SBA_RELINT_3] THEN
  MAP_EVERY EXISTS_TAC [`inv(&2)`; `(&1 - u) / &2`; `u / &2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  VECTOR_ARITH_TAC);;

(* Gnomonic projection after a linear map is invariant under halving.       *)

let MOI_SLP_GNOM_HALF = prove
 (`!(R:real^3->real^3) (A:real^N->real^3) v x.
     linear R /\ (?l y. linear l /\ !x. A x = l x + y) /\ A v = vec 0
     ==> moi_smo_gnom(R(A(v + inv(&2) % (x - v)))) = moi_smo_gnom(R(A x)) /\
         (R(A(v + inv(&2) % (x - v))))$3 = inv(&2) * (R(A x))$3`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(A:real^N->real^3)(v + inv(&2) % (x - v)) = inv(&2) % A x`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_HOMOG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_CMUL; VECTOR_MUL_COMPONENT] THEN
  MATCH_MP_TAC MOI_SLK_GNOM_CMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* The chart of the tetrahedron over a link triangle t, rotated so that the  *)
(* given point p of t goes to the positive third axis.                       *)

let MOI_SLP_TCHART = prove
 (`!c (v:real^N) t p.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     t IN simplicial_link c v /\ aff_dim t = &2 /\ p IN t
     ==> ?U phi (A:real^N->real^3) (R:real^3->real^3).
            (U,phi) IN moi_smo_link_atlas c v /\
            relative_interior t SUBSET U /\
            moi_smo_regmap (convex hull (v INSERT t)) A /\ A v = vec 0 /\
            orthogonal_transformation R /\
            R(A p) = norm(A p) % basis 3 /\ &0 < norm(A p) /\
            (!x. x IN t ==> &0 < (R(A x))$3) /\
            (!x. phi x = moi_smo_gnom(R(A x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_SLP_TET_REG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                 `A:real^N->real^3`] MOI_SLP_REG_GOOD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (CONJUNCTS_THEN2 (LABEL_TAC "dot") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `&0 < norm((A:real^N->real^3) p)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POS_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `p:real^N = v` SUBST_ALL_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[];
      ASM_MESON_TAC[HULL_INC]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(A:real^N->real^3) p` MOI_SLP_ROT_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^N. x IN t ==> &0 < ((R:real^3->real^3)(A x))$3`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_SLP_ROT_POS THEN
    MAP_EVERY EXISTS_TAC [`(A:real^N->real^3) p`; `norm((A:real^N->real^3) p)`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "dot" (MP_TAC o SPECL [`x:real^N`; `p:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(R:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[orthogonal_transformation]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`{l | l IN UNIONS(simplicial_link c v) /\
          v + inv(&2) % (l - v) IN relative_interior(convex hull (v INSERT t)) /\
          &0 < ((R:real^3->real^3)((A:real^N->real^3)
                 (v + inv(&2) % (l - v))))$3}`;
    `\l. moi_smo_gnom((R:real^3->real^3)((A:real^N->real^3)
                       (v + inv(&2) % (l - v))))`;
    `A:real^N->real^3`; `R:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLP_LINK_ATLAS_IN THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
      MOI_SLP_TET_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p0:real^N` (X_CHOOSE_THEN `q0:real^N`
      (X_CHOOSE_THEN `r0:real^N` STRIP_ASSUME_TAC))) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `l:real^N` THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SLP_MID_RELINT_TRI THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MP_TAC(ISPECL [`R:real^3->real^3`; `A:real^N->real^3`; `v:real^N`;
                     `l:real^N`] MOI_SLP_GNOM_HALF) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
      REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    X_GEN_TAC `x:real^N` THEN
    MP_TAC(ISPECL [`R:real^3->real^3`; `A:real^N->real^3`; `v:real^N`;
                   `x:real^N`] MOI_SLP_GNOM_HALF) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The triangle over a link edge and the unfolding chart of it, rotated so   *)
(* that a given relative interior point of the edge goes to the positive     *)
(* third axis.                                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_TRI_FACTS = prove
 (`!c (v:real^N) f.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     f IN simplicial_link c v /\ aff_dim f = &1
     ==> ?p q. ~(v = p) /\ ~(v = q) /\ ~(p = q) /\ ~affine_dependent {v,p,q} /\
               f = convex hull {p,q} /\
               convex hull (v INSERT f) = convex hull {v,p,q} /\
               convex hull {v,p,q} IN c /\
               aff_dim(convex hull {v,p,q}) = &2 /\
               v extreme_point_of convex hull {v,p,q} /\
               f SUBSET convex hull {v,p,q}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SCF_CM_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `f:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (MP_TAC o SPEC `v:real^N`) ASSUME_TAC))))) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `f:real^N->bool`]
    MOI_SCF_LINK_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~affine_dependent(C:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `(v:real^N) INSERT C` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN
    ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `aff_dim(f:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[INT_ARITH `&n - &1:int = &1 <=> &n:int = &2`] THEN
    REWRITE_TAC[INT_OF_NUM_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`] THEN
  SUBGOAL_THEN `~(v:real^N = p) /\ ~(v = q)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~((v:real^N) IN C)` THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull ((v:real^N) INSERT f) = convex hull {v,p,q}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SCF_HULL_INSERT_HULL]; ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {v:real^N,p,q}` ASSUME_TAC THENL
   [UNDISCH_TAC `~affine_dependent((v:real^N) INSERT C)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `convex hull ((v:real^N) INSERT f) = convex hull {v,p,q}`)) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim(convex hull {v:real^N,p,q}) = &1 + &1` THEN
  INT_ARITH_TAC);;

let MOI_SLP_AFFINE_APEX_ZERO = prove
 (`!(A:real^N->real^M) v x.
     (?l y. linear l /\ !x. A x = l x + y) /\
     A(v + inv(&2) % (x - v)) = inv(&2) % A x
     ==> A v = vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^N->real^M`
    (X_CHOOSE_THEN `y:real^M` STRIP_ASSUME_TAC)) MP_TAC) THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; LINEAR_SUB] THEN VECTOR_ARITH_TAC);;

let SPDR5_UCHART_SCALE = prove
 (`!(R:real^3->real^3) (b:real^3) (q:real^3).
     linear R /\ R b = norm b % basis 3 /\ ~(b = vec 0) /\ q = &2 % b
     ==> &0 < &2 * norm b /\ R q = (&2 * norm b) % basis 3`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[NORM_POS_LT] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[LINEAR_CMUL; VECTOR_MUL_ASSOC]]);;

let MOI_SLP_UCHART = prove
 (`!c (v:real^N) f p.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     f IN simplicial_link c v /\ aff_dim f = &1 /\ p IN relative_interior f
     ==> ?U phi (R:real^3->real^3).
            (U,phi) IN moi_smo_link_atlas c v /\
            relative_interior f SUBSET U /\ phi p = vec 0 /\
            orthogonal_transformation R /\
            !t. t IN simplicial_link c v /\ aff_dim t = &2 /\ f SUBSET t
                ==> ?A:real^N->real^3.
                       moi_smo_regmap (convex hull (v INSERT t)) A /\ A v = vec 0 /\
                       (?c0. &0 < c0 /\ R(A p) = c0 % basis 3) /\
                       (!x. x IN t ==> &0 < (R(A x))$3) /\
                       (!x. x IN t INTER U ==> phi x = moi_smo_gnom(R(A x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SCF_CM_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `f:real^N->bool`]
    MOI_SLP_TRI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^N` (X_CHOOSE_THEN `q0:real^N`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `tri = convex hull {v:real^N,p0,q0}` THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tri:real^N->bool`; `v:real^N`]
    MOI_SBA_UNFOLD_STAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real^3` (CONJUNCTS_THEN2
    (LABEL_TAC "unf") (LABEL_TAC "hom"))) THEN
  SUBGOAL_THEN `(moi_smo_open_star c tri,u:real^N->real^3) IN
                moi_smo_star_atlas c (v:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SBA_STAR_ATLAS_IN; IN_UNION] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[MOI_SBA_UNFOLD_ATLAS_IN] THEN
      EXISTS_TAC `tri:real^N->bool` THEN ASM_REWRITE_TAC[];
      USE_THEN "hom" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l:real^N. l IN relative_interior f
                           ==> v + inv(&2) % (l - v) IN relative_interior tri`
  (LABEL_TAC "midf") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "tri" THEN
    MATCH_MP_TAC MOI_SLP_MID_RELINT_EDGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior tri SUBSET moi_smo_open_star c (tri:real^N->bool)`
  (LABEL_TAC "rtri") THENL
   [MATCH_MP_TAC MOI_SBA_RELINT_IN_STAR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN f)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `f:real^N->bool`]
      MOI_SCF_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p:real^N = v)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((v:real^N) IN f)` THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((u:real^N->real^3)(v + inv(&2) % (p - v)) = vec 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SLK_NONZERO THEN
    MAP_EVERY EXISTS_TAC [`moi_smo_open_star c (tri:real^N->bool)`; `v:real^N`] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `moi_sba_unf c tri (u:real^N->real^3)` THEN
      REWRITE_TAC[moi_sba_unf] THEN MESON_TAC[];
      USE_THEN "hom" ACCEPT_TAC;
      ASM SET_TAC[];
      REWRITE_TAC[VECTOR_ARITH `v + a % (p - v):real^N = v <=> a % (p - v) = vec 0`;
                  VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(u:real^N->real^3)(v + inv(&2) % (p - v))` MOI_SLP_ROT_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `linear(R:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[orthogonal_transformation]; ALL_TAC] THEN
  ABBREV_TAC `U = {l | l IN UNIONS(simplicial_link c v) /\
                       v + inv(&2) % (l - v) IN moi_smo_open_star c tri /\
                       &0 < ((R:real^3->real^3)((u:real^N->real^3)
                              (v + inv(&2) % (l - v))))$3}` THEN
  (* The key claim, for every link triangle over f. *)
  SUBGOAL_THEN
   `!t. t IN simplicial_link c v /\ aff_dim t = &2 /\ f SUBSET t
        ==> ?A:real^N->real^3.
               moi_smo_regmap (convex hull (v INSERT t)) A /\ A v = vec 0 /\
               (!x. x IN convex hull (v INSERT t) INTER moi_smo_open_star c tri
                    ==> u x = A x) /\
               (?c0. &0 < c0 /\ (R:real^3->real^3)(A p) = c0 % basis 3) /\
               (!x. x IN t ==> &0 < (R(A x))$3)`
  (LABEL_TAC "key") THENL
   [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
      MOI_SLP_TET_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p1:real^N` (X_CHOOSE_THEN `q1:real^N`
      (X_CHOOSE_THEN `r1:real^N` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `tri SUBSET convex hull ((v:real^N) INSERT t)` ASSUME_TAC THENL
     [UNDISCH_TAC `convex hull ((v:real^N) INSERT f) = tri` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC HULL_MONO THEN
      UNDISCH_TAC `(f:real^N->bool) SUBSET t` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_sba_unf c tri (u:real^N->real^3)` THEN
    REWRITE_TAC[moi_sba_unf] THEN
    DISCH_THEN(MP_TAC o SPEC `convex hull ((v:real^N) INSERT t)` o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uA"))) THEN
    EXISTS_TAC `A:real^N->real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `?l y. linear l /\ !x. (A:real^N->real^3) x = l x + y`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE]; ALL_TAC] THEN
    SUBGOAL_THEN `(A:real^N->real^3) v = vec 0` ASSUME_TAC THENL
     [SUBGOAL_THEN `?x:real^N. x IN relative_interior(convex hull (v INSERT t))`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
        ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; CONVEX_CONVEX_HULL] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_SLP_AFFINE_APEX_ZERO THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^N) IN moi_smo_open_star c tri` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_SED_RELINT_IN_STAR THEN
        EXISTS_TAC `convex hull ((v:real^N) INSERT t)` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      USE_THEN "hom" (MP_TAC o SPECL [`x:real^N`; `inv(&2)`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
      SUBGOAL_THEN `(x:real^N) IN convex hull (v INSERT t) /\
                    v + inv(&2) % (x - v) IN convex hull (v INSERT t)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
          MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN
          REWRITE_TAC[CONVEX_CONVEX_HULL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(u:real^N->real^3) x = A x /\
        u(v + inv(&2) % (x - v)) = A(v + inv(&2) % (x - v))`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN USE_THEN "uA" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
        ALL_TAC] THEN
      MAP_EVERY (fun t -> SUBST1_TAC(SYM(ASSUME t)))
       [`(u:real^N->real^3) x = A x`;
        `(u:real^N->real^3)(v + inv(&2) % (x - v)) =
         A(v + inv(&2) % (x - v))`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                   `A:real^N->real^3`] MOI_SLP_REG_GOOD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (CONJUNCTS_THEN2 (LABEL_TAC "dot") STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(p:real^N) IN t` ASSUME_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(A:real^N->real^3) p =
      &2 % (u:real^N->real^3)(v + inv(&2) % (p - v))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(u:real^N->real^3)(v + inv(&2) % (p - v)) =
                    A(v + inv(&2) % (p - v))` SUBST1_TAC THENL
       [USE_THEN "uA" MATCH_MP_TAC THEN
        REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
         [MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN
          REWRITE_TAC[CONVEX_CONVEX_HULL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          ASM SET_TAC[];
          ASM SET_TAC[]];
        ALL_TAC] THEN
      ASM_SIMP_TAC[MOI_SBA_AFFINE_HOMOG; VECTOR_MUL_ASSOC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < &2 * norm((u:real^N->real^3)(v + inv(&2) % (p - v))) /\
      (R:real^3->real^3)((A:real^N->real^3) p) =
      (&2 * norm((u:real^N->real^3)(v + inv(&2) % (p - v)))) % basis 3`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC SPDR5_UCHART_SCALE THEN REPEAT CONJ_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `&2 * norm((u:real^N->real^3)(v + inv(&2) % (p - v)))` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_SLP_ROT_POS THEN
    MAP_EVERY EXISTS_TAC
     [`(A:real^N->real^3) p`;
      `&2 * norm((u:real^N->real^3)(v + inv(&2) % (p - v)))`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    USE_THEN "dot" (MP_TAC o SPECL [`x:real^N`; `p:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Now the chart. *)
  SUBGOAL_THEN `?t0. t0 IN simplicial_link c v /\ aff_dim t0 = &2 /\
                     (f:real^N->bool) SUBSET t0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:N)` MOI_SMO_SURFACE_COMPLEX) THEN
    REWRITE_TAC[MOI_SMO_SURFACE_COMPLEX_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPEC `simplicial_link c (v:real^N)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `f:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior f SUBSET (U:real^N->bool)` ASSUME_TAC THENL
   [USE_THEN "key" (MP_TAC o SPEC `t0:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `A0:real^N->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "uA0")
      (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pos0")))))) THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `l:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `(l:real^N) IN f` ASSUME_TAC THENL
     [UNDISCH_TAC `(l:real^N) IN relative_interior f` THEN
      MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `(l:real^N) IN t0` ASSUME_TAC THENL
     [UNDISCH_TAC `(f:real^N->bool) SUBSET t0` THEN
      UNDISCH_TAC `(l:real^N) IN f` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `v + inv(&2) % (l - v) IN moi_smo_open_star c (tri:real^N->bool)`
    ASSUME_TAC THENL
     [USE_THEN "rtri" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      USE_THEN "midf" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `f:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(u:real^N->real^3)(v + inv(&2) % (l - v)) = A0(v + inv(&2) % (l - v))`
    SUBST1_TAC THENL
     [USE_THEN "uA0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
      MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN
      REWRITE_TAC[CONVEX_CONVEX_HULL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`R:real^3->real^3`; `A0:real^N->real^3`; `v:real^N`;
                   `l:real^N`] MOI_SLP_GNOM_HALF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE];
      DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[] THEN USE_THEN "pos0" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`U:real^N->bool`;
    `\l. moi_smo_gnom((R:real^3->real^3)((u:real^N->real^3)
                       (v + inv(&2) % (l - v))))`;
    `R:real^3->real^3`] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC MOI_SLP_LINK_ATLAS_IN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `relative_interior f SUBSET (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SLP_GNOM_ZERO THEN
    ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  USE_THEN "key" (MP_TAC o SPEC `t:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "uA1")
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  EXISTS_TAC `A:real^N->real^3` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN EXPAND_TAC "U" THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(u:real^N->real^3)(v + inv(&2) % (x - v)) = A(v + inv(&2) % (x - v))`
  SUBST1_TAC THENL
   [USE_THEN "uA1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
    MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:real^3->real^3`; `A:real^N->real^3`; `v:real^N`;
                 `x:real^N`] MOI_SLP_GNOM_HALF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_SBA_REGMAP_AFFINE];
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The edge chart at an edge [v,w] conical at v, in normal form (A v = 0,    *)
(* A w = basis 3); the cone chart of the link at the link vertex w.          *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_ECHART_NF = prove
 (`!c (v:real^N) w (kappa:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\ ~(v = w) /\
     convex hull {v,w} IN c /\
     (moi_smo_open_star c (convex hull {v,w}),kappa) IN moi_smo_edge_atlas c /\
     (moi_smo_open_star c (convex hull {v,w}),kappa) IN moi_smo_star_atlas c v
     ==> !tet. tet IN c /\ aff_dim tet = &3 /\ convex hull {v,w} SUBSET tet
               ==> ?A th. moi_smo_regmap tet A /\ A v = vec 0 /\ A w = basis 3 /\
                          (!p. p extreme_point_of tet /\ ~(p = v) /\ ~(p = w)
                               ==> &0 <= (A p)$2) /\
                          (!x. x IN tet INTER
                                    moi_smo_open_star c (convex hull {v,w})
                               ==> kappa x =
                                   moi_smo_rotz
                                    (moi_smo_edge_factor c (convex hull {v,w}) * th)
                                    (moi_smo_twist
                                     (moi_smo_edge_factor c (convex hull {v,w}))
                                     (A x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x t. x IN moi_smo_open_star c (convex hull {v,w}) /\ &0 < t /\ t <= &1
          ==> v + t % (x - v) IN moi_smo_open_star c (convex hull {v,w}) /\
              (kappa:real^N->real^3)(v + t % (x - v)) = t % kappa x`
  (LABEL_TAC "hom") THENL
   [UNDISCH_TAC `(moi_smo_open_star c (convex hull {v,w}),kappa) IN
                 moi_smo_star_atlas c (v:real^N)` THEN
    REWRITE_TAC[MOI_SBA_STAR_ATLAS_IN] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(moi_smo_open_star c (convex hull {v,w}),kappa) IN
               moi_smo_edge_atlas (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_smo_edge_atlas; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` (X_CHOOSE_THEN `kappa':real^N->real^3`
    (CONJUNCTS_THEN2 MP_TAC MP_TAC))) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `a:real^N`
      (X_CHOOSE_THEN `b:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "eqe") (LABEL_TAC "nf")))))))) THEN
  SUBGOAL_THEN `convex hull {v:real^N,w} = e'` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SVX_OPEN_STAR_EQ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
      USE_THEN "eqe" SUBST1_TAC THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MESON_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `convex hull {v:real^N,w} = e'`)) THEN
  SUBGOAL_THEN `(a:real^N = v /\ b = w) \/ (a = w /\ b = v)` MP_TAC THENL
   [MATCH_MP_TAC MOI_SED_SEGMENT_ENDS THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "eqe" (fun th -> REWRITE_TAC[th; SEGMENT_CONVEX_HULL]);
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THENL
   [X_GEN_TAC `tet:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "nf" (MP_TAC o SPEC `tet:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `A:real^N->real^3` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `th:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `convex hull {v:real^N,w}`]
    MOI_SCF_CF_PURE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tet:real^N->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "nf" (MP_TAC o SPEC `tet:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` (X_CHOOSE_THEN `th:real`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?x:real^N. x IN relative_interior tet` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `convex(tet:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_SBA_LF_CONVEX]; ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim({}:real^N->bool) = &3` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN moi_smo_open_star c (convex hull {v,w})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SED_RELINT_IN_STAR THEN EXISTS_TAC `tet:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN tet /\ (v:real^N) IN tet` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `convex hull {v:real^N,w} SUBSET tet`)) THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t0. &0 < t0 /\ t0 <= &1
         ==> norm(basis 3 + t0 % ((A:real^N->real^3) x - basis 3)) =
             t0 * norm(A x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t0:real` THEN STRIP_TAC THEN
    USE_THEN "hom" (MP_TAC o SPECL [`x:real^N`; `t0:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `v + t0 % (x - v):real^N IN tet` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[MOI_SBA_LF_CONVEX]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`A:real^N->real^3`; `v:real^N`; `x:real^N`; `t0:real`]
      MOI_SVX_AFFINE_SEG) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[moi_smo_regmap]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `!y. y IN tet INTER moi_smo_open_star c (convex hull {v,w})
          ==> norm((kappa:real^N->real^3) y) = norm((A:real^N->real^3) y)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_SMO_TWIST_NORM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `norm((A:real^N->real^3) (v + t0 % (x - v))) =
      norm((kappa:real^N->real^3) (v + t0 % (x - v)))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SVX_TWO_SCALES THEN
  EXISTS_TAC `(A:real^N->real^3) x` THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let MOI_SLP_TWIST_E3 = prove
 (`!k a. moi_smo_rotz a (moi_smo_twist k (basis 3)) = basis 3`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[moi_smo_rotz; moi_smo_twist; CART_EQ; DIMINDEX_3; FORALL_3;
           VECTOR_3; BASIS_COMPONENT; ARITH] THEN
  REWRITE_TAC[GSYM CX_DEF; COMPLEX_NORM_CX; REAL_ABS_0; REAL_MUL_LZERO] THEN
  REAL_ARITH_TAC);;

let MOI_SLP_EDGE_FACTOR_POS = prove
 (`!c (e:real^N->bool).
     FINITE c /\ (?tet. tet IN c /\ aff_dim tet = &3 /\ e SUBSET tet)
     ==> &0 < moi_smo_edge_factor c e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_smo_edge_factor] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[PI_POS] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN
  REWRITE_TAC[MOI_SED_ALPHA; REAL_OF_NUM_LT] THEN
  REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  SUBGOAL_THEN `FINITE {tet | tet IN c /\ aff_dim tet = &3 /\
                              (e:real^N->bool) SUBSET tet}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let MOI_SLP_ECHART = prove
 (`!c (v:real^N) w.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     {w} IN simplicial_link c v
     ==> ?U phi k.
            (U,phi) IN moi_smo_link_atlas c v /\ w IN U /\ phi w = vec 0 /\
            &0 < k /\
            !t. t IN simplicial_link c v /\ aff_dim t = &2 /\ w IN t
                ==> ?(A:real^N->real^3) th.
                       moi_smo_regmap (convex hull (v INSERT t)) A /\ A v = vec 0 /\
                       A w = basis 3 /\
                       (!x. x IN convex hull (v INSERT t) ==> &0 <= (A x)$2) /\
                       (!x. x IN t INTER U
                            ==> phi x = moi_smo_ang k th
                                          (moi_smo_gnom(moi_smo_rotz th (A x))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SCF_CM_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `{w:real^N}`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[EXTREME_POINT_OF_SING; AFF_DIM_SING; IN_SING] THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_ADD_CONV) THEN STRIP_TAC THEN
  ABBREV_TAC `e = convex hull {v:real^N,w}` THEN
  SUBGOAL_THEN `(v:real^N) extreme_point_of e` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `(:N)` MOI_SMO_EDGE) THEN
  REWRITE_TAC[MOI_SMO_EDGE_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`e:real^N->bool`; `v:real^N`] o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `w:real^N`;
                 `kappa:real^N->real^3`] MOI_SLP_ECHART_NF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "nf") THEN
  SUBGOAL_THEN `?tet0. tet0 IN c /\ aff_dim tet0 = &3 /\ e SUBSET (tet0:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_CF_PURE THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "e" THEN REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  ABBREV_TAC `k = moi_smo_edge_factor c (e:real^N->bool)` THEN
  SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC MOI_SLP_EDGE_FACTOR_POS THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `v + inv(&2) % (w - v) IN moi_smo_open_star c (e:real^N->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`]
      MOI_SBA_RELINT_IN_STAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "e" THEN
    REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `v + inv(&2) % (w - v):real^N = midpoint(v,w)` SUBST1_TAC THENL
     [REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC;
      ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(kappa:real^N->real^3)(v + inv(&2) % (w - v)) = inv(&2) % basis 3`
  ASSUME_TAC THENL
   [USE_THEN "nf" (MP_TAC o SPEC `tet0:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `A0:real^N->real^3` (X_CHOOSE_THEN `th0:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
        (LABEL_TAC "k0"))))))) THEN
    SUBGOAL_THEN `v + inv(&2) % (w - v) IN (tet0:real^N->bool)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `(e:real^N->bool) SUBSET tet0`)) THEN
      EXPAND_TAC "e" THEN REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; IN_SEGMENT] THEN
      EXISTS_TAC `inv(&2)` THEN REPEAT CONJ_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; CONV_TAC REAL_RAT_REDUCE_CONV;
        VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(A0:real^N->real^3)(v + inv(&2) % (w - v)) = inv(&2) % basis 3`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`A0:real^N->real^3`; `v:real^N`; `w:real^N`; `inv(&2)`]
        MOI_SBA_AFFINE_HOMOG) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC MOI_SBA_REGMAP_AFFINE THEN
          EXISTS_TAC `tet0:real^N->bool` THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "k0" (fun th -> REWRITE_TAC[MATCH_MP (REWRITE_RULE[IN_INTER] th)
     (CONJ (ASSUME `v + inv(&2) % (w - v) IN (tet0:real^N->bool)`)
           (ASSUME `v + inv(&2) % (w - v) IN
                    moi_smo_open_star c (e:real^N->bool)`))]) THEN
    ASM_SIMP_TAC[MOI_SMO_TWIST_HOMOG; MOI_SED_ROTZ_CMUL; MOI_SLP_TWIST_E3;
                 REAL_LT_INV_EQ; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`{l | l IN UNIONS(simplicial_link c v) /\
          v + inv(&2) % (l - v) IN moi_smo_open_star c (e:real^N->bool) /\
          &0 < ((\x:real^3. x)((kappa:real^N->real^3)
                 (v + inv(&2) % (l - v))))$3}`;
    `\l. moi_smo_gnom((\x:real^3. x)((kappa:real^N->real^3)
                       (v + inv(&2) % (l - v))))`;
    `k:real`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLP_LINK_ATLAS_IN THEN
    ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    CONJ_TAC THENL [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[IN_SING];
                    CONV_TAC REAL_RAT_REDUCE_CONV];
    MATCH_MP_TAC MOI_SLP_GNOM_ZERO THEN REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `e SUBSET convex hull ((v:real^N) INSERT t)` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_SLP_TET_REG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                 `A1:real^N->real^3`] MOI_SLP_REG_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  USE_THEN "nf" (MP_TAC o SPEC `convex hull ((v:real^N) INSERT t)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `A:real^N->real^3` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `th:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "kA"))))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:real^N. x IN convex hull (v INSERT t) ==> &0 <= ((A:real^N->real^3) x)$2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SED_TET_UHS THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`; `w:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `v + inv(&2) % (x - v) IN convex hull ((v:real^N) INSERT t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  USE_THEN "kA" (fun th -> REWRITE_TAC[MATCH_MP (REWRITE_RULE[IN_INTER] th)
     (CONJ (ASSUME `v + inv(&2) % (x - v) IN convex hull ((v:real^N) INSERT t)`)
           (ASSUME `v + inv(&2) % (x - v) IN
                    moi_smo_open_star c (e:real^N->bool)`))]) THEN
  SUBGOAL_THEN `(A:real^N->real^3)(v + inv(&2) % (x - v)) = inv(&2) % A x`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_HOMOG THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SBA_REGMAP_AFFINE THEN
    EXISTS_TAC `convex hull ((v:real^N) INSERT t)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[MOI_SMO_TWIST_HOMOG; MOI_SED_ROTZ_CMUL; REAL_LT_INV_EQ;
           REAL_OF_NUM_LT; ARITH] THEN
  SIMP_TAC[MOI_SLK_GNOM_CMUL; REAL_LT_INV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC MOI_SLP_TWIST_ANG THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC HULL_INC THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                 `A:real^N->real^3`] MOI_SLP_REG_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `w:real^N`] o CONJUNCT1 o CONJUNCT2 o
    CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Equal norms of gnomonic images (regular distances agree on common faces)  *)
(* and the general form of clause (2) of moi_smo_conical_pd.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_GNOM_NORM_FORMULA = prove
 (`!Y:real^3. norm(moi_smo_gnom Y) pow 2 = (norm Y pow 2 - (Y$3) pow 2) / (Y$3) pow 2`,
  GEN_TAC THEN REWRITE_TAC[NORM_POW_2; DOT_2; DOT_3; MOI_SLK_GNOM_COMPONENTS] THEN
  ASM_CASES_TAC `(Y:real^3)$3 = &0` THEN
  ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_POW_ZERO;
                  ARITH_EQ; REAL_INV_0; REAL_ADD_LID] THEN
  UNDISCH_TAC `~((Y:real^3)$3 = &0)` THEN CONV_TAC REAL_FIELD);;

let MOI_SLP_GNOM_NORM_EQ = prove
 (`!(R1:real^3->real^3) R2 y1 y2 w1 w2 c1 c2.
     orthogonal_transformation R1 /\ orthogonal_transformation R2 /\
     R1 w1 = c1 % basis 3 /\ R2 w2 = c2 % basis 3 /\ &0 < c1 /\ &0 < c2 /\
     norm y1 = norm y2 /\ norm w1 = norm w2 /\ norm(y1 - w1) = norm(y2 - w2)
     ==> norm(moi_smo_gnom(R1 y1)) = norm(moi_smo_gnom(R2 y2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c1 = norm(w1:real^3) /\ c2 = norm(w2:real^3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`R1:real^3->real^3`] ORTHOGONAL_TRANSFORMATION) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w1:real^3` o CONJUNCT2);
      MP_TAC(ISPECL [`R2:real^3->real^3`] ORTHOGONAL_TRANSFORMATION) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w2:real^3` o CONJUNCT2)] THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(R:real^3->real^3) y w c.
      orthogonal_transformation R /\ R w = c % basis 3 /\ &0 < c
      ==> (R y)$3 = (y dot w) / c /\ norm(R y) = norm y`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(R:real^3->real^3) y dot R w = y dot w` MP_TAC THENL
       [ASM_MESON_TAC[orthogonal_transformation]; ALL_TAC] THEN
      ASM_REWRITE_TAC[DOT_RMUL] THEN SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
      ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(ISPECL [`R1:real^3->real^3`; `y1:real^3`; `w1:real^3`; `c1:real`] th) THEN
    MP_TAC(ISPECL [`R2:real^3->real^3`; `y2:real^3`; `w2:real^3`; `c2:real`] th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[NORM_EQ; GSYM NORM_POW_2; MOI_SLP_GNOM_NORM_FORMULA] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DOT_NORM_SUB] THEN ASM_REWRITE_TAC[]);;

let MOI_SLP_EDGE_AT_VERTEX = prove
 (`!L e (w:real^N).
     simplicial_complex L /\ e IN L /\ aff_dim e = &1 /\ {w} IN L /\ w IN e
     ==> ?p. e = segment[w,p]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(w:real^N) extreme_point_of e` MP_TAC THENL
   [MATCH_MP_TAC MOI_SCF_VERTEX_EXTREME THEN
    EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
               AFFINE_INDEPENDENT_2] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `b:real^N` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL];
    EXISTS_TAC `a:real^N` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    REWRITE_TAC[INSERT_AC]]);;

(* The general clause (2) at a vertex w of L from per-triangle data.         *)

let MOI_SLP_VERTEX_GEN = prove
 (`!c (v:real^N) L (sigma:((real^N->bool)#(real^N->real^2))->bool) w U phi k
    (b:(real^N->bool)->real) (tetf:(real^N->bool)->(real^N->bool))
    (A:(real^N->bool)->real^N->real^3) (R:(real^N->bool)->real^3->real^3).
     lf_simplicial_complex c /\ simplicial_complex L /\ {w} IN L /\
     (U,phi) IN sigma /\ w IN U /\ phi w = vec 0 /\ &0 < k /\
     (!s. s IN L /\ aff_dim s = &2 /\ w IN s
          ==> tetf s IN c /\ v IN tetf s /\ s SUBSET tetf s /\ ~(v IN affine hull s) /\
              moi_smo_regmap (tetf s) (A s) /\ A s v = vec 0 /\
              (!x y. x IN affine hull (tetf s) /\ y IN affine hull (tetf s) /\
                     A s x = A s y ==> x = y) /\
              orthogonal_transformation (R s) /\
              (?c0. &0 < c0 /\ R s (A s w) = c0 % basis 3) /\
              (!x. x IN s ==> &0 < (R s (A s x))$3) /\
              (!x. x IN s ==> &0 <= Im(cexp(--(ii * Cx(b s))) *
                                       moi_smo_gnom(R s (A s x)))) /\
              (!x. x IN s INTER U
                   ==> phi x = moi_smo_ang k (b s) (moi_smo_gnom(R s (A s x)))))
     ==> ?U phi k b Q.
              (U,phi) IN sigma /\ w IN U /\ phi w = vec 0 /\ &0 < k /\
              !s. s IN L /\ aff_dim s = &2 /\ w IN s
                  ==> moi_smo_cell_smooth s ((Q:(real^N->bool)->real^N->real^2) s) /\
                      (!x y. x IN s /\ y IN s /\ Q s x = Q s y ==> x = y) /\
                      Q s w = vec 0 /\
                      (!x. x IN s ==> &0 <= Im(cexp(--(ii * Cx(b s))) * Q s x)) /\
                      (!e. e IN L /\ aff_dim e = &1 /\ w IN e /\ e SUBSET s
                           ==> ?a. !x. x IN e ==> ?t. &0 <= t /\ Q s x = t % a) /\
                      (!x. x IN s INTER U ==> phi x = moi_smo_ang k (b s) (Q s x)) /\
                      (!s' x. s' IN L /\ aff_dim s' = &2 /\ w IN s' /\ x IN s INTER s'
                              ==> norm(Q s x) = norm(Q s' x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dat")))))))) THEN
  MAP_EVERY EXISTS_TAC
   [`U:real^N->bool`; `phi:real^N->real^2`; `k:real`;
    `b:(real^N->bool)->real`;
    `\s x. moi_smo_gnom((R:(real^N->bool)->real^3->real^3) s
                         ((A:(real^N->bool)->real^N->real^3) s x))`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  USE_THEN "dat" (MP_TAC o SPEC `s:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `c0:real` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 (LABEL_TAC "pos") (CONJUNCTS_THEN2 ASSUME_TAC
     ASSUME_TAC))))))))))) THEN
  ABBREV_TAC `As = (A:(real^N->bool)->real^N->real^3) s` THEN
  ABBREV_TAC `Rs = (R:(real^N->bool)->real^3->real^3) s` THEN
  ABBREV_TAC `tets = (tetf:(real^N->bool)->(real^N->bool)) s` THEN
  SUBGOAL_THEN `?l y. linear l /\ !x:real^N. (Rs:real^3->real^3)((As:real^N->real^3) x) =
                                            l x + y`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SBA_REGMAP_AFFINE THEN EXISTS_TAC `tets:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`Rs:real^3->real^3`; `vec 0:real^3`] THEN
      REWRITE_TAC[VECTOR_ADD_RID] THEN ASM_MESON_TAC[orthogonal_transformation]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^N->real^3) v + y = vec 0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `v:real^N`) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[orthogonal_transformation; LINEAR_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x z:real^N. x IN affine hull tets /\ z IN affine hull tets /\
                 (l:real^N->real^3) x + y = l z + y ==> x = z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Rs:real^3->real^3)((As:real^N->real^3) x) = Rs(As z)` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!a b:real^3. (Rs:real^3->real^3) a = Rs b ==> a = b` MP_TAC THENL
     [MATCH_MP_TAC(ISPEC `Rs:real^3->real^3` ORTHOGONAL_TRANSFORMATION_INJECTIVE) THEN
      ASM_REWRITE_TAC[];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> &0 < ((l:real^N->real^3) x + y)$3`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `x:real^N` o check (fun th ->
      can (find_term ((=) `Rs:real^3->real^3`)) (concl th) &&
      is_forall (concl th) && can (find_term ((=) `l:real^N->real^3`)) (concl th))) THEN
    USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLP_CELL_SMOOTH_EQ THEN
    EXISTS_TAC `\x:real^N. moi_smo_gnom((l:real^N->real^3) x + y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SLP_GNOM_CELL THEN
      MAP_EVERY EXISTS_TAC [`v:real^N`; `tets:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`l:real^N->real^3`; `y:real^3`; `v:real^N`; `s:real^N->bool`;
                   `tets:real^N->bool`] MOI_SLP_GNOM_INJ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SLP_GNOM_ZERO THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`; `w:real^N`]
      MOI_SLP_EDGE_AT_VERTEX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `(p:real^N) IN s /\ (w:real^N) IN s` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `segment[w:real^N,p] SUBSET s`)) THEN
      REWRITE_TAC[ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    EXISTS_TAC `moi_smo_gnom((Rs:real^3->real^3)((As:real^N->real^3) p))` THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(l:real^N->real^3) ((&1 - u) % w + u % p) + y =
      (&1 - u) % (l w + y) + u % (l p + y)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_SLP_GNOM_RAY THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(Rs:real^3->real^3)((As:real^N->real^3) w) = c0 % basis 3` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s':real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
    USE_THEN "dat" (MP_TAC o SPEC `s':real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `c1:real` STRIP_ASSUME_TAC)
       (K ALL_TAC)))))))))) THEN
    MATCH_MP_TAC MOI_SLP_GNOM_NORM_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`(As:real^N->real^3) w`; `(A:(real^N->bool)->real^N->real^3) s' w`;
      `c0:real`; `c1:real`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(x:real^N) IN tets INTER (tetf:(real^N->bool)->(real^N->bool)) s' /\
      (v:real^N) IN tets INTER tetf s' /\ (w:real^N) IN tets INTER tetf s'`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(s:real^N->bool) SUBSET tets`;
       `(s':real^N->bool) SUBSET (tetf:(real^N->bool)->(real^N->bool)) s'`;
       `(x:real^N) IN s INTER s'`; `(w:real^N) IN s`; `(w:real^N) IN s'`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!a b:real^N. a IN tets INTER (tetf:(real^N->bool)->(real^N->bool)) s' /\
                   b IN tets INTER tetf s'
                   ==> dist((As:real^N->real^3) a,As b) =
                       dist((A:(real^N->bool)->real^N->real^3) s' a,A s' b)`
    (LABEL_TAC "dd") THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SVX_REGMAP_DIST THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tets:real^N->bool`;
                            `(tetf:(real^N->bool)->(real^N->bool)) s'`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM dist] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "dd" (MP_TAC o C MATCH_MP
       (CONJ (ASSUME `(x:real^N) IN tets INTER
                      (tetf:(real^N->bool)->(real^N->bool)) s'`)
             (ASSUME `(v:real^N) IN tets INTER
                      (tetf:(real^N->bool)->(real^N->bool)) s'`)) o
       SPECL [`x:real^N`; `v:real^N`]) THEN
      REWRITE_TAC[ASSUME `(As:real^N->real^3) v = vec 0`;
                  ASSUME `(A:(real^N->bool)->real^N->real^3) s' v = vec 0`;
                  DIST_0];
      USE_THEN "dd" (MP_TAC o C MATCH_MP
       (CONJ (ASSUME `(w:real^N) IN tets INTER
                      (tetf:(real^N->bool)->(real^N->bool)) s'`)
             (ASSUME `(v:real^N) IN tets INTER
                      (tetf:(real^N->bool)->(real^N->bool)) s'`)) o
       SPECL [`w:real^N`; `v:real^N`]) THEN
      REWRITE_TAC[ASSUME `(As:real^N->real^3) v = vec 0`;
                  ASSUME `(A:(real^N->bool)->real^N->real^3) s' v = vec 0`;
                  DIST_0];
      USE_THEN "dd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The general form of clause (3) of moi_smo_conical_pd (an open edge is     *)
(* straight in a chart that is smooth up to the edge on each triangle).      *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_EDGE_GEN = prove
 (`!(v:real^N) L X (sigma:((real^N->bool)#(real^N->real^2))->bool) e U phi
    (l0:real^N->real^3) y0 (tetf:(real^N->bool)->(real^N->bool))
    (A:(real^N->bool)->real^N->real^3) (R:(real^N->bool)->real^3->real^3).
     smooth_manifold_atlas (subtopology euclidean X) sigma /\ UNIONS L = X /\
     simplicial_complex L /\ e IN L /\ aff_dim e = &1 /\
     (U,phi) IN sigma /\ relative_interior e SUBSET U /\
     linear l0 /\ (!x. x IN e ==> &0 < (l0 x + y0)$3) /\
     (!x. x IN relative_interior e ==> phi x = moi_smo_gnom(l0 x + y0)) /\
     (!s. s IN L /\ aff_dim s = &2 /\ e SUBSET s
          ==> v IN tetf s /\ s SUBSET tetf s /\ ~(v IN affine hull s) /\
              (?l y. linear l /\ !x. A s x = l x + y) /\ A s v = vec 0 /\
              (!x y. x IN affine hull (tetf s) /\ y IN affine hull (tetf s) /\
                     A s x = A s y ==> x = y) /\
              orthogonal_transformation (R s) /\
              (!x. x IN s ==> &0 < (R s (A s x))$3) /\
              (!x. x IN s INTER U ==> phi x = moi_smo_gnom(R s (A s x))))
     ==> ?U phi. (U,phi) IN sigma /\ relative_interior e SUBSET U /\
                 (?a p. !x. x IN relative_interior e ==> ?t. phi x = a + t % p) /\
                 !s x. s IN L /\ aff_dim s = &2 /\ e SUBSET s /\
                       x IN relative_interior e
                       ==> ?r. &0 < r /\ s INTER cball(x,r) SUBSET U /\
                               moi_smo_cell_smooth (s INTER cball(x,r)) phi`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "pos0") (CONJUNCTS_THEN2 (LABEL_TAC "phi0")
     (LABEL_TAC "dat"))))))))))) THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `phi:real^N->real^2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`] MOI_SCF_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a:real^N) IN e /\ b IN e` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN
      REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    EXISTS_TAC `moi_smo_gnom((l0:real^N->real^3) a + y0)` THEN
    EXISTS_TAC `moi_smo_gnom((l0:real^N->real^3) b + y0) - moi_smo_gnom(l0 a + y0)` THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "phi0" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(x:real^N) IN relative_interior e`)]) THEN
    UNDISCH_TAC `(x:real^N) IN relative_interior e` THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT] THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(l0:real^N->real^3) ((&1 - u) % a + u % b) + y0 =
      (&1 - u) % (l0 a + y0) + u % (l0 b + y0)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`(l0:real^N->real^3) a + y0`; `(l0:real^N->real^3) b + y0`;
                   `u:real`] MOI_SLP_GNOM_SEGMENT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "pos0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [USE_THEN "pos0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u':real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u':real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
  USE_THEN "dat" (MP_TAC o SPEC `s:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pos")
     (LABEL_TAC "phis"))))))))) THEN
  SUBGOAL_THEN `(x:real^N) IN U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean X) (U:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[smooth_manifold_atlas]; ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r0 / &2` THEN
  SUBGOAL_THEN `s INTER cball(x:real^N,r0 / &2) SUBSET U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball(x:real^N,r0) INTER X` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET X` MP_TAC THENL
     [EXPAND_TAC "X" THEN MATCH_MP_TAC(SET_RULE
        `(s:real^N->bool) IN L ==> s SUBSET UNIONS L`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `cball(x:real^N,r0 / &2) SUBSET ball(x,r0)` MP_TAC THENL
     [REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC; SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  SUBGOAL_THEN `?l y. linear l /\ !z:real^N.
                  (R:(real^N->bool)->real^3->real^3) s
                    ((A:(real^N->bool)->real^N->real^3) s z) = l z + y`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`(R:(real^N->bool)->real^3->real^3) s`; `vec 0:real^3`] THEN
      REWRITE_TAC[VECTOR_ADD_RID] THEN ASM_MESON_TAC[orthogonal_transformation]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SLP_CELL_SMOOTH_EQ THEN
  EXISTS_TAC `\z:real^N. moi_smo_gnom((l:real^N->real^3) z + y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLP_CELL_SMOOTH_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC MOI_SLP_GNOM_CELL THEN
    MAP_EVERY EXISTS_TAC [`v:real^N`; `(tetf:(real^N->bool)->(real^N->bool)) s`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `v:real^N` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `l:real^N->real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[orthogonal_transformation; LINEAR_0];
      MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`] THEN STRIP_TAC THEN
      USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(MATCH_MP ORTHOGONAL_TRANSFORMATION_INJECTIVE
        (ASSUME `orthogonal_transformation
                   ((R:(real^N->bool)->real^3->real^3) s)`)) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `z:real^N` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `l:real^N->real^3`)) (concl th))) THEN
      USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN s INTER U` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^N) IN s INTER cball(x,r0 / &2)` THEN
      UNDISCH_TAC `s INTER cball(x:real^N,r0 / &2) SUBSET U` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "phis" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(z:real^N) IN s INTER U`)]) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Carriers of the simplices of the subdivision L in the link; open          *)
(* triangles of L are open in the link; rotations about the third axis.      *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_L_DIM = prove
 (`!c (v:real^N) L.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     (!s. s IN L ==> ?s'. s' IN simplicial_link c v /\ s SUBSET s')
     ==> !s. s IN L ==> aff_dim s <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
    MOI_SLP_LINK_DIM) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `s':real^N->bool`] AFF_DIM_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_SLP_L_TRI = prove
 (`!c (v:real^N) L.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     (!s. s IN L ==> ?s'. s' IN simplicial_link c v /\ s SUBSET s')
     ==> !s. s IN L /\ aff_dim s = &2
             ==> ?t. t IN simplicial_link c v /\ aff_dim t = &2 /\ s SUBSET t /\
                     relative_interior s SUBSET relative_interior t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_SLP_LINK_DIM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] AFF_DIM_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_RELATIVE_INTERIOR THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let MOI_SLP_L_VERT = prove
 (`!c (v:real^N) L.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     UNIONS L = UNIONS(simplicial_link c v)
     ==> !w. {w} IN L
             ==> {w} IN simplicial_link c v \/
                 (?f. f IN simplicial_link c v /\ aff_dim f = &1 /\
                      w IN relative_interior f) \/
                 (?t. t IN simplicial_link c v /\ aff_dim t = &2 /\
                      w IN relative_interior t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SCF_CM_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^N) IN UNIONS(simplicial_link c v)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `UNIONS L = UNIONS(simplicial_link c (v:real^N))`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `w:real^N`] MOI_SBA_CARRIER) THEN
  ASM_SIMP_TAC[MOI_SLP_SC_LF] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `r:real^N->bool`]
    MOI_SLP_LINK_DIM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= aff_dim(r:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[AFF_DIM_POS_LE] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(r:real^N->bool) = &0 \/ aff_dim r = &1 \/ aff_dim r = &2`
  MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN
    UNDISCH_TAC `aff_dim(r:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `(w:real^N) IN relative_interior {a}` THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SLP_L_EDGE = prove
 (`!c (v:real^N) L.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     simplicial_complex L /\ UNIONS L = UNIONS(simplicial_link c v) /\
     (!s. s IN L ==> ?s'. s' IN simplicial_link c v /\ s SUBSET s')
     ==> !e. e IN L /\ aff_dim e = &1
             ==> ?r. r IN simplicial_link c v /\
                     (aff_dim r = &1 \/ aff_dim r = &2) /\
                     e SUBSET r /\ relative_interior e SUBSET relative_interior r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SCF_CM_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (fun th ->
    can (find_term ((=) `simplicial_link c (v:real^N)`)) (concl th) &&
    is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `midpoint(a:real^N,b) IN UNIONS(simplicial_link c v)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s':real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `convex hull {a:real^N,b} SUBSET s'` THEN
    REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `midpoint(a:real^N,b)`]
    MOI_SBA_CARRIER) THEN
  ASM_SIMP_TAC[MOI_SLP_SC_LF] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `a:real^N`; `b:real^N`;
                 `s':real^N->bool`; `r:real^N->bool`] MOI_SLP_SEG_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `r:real^N->bool`]
      MOI_SLP_LINK_DIM) THEN
    MP_TAC(ISPECL [`e:real^N->bool`; `r:real^N->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL];
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT]]);;

let MOI_SLP_RELINT_OPEN = prove
 (`!L s:real^N->bool.
     simplicial_complex L /\ (!t. t IN L ==> aff_dim t <= &2) /\
     s IN L /\ aff_dim s = &2
     ==> open_in (subtopology euclidean (UNIONS L)) (relative_interior s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `\t:real^N->bool. s SUBSET t`]
    MOI_SCF_SC_OPEN_STAR) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `x:real^N`] MOI_SBA_CARRIER) THEN
    ASM_SIMP_TAC[MOI_SLP_SC_LF] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `s SUBSET (r:real^N->bool)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `s:real^N->bool = r` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `r:real^N->bool`] AFF_DIM_SUBSET) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `aff_dim:(real^N->bool)->int`))
                                 (concl th))) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `x:real^N`] THEN
      ASM_REWRITE_TAC[]]]);;

(* Rotations about the third axis.                                           *)

let MOI_SLP_ROTZ_ORTH = prove
 (`!a. orthogonal_transformation(moi_smo_rotz a)`,
  GEN_TAC THEN REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; MOI_SED_ROTZ_LINEAR] THEN
  REWRITE_TAC[MOI_SMO_TWIST_NORM]);;

let MOI_SLP_ROTZ_E3 = prove
 (`!a. moi_smo_rotz a (basis 3) = basis 3`,
  GEN_TAC THEN
  SIMP_TAC[moi_smo_rotz; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
           BASIS_COMPONENT; ARITH] THEN
  REAL_ARITH_TAC);;

let MOI_SLP_ROTZ_GNOM = prove
 (`!a y. moi_smo_gnom(moi_smo_rotz a y) = cexp(ii * Cx a) * moi_smo_gnom y`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SPEC `y:real^3` MOI_SED_V3_EXPAND) THEN
  REWRITE_TAC[MOI_SED_ROTZ_V3; MOI_SLP_GNOM_V3] THEN
  REWRITE_TAC[complex_div; COMPLEX_MUL_ASSOC]);;

let MOI_SLP_ROTZ_HALF = prove
 (`!a y. &0 <= y$2 /\ &0 < y$3
         ==> &0 <= Im(cexp(--(ii * Cx a)) * moi_smo_gnom(moi_smo_rotz a y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_SLP_ROTZ_GNOM] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC; CEXP_NEG_LMUL; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[IM_DEF; MOI_SLK_GNOM_COMPONENTS] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* Clause (2) at the three kinds of vertices of L: inside a link triangle    *)
(* (tetrahedron chart), inside a link edge (unfolding chart), and at a link  *)
(* vertex (the cone point: edge chart with angular rescaling).               *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_VERTEX_GEN2 = prove
 (`!c (v:real^N) L (sigma:((real^N->bool)#(real^N->real^2))->bool) w U phi k.
     lf_simplicial_complex c /\ simplicial_complex L /\ {w} IN L /\
     (U,phi) IN sigma /\ w IN U /\ phi w = vec 0 /\ &0 < k /\
     (!s. s IN L /\ aff_dim s = &2 /\ w IN s
          ==> ?tet (A:real^N->real^3) (R:real^3->real^3) b.
                tet IN c /\ v IN tet /\ s SUBSET tet /\ ~(v IN affine hull s) /\
                moi_smo_regmap tet A /\ A v = vec 0 /\
                (!x y. x IN affine hull tet /\ y IN affine hull tet /\
                       A x = A y ==> x = y) /\
                orthogonal_transformation R /\
                (?c0. &0 < c0 /\ R (A w) = c0 % basis 3) /\
                (!x. x IN s ==> &0 < (R (A x))$3) /\
                (!x. x IN s ==> &0 <= Im(cexp(--(ii * Cx b)) *
                                         moi_smo_gnom(R (A x)))) /\
                (!x. x IN s INTER U
                     ==> phi x = moi_smo_ang k b (moi_smo_gnom(R (A x)))))
     ==> ?U phi k b Q.
              (U,phi) IN sigma /\ w IN U /\ phi w = vec 0 /\ &0 < k /\
              !s. s IN L /\ aff_dim s = &2 /\ w IN s
                  ==> moi_smo_cell_smooth s ((Q:(real^N->bool)->real^N->real^2) s) /\
                      (!x y. x IN s /\ y IN s /\ Q s x = Q s y ==> x = y) /\
                      Q s w = vec 0 /\
                      (!x. x IN s ==> &0 <= Im(cexp(--(ii * Cx(b s))) * Q s x)) /\
                      (!e. e IN L /\ aff_dim e = &1 /\ w IN e /\ e SUBSET s
                           ==> ?a. !x. x IN e ==> ?t. &0 <= t /\ Q s x = t % a) /\
                      (!x. x IN s INTER U ==> phi x = moi_smo_ang k (b s) (Q s x)) /\
                      (!s' x. s' IN L /\ aff_dim s' = &2 /\ w IN s' /\ x IN s INTER s'
                              ==> norm(Q s x) = norm(Q s' x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])))))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `tetf:(real^N->bool)->(real^N->bool)`
   (X_CHOOSE_THEN `AA:(real^N->bool)->real^N->real^3`
   (X_CHOOSE_THEN `RR:(real^N->bool)->real^3->real^3`
   (X_CHOOSE_THEN `bb:(real^N->bool)->real` ASSUME_TAC)))) THEN
  MATCH_MP_TAC MOI_SLP_VERTEX_GEN THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`;
                        `U:real^N->bool`; `phi:real^N->real^2`; `k:real`;
                        `bb:(real^N->bool)->real`;
                        `tetf:(real^N->bool)->(real^N->bool)`;
                        `AA:(real^N->bool)->real^N->real^3`;
                        `RR:(real^N->bool)->real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;

(* Triangles of L at a point w: in the link triangle containing them.       *)

let MOI_SLP_TRI_AT = prove
 (`!c (v:real^N) L r w s.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     (!s. s IN L ==> ?s'. s' IN simplicial_link c v /\ s SUBSET s') /\
     r IN simplicial_link c v /\ w IN relative_interior r /\
     s IN L /\ aff_dim s = &2 /\ w IN s
     ==> ?t. t IN simplicial_link c v /\ aff_dim t = &2 /\ s SUBSET t /\
             r SUBSET t /\ relative_interior s SUBSET relative_interior t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `L:(real^N->bool)->bool`]
    MOI_SLP_L_TRI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`simplicial_link c (v:real^N)`; `w:real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_SCF_CM_VERTEX]; ASM SET_TAC[]]);;

let MOI_SLP_TRI_VERTS_AT = prove
 (`!L s (w:real^N).
     simplicial_complex L /\ s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s
     ==> ?p q. s = convex hull {w,p,q}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `w:real^N`] MOI_SBA_TRI_VERTS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`]
        MOI_SBA_LF_SIMPLEX) THEN ASM_SIMP_TAC[MOI_SLP_SC_LF];
      MATCH_MP_TAC MOI_SCF_VERTEX_EXTREME THEN
      EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
    MESON_TAC[]]);;

let MOI_SLP_PART2_TRI = prove
 (`!c (v:real^N) L w t0.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     simplicial_complex L /\
     (!s. s IN L ==> ?s'. s' IN simplicial_link c v /\ s SUBSET s') /\
     {w} IN L /\ t0 IN simplicial_link c v /\ aff_dim t0 = &2 /\
     w IN relative_interior t0
     ==> ?U phi k b Q.
              (U,phi) IN moi_smo_link_atlas c v /\ w IN U /\ phi w = vec 0 /\
              &0 < k /\
              !s. s IN L /\ aff_dim s = &2 /\ w IN s
                  ==> moi_smo_cell_smooth s ((Q:(real^N->bool)->real^N->real^2) s) /\
                      (!x y. x IN s /\ y IN s /\ Q s x = Q s y ==> x = y) /\
                      Q s w = vec 0 /\
                      (!x. x IN s ==> &0 <= Im(cexp(--(ii * Cx(b s))) * Q s x)) /\
                      (!e. e IN L /\ aff_dim e = &1 /\ w IN e /\ e SUBSET s
                           ==> ?a. !x. x IN e ==> ?t. &0 <= t /\ Q s x = t % a) /\
                      (!x. x IN s INTER U ==> phi x = moi_smo_ang k (b s) (Q s x)) /\
                      (!s' x. s' IN L /\ aff_dim s' = &2 /\ w IN s' /\ x IN s INTER s'
                              ==> norm(Q s x) = norm(Q s' x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN t0` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t0:real^N->bool`;
                 `w:real^N`] MOI_SLP_TCHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` (X_CHOOSE_THEN `phi:real^N->real^2`
   (X_CHOOSE_THEN `A:real^N->real^3` (X_CHOOSE_THEN `R:real^3->real^3`
     STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t0:real^N->bool`;
                 `A:real^N->real^3`] MOI_SLP_REG_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_SLP_VERTEX_GEN2 THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`;
                        `U:real^N->bool`; `phi:real^N->real^2`; `&1`] THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[MOI_SLP_GNOM_ZERO] THEN MATCH_MP_TAC MOI_SLP_GNOM_ZERO THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `L:(real^N->bool)->bool`;
                 `t0:real^N->bool`; `w:real^N`; `s:real^N->bool`]
    MOI_SLP_TRI_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t:real^N->bool = t0` SUBST_ALL_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `simplicial_link c (v:real^N)` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_SCF_CM_VERTEX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`; `w:real^N`]
    MOI_SLP_TRI_VERTS_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `?l y. linear l /\ !x:real^N. (R:real^3->real^3)((A:real^N->real^3) x) =
                                            l x + y`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`R:real^3->real^3`; `vec 0:real^3`] THEN
    REWRITE_TAC[VECTOR_ADD_RID] THEN ASM_MESON_TAC[orthogonal_transformation];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:real^N->real^3`; `y:real^3`; `w:real^N`; `p:real^N`;
                 `q:real^N`] MOI_SLP_HALF_PLANE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `w:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `l:real^N->real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_MUL_RZERO] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `l:real^N->real^3`)) (concl th))) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `t0:real^N->bool`)) (concl th) &&
      can (find_term ((=) `R:real^3->real^3`)) (concl th))) THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET t0` THEN
    UNDISCH_TAC `(x:real^N) IN convex hull {w,p,q}` THEN
    UNDISCH_TAC `s = convex hull {w:real^N,p,q}` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real`) THEN
  MAP_EVERY EXISTS_TAC [`convex hull ((v:real^N) INSERT t0)`; `A:real^N->real^3`;
                        `R:real^3->real^3`; `b:real`] THEN
  ASM_REWRITE_TAC[MOI_SMO_ANG_ONE] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(s:real^N->bool) SUBSET t0`;
                           `(t0:real^N->bool) SUBSET convex hull (v INSERT t0)`;
                           `s = convex hull {w:real^N,p,q}`] THEN
    SET_TAC[];
    UNDISCH_TAC `~((v:real^N) IN affine hull t0)` THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> ~(x IN t) ==> ~(x IN s)`) THEN
    MATCH_MP_TAC HULL_MONO THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET t0` THEN
    UNDISCH_TAC `s = convex hull {w:real^N,p,q}` THEN SIMP_TAC[];
    EXISTS_TAC `norm((A:real^N->real^3) w)` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `l:real^N->real^3`)) (concl th))) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `t0:real^N->bool`)) (concl th) &&
      can (find_term ((=) `R:real^3->real^3`)) (concl th))) THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET t0` THEN
    UNDISCH_TAC `(x:real^N) IN convex hull {w,p,q}` THEN
    UNDISCH_TAC `s = convex hull {w:real^N,p,q}` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Clause (2) at vertices of L inside link edges and at the link vertices    *)
(* (cone points).                                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_PART2_EDGE = prove
 (`!c (v:real^N) L w f0.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     simplicial_complex L /\
     (!s. s IN L ==> ?s'. s' IN simplicial_link c v /\ s SUBSET s') /\
     {w} IN L /\ f0 IN simplicial_link c v /\ aff_dim f0 = &1 /\
     w IN relative_interior f0
     ==> ?U phi k b Q.
              (U,phi) IN moi_smo_link_atlas c v /\ w IN U /\ phi w = vec 0 /\
              &0 < k /\
              !s. s IN L /\ aff_dim s = &2 /\ w IN s
                  ==> moi_smo_cell_smooth s ((Q:(real^N->bool)->real^N->real^2) s) /\
                      (!x y. x IN s /\ y IN s /\ Q s x = Q s y ==> x = y) /\
                      Q s w = vec 0 /\
                      (!x. x IN s ==> &0 <= Im(cexp(--(ii * Cx(b s))) * Q s x)) /\
                      (!e. e IN L /\ aff_dim e = &1 /\ w IN e /\ e SUBSET s
                           ==> ?a. !x. x IN e ==> ?t. &0 <= t /\ Q s x = t % a) /\
                      (!x. x IN s INTER U ==> phi x = moi_smo_ang k (b s) (Q s x)) /\
                      (!s' x. s' IN L /\ aff_dim s' = &2 /\ w IN s' /\ x IN s INTER s'
                              ==> norm(Q s x) = norm(Q s' x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `f0:real^N->bool`;
                 `w:real^N`] MOI_SLP_UCHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` (X_CHOOSE_THEN `phi:real^N->real^2`
   (X_CHOOSE_THEN `R:real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ut")))))))) THEN
  MATCH_MP_TAC MOI_SLP_VERTEX_GEN2 THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`;
                        `U:real^N->bool`; `phi:real^N->real^2`; `&1`] THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `L:(real^N->bool)->bool`;
                 `f0:real^N->bool`; `w:real^N`; `s:real^N->bool`]
    MOI_SLP_TRI_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "ut" (MP_TAC o SPEC `t:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `c0:real` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 (LABEL_TAC "pos") (LABEL_TAC "phit")))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                 `A:real^N->real^3`] MOI_SLP_REG_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`; `w:real^N`]
    MOI_SLP_TRI_VERTS_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `?l y. linear l /\ !x:real^N. (R:real^3->real^3)((A:real^N->real^3) x) =
                                            l x + y`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`R:real^3->real^3`; `vec 0:real^3`] THEN
    REWRITE_TAC[VECTOR_ADD_RID] THEN ASM_MESON_TAC[orthogonal_transformation];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:real^N->real^3`; `y:real^3`; `w:real^N`; `p:real^N`;
                 `q:real^N`] MOI_SLP_HALF_PLANE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `w:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `l:real^N->real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_MUL_RZERO] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `l:real^N->real^3`)) (concl th))) THEN
    USE_THEN "pos" MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET t` THEN
    UNDISCH_TAC `(x:real^N) IN convex hull {w,p,q}` THEN
    UNDISCH_TAC `s = convex hull {w:real^N,p,q}` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` (LABEL_TAC "half")) THEN
  MAP_EVERY EXISTS_TAC [`convex hull ((v:real^N) INSERT t)`; `A:real^N->real^3`;
                        `R:real^3->real^3`; `b:real`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY UNDISCH_TAC [`(s:real^N->bool) SUBSET t`;
                           `(t:real^N->bool) SUBSET convex hull (v INSERT t)`] THEN
    SET_TAC[];
    UNDISCH_TAC `~((v:real^N) IN affine hull t)` THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> ~(x IN t) ==> ~(x IN s)`) THEN
    MATCH_MP_TAC HULL_MONO THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    EXISTS_TAC `c0:real` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN USE_THEN "pos" MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET t` THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `l:real^N->real^3`)) (concl th))) THEN
    USE_THEN "half" MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[MOI_SMO_ANG_ONE] THEN
    USE_THEN "phit" MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET t` THEN
    UNDISCH_TAC `(x:real^N) IN s INTER U` THEN SET_TAC[]]);;

let MOI_SLP_ROTZ_3 = prove
 (`!a y. (moi_smo_rotz a y)$3 = y$3`,
  REWRITE_TAC[moi_smo_rotz; VECTOR_3]);;

let MOI_SLP_PART2_CONE = prove
 (`!c (v:real^N) L w.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     simplicial_complex L /\
     (!s. s IN L ==> ?s'. s' IN simplicial_link c v /\ s SUBSET s') /\
     {w} IN L /\ {w} IN simplicial_link c v
     ==> ?U phi k b Q.
              (U,phi) IN moi_smo_link_atlas c v /\ w IN U /\ phi w = vec 0 /\
              &0 < k /\
              !s. s IN L /\ aff_dim s = &2 /\ w IN s
                  ==> moi_smo_cell_smooth s ((Q:(real^N->bool)->real^N->real^2) s) /\
                      (!x y. x IN s /\ y IN s /\ Q s x = Q s y ==> x = y) /\
                      Q s w = vec 0 /\
                      (!x. x IN s ==> &0 <= Im(cexp(--(ii * Cx(b s))) * Q s x)) /\
                      (!e. e IN L /\ aff_dim e = &1 /\ w IN e /\ e SUBSET s
                           ==> ?a. !x. x IN e ==> ?t. &0 <= t /\ Q s x = t % a) /\
                      (!x. x IN s INTER U ==> phi x = moi_smo_ang k (b s) (Q s x)) /\
                      (!s' x. s' IN L /\ aff_dim s' = &2 /\ w IN s' /\ x IN s INTER s'
                              ==> norm(Q s x) = norm(Q s' x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `w:real^N`]
    MOI_SLP_ECHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` (X_CHOOSE_THEN `phi:real^N->real^2`
   (X_CHOOSE_THEN `k:real` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "et")))))))) THEN
  MATCH_MP_TAC MOI_SLP_VERTEX_GEN2 THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`;
                        `U:real^N->bool`; `phi:real^N->real^2`; `k:real`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `L:(real^N->bool)->bool`;
                 `{w:real^N}`; `w:real^N`; `s:real^N->bool`]
    MOI_SLP_TRI_AT) THEN
  ASM_REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^N) IN t` ASSUME_TAC THENL
   [UNDISCH_TAC `{w:real^N} SUBSET t` THEN SET_TAC[]; ALL_TAC] THEN
  USE_THEN "et" (MP_TAC o SPEC `t:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` (X_CHOOSE_THEN `th:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "uhs")
     (LABEL_TAC "phit"))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                 `A:real^N->real^3`] MOI_SLP_REG_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "dot") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!x:real^N. x IN t ==> &0 < ((A:real^N->real^3) x)$3`
  (LABEL_TAC "pos3") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "dot" (MP_TAC o SPECL [`x:real^N`; `w:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `(A:real^N->real^3) w = basis 3`] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`convex hull ((v:real^N) INSERT t)`; `A:real^N->real^3`;
                        `moi_smo_rotz th`; `th:real`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY UNDISCH_TAC [`(s:real^N->bool) SUBSET t`;
                           `(t:real^N->bool) SUBSET convex hull (v INSERT t)`] THEN
    SET_TAC[];
    UNDISCH_TAC `~((v:real^N) IN affine hull t)` THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> ~(x IN t) ==> ~(x IN s)`) THEN
    MATCH_MP_TAC HULL_MONO THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[MOI_SLP_ROTZ_ORTH];
    EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[MOI_SLP_ROTZ_E3; VECTOR_MUL_LID] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[MOI_SLP_ROTZ_3] THEN
    USE_THEN "pos3" MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET t` THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_SLP_ROTZ_HALF THEN
    CONJ_TAC THENL
     [USE_THEN "uhs" MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC [`(s:real^N->bool) SUBSET t`;
                             `(t:real^N->bool) SUBSET convex hull (v INSERT t)`;
                             `(x:real^N) IN s`] THEN
      SET_TAC[];
      USE_THEN "pos3" MATCH_MP_TAC THEN
      UNDISCH_TAC `(s:real^N->bool) SUBSET t` THEN
      UNDISCH_TAC `(x:real^N) IN s` THEN SET_TAC[]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "phit" MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET t` THEN
    UNDISCH_TAC `(x:real^N) IN s INTER U` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Clause (3) for the edges of L inside link triangles and inside link       *)
(* edges.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_EDGE_GEN2 = prove
 (`!(v:real^N) L X (sigma:((real^N->bool)#(real^N->real^2))->bool) e U phi
    (l0:real^N->real^3) y0.
     smooth_manifold_atlas (subtopology euclidean X) sigma /\ UNIONS L = X /\
     simplicial_complex L /\ e IN L /\ aff_dim e = &1 /\
     (U,phi) IN sigma /\ relative_interior e SUBSET U /\
     linear l0 /\ (!x. x IN e ==> &0 < (l0 x + y0)$3) /\
     (!x. x IN relative_interior e ==> phi x = moi_smo_gnom(l0 x + y0)) /\
     (!s. s IN L /\ aff_dim s = &2 /\ e SUBSET s
          ==> ?tet (A:real^N->real^3) (R:real^3->real^3).
                v IN tet /\ s SUBSET tet /\ ~(v IN affine hull s) /\
                (?l y. linear l /\ !x. A x = l x + y) /\ A v = vec 0 /\
                (!x y. x IN affine hull tet /\ y IN affine hull tet /\
                       A x = A y ==> x = y) /\
                orthogonal_transformation R /\
                (!x. x IN s ==> &0 < (R (A x))$3) /\
                (!x. x IN s INTER U ==> phi x = moi_smo_gnom(R (A x))))
     ==> ?U phi. (U,phi) IN sigma /\ relative_interior e SUBSET U /\
                 (?a p. !x. x IN relative_interior e ==> ?t. phi x = a + t % p) /\
                 !s x. s IN L /\ aff_dim s = &2 /\ e SUBSET s /\
                       x IN relative_interior e
                       ==> ?r. &0 < r /\ s INTER cball(x,r) SUBSET U /\
                               moi_smo_cell_smooth (s INTER cball(x,r)) phi`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]))))))))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `tetf:(real^N->bool)->(real^N->bool)`
   (X_CHOOSE_THEN `AA:(real^N->bool)->real^N->real^3`
   (X_CHOOSE_THEN `RR:(real^N->bool)->real^3->real^3` ASSUME_TAC))) THEN
  MATCH_MP_TAC MOI_SLP_EDGE_GEN THEN
  MAP_EVERY EXISTS_TAC [`v:real^N`; `X:real^N->bool`; `U:real^N->bool`;
                        `phi:real^N->real^2`; `l0:real^N->real^3`; `y0:real^3`;
                        `tetf:(real^N->bool)->(real^N->bool)`;
                        `AA:(real^N->bool)->real^N->real^3`;
                        `RR:(real^N->bool)->real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_SLP_LINK_PURE = prove
 (`!c (v:real^N) s.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     s IN simplicial_link c v /\ ~(s = {})
     ==> ?t. t IN simplicial_link c v /\ aff_dim t = &2 /\ s SUBSET t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SCF_CM_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(:N)` MOI_SMO_SURFACE_COMPLEX) THEN
  REWRITE_TAC[MOI_SMO_SURFACE_COMPLEX_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `simplicial_link c (v:real^N)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_SLP_RELINT_SEG_NONEMPTY = prove
 (`!L e:real^N->bool.
     simplicial_complex L /\ e IN L /\ aff_dim e = &1
     ==> ?x. x IN relative_interior e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
  SUBGOAL_THEN `convex(e:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_LF_CONVEX; MOI_SLP_SC_LF]; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
  REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC);;

(* Triangles of L over an edge e of L whose open edge lies in the open      *)
(* link simplex r: they lie in link triangles containing r.                  *)

let MOI_SLP_TRI_OVER = prove
 (`!c (v:real^N) L e r s.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     simplicial_complex L /\
     (!s. s IN L ==> ?s'. s' IN simplicial_link c v /\ s SUBSET s') /\
     e IN L /\ aff_dim e = &1 /\ r IN simplicial_link c v /\
     relative_interior e SUBSET relative_interior r /\
     s IN L /\ aff_dim s = &2 /\ e SUBSET s
     ==> ?t. t IN simplicial_link c v /\ aff_dim t = &2 /\ s SUBSET t /\
             r SUBSET t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_SLP_RELINT_SEG_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `x0:real^N`) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `L:(real^N->bool)->bool`;
                 `r:real^N->bool`; `x0:real^N`; `s:real^N->bool`]
    MOI_SLP_TRI_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(e:real^N->bool) SUBSET s` THEN
    UNDISCH_TAC `(x0:real^N) IN relative_interior e` THEN
    MP_TAC(ISPEC `e:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    MESON_TAC[]]);;

let MOI_SLP_PART3_TRI = prove
 (`!c (v:real^N) L e t0.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     simplicial_complex L /\ UNIONS L = UNIONS(simplicial_link c v) /\
     (!s. s IN L ==> ?s'. s' IN simplicial_link c v /\ s SUBSET s') /\
     e IN L /\ aff_dim e = &1 /\ t0 IN simplicial_link c v /\ aff_dim t0 = &2 /\
     e SUBSET t0 /\ relative_interior e SUBSET relative_interior t0
     ==> ?U phi. (U,phi) IN moi_smo_link_atlas c v /\
                 relative_interior e SUBSET U /\
                 (?a p. !x. x IN relative_interior e ==> ?t. phi x = a + t % p) /\
                 !s x. s IN L /\ aff_dim s = &2 /\ e SUBSET s /\
                       x IN relative_interior e
                       ==> ?r. &0 < r /\ s INTER cball(x,r) SUBSET U /\
                               moi_smo_cell_smooth (s INTER cball(x,r)) phi`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_SLP_RELINT_SEG_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `x0:real^N`) THEN
  SUBGOAL_THEN `(x0:real^N) IN t0` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t0:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t0:real^N->bool`;
                 `x0:real^N`] MOI_SLP_TCHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` (X_CHOOSE_THEN `phi:real^N->real^2`
   (X_CHOOSE_THEN `A:real^N->real^3` (X_CHOOSE_THEN `R:real^3->real^3`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pos")
       (LABEL_TAC "phiA"))))))))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t0:real^N->bool`;
                 `A:real^N->real^3`] MOI_SLP_REG_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?l y. linear l /\ !x:real^N. (R:real^3->real^3)((A:real^N->real^3) x) =
                                            l x + y`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`R:real^3->real^3`; `vec 0:real^3`] THEN
    REWRITE_TAC[VECTOR_ADD_RID] THEN ASM_MESON_TAC[orthogonal_transformation];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SLP_EDGE_GEN2 THEN
  MAP_EVERY EXISTS_TAC [`v:real^N`; `UNIONS(simplicial_link c (v:real^N))`;
                        `U:real^N->bool`; `phi:real^N->real^2`;
                        `l:real^N->real^3`; `y:real^3`] THEN
  ASM_SIMP_TAC[MOI_SLP_LINK_SMOOTH_ATLAS] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `l:real^N->real^3`)) (concl th))) THEN
    USE_THEN "pos" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `L:(real^N->bool)->bool`;
                 `e:real^N->bool`; `t0:real^N->bool`; `s:real^N->bool`]
    MOI_SLP_TRI_OVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t:real^N->bool = t0` SUBST_ALL_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `simplicial_link c (v:real^N)` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_SCF_CM_VERTEX];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`convex hull ((v:real^N) INSERT t0)`; `A:real^N->real^3`;
                        `R:real^3->real^3`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY UNDISCH_TAC [`(s:real^N->bool) SUBSET t0`;
                           `(t0:real^N->bool) SUBSET convex hull (v INSERT t0)`] THEN
    SET_TAC[];
    UNDISCH_TAC `~((v:real^N) IN affine hull t0)` THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> ~(x IN t) ==> ~(x IN s)`) THEN
    MATCH_MP_TAC HULL_MONO THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN USE_THEN "pos" MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET t0` THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "phiA" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]]);;

let MOI_SLP_PART3_EDGE = prove
 (`!c (v:real^N) L e f0.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     simplicial_complex L /\ UNIONS L = UNIONS(simplicial_link c v) /\
     (!s. s IN L ==> ?s'. s' IN simplicial_link c v /\ s SUBSET s') /\
     e IN L /\ aff_dim e = &1 /\ f0 IN simplicial_link c v /\ aff_dim f0 = &1 /\
     e SUBSET f0 /\ relative_interior e SUBSET relative_interior f0
     ==> ?U phi. (U,phi) IN moi_smo_link_atlas c v /\
                 relative_interior e SUBSET U /\
                 (?a p. !x. x IN relative_interior e ==> ?t. phi x = a + t % p) /\
                 !s x. s IN L /\ aff_dim s = &2 /\ e SUBSET s /\
                       x IN relative_interior e
                       ==> ?r. &0 < r /\ s INTER cball(x,r) SUBSET U /\
                               moi_smo_cell_smooth (s INTER cball(x,r)) phi`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_SLP_RELINT_SEG_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `x0:real^N`) THEN
  SUBGOAL_THEN `(x0:real^N) IN relative_interior f0` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `f0:real^N->bool`;
                 `x0:real^N`] MOI_SLP_UCHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` (X_CHOOSE_THEN `phi:real^N->real^2`
   (X_CHOOSE_THEN `R:real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ut")))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `f0:real^N->bool`]
    MOI_SLP_LINK_PURE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "ut" (MP_TAC o SPEC `t0:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A0:real^N->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
   (CONJUNCTS_THEN2 (LABEL_TAC "pos0") (LABEL_TAC "phi0")))))) THEN
  SUBGOAL_THEN `?l y. linear l /\ !x:real^N. (R:real^3->real^3)((A0:real^N->real^3) x) =
                                            l x + y`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SBA_AFFINE_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SBA_REGMAP_AFFINE THEN
      EXISTS_TAC `convex hull ((v:real^N) INSERT t0)` THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`R:real^3->real^3`; `vec 0:real^3`] THEN
      REWRITE_TAC[VECTOR_ADD_RID] THEN ASM_MESON_TAC[orthogonal_transformation]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SLP_EDGE_GEN2 THEN
  MAP_EVERY EXISTS_TAC [`v:real^N`; `UNIONS(simplicial_link c (v:real^N))`;
                        `U:real^N->bool`; `phi:real^N->real^2`;
                        `l:real^N->real^3`; `y:real^3`] THEN
  ASM_SIMP_TAC[MOI_SLP_LINK_SMOOTH_ATLAS] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `l:real^N->real^3`)) (concl th))) THEN
    USE_THEN "pos0" MATCH_MP_TAC THEN ASM SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `l:real^N->real^3`)) (concl th))) THEN
    USE_THEN "phi0" MATCH_MP_TAC THEN
    MP_TAC(ISPEC `e:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `L:(real^N->bool)->bool`;
                 `e:real^N->bool`; `f0:real^N->bool`; `s:real^N->bool`]
    MOI_SLP_TRI_OVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "ut" (MP_TAC o SPEC `t:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
   (CONJUNCTS_THEN2 (LABEL_TAC "pos") (LABEL_TAC "phit")))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                 `A:real^N->real^3`] MOI_SLP_REG_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`convex hull ((v:real^N) INSERT t)`; `A:real^N->real^3`;
                        `R:real^3->real^3`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY UNDISCH_TAC [`(s:real^N->bool) SUBSET t`;
                           `(t:real^N->bool) SUBSET convex hull (v INSERT t)`] THEN
    SET_TAC[];
    UNDISCH_TAC `~((v:real^N) IN affine hull t)` THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> ~(x IN t) ==> ~(x IN s)`) THEN
    MATCH_MP_TAC HULL_MONO THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN USE_THEN "pos" MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET t` THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN USE_THEN "phit" MATCH_MP_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET t` THEN
    UNDISCH_TAC `(x:real^N) IN s INTER U` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part (4): in the tetrahedron chart of the link triangle containing a      *)
(* triangle s of L, h is the radial projection of a linear map applied to    *)
(* (z,1); hence h is a smooth immersion on the open triangle in every chart. *)
(* ------------------------------------------------------------------------- *)

let MOI_SLP_LIFT0_LINEAR = prove
 (`linear (\z:real^2. vector[z$1; z$2; &0]:real^3)`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_SLP_LIFT_SPLIT = prove
 (`!z:real^2. vector[z$1; z$2; &1]:real^3 = vector[z$1; z$2; &0] + basis 3`,
  GEN_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
           BASIS_COMPONENT; ARITH] THEN
  REAL_ARITH_TAC);;

let MOI_SLP_AFFINE0_LINEAR = prove
 (`!(M:real^M->real^N).
     (?l y. linear l /\ !x. M x = l x + y) /\ M(vec 0) = vec 0 ==> linear M`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^M->real^N`
    (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `l:real^M->real^N` LINEAR_0) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_ADD_LID] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(M:real^M->real^N) = l` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_RID]);;

(* The linear map M with M(R(A x)) = Fm x on a triangle s of L.              *)

let MOI_SLP_M_EXISTS = prove
 (`!c (v:real^N) t s (A:real^N->real^3) (R:real^3->real^3) (Fm:real^N->real^3) l y.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     t IN simplicial_link c v /\ aff_dim t = &2 /\
     moi_smo_regmap (convex hull (v INSERT t)) A /\ A v = vec 0 /\
     orthogonal_transformation R /\
     s SUBSET t /\ (?V. ~affine_dependent V /\ s = convex hull V) /\
     linear l /\ (!x. x IN s ==> Fm x = l x + y)
     ==> ?M. linear M /\ !x. x IN s ==> M(R(A x)) = Fm x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Fs")))))))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_SLP_TET_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    (X_CHOOSE_THEN `r:real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~((v:real^N) IN affine hull V)` ASSUME_TAC THENL
   [SUBGOAL_THEN `affine hull V SUBSET affine hull (t:real^N->bool)` MP_TAC THENL
     [SUBGOAL_THEN `affine hull V = affine hull (s:real^N->bool)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[AFFINE_HULL_CONVEX_HULL];
        MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]];
      UNDISCH_TAC `~((v:real^N) IN affine hull t)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN V)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(v:real^N) INSERT V`;
                 `\x:real^N. if x = v then vec 0:real^3 else l x + y`]
    MOI_REAL_AFFINE_EXTEND_POINTS) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lH:real^N->real^3` (X_CHOOSE_THEN `yH:real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(lH:real^N->real^3) v + yH = vec 0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> (lH:real^N->real^3) x + yH = Fm x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "Fs" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(x:real^N) IN s`)]) THEN
    MP_TAC(ISPECL [`lH:real^N->real^3`; `l:real^N->real^3`; `yH:real^3`;
                   `y:real^3`; `V:real^N->bool`] MOI_REAL_AFFINE_EQ_ON_CONVEX_HULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `lH:real^N->real^3`)) (concl th) &&
        can (find_term ((=) `(v:real^N) INSERT V`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN
      SUBGOAL_THEN `~(z:real^N = v)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N`; `p:real^N`; `q:real^N`; `r:real^N`;
                 `A:real^N->real^3`] MOI_SBA_REGMAP_INV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^3->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "BA"))) THEN
  MP_TAC(ISPEC `R:real^3->real^3` ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R':real^3->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:real^3. (lH:real^N->real^3)((B:real^3->real^N)(R' z)) + yH` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLP_AFFINE0_LINEAR THEN CONJ_TAC THENL
     [REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
        [`\z:real^3. (B:real^3->real^N)((R':real^3->real^3) z)`;
         `\x:real^N. (lH:real^N->real^3) x + yH`] MOI_SBA_AFFINE_COMPOSE)) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
          [`R':real^3->real^3`; `B:real^3->real^N`] MOI_SBA_AFFINE_COMPOSE)) THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY EXISTS_TAC [`R':real^3->real^3`; `vec 0:real^3`] THEN
        REWRITE_TAC[VECTOR_ADD_RID] THEN ASM_MESON_TAC[orthogonal_transformation];
        MAP_EVERY EXISTS_TAC [`lH:real^N->real^3`; `yH:real^3`] THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `(R':real^3->real^3) (vec 0) = vec 0` SUBST1_TAC THENL
       [ASM_MESON_TAC[orthogonal_transformation; LINEAR_0]; ALL_TAC] THEN
      SUBGOAL_THEN `(B:real^3->real^N) (vec 0) = v` SUBST1_TAC THENL
       [UNDISCH_TAC `(A:real^N->real^3) v = vec 0` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN USE_THEN "BA" MATCH_MP_TAC THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
        ASM_REWRITE_TAC[]]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(B:real^3->real^N)((A:real^N->real^3) x) = x` SUBST1_TAC THENL
     [USE_THEN "BA" MATCH_MP_TAC THEN
      SUBGOAL_THEN `(x:real^N) IN convex hull {v,p,q,r}` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let MOI_SLP_PART4 = prove
 (`!c (v:real^N) L (Fm:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     simplicial_complex L /\ UNIONS L = UNIONS(simplicial_link c v) /\
     (!s. s IN L ==> ?s'. s' IN simplicial_link c v /\ s SUBSET s') /\
     (!s. s IN L ==> ?l y. linear l /\ !x. x IN s ==> Fm x = l x + y) /\
     (!x. x IN UNIONS L ==> ~(Fm x = vec 0)) /\
     (!x z. x IN UNIONS L /\ z IN UNIONS L /\
            inv(norm(Fm x)) % Fm x = inv(norm(Fm z)) % Fm z ==> x = z)
     ==> !s U phi. s IN L /\ aff_dim s = &2 /\ (U,phi) IN moi_smo_link_atlas c v
                   ==> ?g. smooth_map_on (IMAGE phi (U INTER relative_interior s)) g /\
                           (!x. x IN U INTER relative_interior s
                                ==> g(phi x) = inv(norm(Fm x)) % Fm x) /\
                           (!y z. y IN IMAGE phi (U INTER relative_interior s) /\
                                  frechet_derivative g (at y) z = vec 0
                                  ==> z = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sub")
   (CONJUNCTS_THEN2 (LABEL_TAC "aff") (CONJUNCTS_THEN2 (LABEL_TAC "nz")
     (LABEL_TAC "inj"))))))))) THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `U:real^N->bool`; `phi:real^N->real^2`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `L:(real^N->bool)->bool`]
    MOI_SLP_L_TRI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?x0:real^N. x0 IN relative_interior s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `convex(s:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_SBA_LF_CONVEX; MOI_SLP_SC_LF]; ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                 `x0:real^N`] MOI_SLP_TCHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` (X_CHOOSE_THEN `psi:real^N->real^2`
   (X_CHOOSE_THEN `A:real^N->real^3` (X_CHOOSE_THEN `R:real^3->real^3`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pos")
       (LABEL_TAC "psiA"))))))))))))) THEN
  USE_THEN "aff" (MP_TAC o SPEC `s:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?V0:real^N->bool. ~affine_dependent V0 /\ s = convex hull V0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_SCF_SC_VERTICES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                 `s:real^N->bool`; `A:real^N->real^3`; `R:real^3->real^3`;
                 `Fm:real^N->real^3`; `l:real^N->real^3`; `y:real^3`]
    MOI_SLP_M_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "MRA"))) THEN
  MP_TAC(ISPECL [`UNIONS(simplicial_link c (v:real^N))`;
                 `moi_smo_link_atlas c (v:real^N)`;
                 `U:real^N->bool`; `phi:real^N->real^2`;
                 `V:real^N->bool`; `psi:real^N->real^2`;
                 `relative_interior s:real^N->bool`;
                 `\x:real^N. inv(norm((Fm:real^N->real^3) x)) % Fm x`;
                 `\z:real^2. (M:real^3->real^3)(vector[z$1; z$2; &0])`;
                 `(M:real^3->real^3)(basis 3)`] MOI_SLP_PART4_GEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[MOI_SLP_LINK_SMOOTH_ATLAS] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `UNIONS L = UNIONS(simplicial_link c (v:real^N))`)) THEN
    MATCH_MP_TAC MOI_SLP_RELINT_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SLP_L_DIM THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`] THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] (ISPECL
      [`\z:real^2. vector[z$1; z$2; &0]:real^3`; `M:real^3->real^3`]
      LINEAR_COMPOSE)) THEN
    ASM_REWRITE_TAC[MOI_SLP_LIFT0_LINEAR];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN s /\ x IN t` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "psiA" (fun th -> REWRITE_TAC[th]) THEN
    ABBREV_TAC `Y = (R:real^3->real^3)((A:real^N->real^3) x)` THEN
    SUBGOAL_THEN `&0 < (Y:real^3)$3` ASSUME_TAC THENL
     [EXPAND_TAC "Y" THEN USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(M:real^3->real^3)(vector[(moi_smo_gnom Y)$1; (moi_smo_gnom Y)$2; &0]) +
      M(basis 3) = inv((Y:real^3)$3) % (Fm:real^N->real^3) (x:real^N)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(MATCH_MP LINEAR_ADD (ASSUME `linear(M:real^3->real^3)`));
                  GSYM MOI_SLP_LIFT_SPLIT] THEN
      USE_THEN "MRA" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
        (ASSUME `(x:real^N) IN s`))]) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `Y:real^3` MOI_SLK_GNOM_LIFT) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV)
        [th]) THEN
      ASM_SIMP_TAC[LINEAR_CMUL; VECTOR_MUL_ASSOC; REAL_MUL_LINV;
                   REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; DE_MORGAN_THM] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
      USE_THEN "nz" MATCH_MP_TAC THEN
      REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SLP_UNIT_CMUL THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ]];
    MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`] THEN STRIP_TAC THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem C7, MOI_SMO_LINK_PD_STATEMENT.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_SMO_LINK_PD = prove
 (`!u:N->bool. MOI_SMO_LINK_PD_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[MOI_SMO_LINK_PD_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `v:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SLP_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^N->bool)->bool` (X_CHOOSE_THEN
    `Fm:real^N->real^3` (X_CHOOSE_THEN `h':real^3->real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`;
                        `\x:real^N. inv(norm((Fm:real^N->real^3) x)) % Fm x`;
                        `h':real^3->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x z:real^N. x IN UNIONS L /\ z IN UNIONS L /\
                 inv(norm((Fm:real^N->real^3) x)) % Fm x = inv(norm(Fm z)) % Fm z
                 ==> x = z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHISM] o check (fun th ->
      can (find_term ((=) `h':real^3->real^N`)) (concl th))) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x:real^N` th) THEN
                         MP_TAC(SPEC `z:real^N` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_smo_conical_pd] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLP_PART1 THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `L:(real^N->bool)->bool`]
      MOI_SLP_L_VERT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC MOI_SLP_PART2_CONE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_SLP_PART2_EDGE THEN EXISTS_TAC `f:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_SLP_PART2_TRI THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `L:(real^N->bool)->bool`]
      MOI_SLP_L_EDGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THENL
     [MATCH_MP_TAC MOI_SLP_PART3_EDGE THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_SLP_PART3_TRI THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MOI_SLP_PART4 THEN ASM_REWRITE_TAC[]]);;

