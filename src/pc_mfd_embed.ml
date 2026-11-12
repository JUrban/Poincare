(* ========================================================================= *)
(* pc_mfd_embed: the tangent projection of an immersion into real^K          *)
(* (MFD_TPROJ, MFD_TPROJ_SMOOTH) and the Whitney embedding of a compact      *)
(* Hausdorff n-manifold into real^K for every K with 2n + 1 <= K             *)
(* (MFD_EMBEDDING_EXISTS).  The embedding is built chart by chart in the     *)
(* fixed target: each step adds a generic linear perturbation B h with h =   *)
(* (chi phi, chi), and the bad B form a negligible set                       *)
(* (NEGLIGIBLE_DIFFERENTIABLE_IMAGE_LOWDIM).                                 *)
(* ========================================================================= *)

needs "src/pc_mfd_embdefs.ml";;
needs "src/pc_mfd_cutoff.ml";;
needs "src/pc_mfd_diff.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Rectangular matrix fields: smoothness of entries, products, transposes   *)
(* and Jacobians (the square versions are the LRG_SMOOTH lemmas of pc_lrg);  *)
(* the projection J (J^T J)^-1 J^T for an injective J and its invariance     *)
(* under J |-> J T with T invertible.                                        *)
(* ------------------------------------------------------------------------- *)

let GRGE_LINEAR_MATRIFY_ENTRY = prove
 (`!i j. linear (\x:real^(Q,P)finite_prod. lift((matrify x:real^P^Q)$i$j))`,
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT;
              MATRIX_CMUL_COMPONENT; LIFT_ADD; LIFT_CMUL]);;

let GRGE_SMOOTH_VECTORIZE = prove
 (`!s (A:real^M->real^P^Q).
        open s
        ==> (smooth_map_on s (vectorize o A) <=>
             !i j. 1 <= i /\ i <= dimindex(:Q) /\ 1 <= j /\ j <= dimindex(:P)
                   ==> smooth_map_on s (\z. lift(A z$i$j)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(\z. lift((A:real^M->real^P^Q) z$i$j)) =
      (\x:real^(Q,P)finite_prod. lift((matrify x:real^P^Q)$i$j)) o
      ((vectorize:real^P^Q->real^(Q,P)finite_prod) o A)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[GRGE_LINEAR_MATRIFY_ENTRY];
    DISCH_TAC THEN
    GEN_REWRITE_TAC I
     [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE (ASSUME `open(s:real^M->bool)`)] THEN
    REWRITE_TAC[DIMINDEX_FINITE_PROD; o_THM] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(A:real^M->real^P^Q) x`; `k:num`] VECTORIZE_COMPONENT) THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `k <= dimindex(:Q) * dimindex(:P)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\x. lift(vectorize((A:real^M->real^P^Q) x)$k)) =
      (\z. lift(A z$(1 + (k - 1) DIV dimindex(:P))$(1 + (k - 1) MOD dimindex(:P))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^M` THEN AP_TERM_TAC THEN
      MATCH_MP_TAC VECTORIZE_COMPONENT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `~(dimindex(:P) = 0)` ASSUME_TAC THENL
     [REWRITE_TAC[DIMINDEX_NONZERO]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `1 <= 1 + a`;
                 ARITH_RULE `1 + a <= n <=> a < n`; RDIV_LT_EQ] THEN
    UNDISCH_TAC `k <= dimindex(:Q) * dimindex(:P)` THEN
    UNDISCH_TAC `1 <= k` THEN ARITH_TAC]);;

let GRGE_BILINEAR_MATRIX_MUL = prove
 (`bilinear (\(m1:real^(Q,P)finite_prod) (m2:real^(P,R)finite_prod).
               (vectorize:real^R^Q->real^(Q,R)finite_prod)
                 ((matrify m1:real^P^Q) ** (matrify m2:real^R^P)))`,
  REWRITE_TAC[bilinear; linear; MATRIFY_ADD; MATRIFY_CMUL;
              MATRIX_ADD_LDISTRIB; MATRIX_ADD_RDISTRIB;
              MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; VECTORIZE_ADD; VECTORIZE_CMUL]);;

let GRGE_BILINEAR_MATRIFY_MUL = prove
 (`bilinear (\(m:real^(Q,P)finite_prod) (v:real^P). (matrify m:real^P^Q) ** v)`,
  REWRITE_TAC[bilinear; linear; MATRIFY_ADD; MATRIFY_CMUL;
              MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_RMUL]);;

let GRGE_SMOOTH_MATMUL = prove
 (`!s (A:real^M->real^P^Q) (B:real^M->real^R^P).
        open s /\ smooth_map_on s (vectorize o A) /\
        smooth_map_on s (vectorize o B)
        ==> smooth_map_on s (vectorize o (\z. A z ** B z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`s:real^M->bool`;
    `\(m1:real^(Q,P)finite_prod) (m2:real^(P,R)finite_prod).
        (vectorize:real^R^Q->real^(Q,R)finite_prod)
          ((matrify m1:real^P^Q) ** (matrify m2:real^R^P))`;
    `(vectorize:real^P^Q->real^(Q,P)finite_prod) o (A:real^M->real^P^Q)`;
    `(vectorize:real^R^P->real^(P,R)finite_prod) o (B:real^M->real^R^P)`]
   SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[GRGE_BILINEAR_MATRIX_MUL; o_THM; MATRIFY_VECTORIZE] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let GRGE_SMOOTH_MATVEC = prove
 (`!s (A:real^M->real^P^Q) (b:real^M->real^P).
        open s /\ smooth_map_on s (vectorize o A) /\ smooth_map_on s b
        ==> smooth_map_on s (\z. A z ** b z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`s:real^M->bool`;
    `\(m:real^(Q,P)finite_prod) (v:real^P). (matrify m:real^P^Q) ** v`;
    `(vectorize:real^P^Q->real^(Q,P)finite_prod) o (A:real^M->real^P^Q)`;
    `b:real^M->real^P`]
   SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[GRGE_BILINEAR_MATRIFY_MUL; o_THM; MATRIFY_VECTORIZE]);;

let GRGE_SMOOTH_TRANSP = prove
 (`!s (A:real^M->real^P^Q).
        open s /\ smooth_map_on s (vectorize o A)
        ==> smooth_map_on s (vectorize o (\z. transp(A z)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(vectorize:real^Q^P->real^(P,Q)finite_prod) o
    (\z. transp((A:real^M->real^P^Q) z)) =
    ((vectorize:real^Q^P->real^(P,Q)finite_prod) o transp o
     (matrify:real^(Q,P)finite_prod->real^P^Q)) o
    ((vectorize:real^P^Q->real^(Q,P)finite_prod) o A)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[linear; o_THM; MATRIFY_ADD; MATRIFY_CMUL; TRANSP_MATRIX_ADD;
              TRANSP_MATRIX_CMUL; VECTORIZE_ADD; VECTORIZE_CMUL]);;

let GRGE_SMOOTH_JACOBIAN = prove
 (`!s (h:real^N->real^K).
        open s /\ smooth_map_on s h
        ==> smooth_map_on s
              (vectorize o (\z. matrix(frechet_derivative h (at z))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GRGE_SMOOTH_VECTORIZE] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_COMPONENT] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]);;

let GRGE_GRAM_INVERTIBLE = prove
 (`!J:real^N^K. (!v. J ** v = vec 0 ==> v = vec 0) ==> invertible(transp J ** J)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INVERTIBLE_DET_NZ] THEN
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(J:real^N^K) ** x = vec 0` (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[GSYM DOT_EQ_0] THEN
  REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[DOT_LZERO; DOT_RZERO]);;

let GRGE_PROJ_PROPS = prove
 (`!J:real^N^K.
        (!v. J ** v = vec 0 ==> v = vec 0)
        ==> transp(J ** matrix_inv(transp J ** J) ** transp J) =
            J ** matrix_inv(transp J ** J) ** transp J /\
            (J ** matrix_inv(transp J ** J) ** transp J) **
            (J ** matrix_inv(transp J ** J) ** transp J) =
            J ** matrix_inv(transp J ** J) ** transp J /\
            (J ** matrix_inv(transp J ** J) ** transp J) ** J = J /\
            transp J ** (J ** matrix_inv(transp J ** J) ** transp J) = transp J /\
            (!w. (J ** matrix_inv(transp J ** J) ** transp J) ** w = w <=>
                 ?v. w = J ** v)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GRGE_GRAM_INVERTIBLE) THEN
  ABBREV_TAC `M = matrix_inv(transp(J:real^N^K) ** J)` THEN
  SUBGOAL_THEN
   `(M:real^N^N) ** (transp(J:real^N^K) ** J) = mat 1 /\
    (transp J ** J) ** M = mat 1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN ASM_SIMP_TAC[MATRIX_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `transp(M:real^N^N) = M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN
    REWRITE_TAC[GSYM MATRIX_INV_TRANSP; MATRIX_TRANSP_MUL; TRANSP_TRANSP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. (M:real^N^N) ** transp(J:real^N^K) ** J ** x = x) /\
    (!x. transp(J:real^N^K) ** J ** (M:real^N^N) ** x = x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_VECTOR_MUL_LID] THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC];
    REWRITE_TAC[MATRIX_EQ; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[MATRIX_EQ; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[MATRIX_EQ; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `w:real^K` THEN REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `(M:real^N^N) ** transp(J:real^N^K) ** w` THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[]]]);;

let GRGE_PROJ_UNIQUE = prove
 (`!P1 P2:real^K^K.
        transp P1 = P1 /\ transp P2 = P2 /\ P1 ** P2 = P2 /\ P2 ** P1 = P1
        ==> P1 = P2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `transp((P2:real^K^K) ** P1) = P1 ** P2` MP_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_TRANSP_MUL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let GRGE_PROJ_RMUL = prove
 (`!(J:real^N^K) (S:real^N^N).
        (!v. J ** v = vec 0 ==> v = vec 0) /\ invertible S
        ==> (J ** S) ** matrix_inv(transp(J ** S) ** (J ** S)) ** transp(J ** S) =
            J ** matrix_inv(transp J ** J) ** transp J`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!v. ((J:real^N^K) ** (S:real^N^N)) ** v = vec 0 ==> v = vec 0`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. matrix_inv(S:real^N^N) ** x`) THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID;
                 MATRIX_VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(J:real^N^K) ** (S:real^N^N)` GRGE_PROJ_PROPS) THEN
  MP_TAC(ISPEC `J:real^N^K` GRGE_PROJ_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN
   `(((J:real^N^K) ** (S:real^N^N)) **
     matrix_inv(transp(J ** S) ** (J ** S)) ** transp(J ** S)) ** J = J`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(((J:real^N^K) ** (S:real^N^N)) **
       matrix_inv(transp(J ** S) ** (J ** S)) ** transp(J ** S)) ** J =
      ((((J:real^N^K) ** (S:real^N^N)) **
       matrix_inv(transp(J ** S) ** (J ** S)) ** transp(J ** S)) ** (J ** S)) **
      matrix_inv S`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
      ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_RID];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_INV; MATRIX_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((J:real^N^K) ** matrix_inv(transp J ** J) ** transp J) **
    (J ** (S:real^N^N)) = J ** S`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `((J:real^N^K) ** matrix_inv(transp J ** J) ** transp J) ** J = J`) THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GRGE_PROJ_UNIQUE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Immersions in charts; the chain rule through chart transitions; the       *)
(* tangent projection (MFD_TPROJ) and its smoothness (MFD_TPROJ_SMOOTH).     *)
(* ------------------------------------------------------------------------- *)

let GRGE_IMMERSION_CHART = prove
 (`!top atlas (f:A->real^K) c.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_immersion_into atlas f /\ c IN atlas
        ==> smooth_map_on (IMAGE (SND c) (FST c)) (f o chart_inv c) /\
            !y v. y IN IMAGE (SND c) (FST c) /\
                  frechet_derivative (f o chart_inv c) (at y) v = vec 0
                  ==> v = vec 0`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `f:A->real^K`; `U:A->bool`; `phi:A->real^N`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^N`] o
    GEN_REWRITE_RULE I [smooth_immersion_into]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^K` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) U)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (phi:A->real^N) U
        ==> ((f:A->real^K) o chart_inv (U,phi)) y = (g:real^N->real^K) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `g:real^N->real^K` THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`y:real^N`; `v:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `frechet_derivative ((f:A->real^K) o chart_inv (U,phi)) (at y) =
      frechet_derivative (g:real^N->real^K) (at y)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `frechet_derivative ((f:A->real^K) o chart_inv (U:A->bool,phi:A->real^N))
                         (at (y:real^N)) (v:real^N) = vec 0` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let GRGE_CHART_DERIV_CHAIN = prove
 (`!top atlas (f:A->real^K) c c' x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_smooth atlas f /\ c IN atlas /\ c' IN atlas /\ x IN FST c /\ x IN FST c'
        ==> ((f o chart_inv c) has_derivative
             (frechet_derivative (f o chart_inv c') (at (SND c' x)) o
              chart_jac c c' x)) (at (SND c x)) /\
            frechet_derivative (f o chart_inv c) (at (SND c x)) =
            frechet_derivative (f o chart_inv c') (at (SND c' x)) o chart_jac c c' x`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `f:A->real^K`; `U:A->bool`; `phi:A->real^N`;
                       `V:A->bool`; `psi:A->real^N`; `x:A`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN SIMP_TAC[]] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `((f:A->real^K) o chart_inv (V:A->bool,psi:A->real^N)) o
              chart_trans (U:A->bool,phi:A->real^N) (V,psi)` THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `psi:A->real^N`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `(y:real^N) IN IMAGE (phi:A->real^N) (U INTER V)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[o_THM; chart_trans; SND] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `chart_trans (U:A->bool,phi:A->real^N) (V,psi) (phi x) = psi x`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CHART_TRANS_AT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(V:A->bool,psi:A->real^N)) (FST(V,psi))` THEN
    UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)` THEN
    REWRITE_TAC[mfd_smooth] THEN
    DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ASM SET_TAC[]]]);;

let GRGE_IMMERSION_SMOOTH = prove
 (`!top atlas (f:A->real^K).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_immersion_into atlas f
        ==> mfd_smooth atlas f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
  ASM_SIMP_TAC[]);;

let GRGE_CHART_JAC_INVERTIBLE = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c' x.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
        x IN FST c /\ x IN FST c'
        ==> linear(chart_jac c c' x) /\ invertible(matrix(chart_jac c c' x))`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p1:A->bool`; `p2:A->real^N`; `p1':A->bool`; `p2':A->real^N`;
                 `x:A`] CHART_JAC_LINEAR) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p1':A->bool`; `p2':A->real^N`; `p1:A->bool`; `p2:A->real^N`;
                 `x:A`] CHART_JAC_LINEAR) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p1:A->bool`; `p2:A->real^N`; `p1':A->bool`; `p2':A->real^N`;
                 `x:A`] CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
  EXISTS_TAC `matrix(chart_jac (p1':A->bool,p2':A->real^N) (p1,p2) x)` THEN
  ASM_SIMP_TAC[GSYM MATRIX_COMPOSE] THEN REWRITE_TAC[MATRIX_ID]);;

let GRGE_EMB_JAC_FACTS = prove
 (`!top atlas (f:A->real^K) c x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_immersion_into atlas f /\ c IN atlas /\ x IN FST c
        ==> (!v. mfd_emb_jac atlas f x ** v = vec 0 ==> v = vec 0) /\
            invertible(matrix(chart_jac c (chart_at atlas x) x)) /\
            matrix(frechet_derivative (f o chart_inv c) (at (SND c x))) =
            mfd_emb_jac atlas f x ** matrix(chart_jac c (chart_at atlas x) x) /\
            (!v. frechet_derivative (f o chart_inv c) (at (SND c x)) v =
                 matrix(frechet_derivative (f o chart_inv c) (at (SND c x))) ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[GRGE_IMMERSION_SMOOTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`]
                GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "INJ0")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "INJC")) THEN
  SUBGOAL_THEN
   `linear(frechet_derivative ((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N)))
                              (at (SND c (x:A)))) /\
    linear(frechet_derivative ((f:A->real^K) o
             chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x))
           (at (SND(chart_at atlas x) x)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN ASM_MESON_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`; `x:A`]
                GRGE_CHART_JAC_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[mfd_emb_jac] THEN ASM_SIMP_TAC[MATRIX_WORKS] THEN
    DISCH_TAC THEN USE_THEN "INJ0" MATCH_MP_TAC THEN
    EXISTS_TAC `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `c:(A->bool)#(A->real^N)`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`; `x:A`]
                  GRGE_CHART_DERIV_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[MATRIX_COMPOSE; mfd_emb_jac];
    ASM_SIMP_TAC[MATRIX_WORKS]]);;

let MFD_TPROJ = prove
 (`!top atlas (f:A->real^K) x.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_immersion_into atlas f /\ x IN topspace top
     ==> transp(mfd_tproj atlas f x) = mfd_tproj atlas f x /\
         mfd_tproj atlas f x ** mfd_tproj atlas f x = mfd_tproj atlas f x /\
         (!c v. c IN atlas /\ x IN FST c
                ==> mfd_tproj atlas f x **
                    frechet_derivative (f o chart_inv c) (at (SND c x)) v =
                    frechet_derivative (f o chart_inv c) (at (SND c x)) v) /\
         (!w. mfd_tproj atlas f x ** w = w <=>
              ?v. w = frechet_derivative (f o chart_inv (chart_at atlas x))
                                         (at (SND(chart_at atlas x) x)) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`;
                 `x:A`] GRGE_EMB_JAC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `mfd_emb_jac (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) x`
               GRGE_PROJ_PROPS) THEN
  ASM_REWRITE_TAC[GSYM mfd_tproj] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `v:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `c:(A->bool)#(A->real^N)`; `x:A`]
                  GRGE_EMB_JAC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `matrix(chart_jac (c:(A->bool)#(A->real^N))
                      (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x) **
                (v:real^N)` THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC];
    X_GEN_TAC `w:real^K` THEN
    SUBGOAL_THEN
     `matrix(chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))
                       (chart_at atlas x) x) = mat 1`
    (fun th -> REWRITE_TAC[th; MATRIX_MUL_RID]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                   `x:A`] CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[MATRIX_ID]]);;

let MFD_TPROJ_SMOOTH = prove
 (`!top atlas (f:A->real^K).
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_immersion_into atlas f
     ==> mfd_smooth atlas (\x. vectorize(mfd_tproj atlas f x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `Jc = \y:real^N. matrix(frechet_derivative ((f:A->real^K) o
                                chart_inv (c:(A->bool)#(A->real^N))) (at y))` THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)
        ==> !v. (Jc:real^N->real^N^K) y ** v = vec 0 ==> v = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN X_GEN_TAC `v:real^N` THEN
    EXPAND_TAC "Jc" THEN
    SUBGOAL_THEN
     `linear(frechet_derivative ((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N)))
                                (at (y:real^N)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `(vectorize:real^K^K->real^(K,K)finite_prod) o
    (\y. (Jc:real^N->real^N^K) y **
         matrix_inv(transp(Jc y) ** Jc y) ** transp(Jc y))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `chart_inv (c:(A->bool)#(A->real^N)) y IN FST c /\ SND c (chart_inv c y) = y`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `c:(A->bool)#(A->real^N)`;
                   `chart_inv (c:(A->bool)#(A->real^N)) y`] GRGE_EMB_JAC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXPAND_TAC "Jc" THEN ASM_REWRITE_TAC[mfd_tproj] THEN
    MATCH_MP_TAC GRGE_PROJ_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
      ((vectorize:real^N^K->real^(K,N)finite_prod) o (Jc:real^N->real^N^K))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Jc" THEN MATCH_MP_TAC GRGE_SMOOTH_JACOBIAN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
      ((vectorize:real^K^N->real^(N,K)finite_prod) o
       (\y. transp((Jc:real^N->real^N^K) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGE_SMOOTH_TRANSP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
      ((vectorize:real^N^N->real^(N,N)finite_prod) o
       (\y. matrix_inv(transp((Jc:real^N->real^N^K) y) ** Jc y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM INVERTIBLE_DET_NZ] THEN MATCH_MP_TAC GRGE_GRAM_INVERTIBLE THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The genericity lemma.  For smooth u : real^P -> real^K and                 *)
(* w : real^P -> real^(N,1)finite_sum on an open set, with dim P < K, the    *)
(* matrices B with B w(p) + u(p) = 0 for some p with w(p) <> 0 form a        *)
(* negligible set (after vectorize).  If w(p)_i <> 0, B is determined by p   *)
(* and its other n columns: B = B' D_i + c e_i^T with D_i the n x (n+1)     *)
(* matrix that deletes coordinate i and c = -(u + B' D_i w) / w_i, a smooth  *)
(* map from a space of dimension dim P + n K < (n+1) K                        *)
(* (NEGLIGIBLE_DIFFERENTIABLE_IMAGE_LOWDIM).                                  *)
(* ------------------------------------------------------------------------- *)

let GRGE_DELTA_MUL = prove
 (`!a (f:num->real) j. (if j = a then &1 else &0) * f j = if j = a then f a else &0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO]);;

let GRGE_DM_APPLY = prove
 (`!i (x:real^(N,1)finite_sum).
        ((lambda k l. if l = (if k < i then k else k + 1) then &1 else &0)
         :real^(N,1)finite_sum^N) ** x =
        (lambda k. x$(if k < i then k else k + 1))`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[GRGE_DELTA_MUL; SUM_DELTA; IN_NUMSEG; DIMINDEX_FINITE_SUM;
              DIMINDEX_1] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN ASM_ARITH_TAC);;

let GRGE_EM_APPLY = prove
 (`!i (y:real^N).
        1 <= i /\ i <= dimindex(:(N,1)finite_sum)
        ==> ((lambda l k. if (l < i /\ k = l) \/ (i < l /\ k + 1 = l) then &1 else &0)
             :real^N^(N,1)finite_sum) ** y =
            (lambda l. if l < i then y$l else if l = i then &0 else y$(l - 1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA] THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_FINITE_SUM; DIMINDEX_1]) THEN
  ASM_CASES_TAC `(l:num) < i` THENL
   [SUBGOAL_THEN `!k:num. ((l:num) < i /\ k = l) \/ (i < l /\ k + 1 = l) <=> k = l`
    (fun th -> REWRITE_TAC[th]) THENL [GEN_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GRGE_DELTA_MUL; SUM_DELTA; IN_NUMSEG] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(l:num) = i` THENL
   [ASM_REWRITE_TAC[LT_REFL; REAL_MUL_LZERO; SUM_0] THEN
    REWRITE_TAC[ARITH_RULE `~((i:num) < i /\ k = i)`] THEN
    SUBGOAL_THEN `!k:num. ~((i:num) < i /\ k + 1 = i)` (fun th -> REWRITE_TAC[th]) THENL
     [ARITH_TAC; REWRITE_TAC[REAL_MUL_LZERO; SUM_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k:num. ((l:num) < i /\ k = l) \/ (i < l /\ k + 1 = l) <=> k = l - 1`
  (fun th -> REWRITE_TAC[th]) THENL [GEN_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GRGE_DELTA_MUL; SUM_DELTA; IN_NUMSEG] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN ASM_ARITH_TAC);;

let GRGE_EM_DM = prove
 (`!i (x:real^(N,1)finite_sum).
        1 <= i /\ i <= dimindex(:(N,1)finite_sum)
        ==> ((lambda l k. if (l < i /\ k = l) \/ (i < l /\ k + 1 = l) then &1 else &0)
             :real^N^(N,1)finite_sum) **
            (((lambda k l. if l = (if k < i then k else k + 1) then &1 else &0)
              :real^(N,1)finite_sum^N) ** x) =
            x - x$i % basis i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GRGE_DM_APPLY; GRGE_EM_APPLY] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
           BASIS_COMPONENT] THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_FINITE_SUM; DIMINDEX_1]) THEN
  ASM_CASES_TAC `(l:num) < i` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((l:num) = i)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= (l:num) /\ l <= dimindex(:N)`
      (fun th -> SIMP_TAC[th; LAMBDA_BETA]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(l:num) = i` THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= (l:num) - 1 /\ l - 1 <= dimindex(:N)`
    (fun th -> SIMP_TAC[th; LAMBDA_BETA]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((l:num) - 1 < i) /\ l - 1 + 1 = l` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; REAL_ARITH_TAC]);;

let GRGE_OUTER_APPLY = prove
 (`!i (c:real^K) (x:real^(N,1)finite_sum).
        1 <= i /\ i <= dimindex(:(N,1)finite_sum)
        ==> ((lambda k l. if l = i then c$k else &0):real^(N,1)finite_sum^K) ** x =
            x$i % c`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA; VECTOR_MUL_COMPONENT] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
  ONCE_REWRITE_TAC[MESON[] `(if l = i then (c:real^K)$k * (x:real^(N,1)finite_sum)$l
                             else &0) =
                            (if l = i then c$k * x$i else &0)`] THEN
  ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN REAL_ARITH_TAC);;

let GRGE_NONZERO_COMPONENT = prove
 (`!x:real^M. ~(x = vec 0) ==> ?i. 1 <= i /\ i <= dimindex(:M) /\ ~(x$i = &0)`,
  GEN_TAC THEN REWRITE_TAC[CART_EQ; VEC_COMPONENT] THEN MESON_TAC[]);;

let GRGE_SMOOTH_SCALAR_MUL = prove
 (`!s (f:real^M->real) (g:real^M->real^N).
        open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s g
        ==> smooth_map_on s (\x. f x % g x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift((f:real^M->real) x)`;
                 `g:real^M->real^N`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let GRGE_SMOOTH_LINEAR = prove
 (`!s (g:real^M->real^N). open s /\ linear g ==> smooth_map_on s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. x`; `g:real^M->real^N`]
                SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

let GRGE_BAD_NEGLIGIBLE = prove
 (`!(u:real^P->real^K) (w:real^P->real^(N,1)finite_sum) s.
        open s /\ smooth_map_on s u /\ smooth_map_on s w /\
        dimindex(:P) < dimindex(:K)
        ==> negligible
              {b:real^(K,(N,1)finite_sum)finite_prod |
               ?p. p IN s /\ ~(w p = vec 0) /\
                   (matrify b:real^(N,1)finite_sum^K) ** w p + u p = vec 0}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `Dm = \i. (lambda k l. if l = (if k < i then k else k + 1) then &1 else &0)
             :real^(N,1)finite_sum^N` THEN
  ABBREV_TAC
   `Em = \i. (lambda l k. if (l < i /\ k = l) \/ (i < l /\ k + 1 = l) then &1 else &0)
             :real^N^(N,1)finite_sum` THEN
  ABBREV_TAC
   `cc = \i (q:real^(P,(K,N)finite_prod)finite_sum).
           inv(((w:real^P->real^(N,1)finite_sum) (fstcart q))$i) %
           (--((u:real^P->real^K)(fstcart q)) -
            (matrify(sndcart q):real^N^K) **
            ((Dm:num->real^(N,1)finite_sum^N) i ** w(fstcart q)))` THEN
  ABBREV_TAC
   `Th = \i (q:real^(P,(K,N)finite_prod)finite_sum).
           (vectorize:real^(N,1)finite_sum^K->real^(K,(N,1)finite_sum)finite_prod)
             ((matrify(sndcart q):real^N^K) ** (Dm:num->real^(N,1)finite_sum^N) i) +
           (vectorize:real^(N,1)finite_sum^K->real^(K,(N,1)finite_sum)finite_prod)
             ((lambda k l. if l = i
                           then ((cc:num->real^(P,(K,N)finite_prod)finite_sum->real^K)
                                   i q)$k
                           else &0):real^(N,1)finite_sum^K)` THEN
  ABBREV_TAC
   `Si = \i. {q:real^(P,(K,N)finite_prod)finite_sum |
              fstcart q IN s /\
              ~(((w:real^P->real^(N,1)finite_sum)(fstcart q))$i = &0)}` THEN
  SUBGOAL_THEN `open {q:real^(P,(K,N)finite_prod)finite_sum | fstcart q IN s}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on {q:real^(P,(K,N)finite_prod)finite_sum | fstcart q IN s}
      (\q. (u:real^P->real^K)(fstcart q)) /\
    smooth_map_on {q:real^(P,(K,N)finite_prod)finite_sum | fstcart q IN s}
      (\q. (w:real^P->real^(N,1)finite_sum)(fstcart q))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[o_DEF] SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
    EXISTS_TAC `s:real^P->bool` THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_FSTCART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (Si:num->real^(P,(K,N)finite_prod)finite_sum->bool) i SUBSET
        {q | fstcart q IN s} /\ open(Si i)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Si" THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `{q:real^(P,(K,N)finite_prod)finite_sum |
       fstcart q IN s /\ ~(((w:real^P->real^(N,1)finite_sum)(fstcart q))$i = &0)} =
      {q | q IN {q | fstcart q IN s} /\
           (\q. lift((w(fstcart q))$i)) q IN (:real^1) DELETE vec 0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE; IN_UNIV; GSYM LIFT_NUM;
                  LIFT_EQ];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC
   `UNIONS (IMAGE (\i. IMAGE ((Th:num->real^(P,(K,N)finite_prod)finite_sum->
                                     real^(K,(N,1)finite_sum)finite_prod) i)
                             ((Si:num->real^(P,(K,N)finite_prod)finite_sum->bool) i))
                  (1..dimindex(:(N,1)finite_sum)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_LOWDIM THEN CONJ_TAC THENL
     [REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_FINITE_PROD; DIMINDEX_1] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
      UNDISCH_TAC `dimindex(:P) < dimindex(:K)` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT] THEN
    X_GEN_TAC `q:real^(P,(K,N)finite_prod)finite_sum` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(Si:num->real^(P,(K,N)finite_prod)finite_sum->bool) i` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `smooth_map_on ((Si:num->real^(P,(K,N)finite_prod)finite_sum->bool) i)
        (\q. (u:real^P->real^K)(fstcart q)) /\
      smooth_map_on ((Si:num->real^(P,(K,N)finite_prod)finite_sum->bool) i)
        (\q. (w:real^P->real^(N,1)finite_sum)(fstcart q))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `{q:real^(P,(K,N)finite_prod)finite_sum | fstcart q IN s}` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "Th" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[linear; SNDCART_ADD; SNDCART_CMUL; MATRIFY_ADD; MATRIFY_CMUL;
                  MATRIX_ADD_RDISTRIB; MATRIX_MUL_LMUL; VECTORIZE_ADD; VECTORIZE_CMUL];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`(Si:num->real^(P,(K,N)finite_prod)finite_sum->bool) i`;
      `(cc:num->real^(P,(K,N)finite_prod)finite_sum->real^K) i`;
      `\c:real^K. (vectorize:real^(N,1)finite_sum^K->real^(K,(N,1)finite_sum)finite_prod)
                    ((lambda k l. if l = i then c$k else &0):real^(N,1)finite_sum^K)`]
     SMOOTH_MAP_ON_LINEAR_O) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[linear; GSYM VECTORIZE_ADD; GSYM VECTORIZE_CMUL] THEN
      CONJ_TAC THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT;
               VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "cc" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC GRGE_SMOOTH_SCALAR_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(Si:num->real^(P,(K,N)finite_prod)finite_sum->bool) i`;
                     `\q:real^(P,(K,N)finite_prod)finite_sum.
                        lift(((w:real^P->real^(N,1)finite_sum)(fstcart q))$i)`]
                    SMOOTH_MAP_ON_LIFT_INV) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT] THEN
      EXPAND_TAC "Si" THEN SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_NEG_OPEN] THEN
    MP_TAC(ISPECL
     [`(Si:num->real^(P,(K,N)finite_prod)finite_sum->bool) i`;
      `\(m:real^(K,N)finite_prod) (v:real^(N,1)finite_sum).
          (matrify m:real^N^K) ** ((Dm:num->real^(N,1)finite_sum^N) i ** v)`;
      `sndcart:real^(P,(K,N)finite_prod)finite_sum->real^(K,N)finite_prod`;
      `\q:real^(P,(K,N)finite_prod)finite_sum.
         (w:real^P->real^(N,1)finite_sum)(fstcart q)`]
     SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[bilinear; linear; MATRIFY_ADD; MATRIFY_CMUL;
                  MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
                  MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_RMUL];
      MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_SNDCART]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE; IN_NUMSEG] THEN
  X_GEN_TAC `b:real^(K,(N,1)finite_sum)finite_prod` THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^P` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GRGE_NONZERO_COMPONENT) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC
   `pastecart (p:real^P)
      ((vectorize:real^N^K->real^(K,N)finite_prod)
         ((matrify b:real^(N,1)finite_sum^K) ** (Em:num->real^N^(N,1)finite_sum) i))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "Si" THEN REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART] THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `(cc:num->real^(P,(K,N)finite_prod)finite_sum->real^K) i
      (pastecart (p:real^P)
        ((vectorize:real^N^K->real^(K,N)finite_prod)
           ((matrify b:real^(N,1)finite_sum^K) ** (Em:num->real^N^(N,1)finite_sum) i))) =
    (matrify b:real^(N,1)finite_sum^K) ** basis i`
  ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; MATRIFY_VECTORIZE] THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    MAP_EVERY EXPAND_TAC ["Dm"; "Em"] THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GRGE_EM_DM] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
    SUBGOAL_THEN
     `(matrify b:real^(N,1)finite_sum^K) ** (w:real^P->real^(N,1)finite_sum) p =
      --((u:real^P->real^K) p)`
    SUBST1_TAC THENL
     [UNDISCH_TAC
       `(matrify b:real^(N,1)finite_sum^K) ** (w:real^P->real^(N,1)finite_sum) p +
        (u:real^P->real^K) p = vec 0` THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `--u - (--u - c % (v:real^K)) = c % v`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID];
    ALL_TAC] THEN
  EXPAND_TAC "Th" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SNDCART_PASTECART; MATRIFY_VECTORIZE; GSYM VECTORIZE_ADD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM VECTORIZE_MATRIFY] THEN AP_TERM_TAC THEN
  REWRITE_TAC[MATRIX_EQ] THEN X_GEN_TAC `x:real^(N,1)finite_sum` THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  MAP_EVERY EXPAND_TAC ["Dm"; "Em"] THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GRGE_EM_DM; GRGE_OUTER_APPLY] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
  VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tools for the Whitney step: derivatives as smooth functions of (y,v),     *)
(* continuity of manifold-smooth maps, finite chart covers of compact sets,  *)
(* and the cutoff chart map h = (chi phi, chi) with its injectivity          *)
(* properties.                                                               *)
(* ------------------------------------------------------------------------- *)

let GRGE_SMOOTH_DERIV_APPLY = prove
 (`!s (g:real^N->real^M).
        open s /\ smooth_map_on s g
        ==> open {p:real^(N,N)finite_sum | fstcart p IN s} /\
            smooth_map_on {p:real^(N,N)finite_sum | fstcart p IN s}
              (\p. frechet_derivative g (at (fstcart p)) (sndcart p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART];
    DISCH_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\p:real^(N,N)finite_sum.
      vsum(1..dimindex(:N))
        (\k. (sndcart p)$k % frechet_derivative (g:real^N->real^M) (at (fstcart p))
                                                 (basis k))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `p:real^(N,N)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `linear(frechet_derivative (g:real^N->real^M) (at (fstcart(p:real^(N,N)finite_sum))))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC GRGE_SMOOTH_SCALAR_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linear; SNDCART_ADD; SNDCART_CMUL; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL];
    SUBGOAL_THEN
     `(\p:real^(N,N)finite_sum.
         frechet_derivative (g:real^N->real^M) (at (fstcart p)) (basis k)) =
      (\y. frechet_derivative g (at y) (basis k)) o fstcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_FSTCART]]);;

let GRGE_MFD_SMOOTH_CONTINUOUS = prove
 (`!top atlas (f:A->real^K).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_smooth atlas f
        ==> continuous_map (top,euclidean) f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
  X_GEN_TAC `u:real^K->bool` THEN REWRITE_TAC[GSYM OPEN_IN] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `{p:A | p IN FST(c:(A->bool)#(A->real^N)) /\ (f:A->real^K) p IN u}` THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `{p:A | p IN FST(c:(A->bool)#(A->real^N)) /\ (f:A->real^K) p IN u} =
      {p | p IN FST c /\
           SND c p IN {y | y IN IMAGE (SND c) (FST c) /\
                           (f o chart_inv (c:(A->bool)#(A->real^N))) y IN u}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM] THEN ASM_MESON_TAC[FUN_IN_IMAGE];
      ALL_TAC] THEN
    MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
    EXISTS_TAC `euclidean:(real^N)topology` THEN ASM_REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFDD_CHART_CONTINUOUS THEN ASM_MESON_TAC[];
      REWRITE_TAC[GSYM OPEN_IN] THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)` THEN
      REWRITE_TAC[mfd_smooth; ETA_AX] THEN
      DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[IN_ELIM_THM];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]]);;

let GRGE_COMPACT_CHART_COVER = prove
 (`!top atlas C.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_in top C
        ==> ?F0. FINITE F0 /\ F0 SUBSET atlas /\
                 !x. x IN C ==> ?c. c IN F0 /\ x IN FST c`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [compact_in]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `IMAGE FST (atlas:((A->bool)#(A->real^N))->bool)`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; FST] THEN ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      EXISTS_TAC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
      MATCH_MP_TAC CHART_AT THEN EXISTS_TAC `top:A topology` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`FST:(A->bool)#(A->real^N)->A->bool`;
                 `atlas:((A->bool)#(A->real^N))->bool`; `V:(A->bool)->bool`]
                FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:((A->bool)#(A->real^N))->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `F0:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `C SUBSET UNIONS (V:(A->bool)->bool)` THEN
  ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN MESON_TAC[]);;

(* The cutoff chart map h = (chi phi, chi) of a chart (U,phi) and a cutoff  *)
(* chi with compact support L inside U is smooth on the whole manifold.     *)

let GRGE_CUTOFF_MAP_SMOOTH = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) (chi:A->real) L.
        hausdorff_space top /\
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        mfd_smooth atlas (\x. lift(chi x)) /\
        compact_in top L /\ L SUBSET U /\
        (!x. x IN topspace top DIFF L ==> chi x = &0)
        ==> mfd_smooth atlas (\x. pastecart (chi x % phi x) (lift(chi x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth; FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ open_in top (V:A->bool) /\
                open(IMAGE (psi:A->real^N) V)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (psi:A->real^N) V)
      (\z. lift((chi:A->real)(chart_inv (V,psi) z)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool)
                   (\x. lift((chi:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth] THEN
    DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND; o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (L:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_IMP_CLOSED_IN]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `chart_inv (V:A->bool,psi:A->real^N) y IN U` THENL
   [EXISTS_TAC `IMAGE (psi:A->real^N) (V INTER U)` THEN
    SUBGOAL_THEN `open(IMAGE (psi:A->real^N) (V INTER U))` ASSUME_TAC THENL
     [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `V:A->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv (V:A->bool,psi:A->real^N) y` THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC
     `\z. pastecart ((chi:A->real)(chart_inv (V:A->bool,psi:A->real^N) z) %
                     chart_trans (V,psi) (U:A->bool,phi:A->real^N) z)
                    (lift(chi(chart_inv (V,psi) z)))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[o_THM; chart_trans; SND]; ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (IMAGE (psi:A->real^N) (V INTER U))
        (\z. lift((chi:A->real)(chart_inv (V,psi) z)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GRGE_SMOOTH_SCALAR_MUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC CHART_TRANS_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (psi:A->real^N) (V INTER (topspace top DIFF L))` THEN
  SUBGOAL_THEN `open_in top (topspace top DIFF L:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[closed_in]; ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (psi:A->real^N) (V INTER (topspace top DIFF L)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `V:A->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_INTER; IN_DIFF] THEN
    EXISTS_TAC `chart_inv (V:A->bool,psi:A->real^N) y` THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `(\z. vec 0):real^N->real^(N,1)finite_sum` THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; IN_DIFF] THEN
  X_GEN_TAC `p:A` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[o_THM; IN_DIFF; VECTOR_MUL_LZERO; LIFT_NUM; PASTECART_VEC]);;

(* Where chi does not vanish, the cutoff chart map is immersive.            *)

let GRGE_CUTOFF_MAP_IMMERSIVE = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) (chi:A->real) c x v.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        mfd_smooth atlas (\x. lift(chi x)) /\
        c IN atlas /\ x IN FST c /\ x IN U /\ ~(chi x = &0) /\
        frechet_derivative ((\x. pastecart (chi x % phi x) (lift(chi x))) o
                            chart_inv c) (at (SND c x)) v = vec 0
        ==> v = vec 0`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `U:A->bool`; `phi:A->real^N`; `chi:A->real`;
                       `V:A->bool`; `psi:A->real^N`; `x:A`; `v:real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (psi:A->real^N) V)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `chart_inv (V:A->bool,psi:A->real^N) (psi(x:A)) = x /\
    chart_trans (V,psi) (U:A->bool,phi:A->real^N) (psi x) = phi x`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `a' = frechet_derivative
           (\z. lift((chi:A->real)(chart_inv (V:A->bool,psi:A->real^N) z)))
           (at (psi(x:A)))` THEN
  SUBGOAL_THEN
   `((\z. lift((chi:A->real)(chart_inv (V:A->bool,psi:A->real^N) z))) has_derivative
     (a':real^N->real^1)) (at (psi(x:A)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "a'" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool)
                   (\x. lift((chi:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth] THEN
    DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND; o_DEF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`; `U:A->bool`; `phi:A->real^N`; `x:A`]
                CHART_TRANS_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`at(psi(x:A)):(real^N)net`;
    `\z. (chi:A->real)(chart_inv (V:A->bool,psi:A->real^N) z) %
         chart_trans (V,psi) (U:A->bool,phi:A->real^N) z`;
    `\z. lift((chi:A->real)(chart_inv (V:A->bool,psi:A->real^N) z))`;
    `\h. (chi:A->real) x %
         chart_jac (V:A->bool,psi:A->real^N) (U:A->bool,phi:A->real^N) x h +
         drop((a':real^N->real^1) h) % (phi:A->real^N) x`;
    `a':real^N->real^1`] HAS_DERIVATIVE_PASTECART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\z. (chi:A->real)(chart_inv (V:A->bool,psi:A->real^N) z)`;
                   `drop o (a':real^N->real^1)`;
                   `chart_trans (V:A->bool,psi:A->real^N) (U:A->bool,phi:A->real^N)`;
                   `chart_jac (V:A->bool,psi:A->real^N) (U:A->bool,phi:A->real^N)
                              (x:A)`;
                   `psi(x:A):real^N`] HAS_DERIVATIVE_MUL_AT) THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\z. pastecart ((chi:A->real)(chart_inv (V:A->bool,psi:A->real^N) z) %
                    chart_trans (V,psi) (U:A->bool,phi:A->real^N) z)
                   (lift(chi(chart_inv (V,psi) z)))) =
    (\x. pastecart (chi x % phi x) (lift(chi x))) o chart_inv (V,psi)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; chart_trans; SND]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(fun th ->
    UNDISCH_TAC
     `frechet_derivative
        ((\x. pastecart ((chi:A->real) x % (phi:A->real^N) x) (lift(chi x))) o
         chart_inv (V:A->bool,psi:A->real^N)) (at (psi(x:A))) (v:real^N) = vec 0` THEN
    REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[PASTECART_EQ_VEC] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `(chi:A->real) x %
    chart_jac (V:A->bool,psi:A->real^N) (U:A->bool,phi:A->real^N) x v +
    drop((a':real^N->real^1) v) % (phi:A->real^N) x = vec 0` THEN
  ASM_REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_EQ_0] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`; `U:A->bool`; `phi:A->real^N`; `x:A`]
                CHART_JAC_INVERSE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x:A`]
                CHART_JAC_LINEAR) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP LINEAR_0) THEN
  DISCH_THEN(MP_TAC o C AP_THM `v:real^N`) THEN
  ASM_REWRITE_TAC[o_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The generic perturbation step: given a smooth f that is injective and    *)
(* immersive "jointly with h" on a compact set D, a generic matrix B makes   *)
(* f + B h injective and immersive on D.  The bad matrices form finitely     *)
(* many negligible sets (GRGE_BAD_NEGLIGIBLE, with 2 n < K).                 *)
(* ------------------------------------------------------------------------- *)

let GRGE_PERTURB_SMOOTH = prove
 (`!top atlas (f:A->real^K) (h:A->real^P) (B:real^P^K).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_smooth atlas f /\ mfd_smooth atlas h
        ==> mfd_smooth atlas (\x. f x + B ** h x) /\
            !c y v. c IN atlas /\ y IN IMAGE (SND c) (FST c)
                    ==> frechet_derivative ((\x. f x + B ** h x) o chart_inv c)
                                           (at y) v =
                        frechet_derivative (f o chart_inv c) (at y) v +
                        B ** frechet_derivative (h o chart_inv c) (at y) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!c:(A->bool)#(A->real^N).
        (\x. (f:A->real^K) x + (B:real^P^K) ** (h:A->real^P) x) o chart_inv c =
        (\y. (f o chart_inv c) y + ((\z. B ** z) o (h o chart_inv c)) y)`
  ASSUME_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c:(A->bool)#(A->real^N).
        c IN atlas
        ==> open(IMAGE (SND c) (FST c)) /\
            smooth_map_on (IMAGE (SND c) (FST c)) ((f:A->real^K) o chart_inv c) /\
            smooth_map_on (IMAGE (SND c) (FST c)) ((h:A->real^P) o chart_inv c)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mfd_smooth]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_smooth] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `B:real^P^K` MATRIX_VECTOR_MUL_LINEAR) THEN REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `y:real^N`; `v:real^N`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))) has_derivative
     frechet_derivative (f o chart_inv c) (at y)) (at y) /\
    (((h:A->real^P) o chart_inv c) has_derivative
     frechet_derivative (h o chart_inv c) (at y)) (at y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))`;
    `frechet_derivative ((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))) (at y)`;
    `(\z. (B:real^P^K) ** z) o ((h:A->real^P) o chart_inv (c:(A->bool)#(A->real^N)))`;
    `(\z. (B:real^P^K) ** z) o
     frechet_derivative ((h:A->real^P) o chart_inv (c:(A->bool)#(A->real^N))) (at y)`;
    `at (y:real^N)`] HAS_DERIVATIVE_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[o_THM]);;

let GRGE_SMOOTH_PCROSS_FST = prove
 (`!s t (g:real^N->real^M).
        open s /\ open t /\ smooth_map_on s g
        ==> smooth_map_on (s PCROSS t) (\p:real^(N,N)finite_sum. g(fstcart p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\p:real^(N,N)finite_sum. (g:real^N->real^M)(fstcart p)) = g o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[OPEN_PCROSS] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
    SIMP_TAC[];
    MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_SIMP_TAC[OPEN_PCROSS; LINEAR_FSTCART]]);;

let GRGE_SMOOTH_PCROSS_SND = prove
 (`!s t (g:real^N->real^M).
        open s /\ open t /\ smooth_map_on t g
        ==> smooth_map_on (s PCROSS t) (\p:real^(N,N)finite_sum. g(sndcart p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\p:real^(N,N)finite_sum. (g:real^N->real^M)(sndcart p)) = g o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_SIMP_TAC[OPEN_PCROSS] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
    SIMP_TAC[];
    MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_SIMP_TAC[OPEN_PCROSS; LINEAR_SNDCART]]);;

let GRGE_PAIR_BAD_NEGLIGIBLE = prove
 (`!top atlas (f:A->real^K) (h:A->real^(N,1)finite_sum) a b.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_smooth atlas f /\ mfd_smooth atlas h /\ a IN atlas /\ b IN atlas /\
        2 * dimindex(:N) < dimindex(:K)
        ==> negligible
              {B:real^(K,(N,1)finite_sum)finite_prod |
               ?x1 x2. x1 IN FST a /\ x2 IN FST b /\ ~(h x1 = h x2) /\
                       (matrify B:real^(N,1)finite_sum^K) ** (h x1 - h x2) +
                       (f x1 - f x2) = vec 0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `b:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a))
                  ((f:A->real^K) o chart_inv a) /\
    smooth_map_on (IMAGE (SND(b:(A->bool)#(A->real^N))) (FST b))
                  ((f:A->real^K) o chart_inv b) /\
    smooth_map_on (IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a))
                  ((h:A->real^(N,1)finite_sum) o chart_inv a) /\
    smooth_map_on (IMAGE (SND(b:(A->bool)#(A->real^N))) (FST b))
                  ((h:A->real^(N,1)finite_sum) o chart_inv b)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[mfd_smooth]) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\p:real^(N,N)finite_sum.
       (f:A->real^K)(chart_inv (a:(A->bool)#(A->real^N)) (fstcart p)) -
       f(chart_inv (b:(A->bool)#(A->real^N)) (sndcart p))`;
    `\p:real^(N,N)finite_sum.
       (h:A->real^(N,1)finite_sum)(chart_inv (a:(A->bool)#(A->real^N)) (fstcart p)) -
       h(chart_inv (b:(A->bool)#(A->real^N)) (sndcart p))`;
    `IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a) PCROSS
     IMAGE (SND(b:(A->bool)#(A->real^N))) (FST b)`] GRGE_BAD_NEGLIGIBLE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; DIMINDEX_FINITE_SUM] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_SIMP_TAC[OPEN_PCROSS] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a)`;
                       `IMAGE (SND(b:(A->bool)#(A->real^N))) (FST b)`;
                       `(f:A->real^K) o chart_inv (a:(A->bool)#(A->real^N))`]
                      GRGE_SMOOTH_PCROSS_FST);
        MP_TAC(ISPECL [`IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a)`;
                       `IMAGE (SND(b:(A->bool)#(A->real^N))) (FST b)`;
                       `(f:A->real^K) o chart_inv (b:(A->bool)#(A->real^N))`]
                      GRGE_SMOOTH_PCROSS_SND)] THEN
      ASM_REWRITE_TAC[o_THM];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_SIMP_TAC[OPEN_PCROSS] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a)`;
                       `IMAGE (SND(b:(A->bool)#(A->real^N))) (FST b)`;
                       `(h:A->real^(N,1)finite_sum) o chart_inv (a:(A->bool)#(A->real^N))`]
                      GRGE_SMOOTH_PCROSS_FST);
        MP_TAC(ISPECL [`IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a)`;
                       `IMAGE (SND(b:(A->bool)#(A->real^N))) (FST b)`;
                       `(h:A->real^(N,1)finite_sum) o chart_inv (b:(A->bool)#(A->real^N))`]
                      GRGE_SMOOTH_PCROSS_SND)] THEN
      ASM_REWRITE_TAC[o_THM];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `B:real^(K,(N,1)finite_sum)finite_prod` THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:A` (X_CHOOSE_THEN `x2:A` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `pastecart (SND(a:(A->bool)#(A->real^N)) x1)
                        (SND(b:(A->bool)#(A->real^N)) x2)` THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_SUB_EQ;
               PASTECART_IN_PCROSS; FUN_IN_IMAGE]);;

let GRGE_DERIV_BAD_NEGLIGIBLE = prove
 (`!top atlas (f:A->real^K) (h:A->real^(N,1)finite_sum) a.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_smooth atlas f /\ mfd_smooth atlas h /\ a IN atlas /\
        2 * dimindex(:N) < dimindex(:K)
        ==> negligible
              {B:real^(K,(N,1)finite_sum)finite_prod |
               ?y v. y IN IMAGE (SND a) (FST a) /\
                     ~(frechet_derivative (h o chart_inv a) (at y) v = vec 0) /\
                     (matrify B:real^(N,1)finite_sum^K) **
                     frechet_derivative (h o chart_inv a) (at y) v +
                     frechet_derivative (f o chart_inv a) (at y) v = vec 0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a))
                  ((f:A->real^K) o chart_inv a) /\
    smooth_map_on (IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a))
                  ((h:A->real^(N,1)finite_sum) o chart_inv a)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[mfd_smooth]) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a)`;
                 `(f:A->real^K) o chart_inv (a:(A->bool)#(A->real^N))`]
                GRGE_SMOOTH_DERIV_APPLY) THEN
  MP_TAC(ISPECL [`IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a)`;
                 `(h:A->real^(N,1)finite_sum) o chart_inv (a:(A->bool)#(A->real^N))`]
                GRGE_SMOOTH_DERIV_APPLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\p:real^(N,N)finite_sum.
       frechet_derivative ((f:A->real^K) o chart_inv (a:(A->bool)#(A->real^N)))
                          (at (fstcart p)) (sndcart p)`;
    `\p:real^(N,N)finite_sum.
       frechet_derivative ((h:A->real^(N,1)finite_sum) o
                           chart_inv (a:(A->bool)#(A->real^N)))
                          (at (fstcart p)) (sndcart p)`;
    `{p:real^(N,N)finite_sum |
      fstcart p IN IMAGE (SND(a:(A->bool)#(A->real^N))) (FST a)}`]
   GRGE_BAD_NEGLIGIBLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `B:real^(K,(N,1)finite_sum)finite_prod` THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `pastecart (y:real^N) (v:real^N)` THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]);;

let GRGE_NEGLIGIBLE_AVOID = prove
 (`!s:real^N->bool. negligible s ==> ?x. ~(x IN s)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `s = (:real^N)` SUBST1_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[NOT_NEGLIGIBLE_UNIV]]);;

let GRGE_CHART_JAC_INJ = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c' x v.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
        x IN FST c /\ x IN FST c' /\ chart_jac c c' x v = vec 0
        ==> v = vec 0`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                       `x:A`; `v:real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x:A`]
                CHART_JAC_INVERSE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`; `U:A->bool`; `phi:A->real^N`; `x:A`]
                CHART_JAC_LINEAR) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP LINEAR_0) THEN
  DISCH_THEN(MP_TAC o C AP_THM `v:real^N`) THEN
  ASM_REWRITE_TAC[o_THM] THEN MESON_TAC[]);;

let GRGE_GOOD_MATRIX_EXISTS = prove
 (`!top atlas (f:A->real^K) (h:A->real^(N,1)finite_sum) F0.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_smooth atlas f /\ mfd_smooth atlas h /\
        FINITE F0 /\ F0 SUBSET atlas /\ 2 * dimindex(:N) < dimindex(:K)
        ==> ?B:real^(N,1)finite_sum^K.
              (!a b x1 x2. a IN F0 /\ b IN F0 /\ x1 IN FST a /\ x2 IN FST b /\
                           ~(h x1 = h x2)
                           ==> ~(B ** (h x1 - h x2) + (f x1 - f x2) = vec 0)) /\
              (!a y v. a IN F0 /\ y IN IMAGE (SND a) (FST a) /\
                       ~(frechet_derivative (h o chart_inv a) (at y) v = vec 0)
                       ==> ~(B ** frechet_derivative (h o chart_inv a) (at y) v +
                             frechet_derivative (f o chart_inv a) (at y) v = vec 0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `negligible
     (UNIONS {{B:real^(K,(N,1)finite_sum)finite_prod |
               ?x1 x2. x1 IN FST a /\ x2 IN FST b /\
                       ~((h:A->real^(N,1)finite_sum) x1 = h x2) /\
                       (matrify B:real^(N,1)finite_sum^K) ** (h x1 - h x2) +
                       ((f:A->real^K) x1 - f x2) = vec 0} |
              (a:(A->bool)#(A->real^N)) IN F0 /\ (b:(A->bool)#(A->real^N)) IN F0} UNION
      UNIONS {{B:real^(K,(N,1)finite_sum)finite_prod |
               ?y v. y IN IMAGE (SND a) (FST a) /\
                     ~(frechet_derivative (h o chart_inv a) (at y) v = vec 0) /\
                     (matrify B:real^(N,1)finite_sum^K) **
                     frechet_derivative (h o chart_inv a) (at y) v +
                     frechet_derivative (f o chart_inv a) (at y) v = vec 0} |
              (a:(A->bool)#(A->real^N)) IN F0})`
  MP_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`a:(A->bool)#(A->real^N)`; `b:(A->bool)#(A->real^N)`] THEN
      STRIP_TAC THEN MATCH_MP_TAC GRGE_PAIR_BAD_NEGLIGIBLE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_MESON_TAC[SUBSET];
      REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `a:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MATCH_MP_TAC GRGE_DERIV_BAD_NEGLIGIBLE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP GRGE_NEGLIGIBLE_AVOID) THEN
  DISCH_THEN(X_CHOOSE_THEN `B0:real^(K,(N,1)finite_sum)finite_prod` MP_TAC) THEN
  REWRITE_TAC[IN_UNION; IN_UNIONS; EXISTS_IN_GSPEC; IN_ELIM_THM; DE_MORGAN_THM] THEN
  STRIP_TAC THEN EXISTS_TAC `matrify B0:real^(N,1)finite_sum^K` THEN
  ASM_MESON_TAC[]);;

let GRGE_PERTURB_STEP = prove
 (`!top atlas (f:A->real^K) (h:A->real^(N,1)finite_sum) D.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        2 * dimindex(:N) < dimindex(:K) /\
        mfd_smooth atlas f /\ mfd_smooth atlas h /\ compact_in top D /\
        (!x y. x IN D /\ y IN D /\ h x = h y /\ f x = f y ==> x = y) /\
        (!c x v. c IN atlas /\ x IN D /\ x IN FST c /\
                 frechet_derivative (h o chart_inv c) (at (SND c x)) v = vec 0 /\
                 frechet_derivative (f o chart_inv c) (at (SND c x)) v = vec 0
                 ==> v = vec 0)
        ==> ?B:real^(N,1)finite_sum^K.
              mfd_smooth atlas (\x. f x + B ** h x) /\
              (!x y. x IN D /\ y IN D /\ f x + B ** h x = f y + B ** h y ==> x = y) /\
              (!c x v. c IN atlas /\ x IN D /\ x IN FST c /\
                       frechet_derivative ((\x. f x + B ** h x) o chart_inv c)
                                          (at (SND c x)) v = vec 0
                       ==> v = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> EVERY (map2 LABEL_TAC
    ["SMA"; "DIM"; "SMF"; "SMH"; "CPT"; "INJ"; "IMM"] (CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `D:A->bool`]
                GRGE_COMPACT_CHART_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:((A->bool)#(A->real^N))->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "COV")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `h:A->real^(N,1)finite_sum`;
                 `F0:((A->bool)#(A->real^N))->bool`] GRGE_GOOD_MATRIX_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^(N,1)finite_sum^K`
    (CONJUNCTS_THEN2 (LABEL_TAC "G1") (LABEL_TAC "G2"))) THEN
  EXISTS_TAC `B:real^(N,1)finite_sum^K` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `h:A->real^(N,1)finite_sum`;
                 `B:real^(N,1)finite_sum^K`] GRGE_PERTURB_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DER")) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x1:A`; `x2:A`] THEN STRIP_TAC THEN
    USE_THEN "INJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      USE_THEN "COV" (MP_TAC o C MATCH_MP (ASSUME `(x1:A) IN D`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `a:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC) THEN
      USE_THEN "COV" (MP_TAC o C MATCH_MP (ASSUME `(x2:A) IN D`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `b:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC) THEN
      USE_THEN "G1" (MP_TAC o SPECL [`a:(A->bool)#(A->real^N)`;
                                     `b:(A->bool)#(A->real^N)`; `x1:A`; `x2:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(f:A->real^K) x1 + (B:real^(N,1)finite_sum^K) ** h x1 =
                   f x2 + B ** h x2` THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN VECTOR_ARITH_TAC;
      DISCH_TAC THEN
      UNDISCH_TAC `(f:A->real^K) x1 + (B:real^(N,1)finite_sum^K) ** h x1 =
                   f x2 + B ** h x2` THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `x:A`; `v:real^N`] THEN STRIP_TAC THEN
  USE_THEN "COV" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN D`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:(A->bool)#(A->real^N)) IN atlas` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\x:A. (f:A->real^K) x + (B:real^(N,1)finite_sum^K) **
                        (h:A->real^(N,1)finite_sum) x`;
                 `c:(A->bool)#(A->real^N)`; `a:(A->bool)#(A->real^N)`; `x:A`]
                GRGE_CHART_DERIV_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(fun th ->
    UNDISCH_TAC
     `frechet_derivative
        ((\x:A. (f:A->real^K) x + (B:real^(N,1)finite_sum^K) **
                (h:A->real^(N,1)finite_sum) x) o chart_inv (c:(A->bool)#(A->real^N)))
        (at (SND c (x:A))) (v:real^N) = vec 0` THEN
    REWRITE_TAC[th; o_THM]) THEN
  ABBREV_TAC `w = chart_jac (c:(A->bool)#(A->real^N)) a (x:A) v` THEN
  SUBGOAL_THEN `SND(a:(A->bool)#(A->real^N)) (x:A) IN IMAGE (SND a) (FST a)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  USE_THEN "DER" (MP_TAC o SPECL [`a:(A->bool)#(A->real^N)`;
                                  `SND(a:(A->bool)#(A->real^N)) (x:A)`; `w:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `w:real^N = vec 0` ASSUME_TAC THENL
   [ASM_CASES_TAC
     `frechet_derivative ((h:A->real^(N,1)finite_sum) o
                          chart_inv (a:(A->bool)#(A->real^N))) (at (SND a (x:A)))
                         w = vec 0` THENL
     [USE_THEN "IMM" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`a:(A->bool)#(A->real^N)`; `x:A`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `frechet_derivative ((f:A->real^K) o chart_inv (a:(A->bool)#(A->real^N)))
                           (at (SND a (x:A))) w +
        (B:real^(N,1)finite_sum^K) **
        frechet_derivative ((h:A->real^(N,1)finite_sum) o chart_inv a)
                           (at (SND a x)) w = vec 0` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; VECTOR_ADD_RID];
      USE_THEN "G2" (MP_TAC o SPECL [`a:(A->bool)#(A->real^N)`;
                                     `SND(a:(A->bool)#(A->real^N)) (x:A)`; `w:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC GRGE_CHART_JAC_INJ THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `c:(A->bool)#(A->real^N)`; `a:(A->bool)#(A->real^N)`; `x:A`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Whitney step with the cutoff chart map, the induction over finitely   *)
(* many chart cutoffs, and MFD_EMBEDDING_EXISTS (Lee ISM 2nd ed., the        *)
(* compact Whitney embedding theorem, Thm 6.15, by the "easy" chart          *)
(* construction followed by generic linear perturbation, Thm 6.14).          *)
(* ------------------------------------------------------------------------- *)

let GRGE_WHITNEY_STEP = prove
 (`!top atlas (f:A->real^K) C Kc (U:A->bool) (phi:A->real^N) (chi:A->real) L.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        2 * dimindex(:N) < dimindex(:K) /\
        mfd_smooth atlas f /\ compact_in top C /\
        (!x y. x IN C /\ y IN C /\ f x = f y ==> x = y) /\
        (!c x v. c IN atlas /\ x IN C /\ x IN FST c /\
                 frechet_derivative (f o chart_inv c) (at (SND c x)) v = vec 0
                 ==> v = vec 0) /\
        (U,phi) IN atlas /\ mfd_smooth atlas (\x. lift(chi x)) /\
        compact_in top Kc /\ (!x. x IN Kc ==> chi x = &1) /\
        compact_in top L /\ L SUBSET U /\
        (!x. x IN topspace top DIFF L ==> chi x = &0)
        ==> ?f':A->real^K. mfd_smooth atlas f' /\
                 (!x y. x IN C UNION Kc /\ y IN C UNION Kc /\ f' x = f' y ==> x = y) /\
                 (!c x v. c IN atlas /\ x IN C UNION Kc /\ x IN FST c /\
                          frechet_derivative (f' o chart_inv c) (at (SND c x)) v = vec 0
                          ==> v = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> EVERY (map2 LABEL_TAC
    ["HAU"; "SMA"; "DIM"; "SMF"; "CC"; "INJC"; "IMMC"; "UA"; "SCHI"; "CK";
     "CHI1"; "CL"; "LU"; "CHI0"] (CONJUNCTS th))) THEN
  SUBGOAL_THEN `C UNION Kc SUBSET topspace top /\ compact_in top (C UNION Kc:A->bool)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IN_UNION THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[COMPACT_IN_SUBSET_TOPSPACE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`;
                 `\x:A. pastecart ((chi:A->real) x % (phi:A->real^N) x) (lift(chi x))`;
                 `C UNION Kc:A->bool`] GRGE_PERTURB_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC GRGE_CUTOFF_MAP_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `U:A->bool`; `L:A->bool`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x1:A`; `x2:A`] THEN
      REWRITE_TAC[PASTECART_INJ; LIFT_EQ] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x1:A) IN topspace top /\ (x2:A) IN topspace top` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `C UNION Kc SUBSET topspace (top:A topology)` THEN
        UNDISCH_TAC `(x1:A) IN C UNION Kc` THEN UNDISCH_TAC `(x2:A) IN C UNION Kc` THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `(chi:A->real) x1 = &0` THENL
       [SUBGOAL_THEN `(chi:A->real) x2 = &0` ASSUME_TAC THENL
         [UNDISCH_TAC `(chi:A->real) x1 = chi x2` THEN ASM_REWRITE_TAC[] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `~((x1:A) IN Kc) /\ ~((x2:A) IN Kc)` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN DISCH_TAC THENL
           [USE_THEN "CHI1" (MP_TAC o C MATCH_MP (ASSUME `(x1:A) IN Kc`));
            USE_THEN "CHI1" (MP_TAC o C MATCH_MP (ASSUME `(x2:A) IN Kc`))] THEN
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        USE_THEN "INJC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(x1:A) IN C UNION Kc` THEN UNDISCH_TAC `(x2:A) IN C UNION Kc` THEN
        ASM_REWRITE_TAC[IN_UNION] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~((chi:A->real) x2 = &0)` ASSUME_TAC THENL
       [UNDISCH_TAC `(chi:A->real) x1 = chi x2` THEN
        UNDISCH_TAC `~((chi:A->real) x1 = &0)` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(x1:A) IN U /\ (x2:A) IN U` STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `(x1:A) IN L /\ (x2:A) IN L` MP_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THENL
           [UNDISCH_TAC `~((chi:A->real) x1 = &0)`;
            UNDISCH_TAC `~((chi:A->real) x2 = &0)`] THEN
          REWRITE_TAC[] THEN USE_THEN "CHI0" MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[IN_DIFF];
          UNDISCH_TAC `(L:A->bool) SUBSET U` THEN SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(phi:A->real^N) x1 = phi x2` ASSUME_TAC THENL
       [UNDISCH_TAC `(chi:A->real) x1 % (phi:A->real^N) x1 = chi x2 % phi x2` THEN
        UNDISCH_TAC `(chi:A->real) x1 = chi x2` THEN DISCH_THEN SUBST1_TAC THEN
        ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `x1:A` th) THEN MP_TAC(SPEC `x2:A` th)) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `x:A`; `v:real^N`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
       [UNDISCH_TAC `C UNION Kc SUBSET topspace (top:A topology)` THEN
        UNDISCH_TAC `(x:A) IN C UNION Kc` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `(chi:A->real) x = &0` THENL
       [SUBGOAL_THEN `(x:A) IN C` ASSUME_TAC THENL
         [UNDISCH_TAC `(x:A) IN C UNION Kc` THEN REWRITE_TAC[IN_UNION] THEN
          MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
          USE_THEN "CHI1" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN Kc`)) THEN
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        USE_THEN "IMMC" MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`c:(A->bool)#(A->real^N)`; `x:A`] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:A) IN U` ASSUME_TAC THENL
       [SUBGOAL_THEN `(x:A) IN L` MP_TAC THENL
         [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
          UNDISCH_TAC `~((chi:A->real) x = &0)` THEN REWRITE_TAC[] THEN
          USE_THEN "CHI0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
          UNDISCH_TAC `(L:A->bool) SUBSET U` THEN SET_TAC[]];
        ALL_TAC] THEN
      MATCH_MP_TAC GRGE_CUTOFF_MAP_IMMERSIVE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `U:A->bool`; `phi:A->real^N`; `chi:A->real`;
                            `c:(A->bool)#(A->real^N)`; `x:A`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real^(N,1)finite_sum^K`) THEN
  EXISTS_TAC `\x:A. (f:A->real^K) x +
                    (B:real^(N,1)finite_sum^K) **
                    pastecart ((chi:A->real) x % (phi:A->real^N) x) (lift(chi x))` THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[]);;

let GRGE_EMBED_ON_FINITE = prove
 (`!top atlas (U:A->A->bool) (phi:A->A->real^N) (chi:A->A->real) Kc L.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        2 * dimindex(:N) < dimindex(:K)
        ==> !t. FINITE t
                ==> (!x. x IN t
                         ==> (U x,phi x) IN atlas /\
                             mfd_smooth atlas (\y. lift(chi x y)) /\
                             compact_in top (Kc x) /\ (!y. y IN Kc x ==> chi x y = &1) /\
                             compact_in top (L x) /\ L x SUBSET U x /\
                             (!y. y IN topspace top DIFF L x ==> chi x y = &0))
                ==> ?f:A->real^K.
                      mfd_smooth atlas f /\
                      (!x y. x IN UNIONS (IMAGE Kc t) /\ y IN UNIONS (IMAGE Kc t) /\
                             f x = f y ==> x = y) /\
                      (!c x v. c IN atlas /\ x IN UNIONS (IMAGE Kc t) /\ x IN FST c /\
                               frechet_derivative (f o chart_inv c) (at (SND c x)) v =
                               vec 0
                               ==> v = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `(\x. vec 0):A->real^K` THEN
    REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; NOT_IN_EMPTY] THEN
    REWRITE_TAC[mfd_smooth; o_DEF; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  DISCH_THEN(LABEL_TAC "DATA") THEN
  REMOVE_THEN "IH" MP_TAC THEN ANTS_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN USE_THEN "DATA" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real^K` STRIP_ASSUME_TAC) THEN
  USE_THEN "DATA" (MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `UNIONS (IMAGE (Kc:A->A->bool) s)`;
                 `(Kc:A->A->bool) a`; `(U:A->A->bool) a`; `(phi:A->A->real^N) a`;
                 `(chi:A->A->real) a`; `(L:A->A->bool) a`] GRGE_WHITNEY_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_IN_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "DATA" (MP_TAC o SPEC `x:A`) THEN REWRITE_TAC[IN_INSERT] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (IMAGE (Kc:A->A->bool) (a INSERT s)) = UNIONS (IMAGE Kc s) UNION Kc a`
  SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[]);;

let GRGE_LOCAL_CUTOFF = prove
 (`!top atlas (x:A).
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        x IN topspace top
        ==> ?U phi chi W Kc L.
              (U,phi) IN atlas /\ mfd_smooth atlas (\y. lift(chi y)) /\
              open_in top W /\ x IN W /\ W SUBSET Kc /\ compact_in top Kc /\
              (!y. y IN Kc ==> chi y = &1) /\
              compact_in top L /\ L SUBSET U /\
              (!y. y IN topspace top DIFF L ==> chi y = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `topspace top:A->bool`; `x:A`] MFDC_LOCAL_BALL) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `cball((phi:A->real^N) x,r) SUBSET IMAGE phi U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((phi:A->real^N) x,&2 * r)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER topspace top)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Kc = {p:A | p IN U /\ (phi:A->real^N) p IN cball(phi x,r)}` THEN
  SUBGOAL_THEN `compact_in top (Kc:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN MATCH_MP_TAC MFDC_CHART_COMPACT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Kc:A->bool`; `U:A->bool`] MFD_SMOOTH_CUTOFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Kc" THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:A->real` (X_CHOOSE_THEN `V:A->bool`
    (X_CHOOSE_THEN `L:A->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`; `chi:A->real`;
                        `{p:A | p IN U /\ (phi:A->real^N) p IN ball(phi x,r)}`;
                        `Kc:A->bool`; `L:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDC_CHART_BALL_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL];
    EXPAND_TAC "Kc" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
    ASM_MESON_TAC[SUBSET]]);;

let GRGE_IMMERSION_FROM_CHARTS = prove
 (`!top atlas (f:A->real^K).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_smooth atlas f /\
        (!c x v. c IN atlas /\ x IN FST c /\
                 frechet_derivative (f o chart_inv c) (at (SND c x)) v = vec 0
                 ==> v = vec 0)
        ==> smooth_immersion_into atlas f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IMM"))) THEN
  REWRITE_TAC[smooth_immersion_into] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN DISCH_TAC THEN
  EXISTS_TAC `(f:A->real^K) o chart_inv (U:A->bool,phi:A->real^N)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)` THEN
    REWRITE_TAC[mfd_smooth] THEN
    DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND];
    ASM_SIMP_TAC[o_THM];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "IMM" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(U:A->bool,phi:A->real^N)`; `x:A`] THEN
    ASM_REWRITE_TAC[FST; SND]]);;

let GRGE_EMBEDDING_FROM_INJECTIVE = prove
 (`!top atlas (f:A->real^K).
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_space top /\ mfd_smooth atlas f /\
        (!x y. x IN topspace top /\ y IN topspace top /\ f x = f y ==> x = y) /\
        (!c x v. c IN atlas /\ x IN FST c /\
                 frechet_derivative (f o chart_inv c) (at (SND c x)) v = vec 0
                 ==> v = vec 0)
        ==> mfd_embedding (top,atlas) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_embedding] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GRGE_IMMERSION_FROM_CHARTS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (top,subtopology euclidean (IMAGE (f:A->real^K) (topspace top))) f`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_INTO_SUBTOPOLOGY THEN REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC GRGE_MFD_SMOOTH_CONTINUOUS THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC BIJECTIVE_CLOSED_IMP_HOMEOMORPHIC_MAP THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_CLOSED_MAP THEN
    ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN];
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV];
    ASM_MESON_TAC[]]);;

let MFD_EMBEDDING_EXISTS = prove
 (`!top atlas.
     hausdorff_space top /\
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     compact_space top /\ 2 * dimindex(:N) + 1 <= dimindex(:K)
     ==> ?f:A->real^K. mfd_embedding (top,atlas) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                GRGE_LOCAL_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->A->bool` (X_CHOOSE_THEN `phi:A->A->real^N`
    (X_CHOOSE_THEN `chi:A->A->real` (X_CHOOSE_THEN `W:A->A->bool`
    (X_CHOOSE_THEN `Kc:A->A->bool` (X_CHOOSE_THEN `L:A->A->bool`
    (LABEL_TAC "LOC"))))))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_SPACE_ALT]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (W:A->A->bool) (topspace top)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    USE_THEN "LOC" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`W:A->A->bool`; `topspace top:A->bool`; `V:(A->bool)->bool`]
                FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->A->bool`; `phi:A->A->real^N`; `chi:A->A->real`;
                 `Kc:A->A->bool`; `L:A->A->bool`] GRGE_EMBED_ON_FINITE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:A->bool`) THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "LOC" (MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[SUBSET]; STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real^K` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "FINJ") (LABEL_TAC "FIMM")))) THEN
  SUBGOAL_THEN `topspace top SUBSET UNIONS (IMAGE (Kc:A->A->bool) t)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS (IMAGE (W:A->A->bool) t)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `p:A` THEN DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q:A` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "LOC" (MP_TAC o SPEC `q:A`) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[SUBSET]; STRIP_TAC THEN ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  EXISTS_TAC `f:A->real^K` THEN MATCH_MP_TAC GRGE_EMBEDDING_FROM_INJECTIVE THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "FINJ" MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
    MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `x:A`; `v:real^N`] THEN
    STRIP_TAC THEN USE_THEN "FIMM" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`c:(A->bool)#(A->real^N)`; `x:A`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:A) IN topspace top` (fun th -> ASM_MESON_TAC[th; SUBSET]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]]);;

