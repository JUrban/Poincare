(* ========================================================================= *)
(* pc_mfd_embmetric: the adapted ambient metric of a compact embedded        *)
(* manifold.                                                                 *)
(* MFD_EMBED_AMBIENT_METRIC: a smooth positive definite field G on           *)
(* real^K whose pullback by f is g, for which tangent and normal spaces of   *)
(* f(M) are G-orthogonal with G the identity on normals, with uniform        *)
(* eigenvalue bounds on f(M), and constant along the normal fibres near      *)
(* f(M).  G = psi (G0 o r) + (1 - psi) I with G0 = Q^T g Q + (I - J Q) for   *)
(* the pseudo-inverse Q = (J^T J)^-1 J^T, r the smooth retraction of the     *)
(* tube and psi a cutoff.  MFD_EMBED_GRAM: the Gram matrices of f o u for    *)
(* G are the chart Gram matrices of u for g.                                 *)
(* ========================================================================= *)

needs "src/pc_mfd_tube.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Matrix algebra of the adapted metric G0(J,g) = Q^T g Q + (I - J Q), with  *)
(* Q = (J^T J)^-1 J^T for an injective J.                                    *)
(* ------------------------------------------------------------------------- *)

let GRGE_PINV_LEFT = prove
 (`!J:real^N^K.
        (!v. J ** v = vec 0 ==> v = vec 0)
        ==> (matrix_inv(transp J ** J) ** transp J) ** J = mat 1`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP GRGE_GRAM_INVERTIBLE) THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_SIMP_TAC[MATRIX_INV]);;

let GRGE_PINV_RMUL = prove
 (`!(J:real^N^K) (S:real^N^N).
        (!v. J ** v = vec 0 ==> v = vec 0) /\ invertible S
        ==> matrix_inv(transp(J ** S) ** (J ** S)) ** transp(J ** S) =
            matrix_inv S ** (matrix_inv(transp J ** J) ** transp J)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP GRGE_GRAM_INVERTIBLE) THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL] THEN
  SUBGOAL_THEN
   `(transp(S:real^N^N) ** transp(J:real^N^K)) ** J ** S =
    transp S ** ((transp J ** J) ** S)`
  SUBST1_TAC THENL [REWRITE_TAC[MATRIX_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_TRANSP; INVERTIBLE_MATRIX_MUL] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; INVERTIBLE_TRANSP; MATRIX_MUL_LID]);;

let GRGE_G0_PULLBACK = prove
 (`!(J:real^N^K) (g:real^N^N).
        (!v. J ** v = vec 0 ==> v = vec 0)
        ==> transp J **
            (transp(matrix_inv(transp J ** J) ** transp J) ** g **
             (matrix_inv(transp J ** J) ** transp J) +
             (mat 1 - J ** (matrix_inv(transp J ** J) ** transp J))) ** J = g`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GRGE_PINV_LEFT) THEN
  ABBREV_TAC `Q = matrix_inv(transp(J:real^N^K) ** J) ** transp J` THEN
  SUBGOAL_THEN `!x. (Q:real^K^N) ** (J:real^N^K) ** x = x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. transp(J:real^N^K) ** transp(Q:real^K^N) ** x = x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL; TRANSP_MAT;
                    MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_EQ; GSYM MATRIX_VECTOR_MUL_ASSOC;
              MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
              MATRIX_VECTOR_MUL_LID] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_ADD_RID; MATRIX_VECTOR_MUL_RZERO]);;

let GRGE_G0_NORMAL_FIX = prove
 (`!(J:real^N^K) (g:real^N^N) v.
        (!v. J ** v = vec 0 ==> v = vec 0)
        ==> (transp(matrix_inv(transp J ** J) ** transp J) ** g **
             (matrix_inv(transp J ** J) ** transp J) +
             (mat 1 - J ** (matrix_inv(transp J ** J) ** transp J))) **
            ((mat 1 - J ** (matrix_inv(transp J ** J) ** transp J)) ** v) =
            (mat 1 - J ** (matrix_inv(transp J ** J) ** transp J)) ** v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GRGE_PINV_LEFT) THEN
  ABBREV_TAC `Q = matrix_inv(transp(J:real^N^K) ** J) ** transp J` THEN
  SUBGOAL_THEN `!x. (Q:real^K^N) ** (J:real^N^K) ** x = x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID;
              MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; MATRIX_VECTOR_MUL_RZERO] THEN VECTOR_ARITH_TAC);;

let GRGE_G0_SYM = prove
 (`!(J:real^N^K) (g:real^N^N).
        (!v. J ** v = vec 0 ==> v = vec 0) /\ transp g = g
        ==> transp(transp(matrix_inv(transp J ** J) ** transp J) ** g **
                   (matrix_inv(transp J ** J) ** transp J) +
                   (mat 1 - J ** (matrix_inv(transp J ** J) ** transp J))) =
            transp(matrix_inv(transp J ** J) ** transp J) ** g **
            (matrix_inv(transp J ** J) ** transp J) +
            (mat 1 - J ** (matrix_inv(transp J ** J) ** transp J))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP GRGE_PROJ_PROPS) THEN
  REWRITE_TAC[TRANSP_MATRIX_ADD; TRANSP_MATRIX_SUB; TRANSP_MAT; MATRIX_TRANSP_MUL;
              TRANSP_TRANSP] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[MATRIX_MUL_ASSOC]);;

let GRGE_G0_POS = prove
 (`!(J:real^N^K) (g:real^N^N) v.
        (!v. J ** v = vec 0 ==> v = vec 0) /\
        (!w. ~(w = vec 0) ==> &0 < w dot (g ** w)) /\ ~(v = vec 0)
        ==> &0 < v dot
                 ((transp(matrix_inv(transp J ** J) ** transp J) ** g **
                   (matrix_inv(transp J ** J) ** transp J) +
                   (mat 1 - J ** (matrix_inv(transp J ** J) ** transp J))) ** v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "GPOS") ASSUME_TAC))
      THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGE_PROJ_PROPS) THEN
  ABBREV_TAC `Q = matrix_inv(transp(J:real^N^K) ** J) ** transp J` THEN
  ABBREV_TAC `P = (J:real^N^K) ** (Q:real^K^N)` THEN
  SUBGOAL_THEN `(v:real^K) dot ((P:real^K^K) ** v) = (P ** v) dot (P ** v)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
              MATRIX_VECTOR_MUL_LID; DOT_RADD; DOT_RSUB; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN
  SUBGOAL_THEN `(J:real^N^K) ** (Q:real^K^N) ** v = P ** v` SUBST1_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((P:real^K^K) ** v) dot (P ** v) <= v dot v` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(v:real^K) - (P:real^K^K) ** v` DOT_POS_LE) THEN
    REWRITE_TAC[DOT_LSUB; DOT_RSUB] THEN
    MP_TAC(ISPECL [`(P:real^K^K) ** v`; `v:real^K`] DOT_SYM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(Q:real^K^N) ** v = vec 0` THENL
   [SUBGOAL_THEN `(P:real^K^K) ** v = vec 0` SUBST1_TAC THENL
     [EXPAND_TAC "P" THEN ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC;
                                          MATRIX_VECTOR_MUL_RZERO];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_LZERO; MATRIX_VECTOR_MUL_RZERO] THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_SUB_RZERO; DOT_POS_LT] THEN ASM_REWRITE_TAC[];
    USE_THEN "GPOS" (MP_TAC o C MATCH_MP (ASSUME `~((Q:real^K^N) ** v = vec 0)`)) THEN
    UNDISCH_TAC `((P:real^K^K) ** v) dot (P ** v) <= v dot v` THEN REAL_ARITH_TAC]);;

let GRGE_G0_CHART_INV = prove
 (`!(J:real^N^K) (S:real^N^N) (g:real^N^N).
        (!v. J ** v = vec 0 ==> v = vec 0) /\ invertible S
        ==> transp(matrix_inv(transp(J ** S) ** (J ** S)) ** transp(J ** S)) **
            (transp S ** g ** S) **
            (matrix_inv(transp(J ** S) ** (J ** S)) ** transp(J ** S)) +
            (mat 1 - (J ** S) **
                     (matrix_inv(transp(J ** S) ** (J ** S)) ** transp(J ** S))) =
            transp(matrix_inv(transp J ** J) ** transp J) ** g **
            (matrix_inv(transp J ** J) ** transp J) +
            (mat 1 - J ** (matrix_inv(transp J ** J) ** transp J))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GRGE_PINV_RMUL] THEN
  SUBGOAL_THEN `!x. (S:real^N^N) ** matrix_inv S ** x = x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. transp(matrix_inv(S:real^N^N)) ** transp S ** x = x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL; MATRIX_INV; TRANSP_MAT;
                 MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_EQ; MATRIX_TRANSP_MUL; GSYM MATRIX_VECTOR_MUL_ASSOC;
              MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
              MATRIX_VECTOR_MUL_LID] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MFD_EMBED_GRAM: Gram matrices of f o u for G are the chart Gram           *)
(* matrices of u for g, whenever G pulls back to g in every chart.          *)
(* ------------------------------------------------------------------------- *)

let MFD_EMBED_GRAM = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) (u:real^M->A) s y.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     riemannian_metric atlas g /\ smooth_immersion_into atlas f /\
     (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
            ==> metric_local atlas c g w =
                transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                G(f(chart_inv c w)) **
                matrix(frechet_derivative (f o chart_inv c) (at w))) /\
     open s /\ y IN s /\ continuous_map (subtopology euclidean s,top) u /\
     (\z. SND(chart_at atlas (u y)) (u z)) differentiable at y
     ==> transp(jacobian (f o u) (at y)) ** G(f(u y)) ** jacobian (f o u) (at y) =
         transp(jacobian (\z. SND(chart_at atlas (u y)) (u z)) (at y)) ** g(u y) **
         jacobian (\z. SND(chart_at atlas (u y)) (u z)) (at y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "PB") STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(u:real^M->A) y IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (is_comb o concl)) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(u:real^M->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((u:real^M->A) y)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `phi = \z:real^M. SND(c:(A->bool)#(A->real^N)) ((u:real^M->A) z)` THEN
  SUBGOAL_THEN
   `((phi:real^M->real^N) has_derivative frechet_derivative phi (at y)) (at y)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^M->real^N) y = SND(c:(A->bool)#(A->real^N)) ((u:real^M->A) y)`
  ASSUME_TAC THENL [EXPAND_TAC "phi" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))) has_derivative
     frechet_derivative (f o chart_inv c) (at (SND c ((u:real^M->A) y))))
    (at (SND c (u y)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {z | z IN s /\ (u:real^M->A) z IN FST(c:(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`u:real^M->A`; `subtopology euclidean (s:real^M->bool)`;
                   `top:A topology`; `FST(c:(A->bool)#(A->real^N))`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((f:A->real^K) o (u:real^M->A)) has_derivative
     (frechet_derivative (f o chart_inv (c:(A->bool)#(A->real^N)))
                         (at (SND c (u y))) o
      frechet_derivative (phi:real^M->real^N) (at y))) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))) o
                (phi:real^M->real^N)` THEN
    EXISTS_TAC `{z | z IN s /\ (u:real^M->A) z IN FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [EXPAND_TAC "phi" THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `jacobian ((f:A->real^K) o (u:real^M->A)) (at y) =
    matrix(frechet_derivative (f o chart_inv (c:(A->bool)#(A->real^N)))
                              (at (SND c (u y)))) **
    jacobian (phi:real^M->real^N) (at y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[jacobian] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o
      check (fun th -> can (find_term (fun t -> t = `(f:A->real^K) o (u:real^M->A)`))
                           (concl th))) THEN
    MATCH_MP_TAC MATRIX_COMPOSE THEN
    ASM_MESON_TAC[has_derivative];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; GSYM MATRIX_MUL_ASSOC] THEN AP_TERM_TAC THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  USE_THEN "PB" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`;
                                 `SND(c:(A->bool)#(A->real^N)) ((u:real^M->A) y)`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EXPAND_TAC "c" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A smooth cutoff on real^K and uniform bounds for a positive definite      *)
(* smooth quadratic form over a compact set.                                 *)
(* ------------------------------------------------------------------------- *)

let GRGE_EUCLID_CUTOFF = prove
 (`!k w:real^K->bool.
        compact k /\ open w /\ k SUBSET w
        ==> ?psi L. smooth_map_on (:real^K) (\z. lift(psi z)) /\
                    (!z. &0 <= psi z /\ psi z <= &1) /\
                    (!z. z IN k ==> psi z = &1) /\
                    compact L /\ L SUBSET w /\
                    (!z. ~(z IN L) ==> psi z = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^K)topology`; `open_set_atlas (:real^K)`;
                 `k:real^K->bool`; `w:real^K->bool`] MFD_SMOOTH_CUTOFF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN; COMPACT_IN_EUCLIDEAN; GSYM OPEN_IN] THEN
    MP_TAC(ISPEC `(:real^K)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^K->real` (X_CHOOSE_THEN `V:real^K->bool`
    (X_CHOOSE_THEN `L:real^K->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`psi:real^K->real`; `L:real^K->bool`] THEN
  ASM_REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `mfd_smooth (open_set_atlas (:real^K)) (\x. lift((psi:real^K->real) x))`
       THEN
    REWRITE_TAC[mfd_smooth; open_set_atlas; IN_SING; FORALL_UNWIND_THM2; FST; SND;
                IMAGE_ID] THEN
    DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `(\x. lift((psi:real^K->real) x)) o chart_inv((:real^K),(\x:real^K. x))` THEN
    ASM_SIMP_TAC[OPEN_UNIV; o_THM; GRGE_OPEN_SET_CHART_INV; IN_UNIV];
    ASM_MESON_TAC[SUBSET];
    X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_DIFF; IN_UNIV]]);;

let GRGE_QUADFORM_BOUNDS = prove
 (`!(G:real^K->real^K^K) k.
        smooth_map_on (:real^K) (vectorize o G) /\ compact k /\
        (!z v. z IN k /\ ~(v = vec 0) ==> &0 < v dot (G z ** v))
        ==> ?lam Lam. &0 < lam /\ lam <= Lam /\
                      !z v. z IN k
                            ==> lam * norm v pow 2 <= v dot (G z ** v) /\
                                v dot (G z ** v) <= Lam * norm v pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PD"))) THEN
  ASM_CASES_TAC `k:real^K->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`&1`; `&1`] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01; REAL_LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC
   `qf = \p:real^(K,K)finite_sum. sndcart p dot ((G:real^K->real^K^K)(fstcart p) ** sndcart
       p)` THEN
  SUBGOAL_THEN `smooth_map_on (:real^(K,K)finite_sum) (lift o
      (qf:real^(K,K)finite_sum->real))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qf" THEN REWRITE_TAC[o_DEF] THEN
    MP_TAC(ISPECL [`(:real^(K,K)finite_sum)`; `\x y:real^K. lift(x dot y)`;
                   `sndcart:real^(K,K)finite_sum->real^K`;
                   `\p:real^(K,K)finite_sum. (G:real^K->real^K^K)(fstcart p) ** sndcart p`]
                  SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; BILINEAR_DOT] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN REWRITE_TAC[OPEN_UNIV; LINEAR_SNDCART];
      ALL_TAC] THEN
    MATCH_MP_TAC GRGE_SMOOTH_MATVEC THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(vectorize:real^K^K->real^(K,K)finite_prod) o
        (\p:real^(K,K)finite_sum. (G:real^K->real^K^K)(fstcart p)) =
        (vectorize o G) o fstcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
      MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN REWRITE_TAC[OPEN_UNIV; LINEAR_FSTCART];
      MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN REWRITE_TAC[OPEN_UNIV; LINEAR_SNDCART]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(lift o (qf:real^(K,K)finite_sum->real)) continuous_on
                ((k:real^K->bool) PCROSS sphere(vec 0:real^K,&1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(K,K)finite_sum)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact((k:real^K->bool) PCROSS sphere(vec 0:real^K,&1)) /\
                ~((k:real^K->bool) PCROSS sphere(vec 0:real^K,&1) = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_SPHERE; PCROSS_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`qf:real^(K,K)finite_sum->real`;
                 `(k:real^K->bool) PCROSS sphere(vec 0:real^K,&1)`]
                CONTINUOUS_ATTAINS_INF) THEN
  MP_TAC(ISPECL [`qf:real^(K,K)finite_sum->real`;
                 `(k:real^K->bool) PCROSS sphere(vec 0:real^K,&1)`]
                CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^(K,K)finite_sum` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "SUP"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^(K,K)finite_sum` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "INF"))) THEN
  SUBGOAL_THEN
   `!z u. z IN k /\ norm(u:real^K) = &1
          ==> (qf:real^(K,K)finite_sum->real) p1 <= u dot ((G:real^K->real^K^K) z ** u) /\
              u dot (G z ** u) <= qf p2`
  (LABEL_TAC "UNIT") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `pastecart (z:real^K) (u:real^K) IN k PCROSS sphere(vec 0:real^K,&1)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_SPHERE_0]; ALL_TAC] THEN
    USE_THEN "INF" (MP_TAC o C MATCH_MP (ASSUME
      `pastecart (z:real^K) (u:real^K) IN k PCROSS sphere(vec 0:real^K,&1)`)) THEN
    USE_THEN "SUP" (MP_TAC o C MATCH_MP (ASSUME
      `pastecart (z:real^K) (u:real^K) IN k PCROSS sphere(vec 0:real^K,&1)`)) THEN
    EXPAND_TAC "qf" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (qf:real^(K,K)finite_sum->real) p1` ASSUME_TAC THENL
   [UNDISCH_TAC `(p1:real^(K,K)finite_sum) IN k PCROSS sphere(vec 0:real^K,&1)` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_SPHERE_0] THEN STRIP_TAC THEN
    EXPAND_TAC "qf" THEN USE_THEN "PD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `norm(sndcart(p1:real^(K,K)finite_sum)) = &1` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(qf:real^(K,K)finite_sum->real) p1`;
                        `(qf:real^(K,K)finite_sum->real) p2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "INF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:real^K`; `v:real^K`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `v:real^K = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; MATRIX_VECTOR_MUL_RZERO; DOT_LZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "UNIT" (MP_TAC o SPECL [`z:real^K`; `inv(norm(v:real^K)) % v`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `&0 < norm(v:real^K)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `n = norm(v:real^K)` THEN
  ABBREV_TAC `q = (v:real^K) dot ((G:real^K->real^K^K) z ** v)` THEN
  SUBGOAL_THEN `inv n * inv n * q = q / n pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_POW_2; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < n pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Smoothness of matrix sums and constants; G0 in a chart; the local tube    *)
(* data on a uniform tube.                                                   *)
(* ------------------------------------------------------------------------- *)

let GRGE_SMOOTH_MATADD = prove
 (`!s (A:real^M->real^P^Q) B.
        open s /\ smooth_map_on s (vectorize o A) /\ smooth_map_on s (vectorize o B)
        ==> smooth_map_on s (vectorize o (\z. A z + B z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(vectorize:real^P^Q->real^(Q,P)finite_prod) o (\z. (A:real^M->real^P^Q) z + B z) =
    (\z. (vectorize o A) z + (vectorize o B) z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_ADD]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[ETA_AX]);;

let GRGE_SMOOTH_MATSUB = prove
 (`!s (A:real^M->real^P^Q) B.
        open s /\ smooth_map_on s (vectorize o A) /\ smooth_map_on s (vectorize o B)
        ==> smooth_map_on s (vectorize o (\z. A z - B z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(vectorize:real^P^Q->real^(Q,P)finite_prod) o (\z. (A:real^M->real^P^Q) z - B z) =
    (\z. (vectorize o A) z - (vectorize o B) z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_SUB]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[ETA_AX]);;

let GRGE_SMOOTH_MATCONST = prove
 (`!s (C:real^P^Q). smooth_map_on (s:real^M->bool) (vectorize o (\z. C))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_CONST]);;

let GRGE_G0C_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) c.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        riemannian_metric atlas g /\ smooth_immersion_into atlas f /\ c IN atlas
        ==> smooth_map_on (IMAGE (SND c) (FST c))
             ((vectorize:real^K^K->real^(K,K)finite_prod) o
              (\y. transp(matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at
                  y))) **
                                     matrix(frechet_derivative (f o chart_inv c) (at y))) **
                          transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) **
                   metric_local atlas c g y **
                   (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at y)))
                       **
                               matrix(frechet_derivative (f o chart_inv c) (at y))) **
                    transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) +
                   (mat 1 - matrix(frechet_derivative (f o chart_inv c) (at y)) **
                            (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c)
                                                                         (at y))) **
                                        matrix(frechet_derivative (f o chart_inv c) (at
                                            y))) **
                             transp(matrix(frechet_derivative (f o chart_inv c) (at
                                 y)))))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `V = IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  ABBREV_TAC
   `Jc = \y:real^N. matrix(frechet_derivative ((f:A->real^K) o
                                chart_inv (c:(A->bool)#(A->real^N))) (at y))` THEN
  SUBGOAL_THEN
   `!y. matrix(frechet_derivative ((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N)))
                                  (at y)) = (Jc:real^N->real^N^K) y`
  (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "Jc" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on V ((vectorize:real^N^K->real^(K,N)finite_prod) o
      (Jc:real^N->real^N^K))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Jc" THEN MATCH_MP_TAC GRGE_SMOOTH_JACOBIAN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on V ((vectorize:real^K^N->real^(N,K)finite_prod) o
                     (\y. transp((Jc:real^N->real^N^K) y)))`
  ASSUME_TAC THENL [MATCH_MP_TAC GRGE_SMOOTH_TRANSP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     (\y. matrix_inv(transp((Jc:real^N->real^N^K) y) ** Jc y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM INVERTIBLE_DET_NZ] THEN MATCH_MP_TAC GRGE_GRAM_INVERTIBLE THEN
      X_GEN_TAC `v:real^N` THEN EXPAND_TAC "Jc" THEN
      SUBGOAL_THEN
       `linear(frechet_derivative ((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N)))
                                  (at (y:real^N)))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[MATRIX_WORKS] THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on V ((vectorize:real^K^N->real^(N,K)finite_prod) o
                     (\y. matrix_inv(transp((Jc:real^N->real^N^K) y) ** Jc y) **
                          transp(Jc y)))`
  ASSUME_TAC THENL [MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on V ((vectorize:real^N^K->real^(K,N)finite_prod) o
                     (\y. transp(matrix_inv(transp((Jc:real^N->real^N^K) y) ** Jc y) **
                                 transp(Jc y))))`
  ASSUME_TAC THENL [MATCH_MP_TAC GRGE_SMOOTH_TRANSP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     metric_local (atlas:((A->bool)#(A->real^N))->bool) c (g:A->real^N^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)`
       THEN
    REWRITE_TAC[riemannian_metric; metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GRGE_SMOOTH_MATADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC GRGE_SMOOTH_MATSUB THEN ASM_REWRITE_TAC[GRGE_SMOOTH_MATCONST] THEN
    MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[ETA_AX]]);;

let GRGE_G0_CHART_EQ = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G0:A->real^K^K)
    (G0c:(A->bool)#(A->real^N)->real^N->real^K^K) c y.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_immersion_into atlas f /\ c IN atlas /\ y IN IMAGE (SND c) (FST c) /\
        (!x. G0 x =
             transp(matrix_inv(transp(mfd_emb_jac atlas f x) ** mfd_emb_jac atlas f x) **
                    transp(mfd_emb_jac atlas f x)) ** g x **
             (matrix_inv(transp(mfd_emb_jac atlas f x) ** mfd_emb_jac atlas f x) **
              transp(mfd_emb_jac atlas f x)) +
             (mat 1 - mfd_tproj atlas f x)) /\
        (!c y. G0c c y =
               transp(matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at
                   y))) **
                                 matrix(frechet_derivative (f o chart_inv c) (at y))) **
                      transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) **
               metric_local atlas c g y **
               (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at y))) **
                           matrix(frechet_derivative (f o chart_inv c) (at y))) **
                transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) +
               (mat 1 - matrix(frechet_derivative (f o chart_inv c) (at y)) **
                        (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c)
                                                                     (at y))) **
                                    matrix(frechet_derivative (f o chart_inv c) (at y))) **
                         transp(matrix(frechet_derivative (f o chart_inv c) (at y))))))
        ==> G0(chart_inv c y) = G0c c y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) (fun th -> REWRITE_TAC[th])))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `chart_inv (c:(A->bool)#(A->real^N)) y IN FST c /\ SND c (chart_inv c y) = y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[metric_local; mfd_tproj] THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) y` THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^N)) (x:A) = y` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`; `x:A`] GRGE_EMB_JAC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC GRGE_G0_CHART_INV THEN ASM_REWRITE_TAC[]);;

let GRGE_TUBE_LOCZ = prove
 (`!top atlas (f:A->real^K).
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_space top /\ mfd_embedding (top,atlas) f
        ==> ?d. &0 < d /\
                !z. (?p. p IN IMAGE f (topspace top) /\ dist(z,p) < d)
                    ==> ?B c (Y:real^K->real^N).
                          open B /\ z IN B /\ c IN atlas /\ smooth_map_on B Y /\
                          (!z. z IN B
                               ==> Y z IN IMAGE (SND c) (FST c) /\
                                   closest_point (IMAGE f (topspace top)) z =
                                   f(chart_inv c (Y z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`] GRGE_TUBE_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UNI"))) THEN
  EXISTS_TAC `&2 * d` THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^K` THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^K`
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE])
                     ASSUME_TAC)) THEN
  USE_THEN "UNI" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN topspace top`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^K->bool` (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)`
    (X_CHOOSE_THEN `Y:real^K->real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`B:real^K->bool`; `c:(A->bool)#(A->real^N)`;
                        `Y:real^K->real^N`] THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `ball((f:A->real^K) x,&2 * d) SUBSET B` THEN
  REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* MFD_EMBED_AMBIENT_METRIC: the adapted ambient metric.                     *)
(* ------------------------------------------------------------------------- *)

let MFD_EMBED_AMBIENT_METRIC = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K).
     hausdorff_space top /\
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     compact_space top /\ riemannian_metric atlas g /\ mfd_embedding (top,atlas) f
     ==> ?G:real^K->real^K^K.
           smooth_map_on (:real^K) (vectorize o G) /\
           (!z. transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
           (!c y. c IN atlas /\ y IN IMAGE (SND c) (FST c)
                  ==> metric_local atlas c g y =
                      transp(matrix(frechet_derivative (f o chart_inv c) (at y))) **
                      G(f(chart_inv c y)) **
                      matrix(frechet_derivative (f o chart_inv c) (at y))) /\
           (!x u v. x IN topspace top
                    ==> (mfd_tproj atlas f x ** u) dot
                        (G(f x) ** ((mat 1 - mfd_tproj atlas f x) ** v)) = &0 /\
                        ((mat 1 - mfd_tproj atlas f x) ** u) dot
                        (G(f x) ** ((mat 1 - mfd_tproj atlas f x) ** v)) =
                        ((mat 1 - mfd_tproj atlas f x) ** u) dot
                        ((mat 1 - mfd_tproj atlas f x) ** v)) /\
           (?lam Lam. &0 < lam /\ lam <= Lam /\
                      !x v. x IN topspace top
                            ==> lam * norm v pow 2 <= v dot (G(f x) ** v) /\
                                v dot (G(f x) ** v) <= Lam * norm v pow 2) /\
           (?d. &0 < d /\
                !x z. x IN topspace top /\ dist(z,f x) < d /\
                      closest_point (IMAGE f (topspace top)) z = f x
                      ==> G z = G(f x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_immersion_into (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[mfd_embedding]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[GRGE_IMMERSION_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (f:A->real^K) (topspace top))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[GSYM compact_space] THEN
    MATCH_MP_TAC GRGE_MFD_SMOOTH_CONTINUOUS THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`] GRGE_TUBE_LOCZ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LOCZ"))) THEN
  ABBREV_TAC
   `G0 = \x:A. transp(matrix_inv(transp(mfd_emb_jac atlas f x) ** mfd_emb_jac atlas f x) **
                      transp(mfd_emb_jac atlas f x)) ** (g:A->real^N^N) x **
               (matrix_inv(transp(mfd_emb_jac atlas f x) ** mfd_emb_jac atlas f x) **
                transp(mfd_emb_jac (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) x)) +
               (mat 1 - mfd_tproj atlas f x)` THEN
  SUBGOAL_THEN
   `!x. (G0:A->real^K^K) x =
        transp(matrix_inv(transp(mfd_emb_jac atlas f x) ** mfd_emb_jac atlas f x) **
               transp(mfd_emb_jac atlas f x)) ** (g:A->real^N^N) x **
        (matrix_inv(transp(mfd_emb_jac atlas f x) ** mfd_emb_jac atlas f x) **
         transp(mfd_emb_jac (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) x)) +
        (mat 1 - mfd_tproj atlas f x)`
  (LABEL_TAC "G0DEF") THENL [EXPAND_TAC "G0" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `G0c = \(c:(A->bool)#(A->real^N)) (y:real^N).
      transp(matrix_inv(transp(matrix(frechet_derivative ((f:A->real^K) o chart_inv c) (at
          y))) **
                        matrix(frechet_derivative (f o chart_inv c) (at y))) **
             transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) **
      metric_local (atlas:((A->bool)#(A->real^N))->bool) c (g:A->real^N^N) y **
      (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at y))) **
                  matrix(frechet_derivative (f o chart_inv c) (at y))) **
       transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) +
      (mat 1 - matrix(frechet_derivative (f o chart_inv c) (at y)) **
               (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at y))) **
                           matrix(frechet_derivative (f o chart_inv c) (at y))) **
                transp(matrix(frechet_derivative (f o chart_inv c) (at y)))))` THEN
  SUBGOAL_THEN
   `!c y. (G0c:(A->bool)#(A->real^N)->real^N->real^K^K) c y =
      transp(matrix_inv(transp(matrix(frechet_derivative ((f:A->real^K) o chart_inv c) (at
          y))) **
                        matrix(frechet_derivative (f o chart_inv c) (at y))) **
             transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) **
      metric_local (atlas:((A->bool)#(A->real^N))->bool) c (g:A->real^N^N) y **
      (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at y))) **
                  matrix(frechet_derivative (f o chart_inv c) (at y))) **
       transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) +
      (mat 1 - matrix(frechet_derivative (f o chart_inv c) (at y)) **
               (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at y))) **
                           matrix(frechet_derivative (f o chart_inv c) (at y))) **
                transp(matrix(frechet_derivative (f o chart_inv c) (at y)))))`
  (LABEL_TAC "G0CDEF") THENL [EXPAND_TAC "G0c" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c y. c IN atlas /\ y IN IMAGE (SND c) (FST c)
          ==> (G0:A->real^K^K)(chart_inv c y) =
              (G0c:(A->bool)#(A->real^N)->real^N->real^K^K) c y`
  (LABEL_TAC "CHEQ") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GRGE_G0_CHART_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `f:A->real^K`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "G0DEF" ACCEPT_TAC; USE_THEN "G0CDEF" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> transp((G0:A->real^K^K) x) = G0 x /\
            (!v. ~(v = vec 0) ==> &0 < v dot (G0 x ** v)) /\
            (!v. G0 x ** ((mat 1 - mfd_tproj (atlas:((A->bool)#(A->real^N))->bool)
                                              (f:A->real^K) x) ** v) =
                 (mat 1 - mfd_tproj atlas f x) ** v)`
  (LABEL_TAC "G0X") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`;
                   `x:A`] GRGE_EMB_JAC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] RIEMANNIAN_METRIC_POS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "G0DEF" (fun th -> REWRITE_TAC[th; mfd_tproj]) THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC GRGE_G0_SYM THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC GRGE_G0_POS THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN MATCH_MP_TAC GRGE_G0_NORMAL_FIX THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "G0DEF" (K ALL_TAC) THEN REMOVE_THEN "G0CDEF" (K ALL_TAC) THEN
  ABBREV_TAC
   `r = \z:real^K. mfd_emb_inv top (f:A->real^K) (closest_point (IMAGE f (topspace top))
       z)` THEN
  SUBGOAL_THEN
   `!z. (?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d)
        ==> (r:real^K->A) z IN topspace top`
  (LABEL_TAC "RT") THENL
   [X_GEN_TAC `z:real^K` THEN
    DISCH_THEN(fun th -> USE_THEN "LOCZ" (MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real^K->bool` (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)`
      (X_CHOOSE_THEN `Y:real^K->real^N` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(z:real^K) IN B`)) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^K->real^N) z) IN topspace
        top`
    ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    EXPAND_TAC "r" THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^K->real^N)
                       z)`]
                  GRGE_EMB_INV_LEFT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top ==> (r:real^K->A) ((f:A->real^K) x) = x`
  (LABEL_TAC "RF") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "r" THEN
    SUBGOAL_THEN `closest_point (IMAGE (f:A->real^K) (topspace top)) (f x) = f x`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSEST_POINT_SELF THEN ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    MATCH_MP_TAC GRGE_EMB_INV_LEFT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Td = {z:real^K | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) <
      d}` THEN
  SUBGOAL_THEN `open(Td:real^K->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Td" THEN REWRITE_TAC[GRGE_TUBE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on Td ((vectorize:real^K^K->real^(K,K)finite_prod) o
                      (\z. (G0:A->real^K^K) ((r:real^K->A) z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^K` THEN EXPAND_TAC "Td" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> USE_THEN "LOCZ" (MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real^K->bool` (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)`
      (X_CHOOSE_THEN `Y:real^K->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BP")))))))) THEN
    EXISTS_TAC `B:real^K->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `((vectorize:real^K^K->real^(K,K)finite_prod) o
                 (G0c:(A->bool)#(A->real^N)->real^N->real^K^K) c) o (Y:real^K->real^N)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^K` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
      USE_THEN "BP" (MP_TAC o C MATCH_MP (ASSUME `(w:real^K) IN B`)) THEN STRIP_TAC THEN
      SUBGOAL_THEN `(r:real^K->A) w = chart_inv (c:(A->bool)#(A->real^N))
          ((Y:real^K->real^N) w)`
      SUBST1_TAC THENL
       [EXPAND_TAC "r" THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGE_EMB_INV_LEFT THEN
        EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
        ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "CHEQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^K` THEN DISCH_TAC THEN
        USE_THEN "BP" (MP_TAC o C MATCH_MP (ASSUME `(w:real^K) IN B`)) THEN SIMP_TAC[];
        EXPAND_TAC "G0c" THEN REWRITE_TAC[] THEN MATCH_MP_TAC GRGE_G0C_SMOOTH THEN
        EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{p + w | p IN IMAGE (f:A->real^K) (topspace top) /\ w IN cball(vec 0:real^K,d / &2)}`;
    `Td:real^K->bool`] GRGE_EUCLID_CUTOFF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
      EXPAND_TAC "Td" THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM; IN_CBALL_0]
          THEN
      MAP_EVERY X_GEN_TAC [`p:real^K`; `w:real^K`] THEN STRIP_TAC THEN
      EXISTS_TAC `p:real^K` THEN
      ASM_REWRITE_TAC[NORM_ARITH `dist(p + w:real^N,p) = norm w`] THEN
      UNDISCH_TAC `norm(w:real^K) <= d / &2` THEN UNDISCH_TAC `&0 < d` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^K->real` (X_CHOOSE_THEN `L:real^K->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "PSI01")
    (CONJUNCTS_THEN2 (LABEL_TAC "PSI1") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PSI0")))))))) THEN
  SUBGOAL_THEN
   `!x z. x IN topspace top /\ dist(z,(f:A->real^K) x) <= d / &2
          ==> (psi:real^K->real) z = &1`
  (LABEL_TAC "PSIN") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "PSI1" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0] THEN
    MAP_EVERY EXISTS_TAC [`(f:A->real^K) x`; `z - (f:A->real^K) x`] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM dist] THEN ASM_REWRITE_TAC[]; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `G = \z:real^K. (psi:real^K->real) z %% (G0:A->real^K^K) ((r:real^K->A) z) +
                   (&1 - psi z) %% mat 1` THEN
  SUBGOAL_THEN
   `!x. x IN topspace top ==> (G:real^K->real^K^K) ((f:A->real^K) x) = (G0:A->real^K^K) x`
  (LABEL_TAC "GFX") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(psi:real^K->real) ((f:A->real^K) x) = &1` SUBST1_TAC THENL
     [USE_THEN "PSIN" MATCH_MP_TAC THEN EXISTS_TAC `x:A` THEN
      ASM_REWRITE_TAC[DIST_REFL] THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "RF" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A) IN topspace top`)]) THEN
    REWRITE_TAC[REAL_SUB_REFL; MATRIX_CMUL_LZERO; MATRIX_CMUL_LID; MATRIX_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o
                                         (G:real^K->real^K^K))`
  (LABEL_TAC "GSM") THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `z0:real^K` THEN ASM_CASES_TAC `(z0:real^K) IN Td` THENL
     [EXISTS_TAC `Td:real^K->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K) =
        (\z. (psi:real^K->real) z %
             ((vectorize:real^K^K->real^(K,K)finite_prod) o
              (\z. (G0:A->real^K^K) ((r:real^K->A) z))) z +
             (&1 - psi z) % vectorize(mat 1:real^K^K))`
      SUBST1_TAC THENL
       [EXPAND_TAC "G" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_ADD; VECTORIZE_CMUL];
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      MATCH_MP_TAC GRGE_SMOOTH_SCALAR_MUL THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; ETA_AX] THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
        ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      EXISTS_TAC `(:real^K) DIFF L` THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `(\z. vectorize(mat 1:real^K^K)):real^K->real^(K,K)finite_prod` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; o_THM] THEN X_GEN_TAC `w:real^K` THEN DISCH_TAC THEN
      AP_TERM_TAC THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
      USE_THEN "PSI0" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~((w:real^K) IN L)`)])
          THEN
      REWRITE_TAC[MATRIX_CMUL_LZERO; REAL_SUB_RZERO; MATRIX_CMUL_LID; MATRIX_ADD_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. transp((G:real^K->real^K^K) z) = G z /\
        !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)`
  (LABEL_TAC "GPD") THENL
   [X_GEN_TAC `z:real^K` THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `(psi:real^K->real) z = &0` THENL
     [ASM_REWRITE_TAC[MATRIX_CMUL_LZERO; REAL_SUB_RZERO; MATRIX_CMUL_LID; MATRIX_ADD_LID;
                      TRANSP_MAT; MATRIX_VECTOR_MUL_LID; DOT_POS_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^K) IN L` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(r:real^K->A) z IN topspace top` ASSUME_TAC THENL
     [USE_THEN "RT" MATCH_MP_TAC THEN
      SUBGOAL_THEN `(z:real^K) IN Td` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "Td" THEN REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    USE_THEN "G0X" (MP_TAC o C MATCH_MP (ASSUME `(r:real^K->A) z IN topspace top`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "POS") (K ALL_TAC)))
        THEN
    ASM_REWRITE_TAC[TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL; TRANSP_MAT] THEN
    X_GEN_TAC `v:real^K` THEN DISCH_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID;
                DOT_RADD; DOT_RMUL] THEN
    USE_THEN "PSI01" (STRIP_ASSUME_TAC o SPEC `z:real^K`) THEN
    SUBGOAL_THEN `&0 < (psi:real^K->real) z` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "POS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[DOT_POS_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `G:real^K->real^K^K` THEN
  CONJ_TAC THENL [USE_THEN "GSM" ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "GPD" ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `y:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    USE_THEN "GFX" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `chart_inv (c:(A->bool)#(A->real^N)) y IN topspace top`)]) THEN
    USE_THEN "CHEQ" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ
      (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`)
      (ASSUME `(y:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`))]) THEN
    EXPAND_TAC "G0c" THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC GRGE_G0_PULLBACK THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `linear(frechet_derivative ((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N)))
                                (at (y:real^N)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `u:real^K`; `v:real^K`] THEN DISCH_TAC THEN
    USE_THEN "GFX" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A) IN topspace top`)])
        THEN
    USE_THEN "G0X" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN topspace top`)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2 th)]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `x:A`] MFD_TPROJ) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_SUB_LDISTRIB; MATRIX_MUL_RID;
                    MATRIX_SUB_REFL; MATRIX_VECTOR_MUL_LZERO; DOT_RZERO] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`G:real^K->real^K^K`; `IMAGE (f:A->real^K) (topspace top)`]
                  GRGE_QUADFORM_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "GPD" (fun th -> MATCH_MP_TAC(CONJUNCT2(SPEC `z:real^K` th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`lam:real`; `Lam:real`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  EXISTS_TAC `d / &2` THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `z:real^K`] THEN STRIP_TAC THEN
  USE_THEN "GFX" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A) IN topspace top`)]) THEN
  EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(psi:real^K->real) z = &1` SUBST1_TAC THENL
   [USE_THEN "PSIN" MATCH_MP_TAC THEN EXISTS_TAC `x:A` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^K->A) z = x` SUBST1_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGE_EMB_INV_LEFT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_REFL; MATRIX_CMUL_LZERO; MATRIX_CMUL_LID; MATRIX_ADD_RID]);;

